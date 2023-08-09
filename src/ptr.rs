//! Nullable raw pointer type.

use core::fmt;
use core::mem;
use core::mem::MaybeUninit;
use core::ptr;

use crate::offset;
use crate::offset::Offset;
use crate::NonNull;

/// A nullable raw pointer.
///
/// This type is intended as an improved version of `*mut T`, which provides
/// clearer methods for common operations on raw pointers.
///
/// Unlike Rust's raw pointers, this pointer type does not track mutability
/// (which is not deeply useful book-keeping on raw pointers).
///
/// ```
/// # use gep::*;
/// # #[derive(Default, PartialEq, Debug, Clone)]
/// struct Foo {
///   first: i32,
///   second: u64,
/// }
///
/// let data = vec![Foo::default(); 100];
/// let ptr = Ptr::from(data.as_ptr());
/// assert!(!ptr.is_null() && ptr.is_aligned());
///
/// unsafe {
///   ptr.at(42).write_at(gep::field!(Foo.first), -1);
///   ptr.at(42).write_at(gep::field!(Foo.second), 42);
/// }
///
/// assert_eq!(data[42], Foo { first: -1, second: 42 });
/// ```
///
/// # Unsized Types
///
/// Currently, `T: !Sized` is poorly supported (due to lack of good support on
/// `*mut T` itself). In particular, `Ptr<[T]>` should be separated into a
/// `Ptr<T>` and a `usize`, since there is no supported way to get the length
/// out.
#[repr(transparent)]
pub struct Ptr<T: ?Sized> {
  p: *mut T,
}

impl<T: ?Sized> PartialEq<Ptr<T>> for Ptr<T> {
  fn eq(&self, other: &Ptr<T>) -> bool {
    self.p == other.p
  }
}

impl<T: ?Sized> PartialEq<NonNull<T>> for Ptr<T> {
  fn eq(&self, other: &NonNull<T>) -> bool {
    self.p == other.to_raw()
  }
}

impl<T: ?Sized> Eq for Ptr<T> {}

impl<T: ?Sized> Clone for Ptr<T> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<T: ?Sized> Copy for Ptr<T> {}

impl<T: ?Sized> fmt::Debug for Ptr<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Debug::fmt(&self.p, f)
  }
}

impl<T: ?Sized> fmt::Pointer for Ptr<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Pointer::fmt(&self.p, f)
  }
}

impl<T: ?Sized> From<&T> for Ptr<T> {
  fn from(value: &T) -> Self {
    Self::new(value as *const T as *mut T)
  }
}

impl<T: ?Sized> From<&mut T> for Ptr<T> {
  fn from(value: &mut T) -> Self {
    Self::new(value)
  }
}

impl<T: ?Sized> From<*const T> for Ptr<T> {
  fn from(value: *const T) -> Self {
    Self::new(value as *mut T)
  }
}

impl<T: ?Sized> From<*mut T> for Ptr<T> {
  fn from(value: *mut T) -> Self {
    Self::new(value)
  }
}

impl<T: ?Sized> From<ptr::NonNull<T>> for Ptr<T> {
  fn from(value: ptr::NonNull<T>) -> Self {
    Self::new(value.as_ptr())
  }
}

impl<T: ?Sized> From<NonNull<T>> for Ptr<T> {
  fn from(value: NonNull<T>) -> Self {
    Self::new(value.to_raw())
  }
}

impl<T: ?Sized> From<Ptr<T>> for *const T {
  fn from(value: Ptr<T>) -> Self {
    value.to_raw()
  }
}

impl<T: ?Sized> From<Ptr<T>> for *mut T {
  fn from(value: Ptr<T>) -> Self {
    value.to_raw()
  }
}

impl<T: ?Sized> Ptr<T> {
  /// Constructs a new `Ptr` from a raw pointer or reference.
  pub const fn new(ptr: *mut T) -> Self {
    Ptr { p: ptr }
  }

  /// Constructs a new `Ptr` from a reference.
  ///
  /// # Safety
  ///
  /// This function is safe, but `Ptr`s created with it cannot be written
  /// through.
  pub const fn new_from_ref(ptr: &T) -> Self {
    Ptr {
      p: ptr as *const T as *mut T,
    }
  }

  /// Checks whether this pointer is null.
  ///
  /// ```
  /// # use gep::*;
  /// let x = 1997;
  /// assert!(!Ptr::from(&x).is_null());
  /// assert!(Ptr::<i32>::null().is_null());
  /// ```
  pub const fn is_null(self) -> bool {
    // <*const T>::is_null is not const yet for weird corner-case reasons. Miri
    // accepts this as a valid way to check for null, so at the very least
    // Hyrum's law is on our side. :D
    unsafe { mem::transmute::<*mut T, Option<NonNull<T>>>(self.p) }.is_none()
  }

  /// Extracts the underlying raw pointer.
  ///
  /// ```
  /// # use gep::*;
  /// # use std::ptr;
  /// let x = 1997;
  /// let p = Ptr::from(&x);
  /// assert!(ptr::eq(p.to_raw(), &x));
  /// ```
  pub const fn to_raw(self) -> *mut T {
    self.p
  }

  /// Returns this pointer's address.
  ///
  /// This operation discards provenance information, and any pointer created
  /// from this address value will be invalid.
  ///
  /// Compare [`<*mut T>::addr()`](https://doc.rust-lang.org/std/primitive.pointer.html#method.addr-1).
  pub fn addr(self) -> usize {
    self.p as *mut u8 as usize
  }

  /// Exposes this pointer's address.
  ///
  /// This operation discards provenance information, but allows a pointer to be
  /// reconstituted later with [`Ptr::from_exposed_addr()`].
  ///
  /// Compare [`<*mut T>::expose_addr()`](https://doc.rust-lang.org/std/primitive.pointer.html#method.expose_addr-1).
  pub fn expose_addr(self) -> usize {
    self.p as *mut u8 as usize
  }

  /// Converts this pointer into a [`NonNull`] pointer; returns `None` if this
  /// pointer is null.
  ///
  /// ```
  /// # use gep::*;
  /// let x = 1997;
  /// assert_eq!(
  ///   Ptr::from(&x).to_non_null(),
  ///   Some(NonNull::from(&x)),
  /// );
  /// 
  /// assert!(Ptr::<i32>::null().to_non_null().is_none());
  /// ```
  pub const fn to_non_null(self) -> Option<NonNull<T>> {
    if self.is_null() {
      return None;
    }
    unsafe { Some(self.to_non_null_unchecked()) }
  }

  /// Converts this non-null pointer into a [`NonNull`] pointer without
  /// checking.
  ///
  /// ```
  /// # use gep::*;
  /// let x = 1997;
  /// let p = Ptr::from(&x);
  /// 
  /// assert!(!p.is_null());
  /// assert_eq!(
  ///   unsafe { Ptr::from(&x).to_non_null_unchecked() },
  ///   NonNull::from(&x),
  /// );
  /// ```
  /// 
  /// # Safety
  ///
  /// [`Ptr::is_null()`] must return false for this pointer.
  pub const unsafe fn to_non_null_unchecked(self) -> NonNull<T> {
    debug_assert!(
      !self.is_null(),
      "attempted to convert a null pointer to NonNull<T>"
    );
    NonNull::new(ptr::NonNull::new_unchecked(self.p))
  }

  /// Casts this pointer to another type.
  ///
  /// Note that `U: Sized`, because creating a pointer to an unsized type
  /// requires extra metadata (and no stable API exists to do so yet).
  /// 
  /// ```
  /// # use gep::*;
  /// let x = -1;
  /// let y = unsafe {
  ///   Ptr::from(&x).cast::<u32>().read()
  /// };
  /// 
  /// assert_eq!(y, !0);
  /// ```
  pub const fn cast<U>(self) -> Ptr<U> {
    Ptr {
      p: self.p as *mut U,
    }
  }

  /// Dereferences this pointer, producing a reference.
  ///
  /// This function takes `&self`, to avoid creating an unbound lifetime in the
  /// common case.
  ///
  /// ```
  /// # use gep::*;
  /// let x = -1;
  /// let p = Ptr::from(&x).cast::<u32>();
  /// 
  /// assert_eq!(unsafe { p.deref() }, &!0);
  /// ```
  /// 
  /// # Safety
  ///
  /// This operation is equivalent to dereferencing a raw pointer. The following
  /// is an incomplete list of requirements:
  ///
  /// `self` must be non-null, well-aligned, and refer to memory appropriately
  /// initialized for `T`; also, it must not create a reference that aliases any
  /// active `&mut U`.
  pub const unsafe fn deref(&self) -> &T {
    self.deref_unbound()
  }

  /// Dereferences this pointer, producing a reference.
  ///
  /// Unlike [`Ptr::deref()`], this function can produce unbound references.
  ///
  /// # Safety
  ///
  /// This operation is equivalent to dereferencing a raw pointer. The following
  /// is an incomplete list of requirements:
  ///
  /// `self` must be non-null, well-aligned, and refer to memory appropriately
  /// initialized for `T`; also, it must not create a reference that aliases any
  /// active `&mut U`.
  pub const unsafe fn deref_unbound<'a>(self) -> &'a T {
    if cfg!(debug_assertions) {
      // <*mut T>::is_null is not const-stable yet, so we cheat with a little
      // transmute.
      match mem::transmute::<*mut T, Option<&T>>(self.p) {
        Some(r) => return r,
        None => panic!("attempted to deref null pointer"),
      }
    }

    &*(self.p as *const T)
  }

  /// Dereferences this pointer, producing a mutable reference.
  ///
  /// This function takes `&mut self`, to avoid creating an unbound lifetime in
  /// the common case.
  ///
  /// ```
  /// # use gep::*;
  /// let mut x = 0;
  /// let p = Ptr::from(&mut x).cast::<u32>();
  /// *unsafe { p.deref_mut() } = !0;
  /// 
  /// assert_eq!(x, -1);
  /// ```
  /// 
  /// # Safety
  ///
  /// This operation is equivalent to dereferencing a raw pointer. The following
  /// is an incomplete list of requirements:
  ///
  /// `self` must be non-null, well-aligned, and refer to memory appropriately
  /// initialized for `T`; also, it must not create a reference that aliases any
  /// active `&mut U`.
  pub unsafe fn deref_mut(&self) -> &mut T {
    self.deref_mut_unbound()
  }

  /// Dereferences this pointer, producing a reference.
  ///
  /// Unlike [`Ptr::deref_mut()`], this function can produce unbound references.
  ///
  /// # Safety
  ///
  /// This operation is equivalent to dereferencing a raw pointer. The following
  /// is an incomplete list of requirements:
  ///
  /// `self` must be non-null, well-aligned, and refer to memory appropriately
  /// initialized for `T`; also, it must not create a reference that aliases any
  /// active `&mut U`.
  pub unsafe fn deref_mut_unbound<'a>(self) -> &'a mut T {
    debug_assert!(!self.is_null(), "attempted to deref null pointer");
    &mut *self.p
  }

  /// Destroys the pointed-to value; equivalent to [`std::ptr::drop_in_place()`].
  ///
  /// ```
  /// # use gep::*;
  /// # use std::cell::Cell;
  /// struct Handle<'a>(&'a Cell<i32>);
  /// impl<'a> Handle<'a> {
  ///   fn new(c: &'a Cell<i32>) -> Self {
  ///     c.set(c.get() + 1);
  ///     Self(c)
  ///   }
  /// }
  /// 
  /// impl Drop for Handle<'_> {
  ///   fn drop(&mut self) {
  ///     self.0.set(self.0.get() - 1);
  ///   }
  /// }
  /// 
  /// let counter = Cell::new(0);
  /// let mut handle = Handle::new(&counter);
  /// 
  /// assert_eq!(counter.get(), 1);
  /// 
  /// let p = Ptr::from(&mut handle);
  /// unsafe {
  ///   p.destroy();
  ///   p.write(Handle::new(&counter));
  /// }
  /// 
  /// assert_eq!(counter.get(), 1);
  /// ```
  /// 
  /// Tip: given a `Ptr<T>`, you can destroy an array of `n` of them with
  /// `ptr.to_slice(n).destroy()`.
  /// 
  /// # Safety
  ///
  /// This operation is equivalent to dereferencing a raw pointer. The following
  /// is an incomplete list of requirements:
  ///
  /// `self` must be valid for reading and writing, properly aligned, and properly
  /// initialized. See [`std::ptr::drop_in_place()`] for more information.
  pub unsafe fn destroy(self) {
    debug_assert!(!self.is_null(), "attempted to destroy null pointer");
    self.p.drop_in_place()
  }
}

impl<T> Ptr<T> {
  /// Creates a new null pointer.
  pub const fn null() -> Self {
    Ptr::invalid(0)
  }

  /// Creates a new, non-null, dangling pointer.
  /// 
  /// ```
  /// # use gep::*;
  /// assert_ne!(Ptr::<i32>::null(), Ptr::<i32>::dangling());
  /// ```
  pub const fn dangling() -> Self {
    Ptr::invalid(mem::align_of::<T>())
  }

  /// Creates a pointer with the given address and the "invalid" provenance.
  ///
  /// Compare [`std::ptr::invalid()`].
  pub const fn invalid(addr: usize) -> Self {
    Ptr { p: addr as *mut T }
  }

  /// Reconstitutes a pointer using an address previously constructed with
  /// [`Ptr::expose_addr()`].
  ///
  /// ```
  /// # use gep::*;
  /// const KEY: usize = 0xf0f0f0f0f0f0f0f0;
  /// 
  /// let x = 1997;
  /// let p = Ptr::from(&x);
  /// let addr = p.expose_addr() ^ KEY;
  /// 
  /// let q = Ptr::<i32>::from_exposed_addr(addr ^ KEY);
  /// assert_eq!(p, q);
  /// ```
  /// 
  /// Compare [`std::ptr::from_exposed_addr()`].
  pub const fn from_exposed_addr(addr: usize) -> Self {
    Ptr { p: addr as *mut T }
  }

  /// Creates a new pointer with the given address using the provenance
  /// information from `self`.
  ///
  /// Compare [`<*mut T>::with_addr()`](https://doc.rust-lang.org/std/primitive.pointer.html#method.with_addr-1).
  pub fn with_addr(self, addr: usize) -> Ptr<T> {
    let off = (addr as isize).wrapping_sub(self.addr() as isize);
    unsafe { self.at(offset::NotInBounds(offset::ByteOffset(off))) }
  }

  /// Transforms the address of `self` while preserving its provenance.
  ///
  /// This is a convenience wrapper over [`Ptr::with_addr()`].
  pub fn map_addr(self, f: impl FnOnce(usize) -> usize) -> Self {
    self.with_addr(f(self.addr()))
  }

  /// Returns whether this pointer is appropriately aligned for its type.
  /// 
  /// ```
  /// # use gep::*;
  /// # use gep::offset::ByteOffset;
  /// let x = 1997;
  /// let p = Ptr::from(&x);
  /// let q = unsafe { p.at(ByteOffset(1)) };
  /// 
  /// assert!(p.is_aligned());
  /// assert!(!q.is_aligned());
  /// ```
  pub fn is_aligned(self) -> bool {
    self.misalignment() == 0
  }

  /// Like `is_aligned`, but usable inside of assertions in `const` code.
  pub(crate) const fn is_aligned_const_for_assertions(self) -> bool {
    crate::is_aligned_const_for_assertions(self.p)
  }

  /// Returns this pointer's "address misalignment"; i.e., its address modulo
  /// the pointee type's alignment.
  /// 
  /// ```
  /// # use gep::*;
  /// # use gep::offset::ByteOffset;
  /// let x = 1997;
  /// let p = Ptr::from(&x);
  /// let q = unsafe { p.at(ByteOffset(1)) };
  /// 
  /// assert_eq!(p.misalignment(), 0);
  /// assert_eq!(q.misalignment(), 1);
  /// ```
  pub fn misalignment(self) -> usize {
    let mask = mem::align_of::<T>() - 1;
    self.addr() & mask
  }

  /// Makes this pointer well-aligned by rounding its address down.
  /// 
  /// ```
  /// # use gep::*;
  /// # use gep::offset::ByteOffset;
  /// let x = [1997, 42];
  /// let p = Ptr::from(&x).element();
  /// let q = unsafe { p.at(ByteOffset(1)) };
  /// 
  /// unsafe {
  ///   assert_eq!(p.align_down().read(), 1997);
  ///   assert_eq!(q.align_down().read(), 1997);
  /// }
  /// ```
  pub fn align_down(self) -> Self {
    let mask = mem::align_of::<T>() - 1;
    self.map_addr(|a| a & !mask)
  }

  /// Makes this pointer well-aligned by rounding its address up.
  /// 
  /// ```
  /// # use gep::*;
  /// # use gep::offset::ByteOffset;
  /// let x = [1997, 42];
  /// let p = Ptr::from(&x).element();
  /// let q = unsafe { p.at(ByteOffset(1)) };
  /// 
  /// unsafe {
  ///   assert_eq!(p.align_up().read(), 1997);
  ///   assert_eq!(q.align_up().read(), 42);
  /// }
  /// ```
  pub fn align_up(self) -> Self {
    let mask = mem::align_of::<T>() - 1;
    self.map_addr(|a| (a + mask) & !mask)
  }

  /// Performs pointer arithmetic to produce a new pointer.
  ///
  /// If an integer `i` (of any type, possibly signed) is passed in as the
  /// offset, it will compute the address of the `i`th `T` relative to this
  /// pointer. To obtain a pointer to the `i`th byte instead, wrap the integer
  /// in an [`offset::ByteOffset`].
  ///
  /// ```
  /// # use gep::*;
  /// # use gep::offset::ByteOffset;
  /// let x = [1997, 42];
  /// let p = Ptr::from(&x).element();
  ///
  /// unsafe {
  ///   assert_eq!(p.at(1).read(), 42);
  ///   assert_eq!(p.at(ByteOffset(4)).read(), 42);
  /// }
  /// ```
  /// 
  /// If an [`offset::Field`] is passed in as the offset, it will compute the
  /// address of that field within the pointer. If it's a negative field
  /// offset, it will treat this as a pointer to a field and compute the address
  /// of the outer struct. Note that such negative field offsets are only valid
  /// if this pointer was created from a reference to the top of the outer
  /// struct originally.
  ///
  /// ```
  /// # use gep::*;
  /// struct Foo {
  ///   a: u8,
  ///   bar: Bar,
  /// }
  /// 
  /// struct Bar(i32, i32, i32);
  /// 
  /// let x = Foo { a: 5, bar: Bar(-1, -2, -3) };
  /// let p = Ptr::from(&x);
  /// 
  /// unsafe {
  ///   assert_eq!(p.at(field!(Foo.bar.2)).read(), -3);
  /// }
  /// ```
  /// 
  /// [`offset::NotInBounds`] can be used to disable out-of-bounds undefined
  /// behavior for this function, but the resulting pointer may be invalid for
  /// reads and writes.
  ///
  /// ```
  /// # use gep::*;
  /// # use gep::offset::NotInBounds;
  /// let x = [1997, 42];
  /// let p = Ptr::from(&x).element();
  ///
  /// unsafe {
  ///   let invalid = p.at(NotInBounds(2000));
  ///   // invalid.read()  // UB!
  ///   let valid_again = invalid.at(NotInBounds(-1999));
  ///   assert_eq!(valid_again.read(), 42);
  /// }
  /// ```
  /// 
  /// # Safety
  ///
  /// See the safety doc for [`offset::Measurement::apply()`].
  pub unsafe fn at<U>(self, offset: impl Offset<T, U>) -> Ptr<U> {
    self.at_raw(offset.measure()).cast::<U>()
  }

  /// Performs pointer arithmetic to produce a new pointer.
  ///
  /// Unlike [`Ptr::at()`], this function is `const`, but takes an explicit
  /// [`offset::Measurement`] value.
  ///
  ///
  /// ```
  /// # use gep::*;
  /// # use gep::offset::Measurement;
  /// let x = [1997, 42];
  /// let p = Ptr::from(&x).element();
  ///
  /// let m = Measurement::by_bytes(4);
  /// unsafe {
  ///   assert_eq!(p.at_raw(m).read(), 42);
  /// }
  /// ```
  /// 
  /// # Safety
  ///
  /// See the safety doc for [`offset::Measurement::apply()`].
  pub const unsafe fn at_raw(self, offset: offset::Measurement) -> Ptr<T> {
    Ptr {
      p: offset.apply(self.p),
    }
  }

  /// Casts this pointer to a `Ptr<[T]>`, with the given length.
  pub fn to_slice(self, len: usize) -> Ptr<[T]> {
    Ptr {
      p: ptr::slice_from_raw_parts_mut(self.p, len),
    }
  }

  /// Casts this pointer to a `Ptr<MaybeUninit<T>>`.
  pub const fn to_uninit(self) -> Ptr<MaybeUninit<T>> {
    self.cast()
  }

  /// Reads the value at `self`.
  ///
  /// This does not "move"; it effectively performs a bytewise copy of the value
  /// behind the pointer.
  ///
  /// ```
  /// # use gep::*;
  /// let x = 1997;
  /// let p = Ptr::from(&x);
  /// 
  /// assert_eq!(unsafe { p.read() }, 1997);
  /// ```
  /// 
  /// # Safety
  ///
  /// This operation is equivalent to dereferencing a raw pointer. The following
  /// is an incomplete list of requirements:
  ///
  /// `self` must be valid for reads, properly aligned, and properly
  /// initialized. See [`std::ptr::read()`] for more information.
  pub unsafe fn read(self) -> T {
    debug_assert!(!self.is_null(), "attempted to read null pointer");
    debug_assert!(
      self.is_aligned_const_for_assertions(),
      "attempted to read misaligned pointer {self:?}"
    );

    self.p.read()
  }

  /// Reads the value at `self.at(idx)`.
  ///
  /// This is a convenience function for reading at a specified offset.
  ///
  /// ```
  /// # use gep::*;
  /// struct Player {
  ///   name: String,
  ///   health: f32,
  /// }
  /// 
  /// let x = Player { name: "Gep".into(), health: 20.0 };
  /// let p = Ptr::from(&x);
  /// 
  /// unsafe {
  ///   assert_eq!(p.read_at(field!(Player.health)), 20.0);
  /// }
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// for [`Ptr::read()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn read_at<U>(self, idx: impl Offset<T, U>) -> U {
    self.at(idx).read()
  }

  /// Writes to the value at `self`.
  ///
  /// Note: does not run the destructor of `self`'s pointee before overwriting
  /// it.
  ///
  /// ```
  /// # use gep::*;
  /// let mut x = 1997;
  /// let p = Ptr::from(&mut x);
  /// 
  /// unsafe { p.write(42); }
  /// assert_eq!(x, 42);
  /// ```
  ///
  /// # Safety
  ///
  /// This operation is equivalent to dereferencing a raw pointer. The following
  /// is an incomplete list of requirements:
  ///
  /// `self` must be valid for writes, properly aligned, and properly
  /// initialized. See [`std::ptr::write()`] for more information.
  pub unsafe fn write(self, val: T) {
    debug_assert!(!self.is_null(), "attempted to write to null pointer");
    debug_assert!(
      self.is_aligned_const_for_assertions(),
      "attempted to write to misaligned pointer {self:?}"
    );

    self.p.write(val)
  }

  /// Writes to the value at `self.at(idx)`.
  ///
  /// This is a convenience function for writing at a specified offset.
  ///
  /// ```
  /// # use gep::*;
  /// struct Player {
  ///   name: String,
  ///   health: f32,
  /// }
  /// 
  /// let mut x = Player { name: "Gep".into(), health: 20.0 };
  /// let p = Ptr::from(&mut x);
  /// 
  /// unsafe {
  ///   p.write_at(field!(Player.health), 30.0);
  /// }
  /// assert_eq!(x.health, 30.0);
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// for [`Ptr::write()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn write_at<U>(self, idx: impl Offset<T, U>, val: U) {
    self.at(idx).write(val)
  }

  /// Zeroes the value at `self`.
  /// 
  /// ```
  /// # use gep::*;
  /// let mut x = 1997;
  /// let p = Ptr::from(&mut x);
  /// 
  /// unsafe { p.clear_to_zero(); }
  /// assert_eq!(x, 0);
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::write()`] must be met. Also, if the pointee is
  /// not a type for which zero is a valid representation (e.g., a reference),
  /// the pointer will be invalid for reads.
  pub unsafe fn clear_to_zero(self) {
    self.p.write_bytes(0, 1)
  }

  /// Zeroes the value at `self`.
  ///
  /// This is a convenience function for zeroing at a specified offset.
  /// 
  /// ```
  /// # use gep::*;
  /// struct Player {
  ///   name: String,
  ///   health: f32,
  /// }
  /// 
  /// let mut x = Player { name: "Gep".into(), health: 20.0 };
  /// let p = Ptr::from(&mut x);
  /// 
  /// unsafe {
  ///   p.clear_to_zero_at(field!(Player.health));
  /// }
  /// assert_eq!(x.health, 0.0);
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// for [`Ptr::clear_to_zero()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn clear_to_zero_at<U>(self, idx: impl Offset<T, U>) {
    self.at(idx).clear_to_zero()
  }

  /// Destroys the value at `self.at(idx)`.
  ///
  /// This is a convenience function for destroying at a specified offset.
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// for [`Ptr::destroy()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn destroy_at<U>(self, idx: impl Offset<T, U>) {
    self.at(idx).destroy()
  }

  /// Replaces the value at `self`.
  ///
  /// This is like [`Ptr::read()`], but it writes a new value after reading.
  /// 
  /// ```
  /// # use gep::*;
  /// let mut x = 1997;
  /// let p = Ptr::from(&mut x);
  /// 
  /// unsafe {
  ///   assert_eq!(p.replace(42), 1997);
  /// }
  /// assert_eq!(x, 42);
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::read()`] and [`Ptr::write()`] must be satisfied.
  pub unsafe fn replace(self, val: T) -> T {
    let x = self.read();
    self.write(val);
    x
  }

  /// Replaces the value at `self`.
  ///
  /// This is a convenience function for replacing at a specified offset.
  /// 
  /// ```
  /// # use gep::*;
  /// struct Player {
  ///   name: String,
  ///   health: f32,
  /// }
  /// 
  /// let mut x = Player { name: "Gep".into(), health: 20.0 };
  /// let p = Ptr::from(&mut x);
  /// 
  /// unsafe {
  ///   assert_eq!(p.replace_at(field!(Player.health), 30.0), 20.0);
  /// }
  /// assert_eq!(x.health, 30.0);
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// [`Ptr::read()`] and [`Ptr::write()`] (on the result of the pointer
  /// arithmetic operation).
  pub unsafe fn replace_at<U>(self, idx: impl Offset<T, U>, val: U) -> U {
    self.at(idx).replace(val)
  }

  /// Dereferences `self.at(idx)`, producing a reference.
  ///
  /// This is a convenience function for deref-ing at a specified offset.
  /// 
  /// ```
  /// # use gep::*;
  /// struct Player {
  ///   name: String,
  ///   health: f32,
  /// }
  /// 
  /// let mut x = Player { name: "Gep".into(), health: 20.0 };
  /// let p = Ptr::from(&mut x);
  /// 
  /// let name = unsafe { p.deref_at(field!(Player.name)) };
  /// assert_eq!(name, "Gep");
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// [`Ptr::deref()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn deref_at<U>(&self, idx: impl Offset<T, U>) -> &U {
    self.at(idx).deref_unbound()
  }

  /// Dereferences `self.at(idx)`, producing a reference.
  ///
  /// This is a convenience function for deref-ing at a specified offset; this
  /// is the unbound version of [`Ptr::deref_at()`].
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// [`Ptr::deref()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn deref_unbound_at<'a, U>(self, idx: impl Offset<T, U>) -> &'a U {
    self.at(idx).deref_unbound()
  }

  /// Dereferences `self.at(idx)`, producing a mutable reference.
  ///
  /// This is a convenience function for deref-ing at a specified offset.
  /// 
  /// ```
  /// # use gep::*;
  /// struct Player {
  ///   name: String,
  ///   health: f32,
  /// }
  /// 
  /// let mut x = Player { name: "Gep".into(), health: 20.0 };
  /// let p = Ptr::from(&mut x);
  /// 
  /// {
  ///   let name = unsafe { p.deref_mut_at(field!(Player.name)) };
  ///   name.clear();
  ///   name.push_str("Jim");
  /// }
  /// 
  /// assert_eq!(x.name, "Jim")
  /// ```
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// [`Ptr::deref_mut()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn deref_mut_at<U>(&self, idx: impl Offset<T, U>) -> &mut U {
    self.at(idx).deref_mut_unbound()
  }

  /// Dereferences `self.at(idx)`, producing a mutable reference.
  ///
  /// This is a convenience function for deref-ing at a specified offset; this
  /// is the unbound version of [`Ptr::deref_mut_at()`].
  ///
  /// # Safety
  ///
  /// The requirements of [`Ptr::at()`] must be satisfied, as well as those
  /// [`Ptr::deref_mut()`] (on the result of the pointer arithmetic operation).
  pub unsafe fn deref_mut_unbound_at<'a, U>(
    self,
    idx: impl Offset<T, U>,
  ) -> &'a mut U {
    self.at(idx).deref_mut_unbound()
  }
}

impl<T> Ptr<[T]> {
  /// Flattens this pointer into a pointer to the first element.
  /// 
  /// ```
  /// # use gep::*;
  /// let x = [1, 2, 3];
  /// let p = Ptr::from(&x[..]);
  /// 
  /// assert_eq!(p.element(), Ptr::from(&x[0]));
  /// ```
  pub const fn element(self) -> Ptr<T> {
    self.cast::<T>()
  }
}

impl<T, const N: usize> Ptr<[T; N]> {
  /// Flattens this pointer into a pointer to the first element.
  /// 
  /// ```
  /// # use gep::*;
  /// let x = [1, 2, 3];
  /// let p = Ptr::from(&x);
  /// 
  /// assert_eq!(p.element(), Ptr::from(&x[0]));
  /// ```
  pub const fn element(self) -> Ptr<T> {
    self.cast::<T>()
  }
}
