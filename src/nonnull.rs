//! Non-null raw pointer type.

use core::fmt;
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::ptr;

use crate::offset;
use crate::offset::Offset;
use crate::Ptr;

/// A non-null raw pointer.
///
/// This type is intended as an improved version of [`core::ptr::NonNull`],
/// which provides clearer methods for common operations on raw pointers.
///
/// Unlike Rust's raw pointers, this pointer type does not track mutability
/// (which is not deeply useful book-keeping on raw pointers).
///
/// This type has most of the same API as [`Ptr`]. It is `Deref<Target=Ptr>`,
/// which allows any method defined on [`Ptr`] to be called on [`NonNull`].
/// Some functions are duplicated for [`NonNull`], since they return a [`NonNull`]
/// instead of a [`Ptr`]. In `const` contexts, `Deref` coercion is inaccessible,
/// so you'll need to use [`NonNull::to_ptr()`] to access those methods.
///
/// # Unsized Types
///
/// Currently, `T: !Sized` is poorly supported (due to lack of good support on
/// `*mut T` itself). In particular, `NonNull<[T]>` should be separated into a
/// `NonNull<T>` and a `usize`, since there is no supported way to get the length
/// out.
#[repr(transparent)]
pub struct NonNull<T: ?Sized> {
  p: ptr::NonNull<T>,
}

const _: () = {
  const fn assert_pointer_sizes<T: ?Sized>() {
    use core::mem::size_of;

    assert!(size_of::<NonNull<T>>() == size_of::<Ptr<T>>());
    assert!(size_of::<NonNull<T>>() == size_of::<ptr::NonNull<T>>());
    assert!(size_of::<NonNull<T>>() == size_of::<*mut T>());
    assert!(size_of::<NonNull<T>>() == size_of::<Option<NonNull<T>>>());
  }

  assert_pointer_sizes::<u8>();
  assert_pointer_sizes::<i32>();
  assert_pointer_sizes::<[i32]>();
  assert_pointer_sizes::<str>();
  assert_pointer_sizes::<dyn core::fmt::Debug>();
};

impl<T: ?Sized> PartialEq<Ptr<T>> for NonNull<T> {
  fn eq(&self, other: &Ptr<T>) -> bool {
    self.to_raw() == other.to_raw()
  }
}

impl<T: ?Sized> PartialEq<NonNull<T>> for NonNull<T> {
  fn eq(&self, other: &NonNull<T>) -> bool {
    self.to_raw() == other.to_raw()
  }
}

impl<T: ?Sized> Eq for NonNull<T> {}

impl<T: ?Sized> Clone for NonNull<T> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<T: ?Sized> Copy for NonNull<T> {}

impl<T: ?Sized> fmt::Debug for NonNull<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Debug::fmt(&self.p, f)
  }
}

impl<T: ?Sized> fmt::Pointer for NonNull<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Pointer::fmt(&self.p, f)
  }
}

impl<T: ?Sized> From<&T> for NonNull<T> {
  fn from(value: &T) -> Self {
    Self::new(value.into())
  }
}

impl<T: ?Sized> From<&mut T> for NonNull<T> {
  fn from(value: &mut T) -> Self {
    Self::new(value.into())
  }
}

impl<T: ?Sized> From<ptr::NonNull<T>> for NonNull<T> {
  fn from(value: ptr::NonNull<T>) -> Self {
    Self::new(value.into())
  }
}

impl<T: ?Sized> From<NonNull<T>> for *const T {
  fn from(value: NonNull<T>) -> Self {
    value.to_raw()
  }
}

impl<T: ?Sized> From<NonNull<T>> for *mut T {
  fn from(value: NonNull<T>) -> Self {
    value.to_raw()
  }
}

impl<T: ?Sized> From<NonNull<T>> for ptr::NonNull<T> {
  fn from(value: NonNull<T>) -> Self {
    value.p
  }
}

impl<T: ?Sized> Deref for NonNull<T> {
  type Target = Ptr<T>;

  fn deref(&self) -> &Ptr<T> {
    self.as_ptr()
  }
}

impl<T: ?Sized> NonNull<T> {
  /// Constructs a new `NonNull` from a raw pointer or reference.
  ///
  /// Because this function takes `*const T`, it can accept any reference or
  /// pointer type, because they all coerce into `*const T`.
  pub const fn new(ptr: ptr::NonNull<T>) -> Self {
    NonNull { p: ptr }
  }

  /// Converts this pointer into a nullable pointer.
  pub const fn to_ptr(self) -> Ptr<T> {
    Ptr::new(self.p.as_ptr())
  }

  /// Converts a reference to this pointer into a reference to a nullable pointer.
  pub const fn as_ptr(&self) -> &Ptr<T> {
    let cast = Ptr::new(self as *const Self as *mut Self).cast::<Ptr<T>>();
    unsafe { cast.deref_unbound() }
  }

  /// Casts this pointer to another type.
  ///
  /// Note that `U: Sized`, because creating a pointer to an unsized type
  /// requires extra metadata (and no stable API exists to do so yet).
  pub const fn cast<U>(self) -> NonNull<U> {
    unsafe { self.to_ptr().cast().to_non_null_unchecked() }
  }
}

impl<T> NonNull<T> {
  /// Creates a new, non-null, dangling pointer.
  pub const fn dangling() -> Self {
    unsafe { Ptr::dangling().to_non_null_unchecked() }
  }

  /// Creates a pointer with the given address and the "invalid" provenance.
  ///
  /// Compare [`std::ptr::invalid()`].
  ///
  /// # Safety
  ///
  /// `addr` cannot be zero.
  pub const unsafe fn invalid(addr: usize) -> Self {
    Ptr::invalid(addr).to_non_null_unchecked()
  }

  /// Reconstitutes a pointer using an address previously constructed with
  /// [`Ptr::expose_addr()`].
  ///
  /// Compare [`std::ptr::from_exposed_addr()`].
  ///
  /// # Safety
  ///
  /// `addr` cannot be zero.
  pub const unsafe fn from_exposed_addr(addr: usize) -> Self {
    Ptr::invalid(addr).to_non_null_unchecked()
  }

  /// Creates a new pointer with the given address using the provenance
  /// information from `self`.
  ///
  /// Compare [`<*mut T>::with_addr()`](https://doc.rust-lang.org/std/primitive.pointer.html#method.with_addr-1).
  ///
  /// # Safety
  ///
  /// `addr` cannot be zero.
  pub unsafe fn with_addr(self, addr: usize) -> NonNull<T> {
    self.to_ptr().with_addr(addr).to_non_null_unchecked()
  }

  /// Transforms the address of `self` while preserving its provenance.
  ///
  /// This is a convenience wrapper over [`NonNull::with_addr()`].
  ///
  /// # Safety
  ///
  /// `f` cannot return zero.
  pub unsafe fn map_addr(self, f: impl FnOnce(usize) -> usize) -> Self {
    self.with_addr(f(self.addr()))
  }

  /// Returns whether this pointer is appropriately aligned for its type.
  pub fn is_aligned(self) -> bool {
    self.to_ptr().is_aligned()
  }

  /// Returns this pointer's "address misalignment"; i.e., its address modulo
  /// the pointee type's alignment.
  pub fn misalignment(self) -> usize {
    self.to_ptr().misalignment()
  }

  /// Makes this pointer well-aligned by rounding its address down.
  ///
  /// # Safety
  ///
  /// The resulting address cannot be zero.
  pub unsafe fn align_down(self) -> Self {
    self.to_ptr().align_down().to_non_null_unchecked()
  }

  /// Makes this pointer well-aligned by rounding its address up.
  ///
  /// # Safety
  ///
  /// The resulting address cannot be zero.
  pub unsafe fn align_up(self) -> Self {
    self.to_ptr().align_up().to_non_null_unchecked()
  }

  /// Performs pointer arithmetic to produce a new pointer.
  ///
  /// If an integer `i` (of any type, possibly signed) is passed in as the
  /// offset, it will compute the address of the `i`th `T` relative to this
  /// pointer. To obtain a pointer to the `i`th byte instead, wrap the integer
  /// in an [`offset::ByteOffset`].
  ///
  /// If an [`offset::Field`] is passed in as the offset, it will compute the
  /// address of that field within the pointer. If it's a negative field
  /// offset, it will treat this as a pointer to a field and compute the address
  /// of the outer struct. Note that such negative field offsets are only valid
  /// if this pointer was created from a reference to the top of the outer
  /// struct originally.
  ///
  /// [`offset::NotInBounds`] can be used to disable out-of-bounds undefined
  /// behavior for this function, but the resulting pointer may be invalid for
  /// reads and writes.
  ///
  /// # Safety
  ///
  /// See the safety doc for [`offset::Measurement::apply()`].
  pub unsafe fn at<U>(self, offset: impl Offset<T, U>) -> NonNull<U> {
    self.to_ptr().at(offset).to_non_null_unchecked()
  }

  /// Performs pointer arithmetic to produce a new pointer.
  ///
  /// Unlike [`NonNull::at()`], this function is `const`, but takes an explicit
  /// [`offset::Measurement`] value.
  ///
  /// # Safety
  ///
  /// See the safety doc for [`offset::Measurement::apply()`].
  pub const unsafe fn at_raw(self, offset: offset::Measurement) -> NonNull<T> {
    self.to_ptr().at_raw(offset).to_non_null_unchecked()
  }

  /// Casts this pointer to a `NonNull<[T]>`, with the given length.
  pub fn to_slice(self, len: usize) -> NonNull<[T]> {
    unsafe { self.to_ptr().to_slice(len).to_non_null_unchecked() }
  }

  /// Casts this pointer to a `NonNull<MaybeUninit<T>>`.
  pub const fn to_uninit(self) -> NonNull<MaybeUninit<T>> {
    self.cast()
  }
}

impl<T> NonNull<[T]> {
  /// Flattens this pointer into a pointer to the first element.
  pub const fn element(self) -> NonNull<T> {
    self.cast::<T>()
  }
}

impl<T, const N: usize> NonNull<[T; N]> {
  /// Flattens this pointer into a pointer to the first element.
  pub const fn element(self) -> NonNull<T> {
    self.cast::<T>()
  }
}
