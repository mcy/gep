//! Offset measurement types.

use core::fmt;
use core::marker::PhantomData;
use core::mem;
use core::ops;

#[cfg(doc)]
use crate::Ptr;

/// An offset type.
///
/// Offset types specify how to offset a pointer type. The input pointer type
/// must be of type `T`, and the output will be of type `U`.
///
/// All integer types implement `Offset`, with the following semantics:
/// 1. Offsets are measured in units of pointee elements. So, when used on a
///    [`Ptr<i32>`], the integer is multiplied by 4 before being added to the
///    pointer's address.
/// 2. Offsets must land within the bounds of the allocation the pointer is in
/// 3. In debug mode, if the integer type cannot be losslessly converted into
///    `isize`, an assert will fire.
/// 4. The input and output types of the `Offset` impl are equal.
///
/// To disable (1), wrap the integer in a [`ByteOffset`]. To disable (2), wrap
/// it in a [`NotInBounds`].
///
/// There is also the [`Field`] offset type, which can be used to access
/// specific fields of structs and unions.
pub trait Offset<T: ?Sized, U: ?Sized> {
  /// Produces Measurement for use by offsetting methods.
  fn measure(self) -> Measurement;
}

/// A byte offset type; see [`Offset`].
#[derive(Copy, Clone, Debug)]
pub struct ByteOffset<I>(pub I);

/// Measurement generated via an [`Offset`] implementation.
#[derive(Copy, Clone, Debug)]
pub struct Measurement {
  /// The raw offset, which may be in units of elements of bytes.
  pub(crate) offset: isize,
  /// If true, `offset` should be multiplied by the size of the pointee type.
  pub(crate) is_element_wise: bool,
  /// If true, using this offset will not offset the pointer outside of the
  /// allocation it is currently in (compare: `<*mut T>::offset()` vs
  /// `<*mut T>::wrapping_offset()`).
  pub(crate) inbounds: bool,
}

impl Measurement {
  /// Creates a new offset measurement for offsetting by a number of array
  /// elements (i.e., `count` will be multiplied by `size_of::<T>` when
  /// applied).
  ///
  /// This sets `inbounds` to true by default.
  pub const fn by_elements(count: isize) -> Self {
    Self {
      offset: count,
      is_element_wise: true,
      inbounds: true,
    }
  }

  /// Creates a new offset measurement for offsetting by a number of bytes.
  ///
  /// This sets `inbounds` to true by default.
  pub const fn by_bytes(len: isize) -> Self {
    Self {
      offset: len,
      is_element_wise: false,
      inbounds: true,
    }
  }

  /// Updates this offset measurement with the given setting for inbounds
  /// offsetting.
  pub const fn inbounds(self, enforce: bool) -> Self {
    Self {
      inbounds: enforce,
      ..self
    }
  }

  /// Applies this offset measurement to `ptr`.
  ///
  /// # Safety
  ///
  /// This function performs an offsetting operation. The precise requirements
  /// depend on the settings of the offset being applied.
  ///
  /// If this is an `inbounds` offset, the requirements of [`<*mut T>::offset()`]
  /// apply. If this is an element-wise offset, the computed byte-wise must not
  /// overflow [`isize`].
  ///
  /// Additionally, the validity of the resulting pointer for a non-`inbounds`
  /// offset is as per the docs for [`<*mut T>::wrapping_offset()`].
  ///
  /// [`<*mut T>::offset()`]: https://doc.rust-lang.org/std/primitive.pointer.html#method.offset-1
  /// [`<*mut T>::wrapping_offset()`]: https://doc.rust-lang.org/std/primitive.pointer.html#method.wrapping_offset-1
  pub const unsafe fn apply<T>(mut self, ptr: *mut T) -> *mut T {
    if !self.is_element_wise {
      self.is_element_wise = true;
      return self.apply(ptr as *mut u8) as *mut T;
    }

    if cfg!(debug_assertions) {
      let byte_offset =
        match self.offset.checked_mul(mem::size_of::<T>() as isize) {
          Some(offset) => offset,
          None => panic!("computed offset overflows `isize`"),
        };

      let addr = unsafe { mem::transmute::<_, usize>(ptr) };
      assert!(
        !self.inbounds || addr.checked_add_signed(byte_offset).is_some(),
        "offset pointer wrapped around the address space"
      );
    }

    if !self.inbounds {
      return ptr.wrapping_offset(self.offset);
    }

    ptr.offset(self.offset)
  }
}

/// An adaptor for an offset type that permits it to be used out-of-bounds.
///
/// By default, most offset types will require that an offset operation done
/// with them must be "in bounds", such as per the safety requirements of
/// `<*mut T>::offset()`. This adapter disables this behavior: instead of
/// landing out-of-bounds being UB, it just produces an invalid pointer.
#[derive(Copy, Clone, Debug)]
pub struct NotInBounds<I>(pub I);

impl<T: ?Sized, U: ?Sized, I: Offset<T, U>> Offset<T, U> for NotInBounds<I> {
  fn measure(self) -> Measurement {
    Measurement {
      inbounds: false,
      ..self.0.measure()
    }
  }
}

macro_rules! impl_offset {
  ($($int:ty,)+) => {$(
    impl<T: ?Sized> Offset<T, T> for $int {
      fn measure(self) -> Measurement {
        debug_assert!(
          isize::try_from(self).is_ok(),
          "{self} is not in bounds for `isize` (0x{:x}..0x{:x})",
          isize::MIN, isize::MAX);

        Measurement::by_elements(self as isize)
      }
    }

    impl<T: ?Sized> Offset<T, T> for ByteOffset<$int> {
      fn measure(self) -> Measurement {
        Measurement {
          is_element_wise: false,
          ..Offset::<T, T>::measure(self.0)
        }
      }
    }
  )*};
}

impl_offset! {
  u8, u16, u32, u64, u128, usize,
  i8, i16, i32, i64, i128, isize,
}

/// A field offset within a struct or union, analogous to a "pointer to member"
/// in C++.
///
/// Field offsets can be used where an [`Offset`] is required.
///
/// Field offsets can be added together if they're of compatible types, e.g.
/// `Field<T, U> + Field<U, V>` is a `Field<T, V>`. Field offsets can be
/// negated, which can be used, for example, to offset from a field to the top
/// of its struct.
///
/// The [`field!()`][crate::field] macro can be used to create new field offsets.
pub struct Field<T: ?Sized, U: ?Sized> {
  offset: isize,
  _ph: PhantomData<for<'a> fn(&T) -> &U>,
}

#[doc(hidden)]
impl<T: ?Sized, U: ?Sized> Field<T, U> {
  #[doc(hidden)]
  pub fn __new_for_macro(n: isize, _: *const T, _: *const U) -> Self {
    Self {
      offset: n as isize,
      _ph: PhantomData,
    }
  }
}

impl<T: ?Sized> Field<T, T> {
  /// Returns a `Field` that treats a value as its own first field (and, thus
  /// with an offset of zero).
  pub fn this() -> Self {
    Self {
      offset: 0,
      _ph: PhantomData,
    }
  }
}

impl<T, const N: usize> Field<[T; N], T> {
  /// Returns a `Field` that indexes into a an array.
  ///
  /// # Panics
  ///
  /// Panics if `n >= N`.
  pub fn index(n: usize) -> Self {
    assert!(n < N, "index out of bounds: {n} >= {N}");
    Self {
      offset: (n * mem::size_of::<T>()) as isize,
      _ph: PhantomData,
    }
  }
}

impl<T: ?Sized, U: ?Sized, V: ?Sized> ops::Add<Field<U, V>> for Field<T, U> {
  type Output = Field<T, V>;

  fn add(self, that: Field<U, V>) -> Self::Output {
    Field {
      offset: self.offset + that.offset,
      _ph: PhantomData,
    }
  }
}

impl<T: ?Sized, U: ?Sized> ops::Neg for Field<T, U> {
  type Output = Field<U, T>;

  fn neg(self) -> Self::Output {
    Field {
      offset: -self.offset,
      _ph: PhantomData,
    }
  }
}

impl<T: ?Sized, U: ?Sized> Offset<T, U> for Field<T, U> {
  fn measure(self) -> Measurement {
    Measurement::by_bytes(self.offset)
  }
}

impl<T: ?Sized, U: ?Sized> Clone for Field<T, U> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<T: ?Sized, U: ?Sized> Copy for Field<T, U> {}

impl<T: ?Sized, U: ?Sized> fmt::Debug for Field<T, U> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use core::any::type_name;
    write!(
      f,
      "Field<{}, {}>({})",
      type_name::<T>(),
      type_name::<U>(),
      self.offset
    )
  }
}

/// Creates a new [`Field`] value.
///
/// The syntax is `field!(Type path)`, where `path` is a sequence of
/// path components of either the form `.foo` or `[idx]`. For example,
/// `field!(MyType.field)`, `field!([i32; 5][3])`, or `field!((u8, u8).0)`.
///
/// ```
/// # use gep::offset::Field;
/// struct Foo {
///   a: i32,
///   b: [i32; 3],
/// }
///
/// let f: Field<_, i32> = gep::field!((i32, Foo).1.b[1]);
/// ```
#[macro_export]
macro_rules! field {
  (@impl $base:expr, .$field:tt $($($path:tt)+)?) => {{
    let base = $base;
    let field = unsafe { core::ptr::addr_of!((*base).$field) };
    let offset = unsafe { field.cast::<u8>().offset_from(base.cast::<u8>()) };

    $crate::offset::Field::__new_for_macro(offset, base, field)
      + $crate::field!(@impl field, $($($path)+)?)
  }};

  (@impl $base:expr, [$idx:expr] $($($path:tt)+)?) => {{
    let idx: usize = $idx;
    let base = $base;
    let field = unsafe { core::ptr::addr_of!((*base)[idx]) };

    $crate::offset::Field::index(idx)
      + $crate::field!(@impl field, $($($path)+)?)
  }};

  (@impl $base:expr,) => {{
    $crate::offset::Field::this()
  }};

  (_, $($path:tt)+) => {{
    let uninit = core::mem::MaybeUninit::uninit();
    $crate::field!(@impl uninit.as_ptr(), $($path)+)
  }};

  ($($ty:tt)::+ $($path:tt)+) => {{
    let uninit = core::mem::MaybeUninit::<$($ty)::+>::uninit();
    $crate::field!(@impl uninit.as_ptr(), $($path)+)
  }};
}
