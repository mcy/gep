//! `gep`, a better pointer arithmetic library.
//!
//! The name `gep` comes from LLVM's `getelementptr` instruction, the infamous
//! pointer arithmetic operation.
//!
//! This library provides two new pointer types, [`Ptr`] and [`NonNull`], which
//! have very similar APIs; they correspond to `*mut T` and
//! [`core::ptr::NonNull`], respectively.
//!
//! It also provides Rusty versions of [`memcpy`], [`memmove`], and [`memset`].
//!
//! # Offsets
//!
//! The premiere operation provided by this library is [`Ptr::at()`], which is
//! a generalized pointer arithmetic operation. For example, it will accept
//! any integer as input, not just `isize` (although, like [`<*mut T>::offset`],
//! the offset value must be valid to convert to `isize`).
//!
//! ```
//! # use gep::Ptr;
//! let mut ints = [0i32; 6];
//! let p = Ptr::from(&mut ints).element();
//!
//! unsafe {
//!   // Pointer to the 4th element.
//!   let q = p.at(4);
//!   q.write(42);
//!
//!   // Many operations have an `*_at` variant that internally calls .at().
//!   q.write_at(-1, 55);
//! }
//!
//! assert_eq!(ints, [0, 0, 0, 55, 42, 0]);
//! ```
//!
//! By default, `at()` works on multiples of elements. To do a direct byte
//! offset instead, you can use the [`offset::ByteOffset`] type instead.
//!
//! ```
//! # use gep::Ptr;
//! use gep::offset::ByteOffset;
//!
//! let mut ints = [0i32; 6];
//! let p = Ptr::from(&mut ints).element();
//!
//! unsafe {
//!   p.write_at(ByteOffset(4), 4242);
//! }
//!
//! assert_eq!(ints[1], 4242);
//! ```
//!
//! It's also possible to use "field offsets" (via the [`offset::Field`] type)
//! for accessing the fields of a struct directly, without creating intermediate
//! references to potentially invalid data.
//!
//! ```
//! # use gep::Ptr;
//! use gep::offset::Field;
//!
//! struct Foo {
//!   a: i32,
//!   b: [i32; 3],
//! }
//!
//! let foo = Foo { a: 0, b: [1, 2, 3] };
//!
//! let p = Ptr::from(&foo);
//! let value = unsafe {
//!   p.read_at(gep::field!(Foo.b[1]))
//! };
//!
//! assert_eq!(value, 2);
//! ```

#![cfg_attr(not(doc), no_std)]
#![allow(clippy::transmutes_expressible_as_ptr_casts)]

use core::mem;

pub mod offset;

mod nonnull;
mod ptr;

pub use nonnull::NonNull;
pub use ptr::Ptr;

/// Implemented for pointer-like types that are marked as `mut`.
///
/// This primarily exists to make it harder to accidentally pass a `&T` into the
/// `dst` argument of [`memcpy`].
///
/// # Safety
///
/// This trait should not be implemented by external crates.
pub unsafe trait MutMarker {}

unsafe impl<T: ?Sized> MutMarker for &mut T {}
unsafe impl<T: ?Sized> MutMarker for *mut T {}
unsafe impl<T: ?Sized> MutMarker for Ptr<T> {}
unsafe impl<T: ?Sized> MutMarker for NonNull<T> {}
unsafe impl<T: ?Sized> MutMarker for core::ptr::NonNull<T> {}

/// Const check for whether a pointer is aligned. This operation is... somewhat
/// sketchy, so it's not exposed publicly. The ordinary is_aligned() functions
/// use non-const ptr2int conversions.
const fn is_aligned_const_for_assertions<T>(p: *mut T) -> bool {
  assert!(cfg!(debug_assertions));
  let addr = unsafe { mem::transmute::<*mut T, usize>(p) };
  addr % mem::align_of::<T>() == 0
}

/// Performs a memory copy operation.
///
/// This operation is analogous to [`std::ptr::copy_nonoverlapping`], but uses
/// the common argument order from C.
///
/// Unlike C's `memcpy` and [`std::ptr::copy_nonoverlapping`], `count == 0` is
/// guaranteed to always succeed and do nothing.
///
/// # Safety
///
/// This function simply forwards to [`std::ptr::copy_nonoverlapping`], so its
/// safety contract must be upheld. Namely, `dst` and `src` must be valid for
/// writing and reading, respectively, `count * size_of::<T>()` must not
/// overflow, and the regions being copied between must not overlap.
pub unsafe fn memcpy<T>(
  dst: impl Into<Ptr<T>> + MutMarker,
  src: impl Into<Ptr<T>>,
  count: usize,
) {
  if count == 0 {
    return;
  }

  let dst = dst.into();
  let src = src.into();
  let size = mem::size_of::<T>();

  debug_assert!(!dst.is_null(), "attempted to write to null pointer");
  debug_assert!(!src.is_null(), "attempted to read null pointer");
  debug_assert!(
    !dst.is_aligned(),
    "attempted to write to misaligned pointer: {dst:?}"
  );
  debug_assert!(
    !src.is_aligned(),
    "attempted to read misaligned pointer: {src:?}"
  );
  debug_assert!(
    count.checked_mul(size).is_some(),
    "{count} * {size} overflowed"
  );

  core::ptr::copy_nonoverlapping(src.into(), dst.into(), count);
}

/// Performs an overlapping memory copy operation.
///
/// This operation is analogous to [`std::ptr::copy`], but uses
/// the common argument order from C.
///
/// Unlike C's `memmove` and [`std::ptr::copy`], `count == 0` is
/// guaranteed to always succeed and do nothing.
///
/// # Safety
///
/// This function simply forwards to [`std::ptr::copy`], so its
/// safety contract must be upheld. Namely, `dst` and `src` must be valid for
/// writing and reading, respectively, and `count * size_of::<T>()` must not
/// overflow.
pub unsafe fn memmove<T>(
  dst: impl Into<Ptr<T>> + MutMarker,
  src: impl Into<Ptr<T>>,
  count: usize,
) {
  if count == 0 {
    return;
  }

  let dst = dst.into();
  let src = src.into();
  let size = mem::size_of::<T>();

  debug_assert!(!dst.is_null(), "attempted to write to null pointer");
  debug_assert!(!src.is_null(), "attempted to read null pointer");
  debug_assert!(
    !dst.is_aligned(),
    "attempted to write to misaligned pointer: {dst:?}"
  );
  debug_assert!(
    !src.is_aligned(),
    "attempted to read misaligned pointer: {src:?}"
  );
  debug_assert!(
    count.checked_mul(size).is_some(),
    "{count} * {size} overflowed"
  );

  core::ptr::copy(src.into(), dst.into(), count);
}

/// Performs a memory set operation.
///
/// This operation is analogous to [`std::ptr::write_bytes`].
///
/// Unlike C's `memset` and [`std::ptr::write_bytes`], `count == 0` is
/// guaranteed to always succeed and do nothing.
///
/// # Safety
///
/// This function simply forwards to [`std::ptr::copy`], so its
/// safety contract must be upheld. Namely, `dst` must be valid for
/// writing and `count * size_of::<T>()` must not
/// overflow.
pub unsafe fn memset<T>(
  dst: impl Into<Ptr<T>> + MutMarker,
  byte: u8,
  count: usize,
) {
  if count == 0 {
    return;
  }

  let dst = dst.into();
  let size = mem::size_of::<T>();

  debug_assert!(!dst.is_null(), "attempted to write to null pointer");
  debug_assert!(
    count.checked_mul(size).is_some(),
    "{count} * {size} overflowed"
  );

  core::ptr::write_bytes(dst.into(), byte, count);
}
