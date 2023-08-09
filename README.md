# gep

`gep`, a better pointer arithmetic library.

The name `gep` comes from LLVM's `getelementptr` instruction, the infamous
pointer arithmetic operation.

This library provides two new pointer types, [`Ptr`] and [`NonNull`], which
have very similar APIs; they correspond to `*mut T` and
[`core::ptr::NonNull`], respectively.

It also provides Rusty versions of [`memcpy`], [`memmove`], and [`memset`].

## Offsets

The premiere operation provided by this library is [`Ptr::at()`], which is
a generalized pointer arithmetic operation. For example, it will accept
any integer as input, not just `isize` (although, like [`<*mut T>::offset`],
the offset value must be valid to convert to `isize`).

```rust
let mut ints = [0i32; 6];
let p = Ptr::from(&mut ints).element();

unsafe {
  // Pointer to the 4th element.
  let q = p.at(4);
  q.write(42);

  // Many operations have an `*_at` variant that internally calls .at().
  q.write_at(-1, 55);
}

assert_eq!(ints, [0, 0, 0, 55, 42, 0]);
```

By default, `at()` works on multiples of elements. To do a direct byte
offset instead, you can use the [`offset::ByteOffset`] type instead.

```rust
use gep::offset::ByteOffset;

let mut ints = [0i32; 6];
let p = Ptr::from(&mut ints).element();

unsafe {
  p.write_at(ByteOffset(4), 4242);
}

assert_eq!(ints[1], 4242);
```

It's also possible to use "field offsets" (via the [`offset::Field`] type)
for accessing the fields of a struct directly, without creating intermediate
references to potentially invalid data.

```rust
use gep::offset::Field;

struct Foo {
  a: i32,
  b: [i32; 3],
}

let foo = Foo { a: 0, b: [1, 2, 3] };

let p = Ptr::from(&foo);
let value = unsafe {
  p.read_at(gep::field!(Foo.b[1]))
};

assert_eq!(value, 2);
```

License: Apache-2.0
