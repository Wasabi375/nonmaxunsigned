# NonMax-Unsigned

[![Crates.io](https://img.shields.io/crates/v/nonmaxunsigned.svg)](https://crates.io/crates/nonmaxunsigned)
[![docs.rs](https://img.shields.io/docsrs/nonmaxunsigned)](https://docs.rs/nonmaxunsigned)
[![Dependency status](https://deps.rs/repo/github/Wasabi375/nonmaxunsigned/status.svg)](https://deps.rs/repo/github/Wasabi375/nonmaxunsigned)

This crate provides an implementation for non-max integer types
with [null-pointer-optimization] and ensures that the binary representation
of the non-max and the normal integers are the same.

This crate is usable in a `no-std` environment.

> [!WARNING]
> This crate relies on undefined behaviour in the rust compiler and there is no
> guarantee that this will continue to work in the future.

## Example

```rust
use nonmaxunsigned::NonMaxU8;

fn main() {
    let a = NonMaxU8::new(5).unwrap();
    let b = NonMaxU8::new(12).unwrap();

    assert_eq!(NonMaxU8::new(17).unwrap(), a + b);
    assert_eq!(None, NonMaxU8::new(u8::MAX));
}
```

## Maximum Value

The maximum value for the non-max integers is lower than just `max - 1`.
This is neccessary to ensure that the binary representation is the same as the
normal integers.

The maximum value for each non-max version is as follows:

| Integer | Hex | Decimal | Difference Hex | Difference Decimal |
| --- | ---  | --- | --- | --- |
| `u8`    | `0xfe`                  | 255     | `0x1` | 1 |
| `u16`   | `0xfeff`                | 65279     | `0x100` | 256 |
| `u32`   | `0xfeff_ffff`           | 4278190079 | `0x100_0000` | 116777216 |
| `u64`   | `0xfeff_ffff_ffff_ffff` | 18374686479671623679 | `0x100_0000_0000_0000` | 72057594037927936 |



## Features

### endian-conversion

This feature provides access to little and big endian versions of the non-max integer types
as well as conversions between them. The native version for the non-max integers is just
a type alias for the correct endianness.

`non_max.get()` will always return the native endian integer.

```rust
#[cfg(feature = "endian-conversion")]
use nonmaxunsigned::{NonMaxU32Le, NonMaxU32Be, NonMaxU32};

#[cfg(feature = "endian-conversion")]
fn main() {
    let native = NonMaxU32::new(37).unwrap();
    let little = native.to_le();
    let big = native.to_be();

    assert_eq!(little.get(), big.get());
    assert_eq!(native.get(), big.get());
    assert_eq!(native.get(), little.get());

    assert_eq!(little.to_native(), native);
    assert_eq!(little.to_be(), big);

    assert_eq!(little.get_underlying(), 37u32.to_le());
    assert_eq!(big.get_underlying(), 37u32.to_be());
}
#[cfg(not(feature = "endian-conversion"))]
fn main() {}
```

## Similar Crates

There are a few similar crates already existing on crates.io:

* nonmax: <https://crates.io/crates/nonmax>
* nonany: <https://crates.io/crates/nonany>
* nonn: <https://crates.io/crates/nonn>

Unlike those crates this implementation does not [NonZero](https://doc.rust-lang.org/stable/std/num/struct.NonZero.html).
Those crates store the value as `value ^ max` which is never `0` as long as `value != max`.
However this means the binary/hex representation of the stored value is hard to parse.

This implementation instead relies on a large enum `NonMaxU8Internal` which has 254 variants.
Such an enum also leads to [null-pointer-optimization] but does not require the xor trick
to prevent 0 values.
Instead it relies on `core::mem::transmute_copy`.

# License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

[null-pointer-optimization]: https://doc.rust-lang.org/stable/std/option/index.html#representation
