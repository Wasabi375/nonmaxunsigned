# NonMax-Unsigned

This crate provides an implementation for non-max integer types
with [null-pointer-optimization].

This crate is usable in a `no-std` environment.

## Example

```rust
use nonmaxunsigned::U7;

fn main() {
    let a = U7::new(5).unwrap();
    let b = U7::new(12).unwrap();

    assert_eq!(U7::new(17).unwrap(), a + b);
    assert_eq!(None, U7::new(u8::MAX));
}
```

## Similar Crates

There are a few similar crates already existing on crates.io:

* nonmax: <https://crates.io/crates/nonmax>
* nonany: <https://crates.io/crates/nonany>
* nonn: <https://crates.io/crates/nonn>

Unlike those crates this implementation does not [NonZero](https://doc.rust-lang.org/stable/std/num/struct.NonZero.html).
Those crates store the value as `value ^ max` which is never `0` as long as `value != max`.
However this means the binary/hex representation of the stored value is hard to parse.

This implementation instead relies on a large enum `U7Internal` which has 254 variants.
Such an enum also leads to [null-pointer-optimization] but does not require the xor trick
to prevent 0 values.
Instead it relies on `core::mem::transmute_copy`.


[null-pointer-optimization]: https://doc.rust-lang.org/stable/std/option/index.html#representation
