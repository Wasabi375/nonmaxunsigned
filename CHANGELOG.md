<!-- next-header -->

## [Unreleased] - ReleaseDate

## Breaking Changes

* `MAX` value is now lower to allow for `None`:
    * `NonMaxU16::MAX = 0xfeff`
    * `NonMaxU32::MAX = 0xfeff_ffff`
    * `NonMaxU64::MAX = 0xfeff_ffff_ffff_ffff`
* removed `INVALID_UNDERLYING`. Instead every value above `MAX_UNDERLYING` is invalid
* removed `BITS_UNDERLYING`

## Fixes

* The previous implementation had a crucial bug. `Option<NonMaxU16>`, etc 
used a slightly different binary representation from what I expected.
This should now be fixed.
* little and big endian implementations were swapped


## [1.2.0] - 2025-07-13

## Added

* impl `Hash`

## [1.1.0] - 2025-07-13

## Added

* Little/Big-Endian variants of the non-max integers

## [1.0.0] - 2025-07-10

## Changes

* Renamed `U7`, etc to `NonMaxU8`
* Implemented exhaustive test suite

## Fixes

* Fixed all binary-operations implemented via trait, e.g. Sub, Mul, etc
    only add was correct
* minor fixes to documentation

## [0.1.0] - 2025-07-09

## Features

* `U7`, `U15`, `U31`, `U63` that implement methods and traits found for rusts unsigned types

<!-- next-url -->
[Unreleased]: https://github.com/wasabi375/nonmaxunsigned/compare/v1.2.0...HEAD
[1.2.0]: https://github.com/wasabi375/nonmaxunsigned/compare/v1.1.0...v1.2.0
[1.1.0]: https://github.com/wasabi375/nonmaxunsigned/compare/v1.0.0...v1.1.0
[1.0.0]: https://github.com/wasabi375/nonmaxunsigned/compare/v0.1.0...v1.0.0
[0.1.0]: https://github.com/wasabi375/nonmaxunsigned/compare/4784bcdc3f86be0b1d75908e323a40ba49734ad7...v0.1.0
