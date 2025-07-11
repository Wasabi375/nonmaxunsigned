#![doc = include_str!("../README.md")]
#![no_std]
#![deny(missing_docs)]

use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Sub, SubAssign,
};

/// NonMaxU8 is a nonmax version of [u8]
#[derive(Clone, Copy)]
#[repr(transparent)]
#[allow(dead_code)]
pub struct NonMaxU8(NonMaxU8Internal);

/// NonMaxU16 is a nonmax version of [u16]
#[derive(Clone, Copy)]
#[repr(C)]
#[allow(dead_code)]
#[cfg(target_endian = "little")]
pub struct NonMaxU16(NonMaxU8, u8);
/// NonMaxU16 is a nonmax version of [u16]
#[cfg(target_endian = "big")]
#[derive(Clone, Copy)]
#[repr(C)]
#[allow(dead_code)]
pub struct NonMaxU16(u8, NonMaxU8);

/// NonMaxU32 is a nonmax version of [u32]
#[derive(Clone, Copy)]
#[repr(C)]
#[allow(dead_code)]
#[cfg(target_endian = "little")]
pub struct NonMaxU32(NonMaxU8, u8, u16);
/// NonMaxU32 is a nonmax version of [u32]
#[derive(Clone, Copy)]
#[repr(C)]
#[allow(dead_code)]
#[cfg(target_endian = "big")]
pub struct NonMaxU32(u16, u8, NonMaxU8);

/// NonMaxU64 is a nonmax version of [u64]
#[derive(Clone, Copy)]
#[repr(C)]
#[allow(dead_code)]
#[cfg(target_endian = "little")]
pub struct NonMaxU64(NonMaxU8, u8, u16, u32);
/// NonMaxU64 is a nonmax version of [u64]
#[derive(Clone, Copy)]
#[repr(C)]
#[allow(dead_code)]
#[cfg(target_endian = "big")]
pub struct NonMaxU64(u32, u16, u8, NonMaxU8);

// NOTE: copy past from rust-lang: https://github.com/rust-lang/rust/blob/ab68b0fb26485ab1fa6977b2d8b59cc8a171c4aa/library/core/src/internal_macros.rs
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<$u> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            #[track_caller]
            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, other)
            }
        }

        impl $imp<&$u> for $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            #[track_caller]
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
                $imp::$method(self, *other)
            }
        }

        impl $imp<&$u> for &$t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            #[track_caller]
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    };
}

// NOTE: copy past from rust-lang: https://github.com/rust-lang/rust/blob/ab68b0fb26485ab1fa6977b2d8b59cc8a171c4aa/library/core/src/internal_macros.rs
macro_rules! forward_ref_op_assign {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl $imp<&$u> for $t {
            #[inline]
            #[track_caller]
            fn $method(&mut self, other: &$u) {
                $imp::$method(self, *other);
            }
        }
    };
}

macro_rules! impl_binop {
    (impl $imp:ident, $method:ident, $type:ty, $primitive:ty) => {
        impl $imp for $type {
            type Output = $type;

            fn $method(self, other: $type) -> $type {
                let primitive = self.get().$method(other.get());
                match Self::new(primitive) {
                    Some(res) => res,
                    None => panic!(
                        "{}::{} resulted in forbidden max value({}). Use `checked_{}` instead",
                        stringify!($type),
                        stringify!($method),
                        Self::INVALID_UNDERLYING,
                        stringify!($method),
                    ),
                }
            }
        }

        impl $imp<$primitive> for $type {
            type Output = $type;

            fn $method(self, other: $primitive) -> $type {
                let primitive = self.get().$method(other);
                match Self::new(primitive) {
                    Some(res) => res,
                    None => panic!(
                        "{}::{} resulted in forbidden max value({}). Use `checked_{}` instead",
                        stringify!($type),
                        stringify!($method),
                        Self::INVALID_UNDERLYING,
                        stringify!($method),
                    )
                }
            }
        }

        forward_ref_binop!(impl $imp, $method for $type, $type);
        forward_ref_binop!(impl $imp, $method for $type, $primitive);
    };
}

macro_rules! impl_assign_op {
    (impl $imp:ident, $method:ident, $binop:ident, $op:ident, $type:ty, $primitive:ty) => {
        impl $imp for $type where $type: $binop,
        {
            fn $method(&mut self, other: $type) {
                *self = self.$op(other)
            }
        }

        impl $imp<$primitive> for $type where $type: $binop<$primitive> {
            fn $method(&mut self, other: $primitive) {
                *self = self.$op(other)
            }
        }

        forward_ref_op_assign!(impl $imp, $method for $type, $type);
        forward_ref_op_assign!(impl $imp, $method for $type, $primitive);
    };
}

#[allow(unused_macros)]
macro_rules! option_op {
    ($type:ty, $op:ident, $(doc = $doc:tt)*) => {
        $(#[doc = $doc])*
        pub const fn $op(self, rhs: $type) -> Option<$type> {
            match self.get().$op(rhs.get()) {
                Some(primitive) => <$type>::new(primitive),
                None => None,
            }
        }
    };
}

#[cfg(feature = "checked-ops")]
macro_rules! checked_ops {
    ($type:ty) => {
        option_op!($type, checked_add,
            doc = "Checked integer addition. Computes `self + rhs`, returning `None` if overflow occured."
        );
        option_op!($type, checked_sub,
            doc = "Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occured."
        );
        option_op!($type, checked_mul,
            doc = "Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow occured."
        );
        option_op!($type, checked_div,
            doc = "Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0`."
        );
        option_op!($type, checked_div_euclid,
            doc = "Checked Euclidean division. Computes `self.div_euclid(rhs)`, returning `None` if `rhs == 0`."
            doc = ""
            doc = "Strict division on unsigned types is just normal division. There’s no way overflow could ever happen."
            doc = "This function exists so that all operations are accounted for in the strict operations."
            doc = "Since, for the positive integers, all common definitions of division are equal, this is exactly equal to self.strict_div(rhs)."
        );
        option_op!($type, checked_rem,
            doc = "Checked integer division. Computes `self % rhs`, returning `None` if `rhs == 0`."
        );

        #[doc = "Checked integer division. Computes `self << rhs`, returning `None` if `rhs` is larger than or equal to the number of bits in `self`."]
        pub const fn checked_shl(self, rhs:u32) -> Option<$type>{
            match self.get().checked_shl(rhs){
                Some(primitive) =>  <$type>::new(primitive),
                None => None,
            }
        }

        #[doc = "Checked integer division. Computes `self >> rhs`, returning `None` if `rhs` is larger than or equal to the number of bits in `self`."]
        pub const fn checked_shr(self, rhs:u32) -> Option<$type>{
            match self.get().checked_shr(rhs){
                Some(primitive) =>  <$type>::new(primitive),
                None => None,
            }
        }

        /// Returns the logarithm of the number with respect to an arbitrary base, rounded down.
        ///
        /// Returns `None` if the number is zero, or if the base is not at least 2.
        ///
        /// This method might not be optimized owing to implementation details;
        /// `checked_ilog2` can produce results more efficiently for base 2, and `checked_ilog10` can produce results more efficiently for base 10.
        pub const fn checked_ilog(self, base: $type) -> Option<u32> {
            self.get().checked_ilog(base.get())
        }

        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        /// Returns `None` if the number is zero.
        pub const fn checked_ilog2(self) -> Option<u32> {
            self.get().checked_ilog2()
        }

        /// Returns the base 10 logarithm of the number, rounded down.
        ///
        /// Returns `None` if the number is zero.
        pub const fn checked_ilog10(self) -> Option<u32> {
            self.get().checked_ilog10()
        }
    };
}

#[cfg(test)]
macro_rules! test_binop {
    ($op:ident for $type:ty, $primitive:ty => $(($a:expr, $b:expr; $res:expr)),+ access: $access:tt) => {
        #[test]
        fn $op() {
            $(
                assert_eq!(
                    $access(<$type>::new($a).unwrap().$op(<$type>::new($b).unwrap())),
                    ($a as $primitive).$op($b as $primitive),
                    "NonMax op matches primitive op"
                );
                assert_eq!(
                    $access(<$type>::new($a).unwrap().$op(<$type>::new($b).unwrap())),
                    $res,
                    "NonMax op has expected result"
                );
                assert_eq!(
                    ($a as $primitive).$op($b as $primitive),
                    $res,
                    "primitive op has expected result"
                );
            )+
        }
    };
    ($op:ident for $type:ty, $primitive:ty => $(($a:expr, $b:expr; $res:expr)),+) => {
        test_binop!($op for $type, $primitive => $(($a, $b; $res)),+ access: (|v| { <$type>::get(v) }));
    };
    (direct $op:ident for $type:ty, $primitive:ty => $(($a:expr, $b:expr; $res:expr)),+) => {
        test_binop!($op for $type, $primitive => $(($a, $b; $res)),+ access: (|v| { v }));
    };
    (option $op:ident for $type:ty, $primitive:ty => $(($a:expr, $b:expr; $res:expr)),+) => {
        test_binop!($op for $type, $primitive => $(($a, $b; $res)),+ access: (|v| { Option::map(v, |v| { <$type>::get(v) }) }));
    };
    (checked $op:ident for $type:ty, $primitive:ty => $(($a:expr, $b:expr; $res:expr)),+) => {
        #[test]
        fn $op() {
            $(
                {
                    let primitive_res: Option<$primitive> = ($a as $primitive).$op($b as $primitive);
                    let primitive_res = primitive_res
                        .map(|v| <$type>::new(v))
                        .flatten()
                        .map(|v| <$type>::get(v));
                    assert_eq!(
                        Option::map(<$type>::new($a).unwrap().$op(<$type>::new($b).unwrap()), |v| { <$type>::get(v) }),
                        primitive_res,
                        "NonMax op matches primitive op"
                    );
                    assert_eq!(
                        Option::map(<$type>::new($a).unwrap().$op(<$type>::new($b).unwrap()), |v| { v.get() }),
                        $res,
                        "NonMax op has expected result"
                    );
                    assert_eq!(
                        primitive_res,
                        $res,
                        "primitive op has expected result"
                    );
                }
            )+
        }

    };
}

#[cfg(test)]
macro_rules! test_unop {
    ($op:ident for $type:ty, $primitive:ty => $(($a:expr; $res:expr)),+ access: $access:tt) => {
        #[test]
        fn $op() {
            $(
                assert_eq!(
                    $access(<$type>::new($a).unwrap().$op()),
                    ($a as $primitive).$op(),
                    "NonMax op matches primitive op"
                );
                assert_eq!(
                    $access(<$type>::new($a).unwrap().$op()),
                    $res,
                    "NonMax op has expected result"
                );
                assert_eq!(
                    ($a as $primitive).$op(),
                    $res,
                    "primitive op has expected result"
                );

            )+
        }
    };
    ($op:ident for $type:ty, $primitive:ty => $(($a:expr; $res:expr)),+ access: $access:tt) => {
        test_unop!($op for $type, $primitive =>  $(($a; $res)),+ access: (|v| { <$type>::get(v) }));
    };
    (direct $op:ident for $type:ty, $primitive:ty => $(($a:expr; $res:expr)),+) => {
        test_unop!($op for $type, $primitive => $(($a; $res)),+ access: (|v| { v }));
    };
    (option $op:ident for $type:ty, $primitive:ty => $(($a:expr; $res:expr)),+) => {
        test_unop!($op for $type, $primitive => $(($a; $res)),+ access: (|v| { Option::map(v, |v| { <$type>::get(v) }) }));
    };

}

macro_rules! non_max_impl {
    ($type:ty, $primitive:ty, $test_name:ident) => {
        impl $type {

            /// The smallest value that can be respresented by this integer type
            pub const MIN: Self = unsafe {
                // Safety: 0 is never max
                Self::new_unchecked(0)
            };

            /// The largest value that can be respresented by this integer type
            pub const MAX: Self = unsafe {
                // Safety: max - 1 is never max
                Self::new_unchecked(<$primitive>::MAX - 1)
            };


            /// The size of this integer type in bits
            pub const BITS: u32 = <$primitive>::BITS - 1;

            /// The size of the underlying interger type in bits
            #[doc = concat!("This is the same as `BITS` on the result type of [Self::get] ([", stringify!($primitive), "])")]
            pub const BITS_UNDERLYING: u32 = <$primitive>::BITS;

            /// The value of the underlying integer that can *not* be represented
            pub const INVALID_UNDERLYING: $primitive = <$primitive>::MAX;

            /// The maximum value that can be safely converted into [Self]
            pub const MAX_UNDERLYING: $primitive = <$primitive>::MAX - 1;

            /// Create a new [Self] or `None` if value is the max of the underlying integer type
            pub const fn new(value: $primitive) -> Option<Self> {
                if value == Self::INVALID_UNDERLYING {
                    None
                } else {
                    unsafe {
                        // Safety: value is not MAX
                        Some(Self::new_unchecked(value))
                    }
                }
            }

            /// Create a new [Self] without checking if the value is the max of the underlying integer type
            ///
            /// # Safety
            ///
            #[doc = concat!("`value` must not be `", stringify!($primitive), "::MAX`")]
            pub const unsafe fn new_unchecked(value: $primitive) -> Self {
                assert!(value != Self::INVALID_UNDERLYING);
                unsafe {
                    // Safety: $primitive and Self have the same size.
                    // Crate ensures that the only invalid bitpattern for Self
                    // matches $primitive::MAX
                    core::mem::transmute_copy(&value)
                }
            }

            /// Return the underlying integer type
            pub const fn get(self) -> $primitive {
                unsafe {
                    // Safety: primitive type can be created from any bit-pattern
                    // and $type and $primtive have the same size
                    core::mem::transmute_copy(&self)
                }
            }

            /// Computes the absolute difference between `self` and `other`.
            pub const fn abs_diff(self,other:Self) -> Self {
                let primitive = self.get().abs_diff(other.get());
                unsafe {
                    // Safety: diff is nerver max
                    Self::new_unchecked(primitive)
                }
            }

            /// Calculates the quotient of self and rhs, rounding the result towards positive infinity.
            pub const fn div_ceil(self,other:Self) -> Self {
                let primitive = self.get().div_ceil(other.get());
                unsafe {
                    // Safety: div is nerver max
                    Self::new_unchecked(primitive)
                }
            }

            /// Returns `true` if `self` is an integer multiple of `rhs`, and false otherwise.
            ///
            /// This function is equivalent to self % rhs == 0, except that it will not panic for `rhs == 0`.
            /// Instead, `0.is_multiple_of(0) == true`, and for any non-zero `n`, `n.is_multiple_of(0) == false`.
            pub const fn is_multiple_of(self, rhs: Self) -> bool {
                self.get().is_multiple_of(rhs.get())
            }

            /// Returns true if and only if `self == 2^k` for some unsigned integer `k`.
            pub const fn is_power_of_two(self) -> bool {
                self.get().is_power_of_two()
            }

            /// Returns the smallest power of two greater than or equal to self. If the next power of two is
            /// greater than the type’s maximum value, `None` is returned, otherwise the power of two is wrapped in Some.
            pub const fn checked_next_power_of_two(self) -> Option<Self> {
                match self.get().checked_next_power_of_two() {
                    Some(primitive) => Self::new(primitive),
                    None => None
                }
            }

            /// Calculates the smallest value greater than or equal to self that is a multiple of rhs. Returns None if rhs is zero or the operation would result in overflow.
            pub const fn checked_next_multiple_of(self,other:Self) -> Option<Self> {
                match self.get().checked_next_multiple_of(other.get()) {
                    Some(primitive) => Self::new(primitive),
                    None => None
                }
            }

            /// Calculates the midpoint (average) between self and rhs.
            ///
            /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a sufficiently-large unsigned integral type.
            /// This implies that the result is always rounded towards zero and that no overflow will ever occur.
            pub const fn midpoint(self,other:Self) -> Self {
                let primitive = self.get().midpoint(other.get());
                unsafe {
                    // Safety: midpoint is nerver max
                    Self::new_unchecked(primitive)
                }
            }

            /// Returns the logarithm of the number with respect to an arbitrary base, rounded down.
            ///
            /// This method might not be optimized owing to implementation details;
            /// `ilog2` can produce results more efficiently for base 2, and `ilog10` can produce results more efficiently for base 10.
            ///
            /// # Panics
            ///
            /// This function will panic if self is zero, or if base is less than 2.
            pub const fn ilog(self, base: Self) -> u32 {
                self.get().ilog(base.get())
            }


            /// Returns the base 2 logarithm of the number, rounded down.
            ///
            /// # Panics
            ///
            /// This function will panic if self is zero.
            pub const fn ilog2(self) -> u32 {
                self.get().ilog2()
            }

            /// Returns the base 10 logarithm of the number, rounded down.
            ///
            /// # Panics
            ///
            /// This function will panic if self is zero.
            pub const fn ilog10(self) -> u32 {
                self.get().ilog10()
            }

            /// Returns the square root of the number, rounded down.
            pub const fn isqrt(self) -> Self {
                let primitive = self.get().isqrt();
                unsafe {
                    // Safety: squrt is never max
                    Self::new_unchecked(primitive)
                }
            }

            #[cfg(feature = "checked-ops")]
            checked_ops!($type);

        }

        impl PartialEq for $type {
            fn eq(&self, other: &Self) -> bool {
                self.get() == other.get()
            }
        }

        impl Eq for $type {}

        impl PartialOrd for $type {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.get().cmp(&other.get()))
            }
        }

        impl Ord for $type {
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                self.get().cmp(&other.get())
            }
        }

        impl core::fmt::Debug for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_tuple(stringify!($type)).field(&self.get()).finish()
            }
        }

        impl core::fmt::Display for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                self.get().fmt(f)
            }
        }

        impl core::fmt::Binary for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                self.get().fmt(f)
            }
        }

        impl core::fmt::LowerHex for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                self.get().fmt(f)
            }
        }

        impl core::fmt::UpperHex for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                self.get().fmt(f)
            }
        }

        impl core::fmt::Octal for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                self.get().fmt(f)
            }
        }

        impl_binop!(impl Add, add, $type, $primitive);
        impl_binop!(impl Sub, sub, $type, $primitive);
        impl_binop!(impl Mul, mul, $type, $primitive);
        impl_binop!(impl Div, div, $type, $primitive);

        impl_binop!(impl BitAnd, bitand, $type, $primitive);
        impl_binop!(impl BitOr, bitor, $type, $primitive);
        impl_binop!(impl BitXor, bitxor, $type, $primitive);

        impl_assign_op!(impl AddAssign, add_assign, Add, add, $type, $primitive);
        impl_assign_op!(impl SubAssign, sub_assign, Sub, sub, $type, $primitive);
        impl_assign_op!(impl MulAssign, mul_assign, Mul, mul, $type, $primitive);
        impl_assign_op!(impl DivAssign, div_assign, Div, div, $type, $primitive);


        impl_assign_op!(impl BitAndAssign, bitand_assign, BitAnd, bitand, $type, $primitive);
        impl_assign_op!(impl BitOrAssign, bitor_assign, BitOr, bitor, $type, $primitive);
        impl_assign_op!(impl BitXorAssign, bitxor_assign, BitXor, bitxor, $type, $primitive);

        impl TryFrom<$primitive> for $type {
            type Error = PrimitiveIsMaxError<$primitive>;

            fn try_from(value: $primitive) -> Result<Self, Self::Error> {
                Self::new(value).ok_or(PrimitiveIsMaxError(Self::INVALID_UNDERLYING))
            }
        }

        impl Into<$primitive> for $type {
            fn into(self) -> $primitive {
                self.get()
            }
        }

        #[cfg(test)]
        mod $test_name {
            use super::*;

            #[test]
            fn size() {
                assert_eq!(size_of::<$type>(), size_of::<$primitive>());
                assert_eq!(size_of::<Option<$type>>(), size_of::<$primitive>());
            }

            test_binop!(abs_diff for $type, $primitive => (10, 5; 5), (15, 25; 10));
            test_binop!(div_ceil for $type, $primitive => (10, 5; 2), (12, 7; 2));

            test_unop!(direct is_power_of_two for $type, $primitive => (8; true), (42; false));
            test_unop!(option checked_next_power_of_two for $type, $primitive => (8; Some(8)), (42; Some(64)), (<$type>::MAX_UNDERLYING; None));

            test_binop!(direct is_multiple_of for $type, $primitive => (10, 5; true), (42, 11; false));
            test_binop!(checked checked_next_multiple_of for $type, $primitive => (8, 4; Some(8)), (42, 16; Some(48)), (<$type>::MAX_UNDERLYING, 5; None));

            test_binop!(midpoint for $type, $primitive => (10, 0; 5));

            test_binop!(direct ilog for $type, $primitive => (10, 10; 1), (243, 3; 5), (250, 3; 5));
            test_unop!(direct ilog2 for $type, $primitive => (128; 7), (130; 7));
            test_unop!(direct ilog10 for $type, $primitive => (10; 1), (100; 2), (105; 2));

            test_binop!(checked checked_add for $type, $primitive => (10, 20; Some(30)), (<$type>::MAX_UNDERLYING, 1; None), (<$type>::MAX_UNDERLYING, 5; None));
            test_binop!(checked checked_mul for $type, $primitive => (10, 5; Some(50)), (<$type>::INVALID_UNDERLYING / 5, 5; None), (<$type>::MAX_UNDERLYING, 2; None));
            test_binop!(checked checked_div for $type, $primitive => (10, 5; Some(2)), (10, 0; None));
            test_binop!(checked checked_div_euclid for $type, $primitive => (10, 5; Some(2)), (10, 0; None));
            test_binop!(checked checked_sub for $type, $primitive => (10, 5; Some(5)), (5, 10; None), (22, 22; Some(0)));
            test_binop!(checked checked_rem for $type, $primitive => (10, 5; Some(0)), (11, 5; Some(1)), (10, 0; None));

            test_binop!(direct checked_ilog for $type, $primitive => (10, 10; Some(1)), (243, 3; Some(5)), (250, 3; Some(5)), (42, 1; None), (0, 4; None));
            test_unop!(direct checked_ilog2 for $type, $primitive => (128; Some(7)), (130; Some(7)), (0; None));
            test_unop!(direct checked_ilog10 for $type, $primitive => (10; Some(1)), (100; Some(2)), (105; Some(2)), (0; None));

            test_binop!(add for $type, $primitive => (12, 30; 42));
            test_binop!(sub for $type, $primitive => (30, 12; 18));
            test_binop!(mul for $type, $primitive => (5, 12; 60));
            test_binop!(div for $type, $primitive => (120, 8; 15));

            test_binop!(bitor for $type, $primitive => (0b01010, 0b1; 0b01011));
            test_binop!(bitand for $type, $primitive => (0b01010, 0b11; 0b10));
            test_binop!(bitxor for $type, $primitive => (0b01010, 0b11; 0b01001));

            #[test]
            fn checked_shl() {
                {
                    let primitive_res: Option<$primitive> = (0b10 as $primitive).checked_shl(2);
                    let primitive_res = primitive_res
                        .map(|v| <$type>::new(v))
                        .flatten()
                        .map(|v| <$type>::get(v));
                    assert_eq!(
                        Option::map(<$type>::new(0b10).unwrap().checked_shl(2), |v| {
                            <$type>::get(v)
                        }),
                        primitive_res,
                        "NonMax op matches primitive op"
                    );
                    assert_eq!(
                        Option::map(<$type>::new(0b10).unwrap().checked_shl(2), |v| {
                            v.get()
                        }),
                        (Some(0b1000)),
                        "NonMax op has expected result"
                    );
                    assert_eq!(
                        primitive_res,
                        (Some(0b1000)),
                        "primitive op has expected result"
                    );
                }
                {
                    let primitive_res: Option<$primitive> = (25 as $primitive).checked_shl(<$type>::BITS_UNDERLYING);
                    let primitive_res = primitive_res
                        .map(|v| <$type>::new(v))
                        .flatten()
                        .map(|v| <$type>::get(v));
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shl(<$type>::BITS_UNDERLYING),
                            |v| { <$type>::get(v) }
                        ),
                        primitive_res,
                        "NonMax op matches primitive op"
                    );
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shl(<$type>::BITS_UNDERLYING),
                            |v| { v.get() }
                        ),
                        None,
                        "NonMax op has expected result"
                    );
                    assert_eq!(primitive_res, None, "primitive op has expected result");
                }
            }

            #[test]
            fn checked_shr() {
                {
                    let primitive_res: Option<$primitive> = (0b1000 as $primitive).checked_shr(2);
                    let primitive_res = primitive_res
                        .map(|v| <$type>::new(v))
                        .flatten()
                        .map(|v| <$type>::get(v));
                    assert_eq!(
                        Option::map(<$type>::new(0b1000).unwrap().checked_shr(2), |v| {
                            <$type>::get(v)
                        }),
                        primitive_res,
                        "NonMax op matches primitive op"
                    );
                    assert_eq!(
                        Option::map(<$type>::new(0b1000).unwrap().checked_shr(2), |v| {
                            v.get()
                        }),
                        (Some(0b10)),
                        "NonMax op has expected result"
                    );
                    assert_eq!(
                        primitive_res,
                        (Some(0b10)),
                        "primitive op has expected result"
                    );
                }
                {
                    let primitive_res: Option<$primitive> = (25 as $primitive).checked_shr(<$type>::BITS_UNDERLYING);
                    let primitive_res = primitive_res
                        .map(|v| <$type>::new(v))
                        .flatten()
                        .map(|v| <$type>::get(v));
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shr(<$type>::BITS_UNDERLYING),
                            |v| { <$type>::get(v) }
                        ),
                        primitive_res,
                        "NonMax op matches primitive op"
                    );
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shr(<$type>::BITS_UNDERLYING),
                            |v| { v.get() }
                        ),
                        None,
                        "NonMax op has expected result"
                    );
                    assert_eq!(primitive_res, None, "primitive op has expected result");
                }
            }
        }
    };
}

/// Error type returned by [TryFrom] from primitive integer into nonmax versions
///
/// See [NonMaxU8], [NonMaxU16], [NonMaxU32], [NonMaxU64]
#[derive(Debug, Clone, Copy)]
pub struct PrimitiveIsMaxError<T>(pub T);

impl<T: core::fmt::Display> core::fmt::Display for PrimitiveIsMaxError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!("PrimitiveIsMaxError({})", self.0))
    }
}

impl<T: core::fmt::Display + core::fmt::Debug> core::error::Error for PrimitiveIsMaxError<T> {}

non_max_impl!(NonMaxU8, u8, u8_test);
non_max_impl!(NonMaxU16, u16, u16_test);
non_max_impl!(NonMaxU32, u32, u32_test);
non_max_impl!(NonMaxU64, u64, u64_test);

#[repr(u8)]
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
enum NonMaxU8Internal {
    V0 = 0,
    V1 = 1,
    V2 = 2,
    V3 = 3,
    V4 = 4,
    V5 = 5,
    V6 = 6,
    V7 = 7,
    V8 = 8,
    V9 = 9,
    V10 = 10,
    V11 = 11,
    V12 = 12,
    V13 = 13,
    V14 = 14,
    V15 = 15,
    V16 = 16,
    V17 = 17,
    V18 = 18,
    V19 = 19,
    V20 = 20,
    V21 = 21,
    V22 = 22,
    V23 = 23,
    V24 = 24,
    V25 = 25,
    V26 = 26,
    V27 = 27,
    V28 = 28,
    V29 = 29,
    V30 = 30,
    V31 = 31,
    V32 = 32,
    V33 = 33,
    V34 = 34,
    V35 = 35,
    V36 = 36,
    V37 = 37,
    V38 = 38,
    V39 = 39,
    V40 = 40,
    V41 = 41,
    V42 = 42,
    V43 = 43,
    V44 = 44,
    V45 = 45,
    V46 = 46,
    V47 = 47,
    V48 = 48,
    V49 = 49,
    V50 = 50,
    V51 = 51,
    V52 = 52,
    V53 = 53,
    V54 = 54,
    V55 = 55,
    V56 = 56,
    V57 = 57,
    V58 = 58,
    V59 = 59,
    V60 = 60,
    V61 = 61,
    V62 = 62,
    V63 = 63,
    V64 = 64,
    V65 = 65,
    V66 = 66,
    V67 = 67,
    V68 = 68,
    V69 = 69,
    V70 = 70,
    V71 = 71,
    V72 = 72,
    V73 = 73,
    V74 = 74,
    V75 = 75,
    V76 = 76,
    V77 = 77,
    V78 = 78,
    V79 = 79,
    V80 = 80,
    V81 = 81,
    V82 = 82,
    V83 = 83,
    V84 = 84,
    V85 = 85,
    V86 = 86,
    V87 = 87,
    V88 = 88,
    V89 = 89,
    V90 = 90,
    V91 = 91,
    V92 = 92,
    V93 = 93,
    V94 = 94,
    V95 = 95,
    V96 = 96,
    V97 = 97,
    V98 = 98,
    V99 = 99,
    V100 = 100,
    V101 = 101,
    V102 = 102,
    V103 = 103,
    V104 = 104,
    V105 = 105,
    V106 = 106,
    V107 = 107,
    V108 = 108,
    V109 = 109,
    V110 = 110,
    V111 = 111,
    V112 = 112,
    V113 = 113,
    V114 = 114,
    V115 = 115,
    V116 = 116,
    V117 = 117,
    V118 = 118,
    V119 = 119,
    V120 = 120,
    V121 = 121,
    V122 = 122,
    V123 = 123,
    V124 = 124,
    V125 = 125,
    V126 = 126,
    V127 = 127,
    V128 = 128,
    V129 = 129,
    V130 = 130,
    V131 = 131,
    V132 = 132,
    V133 = 133,
    V134 = 134,
    V135 = 135,
    V136 = 136,
    V137 = 137,
    V138 = 138,
    V139 = 139,
    V140 = 140,
    V141 = 141,
    V142 = 142,
    V143 = 143,
    V144 = 144,
    V145 = 145,
    V146 = 146,
    V147 = 147,
    V148 = 148,
    V149 = 149,
    V150 = 150,
    V151 = 151,
    V152 = 152,
    V153 = 153,
    V154 = 154,
    V155 = 155,
    V156 = 156,
    V157 = 157,
    V158 = 158,
    V159 = 159,
    V160 = 160,
    V161 = 161,
    V162 = 162,
    V163 = 163,
    V164 = 164,
    V165 = 165,
    V166 = 166,
    V167 = 167,
    V168 = 168,
    V169 = 169,
    V170 = 170,
    V171 = 171,
    V172 = 172,
    V173 = 173,
    V174 = 174,
    V175 = 175,
    V176 = 176,
    V177 = 177,
    V178 = 178,
    V179 = 179,
    V180 = 180,
    V181 = 181,
    V182 = 182,
    V183 = 183,
    V184 = 184,
    V185 = 185,
    V186 = 186,
    V187 = 187,
    V188 = 188,
    V189 = 189,
    V190 = 190,
    V191 = 191,
    V192 = 192,
    V193 = 193,
    V194 = 194,
    V195 = 195,
    V196 = 196,
    V197 = 197,
    V198 = 198,
    V199 = 199,
    V200 = 200,
    V201 = 201,
    V202 = 202,
    V203 = 203,
    V204 = 204,
    V205 = 205,
    V206 = 206,
    V207 = 207,
    V208 = 208,
    V209 = 209,
    V210 = 210,
    V211 = 211,
    V212 = 212,
    V213 = 213,
    V214 = 214,
    V215 = 215,
    V216 = 216,
    V217 = 217,
    V218 = 218,
    V219 = 219,
    V220 = 220,
    V221 = 221,
    V222 = 222,
    V223 = 223,
    V224 = 224,
    V225 = 225,
    V226 = 226,
    V227 = 227,
    V228 = 228,
    V229 = 229,
    V230 = 230,
    V231 = 231,
    V232 = 232,
    V233 = 233,
    V234 = 234,
    V235 = 235,
    V236 = 236,
    V237 = 237,
    V238 = 238,
    V239 = 239,
    V240 = 240,
    V241 = 241,
    V242 = 242,
    V243 = 243,
    V244 = 244,
    V245 = 245,
    V246 = 246,
    V247 = 247,
    V248 = 248,
    V249 = 249,
    V250 = 250,
    V251 = 251,
    V252 = 252,
    V253 = 253,
    V254 = 254,
}

#[cfg(test)]
mod internal_tests {

    use super::*;

    #[test]
    fn u7_internal_sizes() {
        assert_eq!(1, size_of::<NonMaxU8Internal>());
        assert_eq!(1, size_of::<Option<NonMaxU8Internal>>());
    }

    #[test]
    fn u7_max() {
        assert_eq!(NonMaxU8Internal::V254 as u8, u8::MAX - 1);
    }

    #[test]
    fn endianness_u15() {
        #[cfg(target_endian = "little")]
        let max = NonMaxU16(NonMaxU8(NonMaxU8Internal::V254), u8::MAX);
        #[cfg(target_endian = "big")]
        let max = NonMaxU16(u8::MAX, NonMaxU8(NonMaxU8Internal::V254));

        assert_eq!(
            max.get(),
            u16::MAX - 1,
            "{:b} != {:b}",
            max.get(),
            u16::MAX - 1
        );
        assert_eq!(max, NonMaxU16::MAX);
    }

    #[test]
    fn endianness_u31() {
        #[cfg(target_endian = "little")]
        let max = NonMaxU32(NonMaxU8(NonMaxU8Internal::V254), u8::MAX, u16::MAX);
        #[cfg(target_endian = "big")]
        let max = NonMaxU32(u16::MAX, u8::MAX, NonMaxU8(NonMaxU8Internal::V254));

        assert_eq!(
            max.get(),
            u32::MAX - 1,
            "{:b} != {:b}",
            max.get(),
            u16::MAX - 1
        );
        assert_eq!(max, NonMaxU32::MAX);
    }

    #[test]
    fn endianness_u63() {
        #[cfg(target_endian = "little")]
        let max = NonMaxU64(
            NonMaxU8(NonMaxU8Internal::V254),
            u8::MAX,
            u16::MAX,
            u32::MAX,
        );
        #[cfg(target_endian = "big")]
        let max = NonMaxU16(
            u32::MAX,
            u16::MAX,
            u8::MAX,
            NonMaxU8(NonMaxU8Internal::V254),
        );

        assert_eq!(
            max.get(),
            u64::MAX - 1,
            "{:b} != {:b}",
            max.get(),
            u16::MAX - 1
        );
        assert_eq!(max, NonMaxU64::MAX);
    }
}
