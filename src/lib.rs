#![doc = include_str!("../README.md")]
#![no_std]
#![warn(missing_docs)]

use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Sub, SubAssign,
};

macro_rules! gen_doc {
    ($endian:literal $type:ident, $primitive:ty, $warn:literal, $item:item) => {
        #[doc = concat!("[", stringify!($type), "] is a nonmax, ", $endian, "-endian version of [", stringify!($primitive),"].")]
        #[doc = ""]
        #[doc = concat!("This type behaves mostly like a `", stringify!($primitive), "` however `", stringify!($primitive), "::MAX` is not a valid value.")]
        #[cfg_attr($warn, doc = concat!("Also this is stored as a ", $endian, "-endian integer."))]
        #[cfg_attr($warn, doc = "This means that on systems with a different endianness there might be a small overhead in accessing this value")]
        $item
    };
}

macro_rules! nonmax_struct {
    ($endian:literal $type:ident, $primitive:ty, $inner:tt) => {
        gen_doc!($endian $type, $primitive, true,
            #[derive(Clone, Copy)]
            #[repr(C)]
            #[allow(dead_code)]
            #[cfg(any(target_endian = $endian, feature = "endian-conversion"))]
            pub struct $type $inner;
        );
    };
}

gen_doc!(
    "native"
    NonMaxU8,
    u8,
    false,
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    #[allow(dead_code)]
    pub struct NonMaxU8(NonMaxU8Internal);
);

gen_doc!("native" NonMaxU16, u16, false,
    #[cfg(target_endian = "little")]
    pub type NonMaxU16 = NonMaxU16Le;
);

gen_doc!("native" NonMaxU16, u16, false,
    #[cfg(target_endian = "big")]
    pub type NonMaxU16 = NonMaxU16Be;
);

gen_doc!("native" NonMaxU32, u32, false,
    #[cfg(target_endian = "little")]
    pub type NonMaxU32 = NonMaxU32Le;
);

gen_doc!("native" NonMaxU32, u32, false,
    #[cfg(target_endian = "big")]
    pub type NonMaxU32 = NonMaxU32Be;
);

gen_doc!("native" NonMaxU64, u64, false,
    #[cfg(target_endian = "little")]
    pub type NonMaxU64 = NonMaxU64Le;
);

gen_doc!("native" NonMaxU64, u64, false,
    #[cfg(target_endian = "big")]
    pub type NonMaxU64 = NonMaxU64Be;
);

nonmax_struct!("little" NonMaxU16Le, u16, (u8, NonMaxU8));
nonmax_struct!("little" NonMaxU32Le, u32, ([u8; 3], NonMaxU8));
nonmax_struct!("little" NonMaxU64Le, u64, ([u8; 7], NonMaxU8));

nonmax_struct!("big" NonMaxU16Be, u16, (NonMaxU8, u8));
nonmax_struct!("big" NonMaxU32Be, u32, (NonMaxU8, [u8; 3]));
nonmax_struct!("big" NonMaxU64Be, u64, (NonMaxU8, [u8; 7]));

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
                        "{}::{} resulted in forbidden value > {}. Use `checked_{}` instead",
                        stringify!($type),
                        stringify!($method),
                        Self::MAX_UNDERLYING,
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
                        "{}::{} resulted in forbidden value > {}. Use `checked_{}` instead",
                        stringify!($type),
                        stringify!($method),
                        Self::MAX_UNDERLYING,
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
    ($type:ty, $primitive:ty, $to_endian:ident, $from_endian:ident, $test_name:ident, bytes: $bytes:literal, max_hex: $max_hex:literal) => {
        impl $type {

            /// The smallest value that can be respresented by this integer type
            pub const MIN: Self = unsafe {
                // Safety: 0 is never max
                Self::new_unchecked(0)
            };

            #[doc = concat!("The largest value(", $max_hex, ") that can be respresented by this integer type")]
            pub const MAX: Self = unsafe {
                Self::new_unchecked(Self::MAX_UNDERLYING)
            };

            /// The size of this integer type in bits
            pub const BITS: u32 = <$primitive>::BITS;

            #[doc = concat!("The maximum value(", $max_hex, ") that can be safely converted into [Self]")]
            pub const MAX_UNDERLYING: $primitive = (255 << (8 * ($bytes - 1))) - 1;

            /// Create a new [Self] or `None` if value is the max of the underlying integer type
            pub const fn new(value: $primitive) -> Option<Self> {
                if value > Self::MAX_UNDERLYING {
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
                assert!(value <= Self::MAX_UNDERLYING);
                let value = value.$to_endian();
                unsafe {
                    // Safety: $primitive and Self have the same size.
                    // Crate ensures that the only invalid bitpattern for Self
                    // matches $primitive::MAX
                    core::mem::transmute_copy(&value)
                }
            }

            /// Return the underlying integer type
            ///
            #[cfg_attr(feature = "endian-conversion", doc = "The result is a native-endian integer")]
            pub const fn get(self) -> $primitive {
                let value = self.get_underlying();
                <$primitive>::$from_endian(value)
            }

            /// Return the underlying integer type
            ///
            /// Unlike [Self::get] this does not convert the result into a native-endian integer.
            pub const fn get_underlying(self) -> $primitive {
                unsafe {
                    // Safety: primitive type can be created from any bit-pattern
                    // and $type and $primtive have the same size
                    core::mem::transmute_copy(&self)
                }
            }


            /// Returns the memory representation of this integer as a byte array.
            ///
            #[cfg_attr(feature = "endian-conversion", doc = "The result is in the underlying endianness. `to_ne_bytes` should be used for native endianness.")]
            pub const fn to_bytes(self) -> [u8; $bytes] {
                unsafe {
                    // Safety: size_of(self) == $bytes
                    core::mem::transmute_copy(&self)
                }
            }

            /// Returns the memory representation of this integer as a byte array in native byte order.
            ///
            #[cfg_attr(feature = "endian-conversion", doc = "As the target platform’s native endianness is used,")]
            #[cfg_attr(feature = "endian-conversion", doc = "portable code should use [self.to_le_bytes] or [self.to_be_bytes], as appropriate, instead.")]
            pub const fn to_ne_bytes(self) -> [u8; $bytes] {
                self.get().to_ne_bytes()
            }

            /// Returns the memory representation of this integer as a byte array in little-endian order.
            pub const fn to_le_bytes(self) -> [u8; $bytes] {
                self.get().to_le_bytes()
            }

            /// Returns the memory representation of this integer as a byte array in big-endian order.
            pub const fn to_be_bytes(self) -> [u8; $bytes] {
                self.get().to_be_bytes()
            }

            /// Creates a [Self] from it's memory representation s a byte array in native endianness.
            ///
            /// As the target platform’s native endianness is used, portable code likely wants to use `from_be_bytes` or `from_le_bytes`, as appropriate instead.
            pub const fn from_ne_bytes(bytes: [u8; $bytes]) -> Option<Self> {
                Self::new(<$primitive>::from_ne_bytes(bytes))
            }

            /// Creates a [Self] from it's memory representation s a byte array in little-endian.
            pub const fn from_le_bytes(bytes: [u8; $bytes]) -> Option<Self> {
                Self::new(<$primitive>::from_le_bytes(bytes))
            }

            /// Creates a [Self] from it's memory representation s a byte array in big-endian.
            pub const fn from_be_bytes(bytes: [u8; $bytes]) -> Option<Self> {
                Self::new(<$primitive>::from_be_bytes(bytes))
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

        impl core::hash::Hash for $type {
            fn hash<H>(&self, state: &mut H) where H: core::hash::Hasher {
                self.get().hash(state);
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
            type Error = PrimitiveGreaterMaxError<$primitive>;

            fn try_from(value: $primitive) -> Result<Self, Self::Error> {
                Self::new(value).ok_or(PrimitiveGreaterMaxError(Self::MAX_UNDERLYING))
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

            #[test]
            fn option() {
                let non_max = <$type>::new(89).unwrap();

                assert_eq!(non_max.to_bytes(), unsafe { core::mem::transmute_copy::<_, [u8; $bytes]>(&Some(non_max)) });
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
            test_binop!(checked checked_mul for $type, $primitive => (10, 5; Some(50)), ((<$type>::MAX_UNDERLYING + 1) / 5, 5; None), (<$type>::MAX_UNDERLYING, 2; None));
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
                    let primitive_res: Option<$primitive> = (25 as $primitive).checked_shl(<$type>::BITS);
                    let primitive_res = primitive_res
                        .map(|v| <$type>::new(v))
                        .flatten()
                        .map(|v| <$type>::get(v));
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shl(<$type>::BITS),
                            |v| { <$type>::get(v) }
                        ),
                        primitive_res,
                        "NonMax op matches primitive op"
                    );
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shl(<$type>::BITS),
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
                    let primitive_res: Option<$primitive> = (25 as $primitive).checked_shr(<$type>::BITS);
                    let primitive_res = primitive_res
                        .map(|v| <$type>::new(v))
                        .flatten()
                        .map(|v| <$type>::get(v));
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shr(<$type>::BITS),
                            |v| { <$type>::get(v) }
                        ),
                        primitive_res,
                        "NonMax op matches primitive op"
                    );
                    assert_eq!(
                        Option::map(
                            <$type>::new(25)
                                .unwrap()
                                .checked_shr(<$type>::BITS),
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
pub struct PrimitiveGreaterMaxError<T>(pub T);

impl<T: core::fmt::Display> core::fmt::Display for PrimitiveGreaterMaxError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!("PrimitiveGreaterMaxError({})", self.0))
    }
}

impl<T: core::fmt::Display + core::fmt::Debug> core::error::Error for PrimitiveGreaterMaxError<T> {}

non_max_impl!(NonMaxU8, u8, to_le, from_le, test_u8, bytes: 1, max_hex: "0xfe");

#[cfg(any(target_endian = "little", feature = "endian-conversion"))]
non_max_impl!(NonMaxU16Le, u16, to_le, from_le, u16_test_le, bytes: 2, max_hex: "0xfeff");
#[cfg(any(target_endian = "little", feature = "endian-conversion"))]
non_max_impl!(NonMaxU32Le, u32, to_le, from_le, u32_test_le, bytes: 4, max_hex: "0xfeff_ffff");
#[cfg(any(target_endian = "little", feature = "endian-conversion"))]
non_max_impl!(NonMaxU64Le, u64, to_le, from_le, u64_test_le, bytes: 8, max_hex: "0xfeff_ffff_ffff_ffff");

#[cfg(any(target_endian = "big", feature = "endian-conversion"))]
non_max_impl!(NonMaxU16Be, u16, to_be, from_be, u16_test_be, bytes: 2, max_hex: "0xfeff");
#[cfg(any(target_endian = "big", feature = "endian-conversion"))]
non_max_impl!(NonMaxU32Be, u32, to_be, from_be, u32_test_be, bytes: 4, max_hex: "0xfeff_ffff");
#[cfg(any(target_endian = "big", feature = "endian-conversion"))]
non_max_impl!(NonMaxU64Be, u64, to_be, from_be, u64_test_be, bytes: 8, max_hex: "0xfeff_ffff_ffff_ffff");

macro_rules! impl_endian_conversion {
    ($le:ty, $be:ty) => {
        #[cfg(feature = "endian-conversion")]
        impl $le {
            /// Converts [Self] to little-endian
            ///
            /// This is a no-op added for parity
            #[inline(always)]
            pub fn to_le(self) -> $le {
                self
            }

            /// Creates a [Self] from a little-endian integer
            ///
            /// This is a no-op added for parity
            pub fn from_le(value: $le) -> $le {
                value
            }

            /// Converts [Self] to big-endian
            #[inline(always)]
            pub fn to_be(self) -> $be {
                unsafe {
                    // Safety: self is non_max, this does not change with endianness
                    <$be>::new_unchecked(self.get())
                }
            }

            /// Creates a [Self] from a big-endian integer
            #[inline(always)]
            pub fn from_be(value: $be) -> $le {
                value.to_le()
            }

            /// Converts [Self] to little-endian
            ///
            /// This is a no-op on a little-endian system
            #[cfg(target_endian = "little")]
            #[inline(always)]
            pub fn to_native(self) -> $le {
                self
            }

            /// Converts [Self] to little-endian
            #[cfg(target_endian = "big")]
            #[inline(always)]
            pub fn to_native(self) -> $be {
                self.to_be()
            }
        }

        #[cfg(feature = "endian-conversion")]
        impl $be {
            /// Converts [Self] to little-endian
            #[inline(always)]
            pub fn to_le(self) -> $le {
                unsafe {
                    // Safety: self is non_max, this does not change with endianness
                    <$le>::new_unchecked(self.get())
                }
            }

            /// Creates a [Self] from a little-endian integer
            #[inline(always)]
            pub fn from_le(value: $le) -> $be {
                value.to_be()
            }

            /// Converts [Self] to big-endian
            ///
            /// This is a no-op added for parity
            #[inline(always)]
            pub fn to_be(self) -> $be {
                self
            }

            /// Creates a [Self] from a big-endian integer
            ///
            /// This is a no-op added for parity
            #[inline(always)]
            pub fn from_be(value: $be) -> $be {
                value
            }

            /// Converts [Self] to little-endian
            #[cfg(target_endian = "little")]
            #[inline(always)]
            pub fn to_native(self) -> $le {
                self.to_le()
            }

            /// Converts [Self] to little-endian
            ///
            /// This is a no-op on a big-endian system
            #[cfg(target_endian = "big")]
            #[inline(always)]
            pub fn to_native(self) -> $be {
                self
            }
        }
    };
}

impl_endian_conversion!(NonMaxU16Le, NonMaxU16Be);
impl_endian_conversion!(NonMaxU32Le, NonMaxU32Be);
impl_endian_conversion!(NonMaxU64Le, NonMaxU64Be);

#[repr(u8)]
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
#[cfg_attr(test, derive(strum_macros::EnumIter))]
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
    use core::mem::transmute_copy;

    use super::*;
    use strum::IntoEnumIterator;

    #[test]
    #[cfg(any(target_endian = "little", feature = "endian-conversion"))]
    fn u16_le_none() {
        let none: Option<NonMaxU16Le> = None;
        let none_bytes: [u8; 2] = unsafe { core::mem::transmute_copy(&none) };
        let none_primitive = u16::from_le(unsafe { core::mem::transmute_copy(&none) });

        assert_eq!(none_bytes[1], 255);
        assert!(none_primitive >= 255 << 8);
    }

    #[test]
    #[cfg(any(target_endian = "big", feature = "endian-conversion"))]
    fn u16_be_none() {
        let none: Option<NonMaxU16Be> = None;
        let none_bytes: [u8; 2] = unsafe { core::mem::transmute_copy(&none) };
        let none_primitive = u16::from_be(unsafe { core::mem::transmute_copy(&none) });

        assert_eq!(none_bytes[0], 255);
        assert!(none_primitive >= 255 << 8);
    }

    #[test]
    #[cfg(any(target_endian = "little", feature = "endian-conversion"))]
    fn u32_le_none() {
        let none: Option<NonMaxU32Le> = None;
        let none_bytes: [u8; 4] = unsafe { core::mem::transmute_copy(&none) };
        let none_primitive = u32::from_le(unsafe { core::mem::transmute_copy(&none) });

        assert_eq!(none_bytes[3], 255);
        assert!(none_primitive >= 255 << (8 * 3));
    }

    #[test]
    #[cfg(any(target_endian = "big", feature = "endian-conversion"))]
    fn u32_be_none() {
        let none: Option<NonMaxU32Be> = None;
        let none_bytes: [u8; 4] = unsafe { core::mem::transmute_copy(&none) };
        let none_primitive = u32::from_be(unsafe { core::mem::transmute_copy(&none) });

        assert_eq!(none_bytes[0], 255);
        assert!(none_primitive >= 255 << (8 * 3));
    }

    #[test]
    #[cfg(any(target_endian = "little", feature = "endian-conversion"))]
    fn u64_le_none() {
        let none: Option<NonMaxU64Le> = None;
        let none_bytes: [u8; 8] = unsafe { core::mem::transmute_copy(&none) };
        let none_primitive = u64::from_le(unsafe { core::mem::transmute_copy(&none) });

        assert_eq!(none_bytes[7], 255);
        assert!(none_primitive >= 255 << (8 * 7));
    }

    #[test]
    #[cfg(any(target_endian = "big", feature = "endian-conversion"))]
    fn u64_be_none() {
        let none: Option<NonMaxU64Be> = None;
        let none_bytes: [u8; 8] = unsafe { core::mem::transmute_copy(&none) };
        let none_primitive = u64::from_be(unsafe { core::mem::transmute_copy(&none) });

        assert_eq!(none_bytes[0], 255);
        assert!(none_primitive >= 255 << (8 * 7));
    }

    #[test]
    fn nonmaxu8_internal_sizes() {
        assert_eq!(1, size_of::<NonMaxU8Internal>());
        assert_eq!(1, size_of::<Option<NonMaxU8Internal>>());
    }

    #[test]
    fn nonmaxu8_max() {
        assert_eq!(NonMaxU8Internal::V254 as u8, u8::MAX - 1);
    }

    #[test]
    fn nonmaxu8_internal_variances_correct() {
        for (i, variant) in NonMaxU8Internal::iter().enumerate() {
            assert_eq!(i as u8, unsafe { transmute_copy(&variant) });
            assert_eq!(i as u8, unsafe { transmute_copy(&Some(variant)) });
        }
        assert_eq!(255u8, unsafe {
            transmute_copy(&Option::<NonMaxU8Internal>::None)
        });
    }

    #[cfg(any(target_endian = "big", feature = "endian-conversion"))]
    #[test]
    fn endianness_u16_little() {
        let max = NonMaxU16Be(NonMaxU8(NonMaxU8Internal::V254), u8::MAX);

        assert_eq!(
            max.get(),
            NonMaxU16::MAX_UNDERLYING,
            "{:b} != {:b}",
            max.get(),
            NonMaxU16::MAX_UNDERLYING
        );
        assert_eq!(max, NonMaxU16Be::MAX);
    }

    #[cfg(any(target_endian = "little", feature = "endian-conversion"))]
    #[test]
    fn endianness_u16_big() {
        let max = NonMaxU16Le(u8::MAX, NonMaxU8(NonMaxU8Internal::V254));

        assert_eq!(
            max.get(),
            NonMaxU16::MAX_UNDERLYING,
            "{:b} != {:b}",
            max.get(),
            NonMaxU16::MAX_UNDERLYING
        );
        assert_eq!(max, NonMaxU16Le::MAX);
    }

    #[cfg(any(target_endian = "big", feature = "endian-conversion"))]
    #[test]
    fn endianness_u32_little() {
        let max = NonMaxU32Be(NonMaxU8(NonMaxU8Internal::V254), [u8::MAX; 3]);

        assert_eq!(
            max.get(),
            NonMaxU32::MAX_UNDERLYING,
            "{:b} != {:b}",
            max.get(),
            NonMaxU32::MAX_UNDERLYING
        );
        assert_eq!(max, NonMaxU32Be::MAX);
    }

    #[cfg(any(target_endian = "little", feature = "endian-conversion"))]
    #[test]
    fn endianness_u32_big() {
        let max = NonMaxU32Le([u8::MAX; 3], NonMaxU8(NonMaxU8Internal::V254));

        assert_eq!(
            max.get(),
            NonMaxU32::MAX_UNDERLYING,
            "{:b} != {:b}",
            max.get(),
            NonMaxU32::MAX_UNDERLYING
        );
        assert_eq!(max, NonMaxU32Le::MAX);
    }

    #[cfg(any(target_endian = "big", feature = "endian-conversion"))]
    #[test]
    fn endianness_u64_little() {
        let max = NonMaxU64Be(NonMaxU8(NonMaxU8Internal::V254), [u8::MAX; 7]);

        assert_eq!(
            max.get(),
            NonMaxU64::MAX_UNDERLYING,
            "{:b} != {:b}",
            max.get(),
            NonMaxU64::MAX_UNDERLYING
        );
        assert_eq!(max, NonMaxU64Be::MAX);
    }

    #[cfg(any(target_endian = "little", feature = "endian-conversion"))]
    #[test]
    fn endianness_u64_big() {
        let max = NonMaxU64Le([u8::MAX; 7], NonMaxU8(NonMaxU8Internal::V254));

        assert_eq!(
            max.get(),
            NonMaxU64::MAX_UNDERLYING,
            "{:b} != {:b}",
            max.get(),
            NonMaxU64::MAX_UNDERLYING
        );
        assert_eq!(max, NonMaxU64Le::MAX);
    }
}
