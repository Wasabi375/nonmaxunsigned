use crate::NonMaxU8;

macro_rules! impl_checked {
    ($type:ty, $primitive:ty, $from_endian:ident) => {
        // Safety:
        //  * Self has the same layout as the primitive int
        unsafe impl bytemuck::CheckedBitPattern for $type {
            type Bits = $primitive;

            fn is_valid_bit_pattern(bits: &Self::Bits) -> bool {
                Self::new(<$primitive>::$from_endian(*bits)).is_some()
            }
        }
        unsafe impl bytemuck::Zeroable for $type {}
        unsafe impl bytemuck::NoUninit for $type {}

        unsafe impl bytemuck::ZeroableInOption for $type {}
        unsafe impl bytemuck::PodInOption for $type {}
    };
}

impl_checked!(NonMaxU8, u8, from);

#[cfg(any(target_endian = "little", feature = "endian-conversion"))]
mod little {
    use crate::{NonMaxU16Le, NonMaxU32Le, NonMaxU64Le};

    impl_checked!(NonMaxU16Le, u16, from_le);
    impl_checked!(NonMaxU32Le, u32, from_le);
    impl_checked!(NonMaxU64Le, u64, from_le);
}

#[cfg(any(target_endian = "big", feature = "endian-conversion"))]
mod big {
    use crate::{NonMaxU16Be, NonMaxU32Be, NonMaxU64Be};

    impl_checked!(NonMaxU16Be, u16, from_be);
    impl_checked!(NonMaxU32Be, u32, from_be);
    impl_checked!(NonMaxU64Be, u64, from_be);
}

#[cfg(test)]
mod test {
    macro_rules! test_checked {
        ($name:ident: $type:ty, $primitive:ty, $to_endian:ident) => {
            mod $name {
                use bytemuck::CheckedBitPattern;

                #[test]
                fn valid() {
                    let valid: $primitive = (<$type>::MAX_UNDERLYING).$to_endian();
                    assert!(<$type>::is_valid_bit_pattern(&valid));
                }

                #[test]
                fn invalid() {
                    let invalid: $primitive = (<$type>::MAX_UNDERLYING + 1).$to_endian();
                    assert!(!<$type>::is_valid_bit_pattern(&invalid));
                }
            }
        };
    }

    #[cfg(target_endian = "little")]
    test_checked!(u8: crate::NonMaxU8, u8, to_le);
    #[cfg(target_endian = "big")]
    test_checked!(u8: crate::NonMaxU8, u8, to_be);

    #[cfg(any(target_endian = "little", feature = "endian-conversion"))]
    mod test_little {
        test_checked!(u16: crate::NonMaxU16Le, u16, to_le);
        test_checked!(u32: crate::NonMaxU32Le, u32, to_le);
        test_checked!(u64: crate::NonMaxU64Le, u64, to_le);
    }

    #[cfg(any(target_endian = "big", feature = "endian-conversion"))]
    mod test_big {
        test_checked!(u16: crate::NonMaxU16Be, u16, to_be);
        test_checked!(u32: crate::NonMaxU32Be, u32, to_be);
        test_checked!(u64: crate::NonMaxU64Be, u64, to_be);
    }
}
