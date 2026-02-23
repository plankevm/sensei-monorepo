use crate::{Idx, list_of_lists::ListOfLists};
use alloy_primitives::U256;

const NIBBLE_BITS: usize = 4;
const BITS_PER_LIMB: usize = u32::BITS as usize;
const NIBBLES_PER_LIMB: usize = const {
    assert!(BITS_PER_LIMB.is_multiple_of(NIBBLE_BITS));
    BITS_PER_LIMB / NIBBLE_BITS
};

fn strip_leading(s: &str) -> &[u8] {
    let bytes = s.as_bytes();
    let start = bytes.iter().position(|&c| c != b'0' && c != b'_').unwrap_or(bytes.len());
    &bytes[start..]
}

/// Parses and allocates a numerical string into `limb_storage`, returning the limb list's new
/// index. May allocate an empty list if number is `0` or string is empty.
///
/// # Panics
/// Panics if `s` doesn't match \[0-9A-Fa-f_]*\
pub fn from_radix16_in<I: Idx>(s: &str, limb_storage: &mut ListOfLists<I, u32>) -> I {
    limb_storage.push_with(|mut pusher| {
        let mut i = 0usize;
        let mut limb = 0u32;
        for &c in strip_leading(s).iter().rev() {
            let nibble_shift = i * NIBBLE_BITS;
            let nibble = match c {
                b'0'..=b'9' => c - b'0',
                b'a'..=b'f' => c - b'a' + 10,
                b'A'..=b'F' => c - b'A' + 10,
                b'_' => continue,
                _ => panic!("Unexpected byte 0x{:02x}", c),
            } as u32;
            limb |= nibble << nibble_shift;
            i = (i + 1) % NIBBLES_PER_LIMB;
            if i == 0 {
                pusher.push(limb);
                limb = 0;
            }
        }

        if i > 0 && limb != 0 {
            pusher.push(limb);
        }
    })
}

/// Parses and allocates a numerical string into `limb_storage`, returning the limb list's new
/// index. May allocate an empty list if number is `0` or string is empty.
///
/// # Panics
/// Panics if `s` doesn't match `\[_01]*\`
pub fn from_radix2_in<I: Idx>(s: &str, limb_storage: &mut ListOfLists<I, u32>) -> I {
    limb_storage.push_with(|mut pusher| {
        let mut i = 0usize;
        let mut limb = 0u32;
        for &c in strip_leading(s).iter().rev() {
            let bit_shift = i;
            let bit = match c {
                b'0' => 0,
                b'1' => 1,
                b'_' => continue,
                _ => panic!("Unexpected byte 0x{:02x}", c),
            } as u32;
            limb |= bit << bit_shift;
            i = (i + 1) % BITS_PER_LIMB;
            if i == 0 {
                pusher.push(limb);
                limb = 0;
            }
        }

        if i > 0 && limb != 0 {
            pusher.push(limb);
        }
    })
}

/// Parses and allocates a numerical string into `limb_storage`, returning the limb list's new
/// index. May allocate an empty list if number is `0` or string is empty.
///
/// # Panics
/// Panics if `s` doesn't match \[_0-9]*\
pub fn from_radix10_in<I: Idx>(s: &str, limb_storage: &mut ListOfLists<I, u32>) -> I {
    limb_storage.push_with(|mut pusher| {
        let s = strip_leading(s);

        // Process from most to least significant.
        for &c in s.iter() {
            let dig = match c {
                b'0'..=b'9' => c - b'0',
                b'_' => continue,
                _ => unreachable!("invalid char byte {}", c),
            };
            let carry = mul_add_over_limbs(pusher.current(), 10, dig as u32);
            if carry > 0 {
                pusher.push(carry);
            }
        }
    })
}

fn mul_add_over_limbs(limbs: &mut [u32], mul: u32, add: u32) -> u32 {
    let mul = mul as u64;
    let mut carry = add;
    for limb in limbs.iter_mut() {
        let res = (*limb) as u64 * mul;
        let (new_limb, carry_add): (u32, bool) = (res as u32).overflowing_add(carry);
        *limb = new_limb;
        carry = ((res >> 32) as u32) + carry_add as u32;
    }
    carry
}

const U32_LIMBS_PER_U256: usize = 8;
const INT256_MIN_MAGNITUDE: U256 = U256::from_limbs([0, 0, 0, 1 << 63]);

/// Converts u32 limbs (little-endian) to a U256, optionally negating via two's complement.
///
/// Returns `None` if:
/// - `limbs.len() > 8` (value doesn't fit in 256 bits)
/// - `negative` is true and the magnitude exceeds 2^255 (the max for int256 two's complement)
pub fn limbs_to_u256(limbs: &[u32], negative: bool) -> Option<U256> {
    if limbs.len() > U32_LIMBS_PER_U256 {
        return None;
    }

    let mut u64_limbs = [0u64; 4];
    for (i, u64_limb) in u64_limbs.iter_mut().enumerate() {
        let lo = limbs.get(2 * i).copied().unwrap_or(0) as u64;
        let hi = limbs.get(2 * i + 1).copied().unwrap_or(0) as u64;
        *u64_limb = (hi << 32) | lo;
    }

    let value = U256::from_limbs(u64_limbs);

    if negative && value != U256::ZERO {
        if value > INT256_MIN_MAGNITUDE {
            return None;
        }
        Some(U256::ZERO.wrapping_sub(value))
    } else {
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{list_of_lists::ListOfLists, newtype_index};
    use alloy_primitives::uint;

    newtype_index! {
        struct UintLimbsIdx;
    }

    fn fmt_limbs(limbs: &[u32]) -> String {
        use std::fmt::Write;
        let mut out_string = String::with_capacity(limbs.len() * NIBBLES_PER_LIMB);
        for &limb in limbs.iter().rev() {
            write!(&mut out_string, "{limb:08x}").unwrap();
        }
        out_string
    }

    #[test]
    fn test_hex_roundtrip() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix16_in(
            "4eeb8567ad496f244c24c274bb1c2f12e4b32f933bab58a456cb5a5864dc58d",
            &mut storage,
        );
        assert_eq!(
            fmt_limbs(&storage[idx]),
            "04eeb8567ad496f244c24c274bb1c2f12e4b32f933bab58a456cb5a5864dc58d"
        );
    }

    #[test]
    fn test_hex_roundtrip_underscore() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix16_in(
            "4eeb8567ad_496f244c24c274bb1c2f12e4b32f9_33bab58a4_56cb5a5864dc58d",
            &mut storage,
        );
        assert_eq!(
            fmt_limbs(&storage[idx]),
            "04eeb8567ad496f244c24c274bb1c2f12e4b32f933bab58a456cb5a5864dc58d"
        );
    }

    #[test]
    fn test_decimal_0() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix10_in("0", &mut storage);
        assert_eq!(fmt_limbs(&storage[idx]), "");
    }

    #[test]
    fn test_decimal_1() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix10_in("1", &mut storage);
        assert_eq!(fmt_limbs(&storage[idx]), "00000001");
    }

    #[test]
    fn test_decimal_2pow32() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix10_in("4294967296", &mut storage);
        assert_eq!(fmt_limbs(&storage[idx]), "0000000100000000");
    }

    #[test]
    fn test_decimal_big_simple() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix10_in(
            "1155113192353703119622322190288124313895465211404437846",
            &mut storage,
        );
        assert_eq!(fmt_limbs(&storage[idx]), "000c0f5884d2216eeaea6a190458b0051664ebc6d93f4956");
    }

    #[test]
    fn test_decimal_big_underscore() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix10_in(
            "_1155113_1923537031196___22322190_288124_313895465211404437846",
            &mut storage,
        );
        assert_eq!(fmt_limbs(&storage[idx]), "000c0f5884d2216eeaea6a190458b0051664ebc6d93f4956");
    }

    #[test]
    fn test_binary() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix2_in("0010101000000001001111111110101110", &mut storage);
        assert_eq!(fmt_limbs(&storage[idx]), "a804ffae");
    }

    #[test]
    fn test_binary_underscore() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix2_in("00101_0100000_0001001___1_1__111111010_1110", &mut storage);
        assert_eq!(fmt_limbs(&storage[idx]), "a804ffae");
    }

    #[test]
    fn test_zero() {
        let mut storage: ListOfLists<UintLimbsIdx, u32> = ListOfLists::new();
        let idx = from_radix2_in("000000000000000000000000", &mut storage);
        assert_eq!(fmt_limbs(&storage[idx]), "");
    }

    #[test]
    fn test_limbs_to_u256_zero() {
        assert_eq!(limbs_to_u256(&[], false), Some(U256::ZERO));
    }

    #[test]
    fn test_limbs_to_u256_small_positive() {
        assert_eq!(limbs_to_u256(&[1], false), Some(uint!(1U256)));
        assert_eq!(limbs_to_u256(&[42], false), Some(uint!(42U256)));
        assert_eq!(limbs_to_u256(&[u32::MAX], false), Some(uint!(0xffffffffU256)));
    }

    #[test]
    fn test_limbs_to_u256_multi_limb() {
        // 2^32
        assert_eq!(limbs_to_u256(&[0, 1], false), Some(uint!(0x100000000U256)));
        // 2^64 + 1
        assert_eq!(limbs_to_u256(&[1, 0, 1], false), Some(uint!(0x10000000000000001U256)));
    }

    #[test]
    fn test_limbs_to_u256_max() {
        let max_limbs = [u32::MAX; 8];
        assert_eq!(limbs_to_u256(&max_limbs, false), Some(U256::MAX));
    }

    #[test]
    fn test_limbs_to_u256_negative_one() {
        // -1 in two's complement is all 1s
        assert_eq!(limbs_to_u256(&[1], true), Some(U256::ZERO.wrapping_sub(uint!(1U256))));
    }

    #[test]
    fn test_limbs_to_u256_negative_small() {
        // -42 in two's complement
        assert_eq!(limbs_to_u256(&[42], true), Some(U256::ZERO.wrapping_sub(uint!(42U256))));
    }

    #[test]
    fn test_limbs_to_u256_negative_zero() {
        // -0 is just 0
        assert_eq!(limbs_to_u256(&[], true), Some(U256::ZERO));
    }

    #[test]
    fn test_limbs_to_u256_int256_min() {
        // -2^255 (the minimum int256 value)
        // magnitude = 2^255 = 0x8000...0000
        let mut limbs = [0u32; 8];
        limbs[7] = 0x80000000; // high bit of the highest limb
        let result = limbs_to_u256(&limbs, true);
        // In two's complement, -2^255 has the same bit pattern as its magnitude
        assert_eq!(
            result,
            Some(U256::ZERO.wrapping_sub(uint!(
                0x8000000000000000000000000000000000000000000000000000000000000000U256
            )))
        );
    }

    #[test]
    fn test_limbs_to_u256_too_many_limbs() {
        let limbs = [1u32; 9];
        assert_eq!(limbs_to_u256(&limbs, false), None);
    }

    #[test]
    fn test_limbs_to_u256_negative_overflow() {
        // magnitude = 2^255 + 1, which exceeds the int256 minimum
        let mut limbs = [0u32; 8];
        limbs[7] = 0x80000000;
        limbs[0] = 1; // add 1 to make it 2^255 + 1
        assert_eq!(limbs_to_u256(&limbs, true), None);
    }
}
