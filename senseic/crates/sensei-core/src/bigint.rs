use crate::{Idx, list_of_lists::ListOfLists};

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{list_of_lists::ListOfLists, newtype_index};

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
}
