use bumpalo::Bump;

#[derive(Debug)]
pub struct FrozenBigUint<'a>(&'a mut [u32]);

const NIBBLE_BITS: usize = 4;
const BITS_PER_LIMB: usize = u32::BITS as usize;
const NIBBLES_PER_LIMB: usize = const {
    assert!(BITS_PER_LIMB % NIBBLE_BITS == 0);
    BITS_PER_LIMB / NIBBLE_BITS
};

impl<'arena> FrozenBigUint<'arena> {
    pub fn limbs_le(&self) -> &[u32] {
        &self.0
    }

    /// # Panics
    /// Panics if `s` doesn't match \[0-9A-Fa-f]+\
    pub fn from_radix16_in(s: &str, arena: &'arena Bump) -> Self {
        assert!(!s.is_empty());

        let s = s.as_bytes();
        let limbs = arena.alloc_slice_fill_copy(s.len().div_ceil(NIBBLES_PER_LIMB), 0);

        for (i, &c) in s.iter().rev().enumerate() {
            let limb_index = i / NIBBLES_PER_LIMB;
            let nibble_shift = (i % NIBBLES_PER_LIMB) * NIBBLE_BITS;
            let nibble = match c {
                b'0'..=b'9' => c - b'0',
                b'a'..=b'f' => c - b'a' + 10,
                b'A'..=b'F' => c - b'A' + 10,
                _ => unreachable!("Invalid char byte {}", c),
            } as u32;
            limbs[limb_index] |= nibble << nibble_shift;
        }

        Self(limbs)
    }

    /// # Panics
    /// Panics if `s` doesn't match \[0-1]+\
    pub fn from_radix2_in(s: &str, arena: &'arena Bump) -> Self {
        assert!(!s.is_empty());

        let s = s.as_bytes();
        let limbs = arena.alloc_slice_fill_copy(s.len().div_ceil(u32::BITS as usize), 0);

        for (i, &c) in s.iter().rev().enumerate() {
            let limb_index = i / BITS_PER_LIMB;
            let shift = i % BITS_PER_LIMB;
            let bit = match c {
                b'0' => 0,
                b'1' => 1,
                _ => unreachable!("Invalid char byte {}", c),
            } as u32;
            limbs[limb_index] |= bit << shift;
        }

        Self(limbs)
    }

    /// # Panics
    /// Panics if `s` doesn't match \[0-9]+\
    pub fn from_radix10_in(s: &str, arena: &'arena Bump) -> Self {
        assert!(!s.is_empty());

        let s = s.as_bytes();
        let limb_count = (s.len() * 3322).div_ceil(1000 * BITS_PER_LIMB);
        let mut new = Self(arena.alloc_slice_fill_copy(limb_count, 0));

        for &c in s {
            let dig = match c {
                b'0'..=b'9' => c - b'0',
                _ => unreachable!("invalid char byte {}", c),
            };
            new.mul_add_assign_wrapping(10, dig as u32);
        }

        new
    }

    fn mul_add_assign_wrapping(&mut self, factor: u32, add: u32) {
        let factor = factor as u64;
        let mut carry = add;
        for limb in self.0.iter_mut() {
            let res = (*limb) as u64 * factor;
            let (new_limb, carry_add) = (res as u32).overflowing_add(carry);
            *limb = new_limb;
            carry = ((res >> 32) as u32) + carry_add as u32;
        }
    }
}

impl<'a> std::fmt::LowerHex for FrozenBigUint<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.iter().all(|limb| *limb == 0) {
            write!(f, "0")?;
        } else {
            for (i, &limb) in self.0.iter().rev().skip_while(|limb| **limb == 0).enumerate() {
                if i == 0 {
                    write!(f, "{:x}", limb)?;
                } else {
                    write!(f, "{:0padding$x}", limb, padding = NIBBLES_PER_LIMB)?;
                }
            }
        }
        Ok(())
    }
}

impl<'a> std::fmt::UpperHex for FrozenBigUint<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.iter().all(|limb| *limb == 0) {
            write!(f, "0")?;
        } else {
            for (i, &limb) in self.0.iter().rev().skip_while(|limb| **limb == 0).enumerate() {
                if i == 0 {
                    write!(f, "{:X}", limb)?;
                } else {
                    write!(f, "{:0padding$X}", limb, padding = NIBBLES_PER_LIMB)?;
                }
            }
        }
        Ok(())
    }
}

impl<'a> std::fmt::Binary for FrozenBigUint<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.iter().all(|limb| *limb == 0) {
            write!(f, "0")?;
        } else {
            for (i, &limb) in self.0.iter().rev().skip_while(|limb| **limb == 0).enumerate() {
                if i == 0 {
                    write!(f, "{:b}", limb)?;
                } else {
                    write!(f, "{:0padding$b}", limb, padding = BITS_PER_LIMB)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bumpalo::Bump;

    #[test]
    fn test_hex_roundtrip() {
        let arena = Bump::with_capacity(256);

        assert_eq!(
            format!(
                "{:x}",
                FrozenBigUint::from_radix16_in(
                    "4eeb8567ad496f244c24c274bb1c2f12e4b32f933bab58a456cb5a5864dc58d",
                    &arena
                )
            ),
            "4eeb8567ad496f244c24c274bb1c2f12e4b32f933bab58a456cb5a5864dc58d"
        );
    }

    #[test]
    fn test_decimal() {
        let arena = Bump::with_capacity(256);
        assert_eq!(
            format!(
                "{:x}",
                FrozenBigUint::from_radix10_in(
                    "1155113192353703119622322190288124313895465211404437846",
                    &arena
                )
            ),
            "c0f5884d2216eeaea6a190458b0051664ebc6d93f4956"
        );
    }

    #[test]
    fn test_binary() {
        let arena = Bump::with_capacity(256);
        assert_eq!(
            format!(
                "{:x}",
                FrozenBigUint::from_radix2_in("0010101000000001001111111110101110", &arena)
            ),
            "a804ffae"
        );
    }

    #[test]
    fn test_zero() {
        let arena = Bump::with_capacity(256);
        assert_eq!(
            format!("{:x}", FrozenBigUint::from_radix2_in("000000000000000000000000", &arena)),
            "0"
        );
    }
}
