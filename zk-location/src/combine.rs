//! Shared combine functions for lane-wise Poseidon-like compression over BabyBear.
//! Formula per lane: parent = (a + 2*b)^7 mod p, where p is BabyBear modulus.

#[inline]
fn add_mod(a: u32, b: u32) -> u32 {
    const P: u128 = 0x7800_0001; // BabyBear modulus
    let mut s = (a as u128) + (b as u128);
    if s >= P { s -= P; }
    s as u32
}

#[inline]
fn mul_mod(a: u32, b: u32) -> u32 {
    const P: u128 = 0x7800_0001;
    ((a as u128) * (b as u128) % P) as u32
}

/// Lane combine: (a + 2*b)^7 mod p
#[inline]
pub fn combine_lane(a: u32, b: u32) -> u32 {
    let two_b = add_mod(b, b);
    let x = add_mod(a, two_b);
    // x^7 = x * x^2 * x^4
    let x2 = mul_mod(x, x);
    let x4 = mul_mod(x2, x2);
    let x7 = mul_mod(mul_mod(x4, x2), x);
    x7
}

/// 4-lane digest combine.
#[inline]
pub fn combine_digest(left: [u32; 4], right: [u32; 4]) -> [u32; 4] {
    [
        combine_lane(left[0], right[0]),
        combine_lane(left[1], right[1]),
        combine_lane(left[2], right[2]),
        combine_lane(left[3], right[3]),
    ]
}
