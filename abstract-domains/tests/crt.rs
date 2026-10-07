// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Differential tests of the real shared helpers (not a mirror implementation).
use semi_persistent_abstract_domains::arithmetic::{
    CrtMergeResult, crt_merge, extended_gcd, gcd, gcd_machine_modulus, gcd_wide, granger_modulus,
    mul_wide,
};

macro_rules! crt_cases {
    ($name:ident, $uint:ty) => {
        #[test]
        fn $name() {
            assert!(matches!(
                crt_merge::<$uint>(6, 13, 4, 11),
                CrtMergeResult::Class { modulus: 12, residue: 7 }
            ));
            assert!(matches!(crt_merge::<$uint>(6, 1, 4, 2), CrtMergeResult::Empty));
            let max = <$uint>::MAX;
            for expected in [0, 1, max] {
                match crt_merge(max, expected % max, max - 1, expected % (max - 1)) {
                    CrtMergeResult::Singleton { value } => assert_eq!(value, expected),
                    _ => panic!("expected a singleton with an overflowing LCM"),
                }
            }
            assert!(matches!(crt_merge(max, max - 1, max - 1, max - 2), CrtMergeResult::Empty));
            // The LCM fits, but no second value does. This must also collapse.
            assert!(matches!(crt_merge(max, 1, max, 1), CrtMergeResult::Singleton { value: 1 }));
            assert!(matches!(crt_merge(max, 0, max, 0), CrtMergeResult::Class { modulus, residue: 0 } if modulus == max));
            // Exact boundary: residue + modulus == MAX still has two members.
            let step = max / 2 + 1;
            let residue = max / 2;
            assert!(matches!(crt_merge(step, residue, step, residue), CrtMergeResult::Class { modulus, residue: r } if modulus == step && r == residue));
            assert_eq!(gcd(max, max - 1), 1);
            let eg = extended_gcd(max, max - 1);
            assert_eq!(eg.gcd, 1);
            assert_eq!(eg.x * max as i128 + eg.y * (max - 1) as i128, 1);
            assert_eq!(gcd_machine_modulus(0 as $uint), max as u128 + 1);
            assert_eq!(gcd_machine_modulus(max), 1);
            assert_eq!(gcd_machine_modulus(step), step as u128);
            assert_eq!(mul_wide(max, max), max as u128 * max as u128);
            assert_eq!(granger_modulus(max, 0, max, 0), max as u128 * max as u128);
        }
    };
}
crt_cases!(crt_u8, u8);
crt_cases!(crt_u16, u16);
crt_cases!(crt_u32, u32);
crt_cases!(crt_u64, u64);

type Bits = [u64; 4];

fn brute_class(m: u8, r: u8) -> Bits {
    let mut bits = [0; 4];
    // Each input set is brute-forced over all 256 concrete values once.
    for x in 0..=u8::MAX {
        if x % m == r % m {
            bits[usize::from(x / 64)] |= 1u64 << (x % 64);
        }
    }
    bits
}

fn check_result(result: CrtMergeResult<u8>, expected: Bits, table: &[Bits]) {
    match result {
        CrtMergeResult::Empty => assert_eq!(expected, [0; 4]),
        CrtMergeResult::Singleton { value } => {
            let mut bits = [0; 4];
            bits[usize::from(value / 64)] = 1u64 << (value % 64);
            assert_eq!(bits, expected);
        }
        CrtMergeResult::Class { modulus, residue } => {
            assert!(modulus > 0 && residue < modulus);
            assert!(u16::from(residue) + u16::from(modulus) <= 255);
            assert_eq!(
                table[usize::from(modulus) * 256 + usize::from(residue)],
                expected
            );
        }
    }
}

#[test]
fn exhaustive_u8_crt_intersections() {
    let mut table = vec![[0; 4]; 256 * 256];
    let mut classes = Vec::new();
    for m in 1..=u8::MAX {
        for r in 0..m {
            let bits = brute_class(m, r);
            table[usize::from(m) * 256 + usize::from(r)] = bits;
            classes.push((m, r, bits));
        }
    }
    // Exercise every normalized positive-modulus pair, including duplicate
    // finite singleton encodings. CRT is symmetric, so enumerate unordered
    // pairs; focused/raw-input tests below also exercise swapped operands.
    let mut pairs = 0u64;
    for (i, &(m1, r1, a)) in classes.iter().enumerate() {
        for &(m2, r2, b) in &classes[i..] {
            // Bitwise intersection is exactly the 256-value brute-force oracle,
            // cached to avoid re-enumerating those values for every pair.
            let expected = [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]];
            check_result(crt_merge(m1, r1, m2, r2), expected, &table);
            pairs += 1;
        }
    }
    assert_eq!(classes.len(), 32_640);
    assert_eq!(pairs, 532_701_120);
}

#[test]
fn all_raw_u8_residues_and_operand_orders() {
    let mut table = vec![[0; 4]; 256 * 256];
    for m in 1..=u8::MAX {
        for r in 0..m {
            table[usize::from(m) * 256 + usize::from(r)] = brute_class(m, r);
        }
    }
    for m in 1..=u8::MAX {
        for r in 0..=u8::MAX {
            for (n, s) in [(1, 0), (2, 1), (7, 3), (128, 127), (201, 200), (255, 254)] {
                let a = brute_class(m, r);
                let b = brute_class(n, s);
                let expected = [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]];
                check_result(crt_merge(m, r, n, s), expected, &table);
                check_result(crt_merge(n, s, m, r), expected, &table);
            }
        }
    }
}

#[test]
fn exhaustive_u8_gcd_and_bezout() {
    for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
            let expected = if a == 0 && b == 0 {
                0
            } else {
                (1..=u8::MAX)
                    .rev()
                    .find(|&d| a % d == 0 && b % d == 0)
                    .unwrap()
            };
            let g = gcd(a, b);
            assert_eq!(g, expected);
            assert_eq!(gcd(b, a), g);
            let eg = extended_gcd(a, b);
            assert_eq!(eg.gcd, g);
            assert_eq!(eg.x * i128::from(a) + eg.y * i128::from(b), i128::from(g));
            if b == 0 {
                assert_eq!((eg.x, eg.y), (1, 0));
            } else {
                assert!(eg.x.abs() <= i128::from(b));
            }
            if a != 0 {
                assert!(eg.y.abs() <= i128::from(a));
            }
            for d in 1..=u8::MAX {
                if a % d == 0 && b % d == 0 {
                    assert_eq!(g % d, 0);
                }
            }
        }
    }
}

#[test]
fn gcd_associativity_and_widened_helpers() {
    // Exhaustively test associativity over a small cube; the proof is unbounded.
    for a in 0..32u8 {
        for b in 0..32u8 {
            for c in 0..32u8 {
                assert_eq!(gcd(gcd(a, b), c), gcd(a, gcd(b, c)));
            }
        }
    }
    for m in 0..=u8::MAX {
        let g = gcd_machine_modulus(m);
        assert!(g > 0);
        assert_eq!(256 % g, 0);
        for x in -512..=512i128 {
            assert_eq!(
                x.rem_euclid(256).rem_euclid(g as i128),
                x.rem_euclid(g as i128)
            );
        }
    }
    assert_eq!(gcd_wide(u128::MAX, u128::MAX - 1), 1);
    assert_eq!(gcd_wide(0, 0), 0);
    for m1 in 0..8u8 {
        for r1 in 0..8u8 {
            for m2 in 0..8u8 {
                for r2 in 0..8u8 {
                    let terms = [
                        u128::from(m1) * u128::from(m2),
                        u128::from(m1) * u128::from(r2),
                        u128::from(m2) * u128::from(r1),
                    ];
                    let expected = if terms == [0; 3] {
                        0
                    } else {
                        (1..=49)
                            .rev()
                            .find(|&d| terms.iter().all(|x| x % d == 0))
                            .unwrap()
                    };
                    assert_eq!(granger_modulus(m1, r1, m2, r2), expected);
                }
            }
        }
    }
}
