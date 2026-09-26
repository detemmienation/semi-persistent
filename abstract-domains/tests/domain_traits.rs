// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the reference domains against brute-force concretization.
//! The Verus proofs cover all widths; these tests exercise the executable code
//! (contracts are erased at runtime) exhaustively over sampled u8 intervals.
use semi_persistent_abstract_domains::ibig::IBig;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::interval_z::{Hi, IntervalZ, Lo};
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::semantics::{Euclid, Unsigned};
use semi_persistent_abstract_domains::strided::StridedInterval;
use semi_persistent_abstract_domains::transfer::{Arith, DivRem, DivZero};

type I8 = Interval<u8>;
type U = Unsigned<u8>;
type SI8 = StridedInterval<u8>;

fn iv(lo: u8, hi: u8) -> I8 {
    Interval::new(lo, hi).expect("lo <= hi")
}

fn has(i: &I8, x: u8) -> bool {
    let (lo, hi) = i.bounds();
    lo <= x && x <= hi
}

fn bot_has(b: &BotOr<I8>, x: u8) -> bool {
    match b {
        BotOr::Bot => false,
        BotOr::Val(i) => has(i, x),
    }
}

/// Intervals with bounds on a coarse grid plus the extremes.
fn samples() -> Vec<I8> {
    let pts: Vec<u8> = (0..=255u16)
        .step_by(51)
        .map(|v| v as u8)
        .chain([1, 2, 254, 255])
        .collect();
    let mut out = Vec::new();
    for &a in &pts {
        for &b in &pts {
            if a <= b {
                out.push(iv(a, b));
            }
        }
    }
    out
}

#[test]
fn interval_lattice_and_canonicity() {
    let s = samples();
    for a in &s {
        for b in &s {
            let j = a.join(b);
            let w = a.widen(b);
            let m = a.meet(b);
            for x in 0..=255u8 {
                let in_a = has(a, x);
                let in_b = has(b, x);
                if in_a || in_b {
                    assert!(has(&j, x) && has(&w, x));
                }
                if in_a && in_b {
                    assert!(bot_has(&m, x));
                }
                if a.leq(b) && in_a {
                    assert!(in_b);
                }
            }
            if matches!(m, BotOr::Bot) {
                assert!((0..=255u8).all(|x| !(has(a, x) && has(b, x))));
            }
            // Canonical: equal concretizations are equal bounds.
            if (0..=255u8).all(|x| has(a, x) == has(b, x)) {
                assert_eq!(a.bounds(), b.bounds());
            }
        }
    }
}

#[test]
fn interval_unsigned_transfers() {
    let s = samples();
    for a in &s {
        let n = <I8 as Arith<U>>::neg(a);
        for x in 0..=255u8 {
            if has(a, x) {
                assert!(has(&n, x.wrapping_neg()));
            }
        }
        for b in &s {
            let add = <I8 as Arith<U>>::add(a, b);
            let sub = <I8 as Arith<U>>::sub(a, b);
            let (q, qf) = <I8 as DivRem<U>>::div(a, b);
            let (r, rf) = <I8 as DivRem<U>>::rem(a, b);
            let (blo, bhi) = b.bounds();
            let expect_flag = |f: &DivZero| match f {
                DivZero::Never => assert!(blo > 0),
                DivZero::Maybe => assert!(blo == 0 && bhi > 0),
                DivZero::Always => assert!(bhi == 0),
            };
            expect_flag(&qf);
            expect_flag(&rf);
            for x in (0..=255u8).filter(|&x| has(a, x)) {
                for y in (0..=255u8).filter(|&y| has(b, y)) {
                    assert!(has(&add, x.wrapping_add(y)));
                    assert!(has(&sub, x.wrapping_sub(y)));
                    if let (Some(qv), Some(rv)) = (x.checked_div(y), x.checked_rem(y)) {
                        assert!(bot_has(&q, qv));
                        assert!(bot_has(&r, rv));
                    }
                }
            }
        }
    }
}

fn z(v: i64) -> IBig {
    IBig::from_i64(v)
}

fn zi(lo: Option<i64>, hi: Option<i64>) -> IntervalZ {
    let lo = lo.map_or(Lo::NegInf, |v| Lo::Fin(z(v)));
    let hi = hi.map_or(Hi::PosInf, |v| Hi::Fin(z(v)));
    IntervalZ::new(lo, hi).expect("lo <= hi")
}

fn zhas(i: &IntervalZ, x: i64) -> bool {
    let c = IntervalZ::constant(z(x));
    c.leq(i)
}

#[test]
fn interval_z_lattice_and_arith() {
    let bounds: Vec<Option<i64>> = vec![None, Some(-7), Some(-1), Some(0), Some(3), Some(9)];
    let mut s = Vec::new();
    for &lo in &bounds {
        for &hi in &bounds {
            let ok = match (lo, hi) {
                (Some(a), Some(b)) => a <= b,
                _ => true,
            };
            if ok {
                s.push(zi(lo, hi));
            }
        }
    }
    let probe: Vec<i64> = (-20..=20).collect();
    for a in &s {
        for b in &s {
            let j = a.join(b);
            let m = a.meet(b);
            let add = <IntervalZ as Arith<Euclid>>::add(a, b);
            let sub = <IntervalZ as Arith<Euclid>>::sub(a, b);
            let (q, f) = <IntervalZ as DivRem<Euclid>>::div(a, b);
            match f {
                DivZero::Always => assert!(matches!(q, BotOr::Bot)),
                DivZero::Never => assert!(!zhas(b, 0)),
                DivZero::Maybe => assert!(zhas(b, 0)),
            }
            for &x in &probe {
                let (in_a, in_b) = (zhas(a, x), zhas(b, x));
                if in_a || in_b {
                    assert!(zhas(&j, x));
                }
                if in_a && in_b {
                    assert!(matches!(&m, BotOr::Val(v) if zhas(v, x)));
                }
                for &y in &probe {
                    if in_a && zhas(b, y) {
                        assert!(zhas(&add, x + y) && zhas(&sub, x - y));
                    }
                }
            }
        }
    }
}

fn si(stride: u8, lo: u8, hi: u8) -> SI8 {
    SI8::new(stride, lo, hi).expect("lo <= hi")
}

fn has_si(s: &SI8, x: u8) -> bool {
    s.contains(x)
}

fn bot_has_si(b: &BotOr<SI8>, x: u8) -> bool {
    match b {
        BotOr::Bot => false,
        BotOr::Val(v) => has_si(v, x),
    }
}

/// `lo`/`hi` on a coarse grid plus the extremes, crossed with a handful of
/// strides -- including 0 and non-dividing strides, so `new` has to
/// exercise its own canonicalization (e.g. `si(5, 7, 7)` collapsing to the
/// same value as `si(0, 7, 7)`) rather than only ever seeing pre-canonical
/// input.
fn strided_samples() -> Vec<SI8> {
    let pts: Vec<u8> = (0..=255u16)
        .step_by(51)
        .map(|v| v as u8)
        .chain([1, 2, 254, 255])
        .collect();
    let strides = [0u8, 1, 2, 3, 5];
    let mut out = Vec::new();
    for &lo in &pts {
        for &hi in &pts {
            if lo <= hi {
                for &s in &strides {
                    out.push(si(s, lo, hi));
                }
            }
        }
    }
    out
}

#[test]
fn strided_interval_lattice_and_canonicity() {
    let s = strided_samples();
    for a in &s {
        for b in &s {
            let j = a.join(b);
            let w = a.widen(b);
            let m = a.meet(b);
            for x in 0..=255u8 {
                let in_a = has_si(a, x);
                let in_b = has_si(b, x);
                if in_a || in_b {
                    assert!(has_si(&j, x) && has_si(&w, x));
                }
                if in_a && in_b {
                    assert!(bot_has_si(&m, x));
                }
                if a.leq(b) && in_a {
                    assert!(in_b);
                }
            }
            if matches!(m, BotOr::Bot) {
                assert!((0..=255u8).all(|x| !(has_si(a, x) && has_si(b, x))));
            }
            // Canonical: equal concretizations are equal (stride, lo, hi).
            if (0..=255u8).all(|x| has_si(a, x) == has_si(b, x)) {
                assert_eq!(a.bounds(), b.bounds());
            }
        }
    }
}

/// The review's exact example: (0,7,7), (2,7,7) and (5,7,7) all denote
/// {7}. Canonical wf means they are now literally the same value, not
/// just equal under some separate normalize() step.
#[test]
fn strided_canonical_form_is_unique() {
    let a = si(0, 7, 7);
    let b = si(2, 7, 7);
    let c = si(5, 7, 7);
    assert_eq!(a.bounds(), b.bounds());
    assert_eq!(b.bounds(), c.bounds());
}

/// Same stride, compatible residue: join is exact, just widens the bounds.
#[test]
fn strided_join_same_residue_is_exact() {
    let a = si(3, 2, 8); // {2, 5, 8}
    let b = si(3, 11, 14); // {11, 14}, 11 == 2 (mod 3)
    assert_eq!(a.join(&b).bounds(), (3, 2, 14));
}

/// Two distinct singletons: the two-point set is exactly representable as
/// a stride equal to the gap between them.
#[test]
fn strided_join_two_singletons_is_exact() {
    let a = si(0, 4, 4);
    let b = si(0, 10, 10);
    assert_eq!(a.join(&b).bounds(), (6, 4, 10));
}

/// Incompatible strides fall back to a sound but imprecise join -- this
/// keeps the bounds (unlike the pre-port join, which dropped them and
/// returned unbounded top()), because there is no gcd helper yet to
/// compute the tight common stride.
#[test]
fn strided_join_incompatible_strides_keeps_bounds() {
    let a = si(3, 0, 9);
    let b = si(5, 0, 20);
    let j = a.join(&b);
    let (stride, lo, hi) = j.bounds();
    assert_eq!((stride, lo, hi), (1, 0, 20));
}
