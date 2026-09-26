// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Strided intervals over machine words, generic over the width.
//!
//! Port onto the shared traits (`doc/domain-traits.md`) of the domain
//! previously stamped per-width inside `domains.rs`. Canonical this time:
//! `stride == 0 <==> lo == hi`, and when `stride > 0`, `hi` sits exactly on
//! the stride grid (`(hi - lo) % stride == 0`), so `{7}` has exactly one
//! encoding and `lemma_canonical` is provable. `word::Word` has no generic
//! multiplication, so canonicalizing (snapping `hi` down to the grid) uses
//! `checked_sub` + `urem` instead of the div/mul reasoning the old
//! `normalize()` needed.
#![allow(unused_imports, unused_variables)]
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::*;
use crate::word::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

/// `{lo, lo+stride, lo+2*stride, ..., hi}` in the unsigned reading.
/// `stride == 0` is reserved for singletons (`lo == hi`).
pub struct StridedInterval<W> {
    stride: W,
    lo: W,
    hi: W,
}

/// `from_int` is the identity on in-range integers (same helper as interval.rs).
proof fn lemma_from_small<W: Word>(i: int)
    requires
        0 <= i < W::modulus() as int,
    ensures
        W::from_int(i).view() == i,
{
    W::lemma_from_int(i);
    lemma_small_mod(i as nat, W::modulus());
}

impl<W: Word> StridedInterval<W> {
    pub closed spec fn stride(&self) -> W {
        self.stride
    }

    pub closed spec fn lo(&self) -> W {
        self.lo
    }

    pub closed spec fn hi(&self) -> W {
        self.hi
    }

    pub fn bounds(&self) -> (r: (W, W, W))
        ensures
            r.0 == self.stride(),
            r.1 == self.lo(),
            r.2 == self.hi(),
    {
        (self.stride, self.lo, self.hi)
    }

    pub fn contains(&self, x: W) -> (b: bool)
        ensures
            b == self.gamma(x),
    {
        proof {
            W::lemma_view_bounded(x);
        }
        if !(self.lo.le(x) && x.le(self.hi)) {
            false
        } else if self.stride.eq(W::zero()) {
            true
        } else {
            let diff = x.checked_sub(self.lo).expect("lo <= x");
            proof {
                assert(diff.view() == x.view() - self.lo.view());
            }
            diff.urem(self.stride).eq(W::zero())
        }
    }

    /// Public smart constructor: snaps `hi` down to the last point on the
    /// stride grid, and collapses to the singleton form when only one
    /// point remains (including when `stride` was already 0 or `lo == hi`).
    /// `None` when `lo > hi`, matching `Interval::new`.
    pub fn new(stride: W, lo: W, hi: W) -> (r: Option<Self>)
        ensures
            match r {
                Some(v) => v.wf() && lo.view() <= hi.view(),
                None => lo.view() > hi.view(),
            },
    {
        if !lo.le(hi) {
            return None;
        }
        Some(Self::mk(stride, lo, hi))
    }

    /// `stride == 0` always means singleton(lo) -- `hi` is ignored in that
    /// case, matching `wf`'s `stride == 0 <==> lo == hi` (a caller passing
    /// `stride == 0` with `lo != hi` is asking for a singleton with a
    /// nonsense upper bound, not for the wide range `[lo, hi]`).
    fn mk(stride: W, lo: W, hi: W) -> (r: Self)
        requires
            lo.view() <= hi.view(),
        ensures
            r.wf(),
            forall|x: W| #[trigger] r.gamma(x) <==> if stride.view() == 0 {
                x.view() == lo.view()
            } else {
                lo.view() <= x.view() && x.view() <= hi.view() && (x.view() as int - lo.view()
                    as int) % (stride.view() as int) == 0
            },
    {
        if stride.eq(W::zero()) || lo.eq(hi) {
            let r = StridedInterval { stride: W::zero(), lo, hi: lo };
            proof {
                if stride.view() > 0 {
                    lemma_mod_multiples_basic(0, stride.view() as int);
                }
            }
            r
        } else {
            let diff = hi.checked_sub(lo).expect("lo <= hi");
            proof {
                assert(diff.view() == hi.view() - lo.view());
            }
            let rem = diff.urem(stride);
            proof {
                assert(rem.view() == diff.view() % stride.view());
                lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                lemma_mul_left_inequality(
                    stride.view() as int,
                    0,
                    diff.view() as int / (stride.view() as int),
                );
                assert(rem.view() as int <= diff.view() as int);
            }
            let canon_hi = hi.checked_sub(rem).expect("rem <= diff <= hi - lo");
            proof {
                assert(canon_hi.view() == hi.view() - rem.view());
                assert(canon_hi.view() as int - lo.view() as int == diff.view() as int
                    - rem.view() as int);
                lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                // diff == stride * (diff/stride) + rem, so canon_hi - lo == stride*(diff/stride)
            }
            if canon_hi.eq(lo) {
                let r = StridedInterval { stride: W::zero(), lo, hi: lo };
                proof {
                    assert forall|x: W| #[trigger] r.gamma(x) <==> (lo.view() <= x.view()
                        && x.view() <= hi.view() && (stride.view() == 0 || (x.view() as int
                        - lo.view() as int) % (stride.view() as int) == 0)) by {
                        if x.view() == lo.view() {
                            lemma_mod_multiples_basic(0, stride.view() as int);
                        } else if lo.view() <= x.view() && x.view() <= hi.view() {
                            // x - lo is a nonzero multiple of stride but canon_hi == lo means
                            // the only multiple of stride in [lo, hi] is 0.
                            if (x.view() as int - lo.view() as int) % (stride.view() as int)
                                == 0 {
                                let k = (x.view() as int - lo.view() as int)
                                    / (stride.view() as int);
                                lemma_fundamental_div_mod(
                                    x.view() as int - lo.view() as int,
                                    stride.view() as int,
                                );
                                if k > 0 {
                                    lemma_mul_inequality(1, k, stride.view() as int);
                                    assert(stride.view() as int * 1 <= stride.view() as int
                                        * k);
                                    assert(x.view() as int - lo.view() as int >= stride.view()
                                        as int);
                                    assert(x.view() as int >= lo.view() as int + stride.view()
                                        as int);
                                    assert(canon_hi.view() as int == lo.view() as int);
                                    assert(x.view() as int <= hi.view() as int);
                                    // and canon_hi == hi - rem == lo, i.e. diff == rem, so
                                    // stride does not fit a second time inside [lo,hi].
                                    assert(diff.view() as int == rem.view() as int);
                                    assert(x.view() as int - lo.view() as int
                                        <= diff.view() as int);
                                    assert(false) by {
                                        lemma_mul_inequality(
                                            stride.view() as int,
                                            x.view() as int - lo.view() as int,
                                            1,
                                        );
                                    };
                                }
                            }
                        }
                    }
                };
                r
            } else {
                let r = StridedInterval { stride, lo, hi: canon_hi };
                proof {
                    let q = diff.view() as int / (stride.view() as int);
                    lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                    assert(canon_hi.view() as int - lo.view() as int == stride.view() as int
                        * q);
                    lemma_mul_left_inequality(stride.view() as int, 0, q);
                    assert(canon_hi.view() as int >= lo.view() as int);
                    lemma_mod_multiples_basic(q, stride.view() as int);
                    lemma_mul_is_commutative(stride.view() as int, q);
                    assert((canon_hi.view() as int - lo.view() as int) % (stride.view() as int)
                        == 0);
                }
                proof {
                    assert forall|x: W| #[trigger] r.gamma(x) <==> (lo.view() <= x.view()
                        && x.view() <= hi.view() && (stride.view() == 0 || (x.view() as int
                        - lo.view() as int) % (stride.view() as int) == 0)) by {
                        if lo.view() <= x.view() && x.view() <= canon_hi.view() && (x.view()
                            as int - lo.view() as int) % (stride.view() as int) == 0 {
                            assert(x.view() as int <= hi.view() as int);
                        }
                        if lo.view() <= x.view() && x.view() <= hi.view() && (x.view() as int
                            - lo.view() as int) % (stride.view() as int) == 0 {
                            let k = (x.view() as int - lo.view() as int)
                                / (stride.view() as int);
                            let q = diff.view() as int / (stride.view() as int);
                            lemma_fundamental_div_mod(
                                x.view() as int - lo.view() as int,
                                stride.view() as int,
                            );
                            lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                            lemma_div_is_ordered(
                                x.view() as int - lo.view() as int,
                                diff.view() as int,
                                stride.view() as int,
                            );
                            lemma_mul_left_inequality(stride.view() as int, k, q);
                            assert(x.view() as int - lo.view() as int <= canon_hi.view() as int
                                - lo.view() as int);
                        }
                    };
                }
                r
            }
        }
    }

    /// If a positive `d` is an exact multiple of a positive `s`, `s <= d`.
    proof fn lemma_divisor_le(d: int, s: int)
        requires
            d > 0,
            s > 0,
            d % s == 0,
        ensures
            s <= d,
    {
        let k = d / s;
        lemma_fundamental_div_mod(d, s);
        assert(d == s * k);
        if k == 0 {
            assert(s * 0 == 0);
            assert(d == 0);
        }
        assert(k >= 1);
        lemma_mul_left_inequality(s, 1, k);
    }

    /// Used twice (with `x`/`y` swapped) inside `lemma_canonical` to pin
    /// down the stride once `lo`/`hi` already agree: `x`'s second grid
    /// point (`x.lo + x.stride`) must be a grid point of `y` too, which
    /// forces `y.stride` to divide `x.stride`.
    proof fn lemma_stride_le(x: &Self, y: &Self)
        requires
            x.wf(),
            y.wf(),
            x.lo() == y.lo(),
            x.hi() == y.hi(),
            x.lo().view() < x.hi().view(),
            forall|c: W| #![trigger x.gamma(c)] x.gamma(c) == y.gamma(c),
        ensures
            y.stride().view() <= x.stride().view(),
    {
        let d = x.hi.view() as int - x.lo.view() as int;
        Self::lemma_divisor_le(d, x.stride.view() as int);
        let p_int = x.lo.view() as int + x.stride.view() as int;
        x.hi.lemma_view_bounded();
        lemma_from_small::<W>(p_int);
        let p = W::from_int(p_int);
        lemma_mod_self_0(x.stride.view() as int);
        assert(x.gamma(p));
        assert(y.gamma(p));
        assert((p.view() as int - y.lo.view() as int) % (y.stride.view() as int) == 0);
        Self::lemma_divisor_le(x.stride.view() as int, y.stride.view() as int);
    }

    // ---- general-purpose modular arithmetic building blocks -------------

    proof fn lemma_mod_zero_sum(a: int, b: int, m: int)
        requires
            m > 0,
            a % m == 0,
            b % m == 0,
        ensures
            (a + b) % m == 0,
    {
        lemma_mod_adds(a, b, m);
    }

    proof fn lemma_mod_zero_neg(a: int, m: int)
        requires
            m > 0,
            a % m == 0,
        ensures
            (-a) % m == 0,
    {
        lemma_fundamental_div_mod(a, m);
        let k = a / m;
        assert(a == m * k);
        lemma_mul_unary_negation(m, k);
        assert(-a == m * (-k));
        lemma_mod_multiples_basic(-k, m);
        lemma_mul_is_commutative(m, -k);
    }

    proof fn lemma_mod_zero_diff(a: int, b: int, m: int)
        requires
            m > 0,
            a % m == 0,
            b % m == 0,
        ensures
            (a - b) % m == 0,
    {
        Self::lemma_mod_zero_neg(b, m);
        Self::lemma_mod_zero_sum(a, -b, m);
        assert(a - b == a + (-b));
    }

    /// Divisibility is transitive: `y | x` and `z | y` implies `z | x`.
    proof fn lemma_mod_zero_transitive(x: int, y: int, z: int)
        requires
            y > 0,
            z > 0,
            x % y == 0,
            y % z == 0,
        ensures
            x % z == 0,
    {
        lemma_fundamental_div_mod(x, y);
        lemma_fundamental_div_mod(y, z);
        let p = x / y;
        let q = y / z;
        assert(x == y * p);
        assert(y == z * q);
        assert(x == (z * q) * p);
        lemma_mul_is_associative(z, q, p);
        assert(x == z * (q * p));
        lemma_mod_multiples_basic(q * p, z);
        lemma_mul_is_commutative(z, q * p);
    }

    /// `self_` and `o` share a nonzero stride and agree on residue class
    /// (`self_.lo - o.lo` is a multiple of that stride): a point on one's
    /// grid is on the other's grid too. Says nothing about bounds.
    proof fn lemma_same_grid(self_: &Self, o: &Self, c: W)
        requires
            self_.stride().view() == o.stride().view(),
            self_.stride().view() > 0,
            (self_.lo().view() as int - o.lo().view() as int) % (self_.stride().view() as int)
                == 0,
            (c.view() as int - self_.lo().view() as int) % (self_.stride().view() as int) == 0,
        ensures
            (c.view() as int - o.lo().view() as int) % (self_.stride().view() as int) == 0,
    {
        Self::lemma_mod_zero_sum(
            c.view() as int - self_.lo().view() as int,
            self_.lo().view() as int - o.lo().view() as int,
            self_.stride().view() as int,
        );
        assert(c.view() as int - o.lo().view() as int == (c.view() as int - self_.lo().view()
            as int) + (self_.lo().view() as int - o.lo().view() as int));
    }

    // ---- operation-specific lemmas ---------------------------------------

    /// Bridges the native `abs_diff` (computed by an exec `if self.lo <=
    /// o.lo`) to the signed difference used in spec-level residue checks.
    proof fn lemma_abs_diff_residue(self_lo: W, o_lo: W, abs_diff: W, stride: W)
        requires
            stride.view() > 0,
            abs_diff.view() == if self_lo.view() <= o_lo.view() {
                o_lo.view() - self_lo.view()
            } else {
                self_lo.view() - o_lo.view()
            },
        ensures
            (self_lo.view() as int - o_lo.view() as int) % (stride.view() as int) == 0
                <==> abs_diff.view() as int % (stride.view() as int) == 0,
    {
        if self_lo.view() <= o_lo.view() {
            assert(self_lo.view() as int - o_lo.view() as int == -(abs_diff.view() as int));
            if abs_diff.view() as int % (stride.view() as int) == 0 {
                Self::lemma_mod_zero_neg(abs_diff.view() as int, stride.view() as int);
            }
            if (self_lo.view() as int - o_lo.view() as int) % (stride.view() as int) == 0 {
                Self::lemma_mod_zero_neg(
                    self_lo.view() as int - o_lo.view() as int,
                    stride.view() as int,
                );
            }
        }
    }

    proof fn lemma_leq_sound(self_: &Self, o: &Self, offset: W)
        requires
            self_.wf(),
            o.wf(),
            self_.lo().view() < self_.hi().view(),
            o.lo().view() <= self_.lo().view(),
            self_.hi().view() <= o.hi().view(),
            o.stride().view() > 0,
            self_.stride().view() as int % (o.stride().view() as int) == 0,
            offset.view() == self_.lo().view() - o.lo().view(),
            offset.view() as int % (o.stride().view() as int) == 0,
        ensures
            forall|c: W| #[trigger] self_.gamma(c) ==> o.gamma(c),
    {
        assert forall|c: W| #[trigger] self_.gamma(c) implies o.gamma(c) by {
            if self_.lo.view() <= c.view() && c.view() <= self_.hi.view() && (c.view() as int
                - self_.lo.view() as int) % (self_.stride.view() as int) == 0 {
                Self::lemma_mod_zero_transitive(
                    c.view() as int - self_.lo.view() as int,
                    self_.stride.view() as int,
                    o.stride.view() as int,
                );
                Self::lemma_mod_zero_sum(
                    c.view() as int - self_.lo.view() as int,
                    offset.view() as int,
                    o.stride.view() as int,
                );
                assert(c.view() as int - o.lo.view() as int == (c.view() as int - self_.lo.view()
                    as int) + offset.view() as int);
            }
        };
    }

    /// `self_`, `o` share a nonzero stride and residue class; `r` widens
    /// the bounds to `[min lo, max hi]` on the same grid.
    proof fn lemma_join_compatible(self_: &Self, o: &Self, abs_diff: W, r: &Self)
        requires
            self_.wf(),
            o.wf(),
            self_.stride().view() == o.stride().view(),
            self_.stride().view() > 0,
            Self::residues_match(self_, o, abs_diff),
            r.stride() == self_.stride(),
            r.lo().view() == if self_.lo().view() <= o.lo().view() {
                self_.lo().view()
            } else {
                o.lo().view()
            },
            r.hi().view() == if self_.hi().view() <= o.hi().view() {
                o.hi().view()
            } else {
                self_.hi().view()
            },
        ensures
            r.wf(),
            forall|c: W| #[trigger] self_.gamma(c) ==> r.gamma(c),
            forall|c: W| #[trigger] o.gamma(c) ==> r.gamma(c),
    {
        Self::lemma_abs_diff_residue(self_.lo, o.lo, abs_diff, self_.stride);
        Self::lemma_mod_zero_neg(
            self_.lo().view() as int - o.lo().view() as int,
            self_.stride().view() as int,
        );
        assert forall|c: W| #[trigger] self_.gamma(c) implies r.gamma(c) by {
            if self_.lo.view() <= c.view() && c.view() <= self_.hi.view() && (c.view() as int
                - self_.lo.view() as int) % (self_.stride.view() as int) == 0 {
                if r.lo().view() != self_.lo.view() {
                    Self::lemma_same_grid(self_, o, c);
                }
            }
        };
        assert forall|c: W| #[trigger] o.gamma(c) implies r.gamma(c) by {
            if o.lo.view() <= c.view() && c.view() <= o.hi.view() && (c.view() as int
                - o.lo.view() as int) % (self_.stride.view() as int) == 0 {
                if r.lo().view() != o.lo.view() {
                    Self::lemma_same_grid(o, self_, c);
                }
            }
        };
        // r.wf()'s grid condition, same technique as lemma_meet_same_stride.
        assert((r.hi().view() as int - r.lo().view() as int) % (self_.stride().view() as int)
            == 0) by {
            if r.hi().view() == self_.hi.view() {
                if r.lo().view() != self_.lo.view() {
                    Self::lemma_same_grid(self_, o, self_.hi);
                }
            } else {
                if r.lo().view() != o.lo.view() {
                    Self::lemma_same_grid(o, self_, o.hi);
                }
            }
        };
    }

    proof fn lemma_join_two_points(self_: &Self, o: &Self, r: &Self)
        requires
            self_.wf(),
            o.wf(),
            self_.lo().view() == self_.hi().view(),
            o.lo().view() == o.hi().view(),
            self_.lo().view() != o.lo().view(),
            r.lo().view() == if self_.lo().view() <= o.lo().view() {
                self_.lo().view()
            } else {
                o.lo().view()
            },
            r.hi().view() == if self_.lo().view() <= o.lo().view() {
                o.lo().view()
            } else {
                self_.lo().view()
            },
            r.stride().view() == r.hi().view() - r.lo().view(),
        ensures
            r.wf(),
            forall|c: W| #[trigger] self_.gamma(c) ==> r.gamma(c),
            forall|c: W| #[trigger] o.gamma(c) ==> r.gamma(c),
    {
        lemma_mod_self_0(r.stride().view() as int);
        lemma_mod_multiples_basic(0, r.stride().view() as int);
        assert forall|c: W| #[trigger] self_.gamma(c) implies r.gamma(c) by {}
        assert forall|c: W| #[trigger] o.gamma(c) implies r.gamma(c) by {}
    }

    proof fn lemma_meet_same_stride(self_: &Self, o: &Self, abs_diff: W, r: &Self)
        requires
            self_.wf(),
            o.wf(),
            self_.stride().view() == o.stride().view(),
            self_.stride().view() > 0,
            Self::residues_match(self_, o, abs_diff),
            r.lo().view() == if self_.lo().view() <= o.lo().view() {
                o.lo().view()
            } else {
                self_.lo().view()
            },
            r.hi().view() == if self_.hi().view() <= o.hi().view() {
                self_.hi().view()
            } else {
                o.hi().view()
            },
            r.lo().view() <= r.hi().view(),
            r.stride().view() == if r.lo().view() == r.hi().view() {
                0
            } else {
                self_.stride().view()
            },
        ensures
            r.wf(),
            forall|c: W| #[trigger] r.gamma(c) <== self_.gamma(c) && o.gamma(c),
    {
        Self::lemma_abs_diff_residue(self_.lo, o.lo, abs_diff, self_.stride);
        Self::lemma_mod_zero_neg(
            self_.lo().view() as int - o.lo().view() as int,
            self_.stride().view() as int,
        );
        if r.lo().view() == r.hi().view() {
            // Collapsed to a single point: gamma(r) is just x == r.lo(),
            // which self_.gamma(c) && o.gamma(c) already pins c to (their
            // bounds squeeze to the same point r.lo == r.hi).
            assert forall|c: W| self_.gamma(c) && o.gamma(c) implies #[trigger] r.gamma(c) by {}
            return ;
        }
        // r.lo is max(self_.lo, o.lo) and r.hi is min(self_.hi, o.hi): if c
        // is in both gammas, the bound check is automatic, and the residue
        // check is whichever of the two conjuncts matches r.lo directly --
        // no grid transfer needed, unlike join.
        assert forall|c: W| self_.gamma(c) && o.gamma(c) implies #[trigger] r.gamma(c) by {}
        // r.wf()'s grid condition: whichever of self_/o contributed r.hi
        // already has it on its own grid (wf); same_grid transfers that to
        // r.lo's anchor only when r.lo came from the other side.
        assert((r.hi().view() as int - r.lo().view() as int) % (self_.stride().view() as int)
            == 0) by {
            if r.hi().view() == self_.hi.view() {
                if r.lo().view() != self_.lo.view() {
                    Self::lemma_same_grid(self_, o, self_.hi);
                }
            } else {
                if r.lo().view() != o.lo.view() {
                    Self::lemma_same_grid(o, self_, o.hi);
                }
            }
        };
    }

    proof fn lemma_residue_mismatch_disjoint(self_: &Self, o: &Self, abs_diff: W)
        requires
            self_.wf(),
            o.wf(),
            self_.stride().view() == o.stride().view(),
            self_.stride().view() > 0,
            abs_diff.view() == if self_.lo().view() <= o.lo().view() {
                o.lo().view() - self_.lo().view()
            } else {
                self_.lo().view() - o.lo().view()
            },
            abs_diff.view() as int % (self_.stride().view() as int) != 0,
        ensures
            forall|c: W| #[trigger] self_.gamma(c) ==> !o.gamma(c),
    {
        Self::lemma_abs_diff_residue(self_.lo, o.lo, abs_diff, self_.stride);
        assert forall|c: W| #[trigger] self_.gamma(c) implies !o.gamma(c) by {
            if o.gamma(c) {
                Self::lemma_mod_zero_diff(
                    c.view() as int - o.lo.view() as int,
                    c.view() as int - self_.lo.view() as int,
                    self_.stride.view() as int,
                );
                assert((self_.lo.view() as int - o.lo.view() as int) == (c.view() as int
                    - o.lo.view() as int) - (c.view() as int - self_.lo.view() as int));
            }
        };
    }

    /// Whether `self_`'s and `o`'s residues agree, expressed through the
    /// caller's already-computed native `abs_diff` (see
    /// `lemma_abs_diff_residue`) instead of a fresh spec-level formula.
    pub open spec fn residues_match(self_: &Self, o: &Self, abs_diff: W) -> bool {
        &&& abs_diff.view() == if self_.lo().view() <= o.lo().view() {
            o.lo().view() - self_.lo().view()
        } else {
            self_.lo().view() - o.lo().view()
        }
        &&& abs_diff.view() as int % (self_.stride().view() as int) == 0
    }

    /// `gamma(lo)` and `gamma(hi)` both hold for any wf value -- used
    /// everywhere a proof needs a point known to be in a domain's own
    /// gamma. `gamma(hi)` unfolds directly from `wf`'s own grid condition;
    /// `gamma(lo)` needs `0 % stride == 0` spelled out, since Z3 does not
    /// know that without a hint.
    proof fn lemma_contains_bounds(&self)
        requires
            self.wf(),
        ensures
            self.gamma(self.lo),
            self.gamma(self.hi),
    {
        if self.stride.view() > 0 {
            lemma_mod_multiples_basic(0, self.stride.view() as int);
        }
    }
}

impl<W: Word> Domain for StridedInterval<W> {
    type C = W;

    open spec fn wf(&self) -> bool {
        &&& self.lo().view() <= self.hi().view()
        &&& (self.stride().view() == 0 <==> self.lo().view() == self.hi().view())
        &&& (self.stride().view() > 0 ==> (self.hi().view() as int - self.lo().view() as int) % (
        self.stride().view() as int) == 0)
    }

    open spec fn gamma(&self, c: W) -> bool {
        self.lo().view() <= c.view() && c.view() <= self.hi().view() && (self.stride().view()
            == 0 || (c.view() as int - self.lo().view() as int) % (self.stride().view() as int)
            == 0)
    }

    proof fn lemma_nonempty(&self) {
        self.lemma_contains_bounds();
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        a.lemma_contains_bounds();
        b.lemma_contains_bounds();
        assert(b.gamma(a.lo) && b.gamma(a.hi));
        assert(a.gamma(b.lo) && a.gamma(b.hi));
        // lo, hi agree: each side's own lo/hi is a member of the other side.
        assert(a.lo.view() <= b.lo.view() && b.lo.view() <= a.lo.view());
        assert(a.hi.view() <= b.hi.view() && b.hi.view() <= a.hi.view());
        W::lemma_view_injective(a.lo, b.lo);
        W::lemma_view_injective(a.hi, b.hi);
        // strides agree.
        if a.lo.view() == a.hi.view() {
            // both singletons (stride == 0) since lo == hi forces it in wf.
            W::lemma_view_injective(a.stride, b.stride);
        } else {
            Self::lemma_stride_le(a, b);
            Self::lemma_stride_le(b, a);
            W::lemma_view_injective(a.stride, b.stride);
        }
    }

    fn dup(&self) -> (r: Self) {
        StridedInterval { stride: self.stride, lo: self.lo, hi: self.hi }
    }

    fn top() -> (r: Self) {
        let r = StridedInterval { stride: W::one(), lo: W::zero(), hi: W::max() };
        proof {
            W::lemma_modulus();
            assert((r.hi().view() as int - r.lo().view() as int) % 1 == 0) by (nonlinear_arith);
            assert forall|c: W| #[trigger] r.gamma(c) by {
                c.lemma_view_bounded();
                assert((c.view() as int - 0) % 1 == 0) by (nonlinear_arith);
            }
        }
        r
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        if self.lo.eq(self.hi) {
            o.contains(self.lo)
        } else if o.stride.eq(W::zero()) {
            false
        } else {
            let bounds_ok = o.lo.le(self.lo) && self.hi.le(o.hi);
            if !bounds_ok {
                false
            } else {
                let divides = self.stride.urem(o.stride).eq(W::zero());
                let offset = self.lo.checked_sub(o.lo).expect("o.lo <= self.lo");
                let residue_ok = offset.urem(o.stride).eq(W::zero());
                proof {
                    if divides && residue_ok {
                        Self::lemma_leq_sound(self, o, offset);
                    }
                }
                divides && residue_ok
            }
        }
    }

    fn join(&self, o: &Self) -> (r: Self) {
        let abs_diff = if self.lo.le(o.lo) {
            o.lo.checked_sub(self.lo).expect("self.lo <= o.lo")
        } else {
            self.lo.checked_sub(o.lo).expect("o.lo <= self.lo")
        };
        let compatible = self.stride.eq(o.stride) && !self.stride.eq(W::zero())
            && abs_diff.urem(self.stride).eq(W::zero());
        if compatible {
            let lo = if self.lo.le(o.lo) {
                self.lo
            } else {
                o.lo
            };
            let hi = if self.hi.le(o.hi) {
                o.hi
            } else {
                self.hi
            };
            let r = StridedInterval { stride: self.stride, lo, hi };
            proof {
                Self::lemma_join_compatible(self, o, abs_diff, &r);
            }
            r
        } else if self.stride.eq(W::zero()) && o.stride.eq(W::zero()) && self.lo.eq(o.lo) {
            // the same singleton.
            self.dup()
        } else if self.stride.eq(W::zero()) && o.stride.eq(W::zero())
            && !self.lo.eq(o.lo) {
            // two distinct singletons: exact as a two-point stride.
            let (lo, hi) = if self.lo.le(o.lo) {
                (self.lo, o.lo)
            } else {
                (o.lo, self.lo)
            };
            let stride = hi.checked_sub(lo).expect("lo <= hi");
            let r = StridedInterval { stride, lo, hi };
            proof {
                Self::lemma_join_two_points(self, o, &r);
            }
            r
        } else {
            // Sound but not tight: no gcd helper yet to compute a common
            // stride, so at minimum keep the bounds instead of dropping
            // them like the pre-port join() did.
            let lo = if self.lo.le(o.lo) {
                self.lo
            } else {
                o.lo
            };
            let hi = if self.hi.le(o.hi) {
                o.hi
            } else {
                self.hi
            };
            let r = StridedInterval { stride: W::one(), lo, hi };
            proof {
                assert forall|x: W| #[trigger] self.gamma(x) implies r.gamma(x) by {
                    assert((x.view() as int - lo.view() as int) % 1 == 0) by (nonlinear_arith);
                }
                assert forall|x: W| #[trigger] o.gamma(x) implies r.gamma(x) by {
                    assert((x.view() as int - lo.view() as int) % 1 == 0) by (nonlinear_arith);
                }
            }
            r
        }
    }

    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        if self.hi.lt(o.lo) || o.hi.lt(self.lo) {
            // Provably disjoint by bounds alone.
            proof {
                assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
            }
            BotOr::Bot
        } else if self.lo.eq(self.hi) {
            if o.contains(self.lo) {
                BotOr::Val(self.dup())
            } else {
                proof {
                    assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
                }
                BotOr::Bot
            }
        } else if o.lo.eq(o.hi) {
            if self.contains(o.lo) {
                BotOr::Val(o.dup())
            } else {
                proof {
                    assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
                }
                BotOr::Bot
            }
        } else if self.stride.eq(o.stride) {
            let abs_diff = if self.lo.le(o.lo) {
                o.lo.checked_sub(self.lo).expect("self.lo <= o.lo")
            } else {
                self.lo.checked_sub(o.lo).expect("o.lo <= self.lo")
            };
            if abs_diff.urem(self.stride).eq(W::zero()) {
                let lo = if self.lo.le(o.lo) {
                    o.lo
                } else {
                    self.lo
                };
                let hi = if self.hi.le(o.hi) {
                    self.hi
                } else {
                    o.hi
                };
                if lo.le(hi) {
                    // A same-residue intersection can still collapse to one
                    // point (e.g. touching at a single value), which must
                    // be re-spelled with stride 0 -- wf forbids stride != 0
                    // with lo == hi.
                    let stride = if lo.eq(hi) { W::zero() } else { self.stride };
                    let r = StridedInterval { stride, lo, hi };
                    proof {
                        Self::lemma_meet_same_stride(self, o, abs_diff, &r);
                    }
                    BotOr::Val(r)
                } else {
                    proof {
                        assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
                    }
                    BotOr::Bot
                }
            } else {
                proof {
                    Self::lemma_residue_mismatch_disjoint(self, o, abs_diff);
                }
                BotOr::Bot
            }
        } else {
            // Immediately incompatible strides without a gcd helper: sound
            // conservative fallback rather than claiming Bot or an exact
            // intersection we cannot yet compute.
            BotOr::Val(self.dup())
        }
    }

    /// Deliberately coarse: jumping an unstable bound to 0/MAX (the usual
    /// Cousot move, see `Interval<W>::widen`) would generally leave it off
    /// the stride grid, breaking the new canonical `wf`. Snapping it back
    /// on needs the same gcd machinery join/meet don't have yet, so widen
    /// only recognizes the stable case (soundness only, per
    /// `doc/domain-traits.md` -- termination is fuel's job, not widen's)
    /// and otherwise jumps straight to `top()`.
    fn widen(&self, o: &Self) -> (r: Self) {
        if o.leq(self) {
            self.dup()
        } else {
            let r = Self::top();
            proof {
                assert forall|c: W| self.gamma(c) || o.gamma(c) implies #[trigger] r.gamma(c) by {
                    c.lemma_view_bounded();
                    assert((c.view() as int - 0) % 1 == 0) by (nonlinear_arith);
                }
            }
            r
        }
    }
}

} // verus!
