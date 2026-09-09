//! Kata 3 (PRACTICUM-LATTICE.pdf §1.6 item 3): an interval over u8 with
//! `has` and `add`, and a proof that `has(x) && has(y) ==> has(x + y)` for
//! the result -- written without looking at abstract-domains/src/domains.rs
//! first. See NOTES.md for the after-the-fact comparison.

use vstd::prelude::*;

verus! {

pub struct Interval {
    pub lo: u8,
    pub hi: u8,
}

impl Interval {
    pub open spec fn wf(&self) -> bool {
        self.lo <= self.hi
    }

    pub open spec fn has(&self, x: u8) -> bool {
        self.lo <= x && x <= self.hi
    }

    /// Sound addition over u8, which wraps at the machine level: if the
    /// endpoint sum could overflow for some x, y in range, give up
    /// precision and return top ([0, 255]) rather than track the wrap.
    pub fn add(&self, other: &Interval) -> (result: Interval)
        requires
            self.wf(),
            other.wf(),
        ensures
            result.wf(),
            result == add_spec(*self, *other),
            forall|x: u8, y: u8|
                self.has(x) && other.has(y) ==> #[trigger] result.has(x.wrapping_add(y)),
    {
        let lo_sum: u16 = self.lo as u16 + other.lo as u16;
        let hi_sum: u16 = self.hi as u16 + other.hi as u16;
        if hi_sum <= 255 {
            Interval { lo: lo_sum as u8, hi: hi_sum as u8 }
        } else {
            Interval { lo: 0, hi: 255 }
        }
    }

    // ---- Kata 4: meet, monotonicity, then bottom. Same Interval, no bottom
    // yet -- so meet of two disjoint ranges has nowhere sound to go but top.
    // That's not a bug in what follows; it's the exact problem §3.1 names.

    pub open spec fn top() -> Interval {
        Interval { lo: 0, hi: 255 }
    }

    /// `self` refines `other`: everything `self` could be, `other` also
    /// allows. (§2's notation: values(self) subset-of values(other).)
    pub open spec fn refines(self, other: Self) -> bool {
        forall|x: u8| self.has(x) ==> other.has(x)
    }

    /// What `meet` computes, as ghost/spec-level math -- `proof fn` can't
    /// call the exec `meet` below, so the meet laws are proved about this
    /// mirror instead, and `meet`'s postcondition ties the two together.
    pub open spec fn meet_spec(self, other: Self) -> Interval {
        let lo = if self.lo > other.lo { self.lo } else { other.lo };
        let hi = if self.hi < other.hi { self.hi } else { other.hi };
        if lo > hi { Self::top() } else { Interval { lo, hi } }
    }

    pub fn meet(&self, other: &Interval) -> (r: Interval)
        requires
            self.wf(),
            other.wf(),
        ensures
            r.wf(),
            r == self.meet_spec(*other),
            forall|x: u8| self.has(x) && other.has(x) ==> #[trigger] r.has(x),
    {
        let lo = if self.lo > other.lo { self.lo } else { other.lo };
        let hi = if self.hi < other.hi { self.hi } else { other.hi };
        if lo > hi {
            // No bottom to fall back to yet: sound (vacuously -- there's no
            // x satisfying both sides for the postcondition to say anything
            // about) but useless, exactly as §3.1 says. This is the line
            // Task 1's real fix replaces.
            Interval { lo: 0, hi: 255 }
        } else {
            Interval { lo, hi }
        }
    }

    /// If `self` refines `other` (both well-formed ranges), `other`'s
    /// bounds are looser on both sides. Proved by instantiating `refines`'s
    /// forall at self's own two endpoints -- a well-formed self always has
    /// both of them.
    pub proof fn refines_bounds(self, other: Self)
        requires
            self.wf(),
            other.wf(),
            self.refines(other),
        ensures
            other.lo <= self.lo,
            self.hi <= other.hi,
    {
        assert(self.has(self.lo));
        assert(self.has(self.hi));
    }
}

/// Law 1: commutative. Trivial -- `max`/`min` don't care about argument
/// order, so `meet_spec` is syntactically symmetric already.
pub proof fn meet_commutative(a: Interval, b: Interval)
    requires a.wf(), b.wf(),
    ensures a.meet_spec(b) == b.meet_spec(a),
{
}

/// Law 2: idempotent. Also easy -- `meet_spec(a, a)` takes max(lo,lo) and
/// min(hi,hi), which are just lo and hi again, and a well-formed `a` never
/// hits the lo > hi fallback against itself.
pub proof fn meet_idempotent(a: Interval)
    requires a.wf(),
    ensures a.meet_spec(a) == a,
{
}

/// Law 3: `add` is monotone -- refining the inputs never loosens the
/// output. §3.5 calls this "the one most often skipped and the one the
/// e-graph most needs": without it, a child class getting tighter could
/// make a *parent's* computed value get looser, which is incoherent for an
/// analysis that's only supposed to ever refine.
///
/// This is the one that needed an explicit proof block, not automatic
/// discharge -- see NOTES.md for what made it harder than the meet laws.
pub proof fn add_monotone(a: Interval, a2: Interval, b: Interval, b2: Interval)
    requires
        a.wf(), a2.wf(), b.wf(), b2.wf(),
        a.refines(a2),
        b.refines(b2),
    ensures
        add_spec(a, b).refines(add_spec(a2, b2)),
{
    a.refines_bounds(a2);
    b.refines_bounds(b2);
    // Now in scope: a2.lo <= a.lo, a.hi <= a2.hi, b2.lo <= b.lo, b.hi <= b2.hi.
    //
    // Three cases on whether each side's endpoint sum overflows u8:
    //  - neither overflows: both sides are proper ranges, and the bound
    //    facts above are exactly what's needed to show the a/b range sits
    //    inside the a2/b2 range -- ordinary linear arithmetic.
    //  - a/b doesn't overflow but a2/b2 does: add_spec(a2,b2) is top, which
    //    contains everything.
    //  - a/b overflows: then a2.hi + b2.hi >= a.hi + b.hi > 255 too (from
    //    the bound facts), so a2/b2 overflows as well -- both sides are
    //    top, and top refines top. (The fourth combination, a/b fine but
    //    a2/b2 overflowing less, can't happen for the same reason.)
    assert(add_spec(a, b).refines(add_spec(a2, b2)));
}

/// Ghost mirror of `add`, for the same reason `meet_spec` exists.
pub open spec fn add_spec(a: Interval, b: Interval) -> Interval {
    let lo_sum = a.lo as int + b.lo as int;
    let hi_sum = a.hi as int + b.hi as int;
    if hi_sum <= 255 {
        Interval { lo: lo_sum as u8, hi: hi_sum as u8 }
    } else {
        Interval::top()
    }
}

// ---- Kata 4, second half: add bottom, re-prove the meet laws.
//
// Same idea as `Interval`, but disjoint ranges now have somewhere sound AND
// useful to go: `Bot` means "no concrete value satisfies all the evidence",
// which is a real, meaningful answer -- not the `top` cop-out above.

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IntervalB {
    Bot,
    Range { lo: u8, hi: u8 },
}

impl IntervalB {
    pub open spec fn wf(self) -> bool {
        match self {
            IntervalB::Bot => true,
            IntervalB::Range { lo, hi } => lo <= hi,
        }
    }

    pub open spec fn has(self, x: u8) -> bool {
        match self {
            IntervalB::Bot => false,
            IntervalB::Range { lo, hi } => lo <= x && x <= hi,
        }
    }

    pub open spec fn meet_spec(self, other: Self) -> Self {
        match (self, other) {
            (IntervalB::Bot, _) => IntervalB::Bot,
            (_, IntervalB::Bot) => IntervalB::Bot,
            (IntervalB::Range { lo: l1, hi: h1 }, IntervalB::Range { lo: l2, hi: h2 }) => {
                let lo = if l1 > l2 { l1 } else { l2 };
                let hi = if h1 < h2 { h1 } else { h2 };
                if lo > hi { IntervalB::Bot } else { IntervalB::Range { lo, hi } }
            }
        }
    }

    pub fn meet(&self, other: &IntervalB) -> (r: IntervalB)
        requires
            self.wf(),
            other.wf(),
        ensures
            r.wf(),
            r == self.meet_spec(*other),
            forall|x: u8| self.has(x) && other.has(x) ==> #[trigger] r.has(x),
    {
        match (self, other) {
            (IntervalB::Bot, _) | (_, IntervalB::Bot) => IntervalB::Bot,
            (IntervalB::Range { lo: l1, hi: h1 }, IntervalB::Range { lo: l2, hi: h2 }) => {
                let lo = if *l1 > *l2 { *l1 } else { *l2 };
                let hi = if *h1 < *h2 { *h1 } else { *h2 };
                if lo > hi {
                    // The improvement over `Interval::meet`: disjoint
                    // evidence is now a real, precise answer (Bot) instead
                    // of the useless fallback to top.
                    IntervalB::Bot
                } else {
                    IntervalB::Range { lo, hi }
                }
            }
        }
    }
}

/// Re-proof of law 1 (commutative) with bottom in play. Still trivial: the
/// match is symmetric in `self`/`other` by construction (the `(Bot, _) |
/// (_, Bot)` arm doesn't care which side was bottom), and the Range/Range
/// arm is the same max/min symmetry as before.
pub proof fn meet_commutative_b(a: IntervalB, b: IntervalB)
    requires a.wf(), b.wf(),
    ensures a.meet_spec(b) == b.meet_spec(a),
{
}

/// Re-proof of law 2 (idempotent). Also still trivial, same reason as
/// before plus the new `Bot.meet_spec(Bot) == Bot` case.
pub proof fn meet_idempotent_b(a: IntervalB)
    requires a.wf(),
    ensures a.meet_spec(a) == a,
{
}

/// The law bottom actually adds (§3.5): meet with bottom is bottom, always
/// -- not conditional on anything about `a`. Free from the match arms, but
/// worth stating on its own since it's the property §4.6 leans on ("must
/// not use bottom to license anything" starts from meet-with-bottom being
/// unconditionally bottom).
pub proof fn meet_bottom_absorbing(a: IntervalB)
    requires a.wf(),
    ensures
        a.meet_spec(IntervalB::Bot) == IntervalB::Bot,
        IntervalB::Bot.meet_spec(a) == IntervalB::Bot,
{
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// Exhaustive small-width check, mirroring the Task 1 "Done when"
    /// methodology (all u8 pairs is 65,536 cases): for every well-formed
    /// interval pair and every concrete x/y they contain, the *actual*
    /// wrapped sum must land in `add`'s result. This is runtime evidence on
    /// top of the Verus proof, not a substitute for it.
    #[test]
    fn add_is_sound_exhaustive_small() {
        // Full 0..=255 x 0..=255 for lo/hi would be 256^4 interval pairs;
        // keep this fast by sampling interval endpoints and exhausting the
        // contained x/y pairs instead of every interval.
        let intervals = [
            (0u8, 0u8), (0, 255), (10, 20), (200, 255), (250, 255), (0, 1), (128, 128),
        ];
        for &(a_lo, a_hi) in &intervals {
            for &(b_lo, b_hi) in &intervals {
                let a = Interval { lo: a_lo, hi: a_hi };
                let b = Interval { lo: b_lo, hi: b_hi };
                let r = a.add(&b);
                assert!(r.lo <= r.hi, "add result not well-formed: {r:?}");
                for x in a_lo..=a_hi {
                    for y in b_lo..=b_hi {
                        let sum = x.wrapping_add(y);
                        assert!(
                            r.lo <= sum && sum <= r.hi,
                            "unsound: [{a_lo},{a_hi}] + [{b_lo},{b_hi}] -> [{},{}] misses {x}+{y}={sum}",
                            r.lo, r.hi
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn add_stays_precise_when_no_overflow_possible() {
        let a = Interval { lo: 10, hi: 20 };
        let b = Interval { lo: 5, hi: 5 };
        let r = a.add(&b);
        assert_eq!((r.lo, r.hi), (15, 25), "no overflow possible here, so top would be needlessly imprecise");
    }

    #[test]
    fn add_falls_back_to_top_on_possible_overflow() {
        let a = Interval { lo: 200, hi: 255 };
        let b = Interval { lo: 10, hi: 10 };
        let r = a.add(&b);
        assert_eq!((r.lo, r.hi), (0, 255), "210+10=220 fits but 255+10 wraps, so top is what soundness costs here");
    }

    #[test]
    fn meet_of_disjoint_intervals_is_top_before_bottom() {
        // The exact §3.1 problem: no bottom yet, so disjoint evidence has
        // nowhere sound to go but top -- sound, but useless, since `top`
        // can't be distinguished from "we know nothing at all".
        let a = Interval { lo: 0, hi: 5 };
        let b = Interval { lo: 100, hi: 200 };
        let r = a.meet(&b);
        assert_eq!((r.lo, r.hi), (0, 255));
    }

    #[test]
    fn meet_of_disjoint_intervals_is_bottom_after_adding_it() {
        // Same scenario, `IntervalB`: now there's a real, precise answer.
        let a = IntervalB::Range { lo: 0, hi: 5 };
        let b = IntervalB::Range { lo: 100, hi: 200 };
        assert_eq!(a.meet(&b), IntervalB::Bot);
    }

    #[test]
    fn meet_b_commutative_and_idempotent_spot_check() {
        let a = IntervalB::Range { lo: 3, hi: 9 };
        let b = IntervalB::Range { lo: 5, hi: 12 };
        assert_eq!(a.meet(&b), b.meet(&a));
        assert_eq!(a.meet(&a), a);
        assert_eq!(IntervalB::Bot.meet(&a), IntervalB::Bot);
        assert_eq!(a.meet(&IntervalB::Bot), IntervalB::Bot);
    }
}

impl std::fmt::Debug for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lo, self.hi)
    }
}

impl std::fmt::Debug for IntervalB {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntervalB::Bot => write!(f, "Bot"),
            IntervalB::Range { lo, hi } => write!(f, "[{lo}, {hi}]"),
        }
    }
}
