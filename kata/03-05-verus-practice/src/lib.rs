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
}

impl std::fmt::Debug for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lo, self.hi)
    }
}
