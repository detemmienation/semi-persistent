# Kata 3: u8 interval, `has`/`add`, then compare to `domains.rs`

`src/lib.rs`'s `Interval` was written and verified (`cargo verus verify`:
1 verified, 0 errors) before looking at `abstract-domains/src/domains.rs`
at all. This is the "then compare" part, done after.

## Same shape, same spec

Both define `has`/`wf` identically:

```rust
pub open spec fn wf(self) -> bool { self.lo <= self.hi }
pub open spec fn has(self, x: uN) -> bool { self.lo <= x && x <= self.hi }
```

and both state `add`'s containment postcondition the same way: soundness
against the *wrapped* sum (`c1.wrapping_add(c2)`), because these intervals
sit over a machine word that actually wraps at runtime.

## Where mine differs, and why theirs is the better answer

**Overflow detection.** Mine widens to the next size up (`u8` sums computed
as `u16`) and checks whether the widened `hi` sum exceeds 255. `domains.rs`
instead computes the sum directly at the *same* width via `wrapping_add`,
then detects overflow by checking whether the wrapped result went
**backwards** (`lo < slo || hi < shi || hi < lo` -- the classic
"did-it-get-smaller" overflow idiom).

This isn't a style preference -- it's the reason theirs is one
implementation shared across `u8`/`u16`/`u32`/`u64` via a macro (`$uint`),
while mine is `u8`-specific and would need a *different* trick for `u64`
(there's no verified `u128` here to widen into --
`abstract-domains/doc/proof-status.md` notes `d128` is disabled because its
bitvector obligations exceed current solver capacity). My approach happens
to work at `u8` only because a wider type was conveniently available one
step up; it doesn't generalize, and `domains.rs`'s does. I didn't reach for
the width-generic idiom myself -- I noticed it only by comparing.

**Proof effort.** Mine needed zero explicit proof hints; Verus's default
SMT reasoning discharged the whole `ensures` automatically. `domains.rs`'s
version needs three explicit `assert forall ... implies ... by(bit_vector)`
blocks (lower bound, upper bound, and "the sum didn't wrap" as separate
facts), plus a dedicated `top_has` lemma for the overflow branch.

The reason is the same one: for a *concrete* `u8`, "everything is
`<= 255`" is a tautology Z3 discharges on its own. For an abstract `$uint`
parameter, the solver has no literal bound to reason with -- `!(0 as
$uint) >= x` (bitwise-NOT of zero, i.e. all-ones, i.e. that width's max
value) needs an explicit `by(bit_vector)` hint to become obvious, and the
non-overflow branch's three facts (doesn't wrap, correct lower bound,
correct upper bound) need to be stated and proved as separate steps rather
than falling out of ordinary linear arithmetic. Concreteness bought my
proof its ease; genericity is what costs `domains.rs` the extra machinery.
That trade is the actual lesson of "do it yourself, then compare" here --
not that either version is wrong, but that the width-generic version pays
a real, specific, identifiable proof tax for covering four widths in one
implementation instead of one.

## What I'd change, now that I've seen it

If this were going into the real crate rather than staying a kata, I'd
switch to the `wrapping_add` + backwards-check idiom before generalizing
past `u8` -- not because my version is unsound, but because it's a dead
end the moment a second width is needed, and `domains.rs` already paid the
proof cost of the version that scales.
