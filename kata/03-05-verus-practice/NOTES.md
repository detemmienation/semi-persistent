# Kata 3–5 notes

## Kata 3: u8 interval, `has`/`add`, then compare to `domains.rs`

`src/lib.rs`'s `Interval` was written and verified (`cargo verus verify`:
1 verified, 0 errors) before looking at `abstract-domains/src/domains.rs`
at all. This is the "then compare" part, done after.

### Same shape, same spec

Both define `has`/`wf` identically:

```rust
pub open spec fn wf(self) -> bool { self.lo <= self.hi }
pub open spec fn has(self, x: uN) -> bool { self.lo <= x && x <= self.hi }
```

and both state `add`'s containment postcondition the same way: soundness
against the *wrapped* sum (`c1.wrapping_add(c2)`), because these intervals
sit over a machine word that actually wraps at runtime.

### Where mine differs, and why theirs is the better answer

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

### What I'd change, now that I've seen it

If this were going into the real crate rather than staying a kata, I'd
switch to the `wrapping_add` + backwards-check idiom before generalizing
past `u8` -- not because my version is unsound, but because it's a dead
end the moment a second width is needed, and `domains.rs` already paid the
proof cost of the version that scales.

## Kata 4: meet, monotone, then bottom

Same `Interval`, extended in place (`src/lib.rs`). PDF: "prove meet
commutative and idempotent for it, and add monotone; notice which is hard.
Then add a bottom value and re-prove the meet laws. That is §3.1 in
miniature." All of it verifies: `cargo verus verify` reports 11 verified,
0 errors for the whole file (kata 3 + 4 together).

### The two meet laws: easy, and stayed easy after bottom

`meet_commutative` and `meet_idempotent` both verify with an **empty proof
body** -- Verus's default SMT reasoning discharges them immediately, both
before bottom (`meet_spec` on `Interval`) and after (`meet_commutative_b`/
`meet_idempotent_b` on `IntervalB`). Mechanically this isn't surprising:
`meet_spec` is built from `max`/`min`, which are syntactically symmetric in
their arguments already, and idempotence just substitutes the same value
for both sides of an already-symmetric expression. Adding the `Bot` match
arm doesn't change this -- `(Bot, _) | (_, Bot) => Bot` is symmetric by
construction too.

### Monotone: this was the hard one, and *empirically* hard, not just by reputation

Confirmed by actually breaking it: `add_monotone` needs a helper lemma,
`refines_bounds`, that turns the *quantified* definition of `refines`
(`forall x, self.has(x) ==> other.has(x)`) into two concrete inequalities
(`other.lo <= self.lo`, `self.hi <= other.hi`) by instantiating that
`forall` at `self.lo` and `self.hi` specifically. I deleted the two calls
to `refines_bounds` inside `add_monotone` as a test and reran
`cargo verus verify`: **assertion failed**, immediately, at the final
`assert`. Put them back, it verifies again. So this wasn't a hunch --
Z3 genuinely cannot bridge from the quantified `refines` hypothesis to the
linear-arithmetic fact it needs on its own; it has to be handed the two
instantiated facts explicitly.

What made it hard wasn't Verus syntax, though -- once `refines_bounds` was
in scope, the final three-way case split (neither side overflows / only
the tighter side overflows / both overflow) discharged with a single
`assert(...)` and no further hints. The hard part was the *math*: seeing
that "`a` refines `a2` and `b` refines `b2`" forces `a2.hi + b2.hi >=
a.hi + b.hi`, which rules out the seemingly-plausible fourth case (`a`/`b`
overflows but the *looser* `a2`/`b2` somehow doesn't) as impossible rather
than something to handle. That's exactly the shape of monotonicity bugs
§3.5 warns about generally: "a child class getting tighter can make a
parent get looser" is precisely what this lemma rules out for `add`.

### Bottom, and what it actually bought

`IntervalB` (`Bot | Range { lo, hi }`) re-derives `meet`'s two laws (still
free) and adds the law bottom is *for*: `meet_bottom_absorbing` --
`meet(a, Bot) == Bot` unconditionally. The concrete payoff, demonstrated in
two contrasting tests (`meet_of_disjoint_intervals_is_top_before_bottom`
vs `..._is_bottom_after_adding_it`): the exact same disjoint-evidence
scenario (`[0,5]` meet `[100,200]`) goes from "sound but useless" (`top`,
indistinguishable from knowing nothing) to a real, precise, actionable
answer (`Bot`, "this evidence is contradictory"). That's the §3.1/§4.6
point made concrete rather than just quoted: bottom isn't a nice-to-have,
it's what makes contradiction *detectable* instead of silently smeared
into "could be anything."
