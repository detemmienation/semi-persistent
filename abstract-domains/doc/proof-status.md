# Abstract Domains Proof Status

Last refreshed: 2026-09-27.

## Current result

```text
cargo verus verify
1148 verified, 0 errors
```

The project source contains no executable `admit()` or `assume()` calls. CI
enforces that policy with a source scan and runs ordinary Verus verification.
The pinned `vstd` dependency contains admitted specifications; global
`--no-cheating` fails while compiling `vstd` before reaching this crate. Those
dependency specifications, Verus, and the solver remain part of the trust
boundary.

Enabled executable widths:

- `d8` (`u8`)
- `d16` (`u16`)
- `d32` (`u32`)
- `d64` (`u64`)

The `d128` macro invocation remains disabled because its bitvector obligations
exceed the current solver capacity. Do not describe `u128` as an enabled or
verified executable instance.

Two Rust test suites provide runtime evidence, with different philosophies.
The mirror suite hand-reimplements each macro-stamped legacy type and fuzzes
the reimplementation against itself; it is randomized/exhaustive evidence,
not an independent proof that the mirror matches the verified definitions:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz   # 32 tests
```

The `Domain`-trait suite (`doc/domain-traits.md`'s convention) instead calls
the real executable code directly and brute-forces small (`u8`) instances
against it -- no hand-written reimplementation to drift out of sync:

```text
cargo test -p semi-persistent-abstract-domains --test domain_traits   # 9 tests
```

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths (macro-stamped, `domains.rs`) | every method verifies its stated contract; containment scope is listed below |
| L4 | `StridedInterval<W>` (`strided.rs`), ported onto the shared `Domain`/`Word` traits from `doc/domain-traits.md` | `wf` is canonical (`lemma_canonical` proved); `leq`/`join`/`meet`/`widen` implemented; not yet in a `Product` |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |
| `ReducedProduct` | `reduce`, `add` |
| `StridedInterval<W>` | `new`, `constant`, `leq` (sound and complete), `join`, `meet`, `widen`, `Arith<Unsigned<W>>` (`add`, `sub`, `neg`); precision caveats below |

The `ExecUnum` proofs use native/spec bridge lemmas, the L3 `ChoppedUnum`
soundness theorems, explicit overflow-to-top cases, and interval-to-Unum range
lemmas. `ReducedProduct::add` composes the four component containment
postconditions and then applies the proved containment of `reduce`.

Other executable methods currently prove well-formedness only. In particular,
this includes Tnum multiplication, shifts, negation and subtraction, most
Unum conversions/arithmetic helpers, and ReducedProduct bitwise operations,
subtraction, multiplication, division, shifts, joins, meets, and negation.
Their implementations and finite mirror tests are evidence, but not universal
containment theorems. Adding those postconditions and proofs is the remaining
L4 soundness work.

`StridedInterval<W>` (`src/strided.rs`) is the first domain in this crate
ported onto the shared `Domain`/`Word`/`lattice::BotOr` interface fixed by
`doc/domain-traits.md` (added in #116); `Interval<W>` and `IntervalZ`
(`interval.rs`, `interval_z.rs`) are the reference ports the interface was
designed against. Until every domain is migrated, the crate has two
coexisting shapes for machine-word domains: the legacy per-width macro
stamping in `domains.rs` (`ExecTnum`, `ExecAnum`, `ExecUnum`, the old
`Interval`, `ReducedProduct`) and the new generic-over-`W` shape. The two
are independent; nothing here claims anything about the legacy macro
types' status beyond what the Layer table already says.

`wf` is canonical: `stride == 0 <==> lo == hi`, and when `stride > 0`,
`(hi - lo) % stride == 0`. Unlike the pre-port representation, `(0,7,7)`,
`(2,7,7)`, and `(5,7,7)` are no longer three legal encodings of `{7}` --
only `(0,7,7)` is well-formed, and `lemma_canonical` proves that any two
wf values with the same concretization are the same value. `leq`, `join`,
`meet`, and `widen` are all proved sound against `gamma`, and `leq` is
also proved complete (`b <==> gamma(self) ⊆ gamma(o)`). `new` exports
exactly which set it builds, and `constant(c)` builds `{c}`. No other
contract states optimality or exactness. Known precision gaps, none of
which is a soundness bug:

- `meet` is not proved exact: its `Val` contract only says the result
  contains the intersection. It is exact (and `Bot` exactly when the
  intersection is empty) when one operand is a singleton or one stride
  divides the other, which includes `meet(top(), x) == x`; the tests
  check this exhaustively on the u8 samples. When neither stride divides
  the other, `meet` clips the larger-stride operand to the common bounds,
  which may keep points off the other grid and may return a value for an
  empty intersection. `meet` is commutative in all cases.
- When both operands share a nonzero stride and residue class, `join`
  is the least upper bound but **not** the exact union --
  widening the range can span a gap neither operand covers. `join(si(3,
  2,8), si(3,14,17))` claims `11`, which is in neither operand
  (`strided_join_same_residue_is_not_always_exact` in
  `tests/domain_traits.rs` pins this down after "the same-stride join is
  exact" was flagged as a misleading claim in review). Two distinct
  singletons are the one `join` case that *is* exact, since a two-point
  set has no representable "gap". Otherwise `join` keeps the bounds
  `[min lo, max hi]` and uses an operand's stride when it divides the
  other stride and the distance between the `lo`s (so `{4} ⊔ (2,0,10)` is
  `(2,0,10)`), else stride 1.
- `widen` keeps the join's stride and moves an unstable bound to the last
  grid point before the end of the range rather than to 0/MAX, which
  would usually be off the grid. On `i = 0; while i < 200 { i += 4 }` it
  reaches `(4,0,252)`, and one decreasing iteration gives `(4,0,200)`
  (`strided_widen_keeps_the_stride`).

- `Arith<Unsigned<W>>`: `add` and `sub` use a common grid of the two
  strides (an operand's stride when it divides the other, else 1) and
  shift the bounds. They are exact when the operands share a grid and no
  result wraps or every result wraps; when only some results wrap they
  return Top. `neg` is exact when 0 is not in the set; otherwise it joins
  `{0}` with the exact negation of the rest. Signedness lives in the
  semantics, so `Arith<Signed<W>>` on the same carrier is still open.

The tight join stride is `gcd(s1, s2, |lo1 - lo2|)` (Balakrishnan &
Reps), and the same gcd gives the tight `add`/`sub` stride; the exact
meet for non-dividing strides needs CRT. Both come
from the `gcd`/`crt_merge` helpers in #112, which has not landed yet.
`DivRem`, bitwise operations, shifts, casts, comparisons, and reduction into a
`Product` are still open.
