# Abstract Domains Proof Status

Last refreshed: 2026-10-06.

## Current result

```text
cargo verus verify
1262 verified, 0 errors
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
verified executable instance. The CRT implementation uses verified `u128`
intermediates for the four enabled widths; this does not enable `d128`.

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

The CRT/helper suite calls the real shared `arithmetic` implementation:

```text
cargo test --test crt
```

Its 8 tests cover all four word widths, GCD/Bézout properties, widened
arithmetic and exact finite CRT outcomes. The exhaustive u8 oracle precomputes
each input class by testing all 256 concrete values, then compares bitset
intersections against the helper for all 532,701,120 unordered pairs of the
32,640 normalized positive-modulus descriptions (including duplicate finite
singleton encodings). Separate checks exercise every raw u8 residue with six
partner classes in both operand orders. The focused target takes about 40
seconds in the local debug build; it does not require an ignored/release-only
test or a mirror implementation.

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths (macro-stamped, `domains.rs`) | every method verifies its stated contract; containment scope is listed below |
| L4 | `StridedInterval<W>` (`strided.rs`), ported onto the shared `Domain`/`Word` traits from `doc/domain-traits.md` | `wf` is canonical (`lemma_canonical` proved); `leq`/`join`/`meet`/`widen` implemented; not yet in a `Product` |
| L4 | Shared GCD/CRT helpers | shared mathematical proofs, deterministic GCD, Bézout, generic exact finite CRT and widened helpers verified |
| L4 | `Congruence<W>` | generic unsigned semantics, canonical normalization, nonemptiness and canonicality proved; full `Domain` implementation deferred to the later lattice PR |

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

### Shared arithmetic helpers

`src/arithmetic.rs` owns the shared foundation; the width-independent `int`/
`nat` proofs are no longer instantiated by `abstract_domain!`. `Word` supplies
lossless `to_u64` and `from_u64` bridges (the latter requires an in-range
input) and proves its modulus is at most 2^64. The generic APIs support u8/u16/u32/u64. A single
private u64/i128/u128 engine retains the verified extended-Euclidean and CRT
calculations without repeating them for each width.

- `gcd_spec` is deterministic and recursive, decreasing on the second operand.
  `gcd<W>` and `gcd_wide` return exactly this specification. Shared proofs
  establish divisibility of both inputs, Euclidean-step correctness, uniqueness,
  divisibility maximality, symmetry and associativity, including zero inputs.
- `extended_gcd<W>` returns the named `ExtendedGcd<W> { gcd, x, y }`. It proves
  equality with `gcd_spec`, Bézout's identity, and the original coefficient bounds.
  Its private recursive engine retains the explicit decreasing argument.
- `crt_merge<W>` requires **positive moduli** and accepts unreduced residues.
  Its `wf` and `has` contracts exactly describe all representable common
  solutions. The u128 engine preserves integer CRT exactness and computes
  the exact LCM and least nonnegative common solution before classification.

| Result | Verified finite-word meaning |
| --- | --- |
| `Class { modulus, residue }` | `0 < modulus`, `residue < modulus`, and `residue + modulus < W::modulus()`; the class contains at least two words and is exactly the intersection. |
| `Singleton { value }` | Exactly one representable common solution, whether the LCM overflows the word or merely cannot reach a second member from the residue. |
| `Empty` | No representable common solution, including incompatible constraints and compatible classes whose least solution exceeds `MAX`. |

Callers no longer inspect a widened residue or reconstruct overflow cases.
Congruence's modulus-zero constants must be handled **before** calling CRT.
No conversion into `BotOr<Congruence<W>>` or Congruence meet is implemented here.
The unused `crt_compatible` and `checked_lcm` executables were removed after
checking callers; their necessary mathematical facts remain shared. There are
no existential GCD result specifications or `#![auto]` shortcuts in this module.
Unrelated pre-existing domain proofs retain their existing annotations.

`gcd_machine_modulus<W>` computes `gcd(m, 2^N)` in u128, including `m = 0` and
`N = 64`. `lemma_wrapping_congruence` proves that reduction modulo 2^N preserves
congruence modulo this GCD, for negative as well as nonnegative integers.
`mul_wide` and `granger_modulus` compute exact widened products and
`gcd(gcd(m1*m2, m1*r2), m2*r1)`. They provide the requested shared foundation;
no Congruence multiplication or other transfer operation is implemented.

PR #112 depends on updated #106 (`732f6db`). Congruence's `Domain` implementation,
refinement, join, meet, widen and arithmetic transfers remain deferred to #114
or later. No proof bypasses or new trusted items were introduced.

### Congruence

`src/congruence.rs` implements the semantic core as `Congruence<W: Word>`
(with the bound on its implementation). Fields are private. The existing
`domains::d8/d16/d32/d64::Congruence` names are aliases of the generic type.
The canonical representation is:

- Singleton: `modulus = 0, residue = x`.
- Progression: `0 < modulus`, `residue < modulus`, and
  `residue + modulus < W::modulus()` in mathematical arithmetic.
- Top: the unique progression `(1, 0)`.

`gamma` (also exposed as `has`) interprets words as unsigned finite-width
values. A singleton contains exactly its residue; a progression contains
exactly the words whose remainder modulo its modulus is its residue.
`contains` is proved equivalent to both specifications. This is set membership,
not a signed or wrapping arithmetic transfer semantics.

`new(m, r)` normalizes a raw class: for `m = 0` it denotes `{r}`, otherwise
it denotes `{x | x % m = r % m}`. This raw-input interpretation differs from
applying the old `has` to an unreduced, malformed pair (which could be empty).
The constructor proves preservation of the raw class through `raw_has` and
establishes `wf`. It uses `Word::urem` and `checked_add`; when the normalized
residue plus the modulus is not representable, it returns a singleton.
For example, `Congruence::<u8>::new(201, 200)` has the same canonical pair as
`constant(200)`. `constant` and `top` have semantic and representation contracts.
`normalize()` on a constructed value is proved to be identity.

`lemma_nonempty` witnesses the residue. `lemma_canonical` proves that equal
gamma sets of well-formed values imply structural equality: residues are the
least members, and nonconstant steps are determined by the second members.
Both use the common `Domain` proof obligations as inherent methods, without
proof bypasses or changes to the trust boundary.

PR #106 deliberately does **not** implement `Domain`: the current trait also
requires `leq`, `join`, `meet`, and `widen`. Those belong to #114; shared
GCD/extended-GCD/CRT helpers are supplied by #112 as described above. Neither
PR implements those Congruence operations or arithmetic transfers. Congruence has no internal bottom;
future empty results will use the existing external `BotOr` architecture.

`cargo test --test congruence` passes 4 tests against the real implementation.
The exhaustive oracle checks all 65,536 raw u8 pairs against all 256 words,
including normalization, nonemptiness, canonical invariants, and unique
representation of all 16,640 distinct sets. Other cases cover constant/top,
singleton collapse, second-member boundaries, all four word widths and legacy
aliases. The old six Congruence mirror tests were replaced by this target.

`cargo test` passes 47 integration tests: 8 CRT/helper, 4 Congruence,
3 reference-domain and 32 mirror tests (0 failures; 1 unrelated doctest ignored).
The verification count above uses the repository-pinned Verus
`0.2026.09.20.aef82ed`, matching the pinned `vstd` dependency.
