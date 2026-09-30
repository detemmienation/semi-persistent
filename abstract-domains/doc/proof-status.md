# Abstract Domains Proof Status

Last refreshed: 2026-09-29.

## Current result

```text
cargo verus verify
1210 verified, 0 errors
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

The separate Rust mirror suite contains 32 tests:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz
```

Those tests mirror the Verus definitions and provide randomized/exhaustive
finite evidence. They are not an independent proof that a separate executable
implementation corresponds to the verified definitions.

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
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths | every method verifies its stated contract; containment scope is listed below |
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
