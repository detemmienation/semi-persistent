# Abstract Domains Proof Status

Last refreshed: 2026-09-26.

## Last verified #106 baseline (before the #112 transplant)

```text
cargo verus verify
1128 verified, 0 errors
```

The old #112 branch recorded 1254 verified, 0 errors before migration.
Neither count is a verification result for the transplanted #112 tree;
verification of that tree is pending.

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

The CRT suite calls the actual executable helpers and contains 4 tests,
one for each enabled width:

```text
cargo test -p semi-persistent-abstract-domains --test crt
```

It covers normalized inputs, compatible and incompatible constraints, and LCM
overflow with a representable solution (including `MAX`) or no representable
solution. The old #112 branch recorded passing results for 38 mirror tests
and 4 CRT tests. The new #106 base replaces six Congruence mirror tests with
4 real implementation tests; the mirror suite now contains 32 tests.
The transplanted tree has not yet been retested.

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths | every method verifies its stated contract; containment scope is listed below |
| L4 | Shared GCD/CRT helpers | transplanted from #112; exact CRT and overflow contracts previously verified at all four enabled widths; revalidation pending |
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

The helpers remain inside `abstract_domain!` in `domains.rs` for use by
Congruence and future Strided Interval operations.

- `gcd` proves `is_gcd`, including `gcd(0, 0) = 0`, using the Euclidean-step lemma.
- `extended_gcd` proves the GCD, Bézout identity, and coefficient bounds.
- `crt_compatible` checks residue compatibility modulo the GCD. Supporting
  lemmas prove that common solutions imply compatibility and incompatible
  constraints have no common integer solution.
- `checked_lcm` returns the exact LCM when it fits in `$uint`; `None` proves
  that the exact LCM exceeds the width's maximum. Both inputs must be positive.
- `crt_merge` accepts positive moduli and normalizes the input residues.
  Its result distinguishes the following cases:

| Result | Verified guarantee |
| --- | --- |
| `Merged { modulus, residue }` | The modulus is the exact LCM, the residue is canonical, and the class represents exactly all common integer solutions. |
| `Incompatible` | There is no common integer solution. |
| `ModulusOverflow { wide_residue }` | The inputs are compatible and the exact LCM exceeds `MAX`. The canonical common residue is computed in `u128`; a representable value is a common solution exactly when it equals `wide_residue`. |

In the overflow case, `wide_residue <= MAX` identifies the unique representable
solution; otherwise the representable intersection is empty. The executable
arithmetic is verified to avoid overflow. These helpers handle regular modular
constraints only; Singleton, Bottom, and interval bounds belong to callers.

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
GCD/extended-GCD/CRT helpers belong to #112. This PR adds neither those
operations nor arithmetic transfers. Congruence has no internal bottom;
future empty results will use the existing external `BotOr` architecture.

`cargo test --test congruence` passes 4 tests against the real implementation.
The exhaustive oracle checks all 65,536 raw u8 pairs against all 256 words,
including normalization, nonemptiness, canonical invariants, and unique
representation of all 16,640 distinct sets. Other cases cover constant/top,
singleton collapse, second-member boundaries, all four word widths and legacy
aliases. The old six Congruence mirror tests were replaced by this target.

The #106 baseline `cargo test` passed 39 integration tests: 4 Congruence, 3 reference-domain,
and 32 mirror tests (0 failures; 1 unrelated doctest ignored).
The #106 baseline verification count above uses the repository-pinned Verus
`0.2026.09.20.aef82ed`, matching the pinned `vstd` dependency.
