# Kata 1 — union-find + hash-consing + rebuild

Practicum ramp-up kata 1 (`PRACTICUM-LATTICE.pdf` §1.6, item 1):

> Union-find with path compression and union by rank from scratch,
> property-tested against a naive set-of-sets model. Add hash-consing,
> build a bare e-graph with `add`, `find`, `union`, `rebuild` in 200 lines,
> then demonstrate the bug you get by *not* rebuilding.

`src/main.rs`: `Rng` (a tiny PRNG), `NaiveUf`(the property-test oracle), 
`UnionFind`, `EGraph`, `main` (the bug demo), and the tests — 
in that order, top to bottom. `Rng`/`NaiveUf` are gated
`#[cfg(test)]` since only the tests use them.

Deliberately detached from the parent repo's workspace (own `[workspace]`
table in `Cargo.toml`) — not part of the verified engine, must never enter
`cargo verus verify`'s scope.

## Running it

```sh
cargo test           # 3 tests: union-find properties + e-graph/congruence
cargo run            # prints the rebuild bug happening, step by step
cargo clippy --all-targets
```

## What's being checked

- **`union_find_agrees_with_naive_model`**: after any sequence of `union`
  calls, the fast union-find and the naive model must agree on which
  elements share a class — checked over every pair after every union.
  Representative identity is never compared (implementation choice, not
  specified behavior — see `doc/book/src/06-egraphs-and-congruence.md`'s
  "the survivor is an implementation choice, not a preferred term").
- **`rebuild_restores_congruence_and_cascades`**: the exact scenario from
  that chapter's "Congruence" section. `f(a)`/`f(b)` stay in separate
  classes after `union(a, b)` until `rebuild()` walks the absorbed class's
  use-list and restores congruence closure — and one `rebuild()` call must
  cascade through more than one level (`g(f(a))`/`g(f(b))`), not just fix
  the immediate parents. `assert_ne!` right after the union, before any
  rebuild, is the bug reproducing correctly, not a mistake in the test.

`cargo run` prints the same scenario so you can watch it instead of just
reading a green checkmark:

```
without rebuild: same=false  (f(a)=2, f(b)=3)
after rebuild:   same=true  (f(a)=2, f(b)=2)
```
