# Kata 2 notes

PDF §1.6 item 2. Two things recorded here: the `--union-by` investigation
(`union_by.egg`) and the `EGRAPH_DUMP_PLAN=1` walkthrough of §2's example
(`section2_plan.egg`).

## Part 1: a rule set whose result depends on `--union-by`

This one didn't land as a finished example -- I could not build one that
flips a `(check ...)` result within reasonable effort, but the
investigation surfaced a genuine mechanism and a genuine (if currently
masked) limit to it. Reporting how far I got, in the spirit of kata 5.

### Tool: `EGRAPH_TRACE_DELTA=1`

Found in `egraph/src/saturate.rs:582`. Set it (any value) and the engine
prints each semi-naive round's touched/delta log to stderr:

```
[semi round 1] touched=[e8, e26, e25, ...]
```

This turns the investigation from guessing into direct observation.

### Attempt 1: symmetric by accident

First construction (not kept as a file): two singleton-ish classes
`tagA`/`tagB`, each with one parent (`p`/`q`) and one trigger marker
(`mA`/`mB`), merged mid-run by a rule action. All 4 `--union-by` values
under `--use-semi-naive` gave byte-identical output, including the
touched-log trace itself.

Reason, once I looked closely: `tagA` and `tagB` were built with *equal*
rank, size, and use-list length. Every `--union-by` policy's tie-break
picks the same survivor when the weights are tied, so this construction
never actually made two policies disagree. Two earlier, even simpler
attempts had the same flaw for the same reason.

### Attempt 2: real weight divergence (`union_by.egg`)

Deliberately built `A` to rank ~3 via an 8-leaf balanced union tree (rank
only increments on a tie, so a balanced binary merge of 8 singletons reaches
rank 3, and drags in all 8 as members along the way -- rank and size are
coupled through the same merge history, which is itself worth knowing).
Built `B` to rank ~1 but 20 members, by always issuing `(union (B) (eK))`
with `B` first so only the *first* tie bumps its rank; every later fold-in
loses the tie without incrementing.

Result: `--union-by rank` and `--union-by uses` keep `A` (absorb `B`);
`--union-by size` and `--union-by sum` keep `B` (absorb `A`) -- confirmed
directly via the trace: round-1 touched-set size is 21 items when `B` is
absorbed (its ~20 members) vs 10 when `A` is absorbed (~8 members). This
part is a solid, reproducible, real difference driven by `--union-by`.

But `print-stats` (iterations, match-steps, node/class counts, `saturated`)
and the downstream `(rule ((p x) (q x)) ((done x)))` rule's firing round
were still identical across all four policies.

### Why the difference doesn't surface

Read `saturate.rs`'s round loop: **every** round rebuilds a full index
(`IndexStore::build_with`) unconditionally, in addition to the delta index,
and that full index is built from live `find()` results, not stale stored
keys. So a rule needing an "old" fact always resolves it correctly via the
fresh full index, regardless of whether that fact's node happened to be the
one pushed to `touched` this round. The touched-log asymmetry between which
side (`p(A)` or `q(B)`) needed hash-cons key rewriting is real, but it only
ever needs to supply the *new* side of a delta join -- the old side has a
standing safety net. For an ordinary conjunctive rule, that's enough to
make survivor choice invisible.

### Where I'd look next (not attempted)

AC completion's incremental round (`egraph/src/egraph.rs`'s `cc_round`,
`--derive-ac-eqs`) reads the *same* touched log but, per its own doc
comment, only generates critical pairs with at least one endpoint in the
delta -- old×old pairs are skipped except on an explicit full round. That's
a real asymmetry with no full-index fallback, unlike the ordinary rule path
above. This looked like the most promising remaining lever, but building
and understanding a Kapur-superposition example well enough to predict (not
just stumble into) a result is its own project, and drifts pretty far from
what week 1-2 is meant to build intuition for. Parking it here rather than
chasing it further.

### Bottom line

`--union-by` demonstrably changes internal state (the touched/delta log
content, verified via `EGRAPH_TRACE_DELTA=1`) but, for ordinary
conjunctive-rule saturation, that difference is absorbed by the full index
being rebuilt fresh every round. This is itself informative: it's concrete
evidence *for* the engine's own claim ("survivor identity should be
semantically irrelevant," `02-classes-and-union-find.md`) rather than a
counterexample to it, in the cases I tried. A genuine counterexample, if
one exists in ordinary (non-AC-completion) saturation, needs a different
idea than "make the merge weights disagree" -- that part alone isn't
sufficient, as attempt 2 shows.

## Part 2: explaining §2's query plan

Program: `section2_plan.egg`. It's §2's sorts/functions/terms from the PDF,
plus one plain rewrite standing in for the abstract-guard version §2
actually wants (that needs Task 2/3's lattice-on-classes machinery, which
doesn't exist yet):

```lisp
(rewrite (Ite (True) x y) x)
```

"If the condition is literally the `True()` class, `Ite` picks the
then-arm." Run with:

```sh
EGRAPH_DUMP_PLAN=1 ./target/release/semi-persistent \
  kata/02-rules-and-plan/section2_plan.egg
```

Output:

```
=== plan: 2 atoms, 5 steps ===
step[0]: Join target=v0 atom=0 lookups=[ByOp { op: op53 }]
step[1]: Join target=v1 atom=1 lookups=[ByOp { op: op57 }, ByChildPos { child: Local(VarId(0)), pos: 0 }]
step[2]: CheckChildEq parent=v1 pos=0 expected=Local(VarId(0))
step[3]: ExtractChild target=v2 parent=v1 pos=1
step[4]: ExtractChild target=v3 parent=v1 pos=2
```

Two atoms because the pattern `(Ite (True) x y)` has two applied operators:
`True` (0-ary) and `Ite` (3-ary). `x`/`y` aren't atoms -- they're free
pattern variables, bound by extraction once their parent is found, not by a
lookup of their own.

### Step by step: what's bound when it runs

**step[0]** -- `Join target=v0 atom=0 lookups=[ByOp{op: op53}]`.
Binds `v0` to (a representative of) the class of every node with operator
`op53`. `op53` is `True`'s registered operator id -- the exact number
reflects internal registration order (the literal-model/sort machinery
reserves a run of ids before user-declared functions get theirs), not
anything meaningful on its own. `True` is 0-ary, so this is the whole
lookup: no children to constrain it by. After this step, `v0` = the class
containing `(True)`.

**step[1]** -- `Join target=v1 atom=1 lookups=[ByOp{op: op57}, ByChildPos{child: Local(VarId(0)), pos: 0}]`.
Binds `v1` to a node with operator `op57` (`Ite`) whose **child at position
0 is `v0`**. This is the join: rather than finding every `Ite` node and then
separately checking its first child, the scheduler picked to build the
index lookup directly keyed on `(op=Ite, child@0=v0)`, using the
`by_child_pos` index (`08-query-compilation.md`'s `ByChildPos` family) --
narrower and cheaper than enumerating all `Ite` nodes first. After this
step, `v1` = a specific `Ite` e-node whose condition child is (candidate-)
`v0`.

**step[2]** -- `CheckChildEq parent=v1 pos=0 expected=Local(VarId(0))`.
Re-verifies that `v1`'s child at position 0 really does canonicalize to
`v0`, right now. This looks redundant with step[1]'s `ByChildPos` filter,
but it isn't: the index lookup in step[1] narrows *candidates*, this step
is the actual correctness check against the *current* union-find state at
the moment this step runs. This is the shape `08-query-compilation.md`
calls out directly: "a re-join keyed on a variable no earlier step binds"
is a matcher-defect smell; here the re-check exists precisely because
step[1]'s index narrowing isn't itself proof of a live match. Skipping it
would risk exactly the silent-wrong-op failure the design doc warns about.

**step[3]** -- `ExtractChild target=v2 parent=v1 pos=1`.
Now that `v1` is a confirmed, fully-bound `Ite` node, pull its child at
position 1 (the then-arm) into `v2`. This is where the rewrite's pattern
variable `x` gets its value.

**step[4]** -- `ExtractChild target=v3 parent=v1 pos=2`.
Same thing for position 2 (the else-arm) into `v3`, binding `y`. The
rewrite's RHS is just `x`, so only `v2` actually gets used to build the
replacement -- `v3`/`y` is extracted because the pattern binds it (it's a
named position in `(Ite (True) x y)`), even though this particular rule
never reads it back. A rule whose RHS *did* use `y` would need exactly this
step; a rule that dropped `y` from the pattern entirely wouldn't generate
it.

### Confirming it actually fires

The program checks `(!= t three)` before `(union c (True))` (true: `t`'s
condition isn't known yet, so it's a fresh `Ite` node, not folded to either
arm) and `(= t three)` after `(union c (True))` and `(run 1)` -- both
checks pass. `c` becoming the same class as `(True)` is exactly what
step[0]/step[1]'s join needs to newly line up, so this rewrite becomes
matchable only once the union has happened -- reproducing, with a plain
rewrite instead of an abstract guard, the same "nothing fires until the
condition is known" shape §2's own example describes for `Clamp`.
