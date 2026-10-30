# S006 handover — 2026-10-30

## Repository
S005 PR #4 was merged into main at `e9577bfe6065ea061c28295d9d3182847c75e4f7`
after final-head green CI run #87. S006 PR #5 adds the work described below.
Check its final-head GitHub Actions runs and branch SHA before merging.

## Exact mathematical progress
**IG-P6:** Connected graph-atlas n=6 index 1 has edges
`01,12,14,15,23`, and positive integer uniformising rates
`(3,6,4,5,3,3)`. Its three MIS each have probability **1/3**
under both the independent 720-permutation oracle and the exact
first-choice recurrence. A one-parameter strictly positive rational
family also follows from the closed formulas. See
`proof/SIX_VERTEX_INDEX1.md`, `experiments/six_vertex_witnesses.py`
and `tests/test_s006.py`.

Connected n≤6 atlas: **143 total / 70 positive / 4 negative /
69 unresolved**. All unresolved instances have six vertices.
The six-vertex classification is NOT finished; finite search failure
cannot be classified as non-EGU.

## Lean proof and scope
`InverseGreedy/OrderTreeNormalization.lean` proves, via induction on
fuel and deleting the first chosen vertex, that the total mass of
the complete recursive weighted head-choice tree is exactly one
when all rates are positive and fuel ≥ number of active vertices.
There is no factorial-size `decide`; it reuses the previously
formalised first-choice probability normalisation.

**Scope limitation:** The proof normalises a recursively defined
tree mass, not literally the sum of the existing `orderMass` over
`List.permutations`. Identifying every leaf with its corresponding
`orderMass`, grouping leaves by `greedyOutput` to obtain
`finiteRaceLaw`, and identifying the finite tree with independent
continuous Exp clocks remain open. Never imply otherwise.

**Lean CI verification is pending until the final PR SHA passes.**
Do not label IG-L9 Lean-verified before that.

## Next
`sessions/S007.md` targets a genuine leaf-by-leaf Lean permutation
identity and the greedy pushforward law, with additional exact
six-vertex certificates and remaining Exponential-clock obligations.
Keep the equal-rate predecessor read-only. No independent novelty
or priority claim is made.
