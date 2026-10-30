# S005 handover — 2026-10-30

## Breakthrough: connected n=5 is fully classified

**IG-P5:** exactly 20 of the 21 connected unlabeled graphs on five
vertices are EGU; P5 is the unique non-EGU instance. The seven
previously open n=5 atlas indices 1,4,5,6,9,11,15 all have exact,
strictly positive uniformising rates. Six witnesses are integer
vectors, and index 15 has rates in Q(√3); the latter's four
probabilities are proved by explicit quadratic identities.

Proof: proof/FIVE_VERTEX_ATLAS.md. Reproducible rates and exact
recurrence + independent order-mass oracles:
experiments/five_vertex_witnesses.py, tests/test_s005.py.

Updated n≤6 atlas: **143 = 69 proven positive, 4 proven negative,
70 unresolved**. Every unresolved case is connected on six vertices.
Historical S004 snapshot is unchanged. This is NOT a general
characterisation of all EGU graphs.

## Lean progress and remaining gap

S005 added InverseGreedy/OrderMassBridge.lean, proving strict
positivity of an individual finite priority-order mass and a
first-choice atom, provided all rates are positive. The S004 algebraic
finite race law remains. These local lemmas are not a normalisation
over the permutation space, not the grouping-by-greedy-output theorem,
and not a probability-law equivalence with independent Exp clocks.
The required bridges remain the top S006 priority. Only mark the new
module Lean-verified after exact CI result is checked.

## Verification

The GitHub Actions Python exact job on S005 head 62916d4 passed,
including the complete five-vertex witness tests and connected
n≤6 partial atlas. The Lean job and final PR check must be inspected
separately on the final head SHA before declaring success.

## Next

sessions/S006.md: structural permutation decomposition, greedy
terminal-law identity and continuous Exp clock theorem; extend
exact certification among 70 remaining n=6 candidates.
No novelty/priority certification. Equal-rate predecessor read-only.
