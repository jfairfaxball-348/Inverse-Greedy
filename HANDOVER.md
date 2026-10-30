# S004 handover — 2026-10-30

## New certified negative: IG-N4
The connected six-vertex graph K1∨P5 (cone over P5) is not EGU.
It is connected n=6 atlas index 68. The proof is a direct
corollary of IG-P4 (join necessity) and IG-N2 (P5 strict minor).
For any five path rates with sum A and universal vertex rate c,
the cone output law has p({z})=c/(A+c) and p(I)=A/(A+c)*p_P5(I).
The common factor on P5 output events is strictly positive and
preserves the strict P5 probability minor. This is a mathematical
proof for all positive rates, not numerical nonexistence evidence.
See proof/CONE_P5_OBSTRUCTION.md.

## Partial atlas
Connected n≤6: **143 graphs = 62 certified positive / 4 certified
negative / 77 unresolved**. One more case closed than S003.
No change to the 62 positive classifications. n5 still 13/1/7;
n6 now 39/3/70. New classification appears in
experiments/census.py and results/S004_ATLAS.md.

## Formal finite law work
New InverseGreedy/FiniteRace.lean defines normalisation
`activeRate`, `firstChoice`, sequential `orderMass`,
`greedyOutput`, `afterChoice`, and fuel-bounded
`finiteRaceLaw`. It states and proves rate positivity,
first-choice total mass one, and first-choice unfolding of the
bounded output law. **Verify this module's CI status at the merged
SHA before stating it is Lean-verified.**

Important boundary: these objects are finite algebraic
combinatorial models. No Lean theorem yet identifies them with
independent continuous Exp clocks, or proves the P6/C6 named-event
law identities from `greedyOutput`. The paper-level proofs
remain valid; do not conflate formal gaps with mathematical gaps.

## Regressions
tests/test_s004.py verifies K1∨P5 at atlas index 68,
all 729 rates from {1,2,3}^6 for the exact join factorisation
and strict inherited P5 minor, and two weighted-permutation oracle
comparisons. Full project Python tests and atlas run in GitHub CI.

## Next
sessions/S005.md. Close the weighted-order → greedy-output
recursion theorem in Lean, then P6 combinatorial events,
independence and quantitative TV; tackle remaining n=5 cases
with genuine exact certificates. Do not reclassify graphs using
optimiser failure; no new novelty/priority assertion.
