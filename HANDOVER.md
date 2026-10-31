# S009 handover — 2026-10-31

## Release and verification

S009 working PR: https://github.com/jfairfaxball-348/Inverse-Greedy/pull/8.
The mathematical proof and exact test suite were committed on branch
`research/s009-corona-p3`; only a **green exact-head CI** authorises
labelling the imported Lean theorem verified. The first push at
`4d17c52` passed the Lean job but failed Python historical snapshots,
not the new theorem tests. The S006/S007 regression snapshots were
repaired via `include_s009=False`. Record final exact-head green
CI and merge SHA separately after checks.

## New mathematical obstruction — IG-N5

For every m>=2 the star-corona K_(1,m) with one private leaf per
vertex is NON-EGU under all strictly positive asymmetric exponential
rates. Condition on independent pair-winning indicators X_i; if
the hub is not selected, spoke subset S has output probability
q_S = product(x_i or 1-x_i) * (B+sum_{i in S}u_i)/
(b+B+sum_{i in S}u_i). A strict two-spoke minor
q_{S+i}q_{S+j} > q_S q_{S+i+j} precludes all probabilities equal.
Proof: proof/STAR_CORONA_OBSTRUCTION.md, with the detailed m=2
instance in proof/CORONA_P3_OBSTRUCTION.md.

The connected six-vertex atlas index 3 (corona(P3)) is thereby
proved negative for ALL positive rates. Partial connected atlas
n<=6: **90 EGU, 8 non-EGU, 45 unresolved** (all open n=6).

Tests exercise 729 rate vectors exactly, the all-720 order oracle,
and star-corona closed forms m=2,3,4.

## Lean scope

CoronaP3Minor.lean contains only the **algebraic** strict factorisation,
not the probability-law derivation. The finite full-permutation sum
normalisation, greedyOutput pushforward to finiteRaceLaw and
independent continuous Exponential-clock equivalence remain OPEN.
S008 support and S007 leaf mass identities remain separate.

## Next

sessions/S010.md. Prove structural List.permutations decomposition,
then normalisation, then deletion-consistent greedy pushforward in Lean.
Only after that bridge attempt continuous exponential measures.
Search other six-vertex families using exact rate certificates and
all-positive impossibility inequalities. Never use near-zero
boundary optimizer residuals as exact witnesses.

No independent novelty certification, arXiv or Palomar submission.
