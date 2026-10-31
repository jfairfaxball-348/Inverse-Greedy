# S009 handover — 2026-10-31

## Release and verification

**S009 PR #8 merged successfully** on 2026-10-31:
https://github.com/jfairfaxball-348/Inverse-Greedy/pull/8

The exact final PR head was `ed0d02d4c6d7819ac51adf86b4da9957ae342a65`.
Both the **Python exact** and imported **Lean** jobs passed at this
same SHA in BOTH GitHub Actions runs:

- Push run **41188364427**: success.
- Pull-request run **41188368166**: success.

Squash merge commit: `956961822b2a758f39de9c555283895845f478b2`.
This post-merge documentation release records verified results; earlier
intermediate CI failures (stale historical snapshots and a trivial Lean
add-zero simplification) were corrected before final green tests.
S006/S007 historical snapshot tests use `include_s009=False`.

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

An additional IG-N6 theorem constructs positive rate vectors with
TV(t) < m/((2^m+1)^2*t), proving uniformity is approachable but
**never attained** for every m>=2. This accounts for apparent
optimizer boundary convergence, not a positive witness.

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
