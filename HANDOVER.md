# S008 handover — 2026-10-31

## Release status

**S008 PR #7 merged successfully** on 2026-10-31:
https://github.com/jfairfaxball-348/Inverse-Greedy/pull/7
The final PR head was `ff29b0bb1dcd0f5e93d837108375874aa86384a3`.
BOTH Python exact and imported Lean jobs passed at this exact SHA:
- Push CI run **41183416574**: success.
- Pull-request CI run **41183420188**: success.
The squash merge commit was
`eda6d0bbb6cbfc5a5618ae3e38a863624fa86936`.
This post-merge documentation-only update records the verified release.

## New mathematics — IG-P8

For every m >= 1, K_m with one private leaf per clique vertex is EGU.
Give each leaf rate 1 and each central clique vertex positive rate
beta=(m+1)^(1/m)-1. Exactly m+1 maximal independent sets exist.
All leaves are selected precisely when every leaf arrives before its
partner centre. This has probability (1+beta)^(-m)=1/(m+1), from
independent exponential races on disjoint leaf-centre pairs. The m
other MIS are equally likely by permutation symmetry of all pairs,
so each has probability 1/(m+1). Complete proof:
proof/CLIQUE_CORONA.md.

Connected n=6 atlas index 8, edges 04,15,23,34,35,45, is this graph
for m=3. Strictly positive rates are (1,1,1,cuberoot(4)-1,
cuberoot(4)-1,cuberoot(4)-1); all four MIS have probability 1/4.
Python independently checks exact Q(cuberoot(4)) recursion and all
720 weighted permutations, not floating point. m=2 also recovers P4.

## Current partial atlas

143 connected graphs through n=6: 90 exact positives, 7 proved
negatives, 46 unresolved, all unresolved n=6. S006 and S007 regression
snapshots remain available via include_s008=False (and the historical
include_false_twins=False when applicable). Unknown does not imply no
strictly positive solution.

## Lean boundary

New FullPermutationSupport.lean connects actual Mathlib
List.permutations membership with duplicate-free complete vertex
lists, and applies S007 leaf-level mass identity to those lists.
This is only a support theorem; normalisation of the full summed
permutation law, grouping by greedyOutput to finiteRaceLaw, and
independent exponential clocks remain open. Report verification only
for the particular exact CI SHA that passed.

## Next

sessions/S009.md. Focus first on full finite permutation normalisation
and pushforward by a deletion-consistency / rejected-vertex coupling.
Numerical scans of 47 S007-open graphs were exploratory only; some
near-zero optimizer residuals occur at rates approaching zero or
infinity and provide no positive exact certificate or impossibility.
In particular atlas index 3 (corona P3) remains open.

Do not assert novelty, an arXiv submission, or a complete classification.
