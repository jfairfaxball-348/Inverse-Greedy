# S008: connected n<=6 atlas with an exact cubic corona witness

**Status:** 143 connected unlabeled graphs through n=6, including
90 EGU, 7 proved non-EGU, 46 genuinely unresolved (all n=6).

| n | connected | proved EGU | proved non-EGU | unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 20 | 1 | 0 |
| 6 | 112 | 60 | 6 | 46 |
| **Total** | **143** | **90** | **7** | **46** |

## New exact positive at connected six-vertex atlas index 8

Edges, original atlas labels: 04, 15, 23, 34, 35, 45.
This is K3 with a private leaf attached to each triangle vertex:
leaves 0,1,2 and central vertices 3,4,5.

Rates: (1,1,1,beta,beta,beta), beta=cuberoot(4)-1 > 0.
Equivalently beta is the unique positive real zero of
beta^3 + 3 beta^2 + 3 beta - 3 = 0.

Four maximal independent sets and exact probabilities:

| vertices | bitmask | probability |
|---|---:|---:|
| {0,1,2} | 7 | 1/4 |
| {0,1,3} | 11 | 1/4 |
| {1,2,4} | 22 | 1/4 |
| {0,2,5} | 37 | 1/4 |

Two independent exact oracles in tests/test_s008.py: weighted
first-choice recursion and complete all-720-order priority enumeration,
both evaluated in the algebraic number field Q(cuberoot(4)).
The exact general constructive theorem appears in
proof/CLIQUE_CORONA.md.

For historical snapshots compare results/S007_ATLAS.md; the prior
false-twin theorem and all seven negative obstructions are unchanged.
Failed searches and numerical optimizer residuals are not EGU proofs
nor nonexistence theorems. No independent novelty certification.
