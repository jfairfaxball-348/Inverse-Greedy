# S005 connected-graph certificate atlas: n ≤ 6

Reproduce with `python experiments/census.py --max-n 6 --max-rate 4`.
The graph enumeration is exhaustive; the classification remains
**partial at order six**, not a proof from bounded rate search.

| n | Connected unlabeled | Proven EGU | Proven non-EGU | Unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 20 | 1 | 0 |
| 6 | 112 | 39 | 3 | 70 |
| **Total** | **143** | **69** | **4** | **70** |

## New positive certificates

Previously unresolved connected n=5 atlas indices
**1,4,5,6,9,11,15** all admit strictly positive rate witnesses.
Indices 1,4,5,6,9,11 have integer vectors, and index 15 has
exact Q(√3) rates. Full edge-labelled vector table and analytic
verification: `proof/FIVE_VERTEX_ATLAS.md`.
Exact tests: `tests/test_s005.py`, two independent oracles.

## Proven negatives (unchanged)

- n=5 index 2: P5 strict minor
- n=6 index 5: P6 triple-race bottleneck and TV separation
- n=6 index 18: C6 opposite-pair product bound
- n=6 index 68: K1∨P5 from join necessity

The finite integer rate search is *not* used to declare graphs
non-EGU. The connected n=6 classification still has 70 open cases.
S001–S004 frozen atlasses remain historical snapshots.
