# S002 exact partial atlas: connected unlabeled graphs through six vertices

Reproduce (optional NetworkX):
`python experiments/census.py --max-n 6 --max-rate 4`.
Add `--json` to obtain each instance's edges, atlas index, outcome
count and constructive witness/proof source. All reported positive
rational witnesses were checked by exact Fraction recurrence.

| n | Connected | Proved EGU | Proved not EGU | Unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 13 | 1 | 7 |
| 6 | 112 | 39 | 1 | 72 |
| **Total** | **143** | **62** | **2** | **79** |

Positive proof sources: all cographs by union/join construction;
additional exact rational rates of the form
(r0,...,r[n-2],1), with each other r_i ∈ {1,2,3,4};
P4 via a written algebraic irrational witness.

Negative graph instances only: P5 (index **2** at n5,
proof/P5_OBSTRUCTION.md), C6 (index **18** at n6,
proof/C6_OBSTRUCTION.md). Indices are within the *connected subset*
of NetworkX graph_atlas_g() for each n, not full global atlas indices.

**This is an exhaustive graph enumeration, NOT a complete
uniformisability classification.** All 79 unresolved graphs might
be positive or negative. A failed bounded integer search or
numerical least-squares fit is NOT a nonexistence proof.
P6 remains a lead only. S003 will target exact algebraic and
infeasibility certificates for further cases.
