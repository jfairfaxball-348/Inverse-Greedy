# S009: connected n<=6 partial atlas after star-corona obstruction

**143** connected unlabeled graphs of order 1 through 6:
**90 certified EGU**, **8 proved non-EGU**, **45 unresolved** (all n=6).

| n | connected | EGU | non-EGU | unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 20 | 1 | 0 |
| 6 | 112 | 60 | 7 | 45 |
| **Total** | **143** | **90** | **8** | **45** |

**New certified negative: connected n=6 index 3.**
Original NetworkX graph-atlas edges: 01,12,13,24,35.
This graph is corona(P3), equivalently the star corona K_(1,2).
For *every strictly positive real vector* the four spoke-selection
output probabilities satisfy the universal strict determinant
p_a*p_c > p_empty*p_ac. Equal probability over the graph's five MIS
would make the determinant zero. The proof is universal and analytical:
proof/CORONA_P3_OBSTRUCTION.md.

This is the order-six base case of an infinite family, all pendant
star coronas K_(1,m) for m>=2: proof/STAR_CORONA_OBSTRUCTION.md.
Exact tests: 729 first-choice rational vectors, independent complete
permutation law, higher-star recursions (m=3,4).

S008 index 8 remains EGU with cubic algebraic rates.
S006/S007 historical snapshots are preserved via
include_s009=False; all previously certified results remain intact.

**Unresolved is not non-EGU.** No exhaustive n=6 classification,
independent novelty certification or continuous-clock Lean law claimed.
