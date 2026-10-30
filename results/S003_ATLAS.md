# S003 connected-graph atlas: n ≤ 6

Command (NetworkX optional): `python experiments/census.py --max-n 6 --max-rate 4`.
Python CI run #32 on S003 commit c6460366 successfully reran exact tests,
the weighted-permutation oracle and this complete six-vertex census.

| n | Connected unlabeled | Certified EGU | Certified not EGU | Unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 13 | 1 | 7 |
| 6 | 112 | 39 | 2 | 71 |
| **Total** | **143** | **62** | **3** | **78** |

Negative cases and within-connected-order NetworkX atlas indices:

- n=5 index 2: P5 (strict probability minor, proof/P5_OBSTRUCTION.md).
- n=6 index 5: P6 (exact two-block event + TV ≥1/25,
  proof/P6_OBSTRUCTION.md).
- n=6 index 18: C6 (sharp opposite-pair product ≤1/729,
  proof/C6_OBSTRUCTION.md).

All positive witnesses are either cograph rational constructions,
finite *exact* rational-rate certificates checked by Fraction recursion,
or the P4 algebraic witness. Exhaustive *graph enumeration* is not
complete EGU *classification*: all 78 unresolved cases remain open.
Rate search limited to integers 1..4 (last coordinate 1), with no
asserted exhaustive positive-real implications.

The P6 negative certificate is not inherited by arbitrary induced-P6
supergraphs. Each listed obstruction propagates to graphs having it
as a connected component by IG-P2.
