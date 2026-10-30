# S006 connected-graph certificate atlas: n ≤ 6

Reproduce with `python experiments/census.py --max-n 6 --max-rate 4`.
This is a **partial classification**: only positive exact witnesses and
mathematical obstructions are counted as proved. Numerical search
failures never certify nonexistence.

| n | Connected unlabeled | Proven EGU | Proven non-EGU | Unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 20 | 1 | 0 |
| 6 | 112 | 40 | 3 | 69 |
| **Total** | **143** | **70** | **4** | **69** |

New exact positive n=6 certificate: **connected index 1** (edges
`01,12,14,15,23`), with positive integer rates `(3,6,4,5,3,3)`.
Its three maximal independent sets have probability exactly 1/3.
Independent complete priority enumeration agrees for all 720 orders.
See `proof/SIX_VERTEX_INDEX1.md` for formulas and a positive rational
one-parameter family, and `tests/test_s006.py` for verification.

All n=5 connected cases were settled in S005 (20 positive, only
P5 negative), and S001–S005 snapshots remain frozen.

Negative atlas indices: n=5 index 2 (P5); n=6 indices 5 (P6),
18 (C6), and 68 (K1∨P5). These have mathematical obstructions,
not merely failed integer or floating-point searches.
All 69 open cases are connected six-vertex graphs.
