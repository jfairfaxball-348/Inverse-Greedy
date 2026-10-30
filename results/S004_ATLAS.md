# S004 connected-graph atlas: n ≤ 6

Reproducible command (requires NetworkX):
`python experiments/census.py --max-n 6 --max-rate 4`.
The graph enumeration is exhaustive; the positive-real-rate EGU
classification is intentionally incomplete.

| n | Connected unlabeled | Certified EGU | Certified not EGU | Unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 13 | 1 | 7 |
| 6 | 112 | 39 | 3 | 70 |
| **Total** | **143** | **62** | **4** | **77** |

Certified negative cases (indices within connected graphs at each order):

- n=5 index 2: P5, strict output-probability minor (IG-N2)
- n=6 index 5: P6, disjoint triple races, TV ≥ 2√(2/5)−6/5
  (strengthened in S004; older certified 1/25 bound remains valid) (IG-N3)
- n=6 index 18: C6, three opposite-pair product inequality (IG-N1)
- **n=6 index 68: cone K1∨P5**, join necessity plus IG-N2 (IG-N4)

Proof of the new negative: `proof/CONE_P5_OBSTRUCTION.md`.
Exact test: `tests/test_s004.py`, 729 positive rate vectors
and selected independent weighted-permutation oracles.

All 62 positives still have constructive cograph rate choices,
exact positive rational-rate certificates or the P4 algebraic
construction. The finite rate search uses integer coordinates
1..4 (with final coordinate 1); failure to find a rate vector
is never a negative certificate.

The S003 frozen historical atlas is preserved at
`results/S003_ATLAS.md`. This is a partial certificate atlas,
not a classification of all 143 connected graphs.
