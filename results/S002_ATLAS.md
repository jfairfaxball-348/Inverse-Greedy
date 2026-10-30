# S002: Certified partial graph atlas (through six vertices)

**Scope:** Exhaustive enumeration of connected *unlabeled* graphs
in NetworkX graph_atlas_g() at each order n=1,...,6. Each graph
receives a checked certificate where available, otherwise a
deliberate 'unresolved' label, never an impossibility inference.

Command: `python experiments/census.py --max-n 6 --max-rate 4`
(optional dependency: networkx). JSON including each graph edge list,
atlas index, actual rational-rate vector and proof source is available
with `--json`. Uses exact Fraction recursion; no floating point.

| n | Connected graphs | Proved positive | Proved negative | Unresolved |
|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 13 | 1 | 7 |
| 6 | 112 | 39 | 1 | 72 |
| **Total** | **143** | **61** | **2** | **79** |

Positive certificates are:
- all cographs, by the constructive disjoint-union/join theorem;
- additional exact rational witnesses searched on vectors
  (r_0,...,r_(n-2),1), with r_i integer in [1,4];
- P4 by the separately proved positive algebraic witness.

Negative certificates are only **P5 (atlas index 2 at n=5)**
and **C6 (atlas index 18 at n=6)**. These indices refer to
the *connected subset* of graph_atlas_g(), not global atlas IDs.

This is an exhaustive **enumeration**, NOT an exhaustive
semialgebraic **classification**. The 79 unresolved instances
may be positive or negative. Numerical least-squares failures,
including the P6 lead, remain noncertifying.

Independent internal checks: cograph witnesses have precisely
the expected number of maximal independent sets and equal exact
Fraction probabilities; P5 strict identity was tested at all
243 rates from [1,3]^5. Additional independent permutation-oracle
checks appear in tests/test_exact.py.

The certificate search is bounded and intentionally incomplete.
Exact algebraic witness detection beyond P4, or a fully general
real-closed-field decision procedure, is future work.
