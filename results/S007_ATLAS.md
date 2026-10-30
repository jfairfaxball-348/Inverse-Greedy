# S007: connected n<=6 atlas after false-twin invariance

**Status:** 143 connected unlabeled graphs through order six; 89 EGU,
7 non-EGU, 47 genuinely unresolved (all with six vertices).

| n | connected | proved EGU | proved non-EGU | unresolved |
|--:|--:|--:|--:|--:|
| 1 | 1 | 1 | 0 | 0 |
| 2 | 1 | 1 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 |
| 4 | 6 | 6 | 0 | 0 |
| 5 | 21 | 20 | 1 | 0 |
| 6 | 112 | 59 | 6 | 47 |
| **Total** | **143** | **89** | **7** | **47** |

The theorem `proof/FALSE_TWIN_INVARIANCE.md` proves that contracting
two **nonadjacent vertices with equal open neighbourhoods** preserves
the entire weighted terminal-law distribution after adding their rates.
Deleting one twin maps MIS bijectively; conversely split its parent
rate equally. This is an exact general theorem, not a six-vertex
search heuristic. The complete S005 n=5 theorem therefore yields
positive or negative results, as appropriate.

Each index is relative to the **connected six-vertex graphs** in
NetworkX `graph_atlas_g()` order; edge pairs retain original vertex
labels (for example `01` means edge 0--1). Twin pairs and the
corresponding n=5 atlas index are recorded in the main proof.
Graph structure is rechecked by the test suite before classification.

| n=6 index | contracted n=5 index | original graph edges | outcome |
|---:|---:|---|:---|
| 2 | 1 | `01,02,03,34,35` | EGU |
| 4 | 2 | `04,05,13,23,34` | non-EGU |
| 7 | 4 | `03,04,14,24,34,35` | EGU |
| 10 | 1 | `02,03,04,05,12,13` | EGU |
| 13 | 2 | `02,13,24,25,34,35` | non-EGU |
| 14 | 5 | `01,02,03,34,35,45` | EGU |
| 16 | 2 | `04,05,13,14,23,24` | non-EGU |
| 27 | 5 | `04,05,13,14,23,24,34` | EGU |
| 28 | 6 | `02,12,14,23,25,34,45` | EGU |
| 32 | 1 | `02,12,13,14,25,35,45` | EGU |
| 33 | 5 | `02,05,13,14,23,34,35` | EGU |
| 43 | 9 | `01,02,04,12,13,15,23,25` | EGU |
| 45 | 4 | `01,02,03,04,13,15,23,25` | EGU |
| 48 | 5 | `01,02,04,13,15,23,25,35` | EGU |
| 54 | 11 | `01,03,04,05,12,23,25,34` | EGU |
| 59 | 6 | `01,05,12,14,23,25,34,45` | EGU |
| 63 | 9 | `02,12,13,14,23,25,34,35,45` | EGU |
| 66 | 15 | `01,02,03,04,05,12,23,25,34` | EGU |
| 72 | 9 | `02,03,05,12,13,23,24,34,45` | EGU |
| 77 | 11 | `01,03,05,12,23,24,25,34,45` | EGU |
| 85 | 15 | `02,03,05,12,13,23,24,25,34,45` | EGU |
| 101 | 15 | `01,02,04,05,14,15,23,24,25,34,35` | EGU |

Of the 19 newly positive graphs, 16 have explicit lifted
**rational** rates and 3 (indices 66,85,101) have explicit lifted
**Q(sqrt(3))** rates, derived from the S005 witnesses. Every new
positive is independently checked by the exact 720-permutation oracle
and the independent first-choice recursion in tests/test_s007.py.

The new non-EGU indices 4,13,16 contract specifically to P5. This
uses a universal strict impossibility argument; **failed bounded
integer searches have not been interpreted as counterexamples**.

Reproduce via:
```
python -m unittest discover -s tests -v
python experiments/census.py --max-n 6 --max-rate 4
```

No all-graph classification, continuous-clock Lean theorem or
independent novelty/priority certification is asserted.
