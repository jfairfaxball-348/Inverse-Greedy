# Inverse Greedy

**Exact Uniformity and Controllability of Random Greedy Independent Sets**

Author: John Fairfax-Ball. Programme started 2026-10-30.

## Research question
For a finite simple graph G assign independent Exp(λ_v) arrival clocks
to vertices, with **strictly positive rates**. Greedily accept each
vertex when none of its already accepted neighbours exists. The output
is a maximal independent set (MIS). Which graphs permit rates making
the output exactly **uniform over all MIS**? Such graphs are called EGU.

## Current mathematical results
- **IG-R1:** exact first-choice weighted recurrence of the terminal law.
- **IG-P1:** complete multipartite graphs are EGU; a star's centre gets
  the sum of the leaf rates.
- **IG-P2:** disjoint union is EGU iff every component is EGU.
- **IG-P3:** P4 is EGU with symmetric positive algebraic rate ratio
  (1+√3)/2.
- **IG-P4 (S002):** join G∨H is EGU iff both factors are EGU.
  Rescaling factor totals by their MIS counts gives uniformity.
  Consequently **every finite cograph** (P4-free graph) has a
  constructive positive **rational-rate** witness.
- **IG-P5 (S005):** complete connected n=5 classification: 20 EGU,
  the sole non-EGU graph is P5. Consequently, among *all* simple
  graphs on at most five vertices, only P5 is non-EGU (by union
  closure). Seven new exact witnesses (six integer and one Q(√3))
  close all seven open instances.
- **IG-P6 (S006):** six-vertex connected atlas index 1 (edges
  01,12,14,15,23) is EGU with strictly positive integer rates
  (3,6,4,5,3,3); all three MIS have probability 1/3 exactly.
  An explicit positive rational one-parameter family also works.
- **IG-P7 (S007):** false-twin invariance. Contracting two
  nonadjacent vertices with identical open neighbourhoods and adding
  their exponential rates preserves the entire terminal greedy law;
  conversely split the contracted rate. This settles 19 additional
  six-vertex graphs as EGU (16 exact rational and 3 exact Q(√3)
  lifted witnesses) and 3 more as non-EGU by contraction to P5.
  See proof/FALSE_TWIN_INVARIANCE.md and tests/test_s007.py.
- **IG-N1:** C6 cannot be EGU: product of the three opposite-pair
  probabilities ≤1/729, while uniformity would require 1/125.
- **IG-N2 (S002):** P5 cannot be EGU: its four probabilities obey a
  strict minor p024*p13 > p03*p14. Since all graphs on ≤4 vertices
  are EGU, P5 is a **smallest-order obstruction**.
- **IG-N3 (S003):** P6 cannot be EGU: independent triple-race events
  produce an exact two-event bottleneck. Its output law has total
  variation distance **at least 1/25** from uniform, for all positive rates.

- **IG-N4 (S004):** the six-vertex cone over P5 (K1∨P5) is not EGU by the join theorem; it is atlas index 68.

These are self-contained informal mathematical proofs. Lean verification
and independent novelty certification must be distinguished; see
CLAIMS.md. Proofs in proof/FOUNDATIONS.md,
proof/JOIN_COGRAPHS.md, proof/P5_OBSTRUCTION.md,
proof/C6_OBSTRUCTION.md, proof/P6_OBSTRUCTION.md.

## Run experiments

Standard-library-only exact rational arithmetic:

    python -m unittest discover -s tests -v
    python experiments/exact.py

Optional NetworkX atlas enumeration:

    python -m pip install 'networkx>=3.4,<4'
    python experiments/census.py --max-n 6 --max-rate 4
    python experiments/census.py --max-n 6 --max-rate 4 --json

The **143 connected unlabeled graphs through six vertices**
currently have **89 proven positive**, **7 proven negative
(P5, P6, C6, K1∨P5, and three false-twin P5 expansions)**, and
**47 unresolved** instances. This is an
exhaustive enumeration but NOT an exhaustive classification:
a failed finite rate search or numerical optimisation does not
prove impossibility. See results/S007_ATLAS.md.

Optional numerical only:

    python -m pip install scipy numpy networkx
    python experiments/scan_small.py --max-n 6 --starts 4

## Lean
Lean 4/Mathlib are pinned. Compile using `lake exe cache get` and
`lake build` or inspect the latest GitHub Actions run.
InverseGreedy/ExponentialRace.lean formalises one pair formula identity;
InverseGreedy/CubicAMGM.lean formalises the cubic SOS inequality.
InverseGreedy/C6Product.lean **compiles the sharp six-factor bound**
(CI run #35, commit 181cda3), and P6Bottleneck.lean compiles the
P6 algebraic contradiction at the same SHA. Its quantitative TV
lemma was also verified at SHA b4e6fdd (CI run #40).
S004 adds a finite weighted-selection/ordering model, greedy output map,
first-choice normalisation and bounded output-law recurrence in
InverseGreedy/FiniteRace.lean (CI run #67 at de1b562b passed).
InverseGreedy/P6Orders.lean introduces explicit finite-order event
predicates and worked examples (verified in CI #75 at 030fc3aa);
the all-720-orders Lean proof is
still open, though the exhaustive Python check passed in S003. Check CLAIMS.md and the exact CI SHA
for whether the imported module compiled.
S005 formally proves positivity of individual finite order masses
(CI #82 at commit 62916d4). S006 adds a structural Lean proof of
**total head-choice tree mass = 1** for positive rates, verified in green CI #92 at commit 95314a7 (see CLAIMS.md); this is not yet
the theorem equating the tree leaves with the original `orderMass`
of permutations or their pushforward law.
S007 adds OrderLeafBridge.lean, identifying each duplicate-free
priority leaf's product of first-choice probabilities with
`orderMass` (Lean-verified at SHA 543cfe9, green CI run 41131451454); the full
permutation summation and greedy pushforward are still open.
**An equivalence to independent exponential clocks and the P6/C6
symbolic event-law formulas have NOT been formalised end-to-end in Lean.** Never report more than the
specific build SHA proves.

## Navigation
proof/FALSE_TWIN_INVARIANCE.md — S007 structural closure and obstructions;
results/S007_ATLAS.md — new 89/7/47 partial census;
proof/FIVE_VERTEX_ATLAS.md — full n=5 theorem;
proof/SIX_VERTEX_INDEX1.md and results/S006_ATLAS.md — new n=6 witness;
CLAIMS.md — rigorous status ledger;
AGENTS.md — execution and honesty rules;
HANDOVER.md and ROADMAP.md — progress/next work;
sessions/S008.md — installed next session;
PRIOR_ART.md — preliminary literature, not priority certificate.

The separate [Greedy Uniformity on Trees](https://github.com/jfairfaxball-348/Greedy-Uniformity-on-Trees)
(arXiv:2610.02276) is the **equal-rate** predecessor, read-only.
No Inverse Greedy arXiv publication or Palomar registration is claimed.
