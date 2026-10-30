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
- **IG-N1:** C6 cannot be EGU: product of the three opposite-pair
  probabilities ≤1/729, while uniformity would require 1/125.
- **IG-N2 (S002):** P5 cannot be EGU: its four probabilities obey a
  strict minor p024*p13 > p03*p14. Since all graphs on ≤4 vertices
  are EGU, P5 is a **smallest-order obstruction**.
- **IG-N3 (S003):** P6 cannot be EGU: independent triple-race events
  produce an exact two-event bottleneck. Its output law has total
  variation distance **at least 1/25** from uniform, for all positive rates.

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
currently have **62 proven positive**, **3 proven negative
(P5, P6 and C6)**, and **78 unresolved** instances. This is an
exhaustive enumeration but NOT an exhaustive classification:
a failed finite rate search or numerical optimisation does not
prove impossibility. See results/S003_ATLAS.md.

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
lemma is a later addition subject to its own CI verification.
**The stochastic greedy law and event-to-rational formulas have NOT
been formalised end-to-end in Lean.** Never report more than the
specific build SHA proves.

## Navigation
CLAIMS.md — rigorous status ledger;
AGENTS.md — execution and honesty rules;
HANDOVER.md and ROADMAP.md — progress/next work;
sessions/S004.md — installed next session;
PRIOR_ART.md — preliminary literature, not priority certificate.

The separate [Greedy Uniformity on Trees](https://github.com/jfairfaxball-348/Greedy-Uniformity-on-Trees)
(arXiv:2610.02276) is the **equal-rate** predecessor, read-only.
No Inverse Greedy arXiv publication or Palomar registration is claimed.
