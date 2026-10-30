# Inverse Greedy

**Exact Uniformity and Controllability of Random Greedy Independent Sets**

Author: John Fairfax-Ball. Started 2026-10-30 (S001).

## Question

Given a finite simple graph G, assign independent Exp(lambda_v) arrival times with strictly positive rates. Scan vertices in arrival order and accept v iff it has no already accepted neighbour. The output is a maximal independent set I. Which graphs G admit rates making P_{G,lambda}(I) uniform over *all* maximal independent sets?

## First results

- IG-R1 (proved): P_G(I) = sum_{v in I} lambda_v/Lambda(V) * P_{G-N[v]}(I-v), restricting rates to the residual graph and P_empty(empty)=1.
- IG-P1 (proved): Every complete multipartite graph is uniformisable: choose equal **total** arrival rate in each part. A star K(1,m) is uniformised by giving each leaf rate 1 and its centre rate m.
- IG-P2 (proved): A disjoint union is uniformisable if and only if each component is. Probabilities factor over components.
- IG-P3 (proved): P4 is uniformised by rates (x,y,y,x) where x/y=(1+sqrt(3))/2.
- IG-N1 (proved informally): C6 is **not** uniformisable for any strictly positive rates. The product of its three opposite-pair probabilities is at most 1/729; uniformity would force product 1/125. See proof/C6_OBSTRUCTION.md.

Proved = self-contained written mathematical argument, **not** novel-priority certification or Lean verification. The C6 theorem is not yet Lean formalised. Equal-rate and variable-rate models must never be confused.

## Run

Python standard library only for exact Fraction arithmetic:

    python -m unittest discover -s tests -v
    python experiments/exact.py

Optional numerical exploration (networkx/numpy/scipy required):

    python experiments/scan_small.py --max-n 6 --starts 4

Optimizer failures are NOT proofs of nonexistence. Lean 4 and Mathlib are pinned to v4.35.0-rc3; compile with lake update, lake exe cache get, lake build. GitHub Actions status must be checked before claiming Lean success.

## Navigation

PROJECT_CHARTER.md — definitions and scope.
proof/FOUNDATIONS.md — derivations and positive constructions.
proof/C6_OBSTRUCTION.md — sharp AM-GM certificate.
CLAIMS.md — statuses and provenance.
PRIOR_ART.md — initial related literature, not a novelty audit.
ROADMAP.md, HANDOVER.md, sessions/S002.md — milestones and next task.
AGENTS.md — execution rules.

## Relationship to predecessor

The separate [Greedy Uniformity on Trees](https://github.com/jfairfaxball-348/Greedy-Uniformity-on-Trees) project (arXiv:2610.02276) proves that **equal-rate** greedy sampling is uniform on a nonempty tree only for K1 and K2. Non-equal exponential rates here change the question. The prior repository is read-only.

No licence has yet been chosen for this new repository.
