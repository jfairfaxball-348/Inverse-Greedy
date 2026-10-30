# S001 claim ledger (2026-10-30)

Status definitions: **proved-informal** = self-contained written proof, not formalised or necessarily new; **tested-exact** = verified on stated finite inputs only; **Lean-target** = not yet Lean checked; **open** = not proved.

| ID | Claim | Status | Evidence |
|---|---|---|---|
| IG-R1 | Weighted first-arrival recurrence | proved-informal, tested-exact | proof/FOUNDATIONS.md; experiments/exact.py; independent permutation-oracle tests |
| IG-P1 | Complete multipartite graphs uniformisable; stars included | proved-informal, tested-exact on examples | proof/FOUNDATIONS.md |
| IG-P2 | Disjoint-union factorisation and EGU iff components EGU | proved-informal, tested-exact on example | proof/FOUNDATIONS.md |
| IG-P3 | P4 uniformisable with positive algebraic rates | proved-informal | proof/FOUNDATIONS.md |
| IG-N1 | C6 p1*p2*p3 <= 1/729 and is not EGU | proved-informal; tested-exact examples; Lean-target | proof/C6_OBSTRUCTION.md |
| IG-L1 | Lean algebraic C6 pair identity | source drafted; CI verification pending | InverseGreedy/ExponentialRace.lean |
| IG-O1 | Structural classification of EGU graphs | open | ROADMAP.md |
| IG-O2 | Certified small graph feasibility atlas | open | ROADMAP.md |
| IG-O3 | Full Lean formalisation of C6 obstruction | open | ROADMAP.md |
| IG-O4 | Novelty and publication-priority audit | open | PRIOR_ART.md |

No Palomar registration, arXiv publication, peer-review result, or completed Lean formal theorem is claimed for Inverse Greedy.
