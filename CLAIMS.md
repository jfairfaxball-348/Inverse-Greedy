# Claim ledger — S002 (2026-10-30)

Status meanings: **proved-informal** is a written proof (not Lean or novelty);
**tested-exact** refers to finite inputs only; **Lean-verified** means
actual successful CI on the commit; **open** means not established.

| ID | Claim | Status | Evidence |
|---|---|---|---|
| IG-R1 | Weighted first-choice law | proved-informal, tested-exact | proof/FOUNDATIONS.md |
| IG-P1 | Complete multipartite graphs EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P2 | Disjoint union EGU iff every component EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P3 | P4 EGU with positive algebraic rates | proved-informal | proof/FOUNDATIONS.md |
| **IG-P4** | **Join G∨H EGU iff both EGU; every cograph EGU with positive rational rates** | **proved-informal; tested-exact on all cographs n≤6** | proof/JOIN_COGRAPHS.md; experiments/cograph.py |
| IG-N1 | C6 opposite-pair product ≤1/729; not EGU | proved-informal, tested-exact | proof/C6_OBSTRUCTION.md |
| **IG-N2** | **P5 has strict output minor p024*p13 > p03*p14; not EGU; smallest order obstruction** | **proved-informal; exact tests at 243 rate tuples** | proof/P5_OBSTRUCTION.md |
| IG-L1 | C6 pair algebra identity | Lean-verified S001 | InverseGreedy/ExponentialRace.lean |
| IG-L2 | Cubic three-term AM-GM SOS | Lean-verified S002 (PR CI run #9, SHA 59b05ba) | InverseGreedy/CubicAMGM.lean |
| IG-L3 | C6 six-factor algebraic inequality and 1/5 contradiction | **pending latest CI**; *not* full stochastic model | InverseGreedy/C6Product.lean |
| IG-A2 | Enumerate 143 connected graphs n≤6: 62 positive certificates, 2 proved negative, 79 open | exact partial census, **not complete classification** | results/S002_ATLAS.md |
| IG-O1 | Characterise all EGU graphs | open | ROADMAP.md |
| IG-O2 | Certify remaining 79 atlas cases | open | ROADMAP.md |
| IG-O3 | Full Lean connection from exponential race to rational MIS event law | open | ROADMAP.md |
| IG-O4 | Independently verified originality | open | PRIOR_ART.md |

P5 and C6 obstructions apply also to graphs with those as **connected
components**, not merely induced subgraphs. No arXiv publication,
Palomar registration or priority certificate is claimed for S002.
