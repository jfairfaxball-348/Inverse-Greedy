# Claim ledger — S002 (2026-10-30)

Status meanings: **proved-informal** is a complete written proof, not machine-checked or independently novel; **tested-exact** is finite arithmetic checking; **Lean-verified** requires actual successful CI at the stated SHA; **open** means unestablished.

| ID | Claim | Status | Evidence |
|---|---|---|---|
| IG-R1 | Weighted first-choice probability law | proved-informal, tested-exact | proof/FOUNDATIONS.md; experiments/exact.py |
| IG-P1 | Complete multipartite graphs EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P2 | Disjoint union EGU iff each component EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P3 | P4 EGU with positive algebraic rates | proved-informal | proof/FOUNDATIONS.md |
| **IG-P4** | Join G∨H EGU iff both EGU; every finite cograph EGU with positive rational rates | **proved-informal; tested-exact for n≤6** | proof/JOIN_COGRAPHS.md; experiments/cograph.py |
| IG-N1 | C6 opposite-pair product ≤1/729; not EGU | proved-informal, tested-exact | proof/C6_OBSTRUCTION.md |
| **IG-N2** | **P5 strict output minor p024*p13 > p03*p14; not EGU; smallest-order obstruction** | **proved-informal; exact tests on 243 rate vectors** | proof/P5_OBSTRUCTION.md |
| IG-L1 | C6 pair formula algebraic identity | Lean-verified S001 | InverseGreedy/ExponentialRace.lean |
| IG-L2 | Cubic AM-GM sum-of-squares lemma | Lean-verified S002 on PR run #9, SHA 59b05ba | InverseGreedy/CubicAMGM.lean |
| IG-L3 | C6 six-denominator algebraic inequality and 1/5 contradiction | **UNVERIFIED draft**, excluded from compiled library after CI timeouts; S003 target | InverseGreedy/C6Product.lean |
| IG-A2 | Exact partial connected graph atlas n≤6: 143 total, 62 positive, 2 negative, 79 unresolved | partial finite certificates, not complete classification | results/S002_ATLAS.md |
| IG-O1 | Characterise all EGU graphs | open | ROADMAP.md |
| IG-O2 | Certify 79 unresolved atlas cases | open | ROADMAP.md |
| IG-O3 | Full Lean exponential race to event-law proof | open | ROADMAP.md |
| IG-O4 | Independently certified novelty | open | PRIOR_ART.md |

Obstructions P5/C6 apply to graphs with such connected **components**, not arbitrary induced copies in connected supergraphs. No arXiv publication, Palomar registration or priority claim for S002.
