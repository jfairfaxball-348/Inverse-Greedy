# Claim ledger — S005 (2026-10-30)

Status meanings: **proved-informal** is a complete written proof, not machine-checked or independently novel; **tested-exact** is finite arithmetic checking; **Lean-verified** requires actual successful CI at the stated SHA; **open** means unestablished.

| ID | Claim | Status | Evidence |
|---|---|---|---|
| IG-R1 | Weighted first-choice probability law | proved-informal, tested-exact | proof/FOUNDATIONS.md; experiments/exact.py |
| IG-P1 | Complete multipartite graphs EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P2 | Disjoint union EGU iff each component EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P3 | P4 EGU with positive algebraic rates | proved-informal | proof/FOUNDATIONS.md |
| **IG-P4** | Join G∨H EGU iff both EGU; every finite cograph EGU with positive rational rates | **proved-informal; tested-exact for n≤6** | proof/JOIN_COGRAPHS.md; experiments/cograph.py |
| **IG-P5** | All connected graphs n≤5 classified: n=5 20 EGU / P5 unique non-EGU; seven new rate witnesses | **proved-informal; tested-exact** | proof/FIVE_VERTEX_ATLAS.md; tests/test_s005.py; exact Q(√3) algebra |
| IG-N1 | C6 opposite-pair product ≤1/729; not EGU | proved-informal, tested-exact | proof/C6_OBSTRUCTION.md |
| **IG-N2** | **P5 strict output minor p024*p13 > p03*p14; not EGU; smallest-order obstruction** | **proved-informal; exact tests on 243 rate vectors** | proof/P5_OBSTRUCTION.md |
| **IG-N3b** | P6 TV separation ≥ 2√(2/5)−6/5 ≈ 0.064911, strictly stronger than 1/25 | **proved-informal, not Lean-verified** | proof/P6_TV_SHARPENING.md; disjoint-event deficit argument |
| **IG-N4** | K1∨P5 (cone over P5) cannot be EGU; six-vertex atlas index 68 | **proved-informal; tested-exact on 729 rate vectors** | proof/CONE_P5_OBSTRUCTION.md; tests/test_s004.py; inherited from IG-N2 + IG-P4 |
| IG-L1 | C6 pair formula algebraic identity | Lean-verified S001 | InverseGreedy/ExponentialRace.lean |
| IG-L2 | Cubic AM-GM sum-of-squares lemma | Lean-verified S002 on PR run #9, SHA 59b05ba | InverseGreedy/CubicAMGM.lean |
| IG-L3 | C6 six-denominator inequality and 1/5 contradiction (pure algebra, not race semantics) | **Lean-verified** at commit 181cda3, GitHub CI run #35 | InverseGreedy/C6Product.lean |
| IG-L4 | P6 bottleneck algebraic contradiction | **Lean-verified** at commit 181cda3, CI run #35 | InverseGreedy/P6Bottleneck.lean |
| IG-L5 | P6 algebraic quantitative 1/25 gap (conditional on two race-event bounds) | **Lean-verified** at commit b4e6fdd, CI run #40 | InverseGreedy/P6Bottleneck.lean |
| IG-L6 | Finite weighted choice and order-mass definitions; first-choice normalisation; bounded greedy output recurrence | **Lean-verified** at de1b562b, run #67; does not assert exponential-clock equivalence | InverseGreedy/FiniteRace.lean |
| IG-L7 | P6 neighbour model, combinatorial event flags and worked-order examples | **Lean-verified** CI run #75 at 030fc3aa (worked examples only); all-720 event theorem remains open | InverseGreedy/P6Orders.lean; tests/test_s003.py |
| **IG-L8** | Strict positivity of individual finite weighted priority-order masses and first-choice atoms | **Lean-verified** CI #82 at 62916d4; no full permutation normalisation or Exp clock bridge | InverseGreedy/OrderMassBridge.lean |
| IG-A3 | Exact partial connected graph atlas n≤6: 143 total, 62 positive, 3 negative, 78 unresolved | partial finite certificates, not complete classification; Python CI run #32 | results/S003_ATLAS.md |
| **IG-A4** | Revised connected n≤6 atlas: 143 total, 62 positive, 4 negative, 77 unresolved | finite partial certificates, not complete classification | results/S004_ATLAS.md |
| **IG-A5** | Updated connected n≤6 partial atlas: 143 total, 69 positive, 4 negative, 70 unresolved (all n=6) | proved-informal/finite exact certificates | results/S005_ATLAS.md; tests/test_s005.py |
| IG-O1 | Characterise all EGU graphs | open | ROADMAP.md |
| IG-O2 | Certify 70 unresolved atlas cases | open | ROADMAP.md |
| IG-O3 | Full Lean exponential race to event-law proof | open | ROADMAP.md |
| IG-O4 | Independently certified novelty | open | PRIOR_ART.md |

Obstructions P5/P6/C6 apply to graphs with such connected **components**, not arbitrary induced copies in connected supergraphs. No Inverse Greedy arXiv publication, Palomar registration or independent priority claim for S005.
