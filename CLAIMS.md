# Claim ledger — S010 (2026-10-31)

Status meanings: **proved-informal** is a complete written proof, not machine-checked or independently novel; **tested-exact** is finite arithmetic checking; **Lean-verified** requires actual successful CI at the stated SHA; **open** means unestablished.

| ID | Claim | Status | Evidence |
|---|---|---|---|
| IG-R1 | Weighted first-choice probability law | proved-informal, tested-exact | proof/FOUNDATIONS.md; experiments/exact.py |
| IG-P1 | Complete multipartite graphs EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P2 | Disjoint union EGU iff each component EGU | proved-informal | proof/FOUNDATIONS.md |
| IG-P3 | P4 EGU with positive algebraic rates | proved-informal | proof/FOUNDATIONS.md |
| **IG-P4** | Join G∨H EGU iff both EGU; every finite cograph EGU with positive rational rates | **proved-informal; tested-exact for n≤6** | proof/JOIN_COGRAPHS.md; experiments/cograph.py |
| **IG-P5** | All graphs on at most five vertices classified: only P5 non-EGU; connected n=5 has 20 EGU / 1 negative; seven new rate witnesses | **proved-informal; tested-exact** | proof/FIVE_VERTEX_ATLAS.md; tests/test_s005.py; exact Q(√3) algebra |
| **IG-P6** | Connected six-vertex atlas index 1 is EGU: exact integer rates (3,6,4,5,3,3), with a positive one-parameter rational family | **proved-informal; tested-exact** | proof/SIX_VERTEX_INDEX1.md; tests/test_s006.py |
| **IG-P7** | False-twin extension/contraction preserves exact finite exponential greedy output law and EGU equivalence | **proved-informal; tested-exact** (19 new positive witnesses checked by two exact methods; 3 new negative P5 contractions) | proof/FALSE_TWIN_INVARIANCE.md; tests/test_s007.py |
| **IG-P8** | Every clique-corona K_m with one pendant leaf per clique vertex is EGU at leaf rate 1 and clique rate (m+1)^(1/m)-1; n=6 index 8 has an exact cubic positive witness | **proved-informal; tested-exact** by two independent Q(cuberoot(4)) oracles | proof/CLIQUE_CORONA.md; tests/test_s008.py |
| **IG-P9** | AEGU (TV infimum zero) is closed under disjoint union **iff** both factors are AEGU. If one factor is uniform, joining its output by disjoint union preserves the other's exact TV error. | **proved-informal; tested-exact** for star coronas disjoint union K2 | proof/APPROXIMATE_EGU_CLOSURE.md; tests/test_s010.py |
| **IG-P10** | For two nonempty graphs, graph join is AEGU iff both factors are AEGU, even when the infimum is not attained. Normalized block-total rates give an exact weighted sum of component TVs. In particular C_m join K1 is unattained AEGU. | **proved-informal; tested-exact**; 7! independent oracle for base case | proof/APPROXIMATE_EGU_CLOSURE.md; tests/test_s010.py |
| **IG-N5** | **Every star corona K_(1,m) circ K1 with m>=2 is non-EGU, including n=6 atlas index 3 (corona P3).** The 2x2 probability minor is strictly positive for all positive real rates. | **proved-informal; tested-exact** (729 vectors + complete permutation checks; m=2,3,4 examples) | proof/STAR_CORONA_OBSTRUCTION.md; proof/CORONA_P3_OBSTRUCTION.md; tests/test_s009.py |
| **IG-N6** | Star coronas K_(1,m) circ K1, m>=2, have **infimum TV distance 0 to uniform but never attain it**; explicit strictly positive t-family and exact TV formula/upper bound | **proved-informal; tested-exact** | proof/STAR_CORONA_OBSTRUCTION.md; tests/test_s009.py |
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
| **IG-L9** | Structural cardinality-induction normalisation of the finite weighted-order head-choice tree; does **not** yet identify tree leaves with `orderMass`, nor prove the Exp-clock law | **Lean-verified** at 7fc4802, green final-head CI #103 and #104 (original theorem already green at #92) | InverseGreedy/OrderTreeNormalization.lean |
| **IG-L10** | Duplicate-free leaf product of successive finset first-choice masses equals `orderMass` | **Lean-verified** at SHA 543cfe9, green Actions run 41131451454; does not enumerate full permutations or prove greedy pushforward | InverseGreedy/OrderLeafBridge.lean |
| **IG-L11** | Membership in actual List.permutations iff nodup and matching vertex finset, with S007 orderLeafMass = orderMass for each supported permutation | **Lean-verified at final PR SHA ff29b0bb; Python + Lean successful in push CI 41183416574 and PR CI 41183420188**; neither sum normalization nor greedy pushforward | InverseGreedy/FullPermutationSupport.lean |
| **IG-L12** | Strict positive rational factorisation and Bernoulli-weighted 2x2 star-corona minor, for abstract positive parameters; no stochastic law identification | **Lean-verified at exact PR SHA ed0d02d4; Python and Lean passed push CI 41188364427 and PR CI 41188368166**; stochastic output-law bridge remains open | InverseGreedy/CoronaP3Minor.lean |
| **IG-L13** | After selecting an active vertex, afterChoice strictly decreases active cardinality; finiteRaceLaw is independent of fuel above active.card, for every rate vector and target; any vertex blocked by the accepted prefix can be removed from that full greedy scan. **Not** the complete permutation-law pushforward. | **Lean-verified at exact branch SHA fbf578c2** (successful imported Lean and Python PR jobs); recheck final release head | InverseGreedy/FiniteLawFuel.lean; PR #9 |
| **IG-A9** | Partial connected n<=6 atlas 90 EGU / 8 non-EGU / 45 unresolved; index 3 proved negative by all-positive star-corona obstruction | **proved-informal; tested-exact**; no complete n=6 classification | results/S009_ATLAS.md; tests/test_s009.py |
| IG-A3 | Exact partial connected graph atlas n≤6: 143 total, 62 positive, 3 negative, 78 unresolved | partial finite certificates, not complete classification; Python CI run #32 | results/S003_ATLAS.md |
| **IG-A4** | Revised connected n≤6 atlas: 143 total, 62 positive, 4 negative, 77 unresolved | finite partial certificates, not complete classification | results/S004_ATLAS.md |
| **IG-A5** | Updated connected n≤6 partial atlas: 143 total, 69 positive, 4 negative, 70 unresolved (all n=6) | proved-informal/finite exact certificates | results/S005_ATLAS.md; tests/test_s005.py |
| **IG-A6** | Connected n≤6: 143 total, 70 positive / 4 negative / 69 unresolved; all unresolved order six | **partial finite certificate atlas** | results/S006_ATLAS.md |
| **IG-A7** | Connected n<=6 partial atlas: 89 positive, 7 negative, 47 unresolved; 19 rational/quadratic lifts and 3 P5 false-twin obstructions | **proved-informal; tested-exact**; no complete n=6 classification | results/S007_ATLAS.md; tests/test_s007.py |
| **IG-A8** | Updated connected n<=6 partial atlas: 90 positives, 7 negatives, 46 open; index 8 is the exact cubic corona K3 | **proved-informal; tested-exact** | results/S008_ATLAS.md; tests/test_s008.py |
| IG-O1 | Characterise all EGU graphs | open | ROADMAP.md |
| IG-O2 | Certify 45 unresolved atlas cases | open | ROADMAP.md |
| IG-O3 | Full Lean exponential race to event-law proof | open | ROADMAP.md |
| IG-O4 | Independently certified novelty | open | PRIOR_ART.md |
| IG-O5 | Formal full List.permutations mass normalisation and weighted greedy pushforward, then independent exponential clock semantics | open | sessions/S011.md |

Obstructions P5/P6/C6 apply to graphs with such connected **components**, not arbitrary induced copies in connected supergraphs. No Inverse Greedy arXiv publication, Palomar registration or independent priority claim for S009.

S010 AEGU statements concern **infimum** total variation, not finite-rate exact EGU. The six-vertex partial atlas remains **90/8/45**; no new n<=6 classification or independent novelty claim.
