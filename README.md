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
- **IG-R2/IG-R3 (S011):** the finite positive weighted priority-order
  law is **deletion-consistent**: erasing any subset, including after
  conditioning on the first vertex, yields the size-biased order law
  on the retained set. Consequently its greedy-output pushforward
  satisfies exactly the recursive first-choice law, for finite simple
  graphs. Both theorems have complete informal proofs and independent
  exact arithmetic tests, but the *law-level Lean pushforward* is
  not yet formally compiled. See proof/PRIORITY_DELETION_CONSISTENCY.md.
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
- **IG-P8 (S008):** for every m>=1, the clique K_m with one private
  pendant leaf attached to each clique vertex is EGU. Give leaves rate
  1 and all clique vertices rate (m+1)^(1/m)-1 > 0; each of the m+1
  MIS then has probability 1/(m+1). At m=3 this proves connected n=6
  atlas index 8 EGU with the exact algebraic rates
  (1,1,1,cuberoot(4)-1,cuberoot(4)-1,cuberoot(4)-1), verified
  independently by first-choice recursion and all 720 weighted
  permutations in Q(cuberoot(4)). See proof/CLIQUE_CORONA.md.
- **IG-N1:** C6 cannot be EGU: product of the three opposite-pair
  probabilities ≤1/729, while uniformity would require 1/125.
- **IG-N1b (S012):** C6 is not even *approximately* EGU (AEGU).
  For **every positive rate vector** its greedy-output law has
  total-variation distance at least **4/45** from the uniform law on
  its five MIS. The existing three opposite-pair probability product
  bound forces one pair outcome to have mass at most 1/9, while the
  uniform target assigns 1/5. The 4/45 bound need not be sharp.
  See proof/C6_TV_GAP.md and tests/test_s012_c6_gap.py.
- **IG-N2 (S002):** P5 cannot be EGU: its four probabilities obey a
  strict minor p024*p13 > p03*p14. Since all graphs on ≤4 vertices
  are EGU, P5 is a **smallest-order obstruction**.
- **IG-N3 (S003):** P6 cannot be EGU: independent triple-race events
  produce an exact two-event bottleneck. Its output law has total
  variation distance **at least 1/25** from uniform, for all positive rates.

- **IG-N5 (S009):** every pendant corona of a star K_(1,m),
  m>=2, is **non-EGU for all strictly positive rates**, by a
  strict 2x2 probability minor among four spoke-selection outputs.
  Its smallest member is the corona of P3, connected n=6 atlas
  index 3; this supplies an eighth exact negative certificate.
  The same family has **unattained TV infimum zero**: a positive
  one-parameter rate family approaches uniform arbitrarily closely.
  See proof/STAR_CORONA_OBSTRUCTION.md and
  proof/CORONA_P3_OBSTRUCTION.md.
- **IG-N4 (S004):** the six-vertex cone over P5 (K1∨P5) is not EGU by the join theorem; it is atlas index 68.

- **IG-P9/IG-P10 (S010):** Define *approximately EGU* (AEGU) by
  infimum zero of total variation from the uniform MIS law, without
  requiring exact attainment. A disjoint union is AEGU iff both
  components are AEGU; a join of two nonempty graphs is AEGU iff both
  factors are AEGU. The S009 star coronas therefore generate further
  **unattained** AEGU families: C_m disjoint union K2 and C_m join K1,
  with explicit positive rates and exact TV identities.
  See proof/APPROXIMATE_EGU_CLOSURE.md and tests/test_s010.py.

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

    python -m pip install 'networkx>=3.4,<4' 'sympy>=1.13,<2'
    python experiments/census.py --max-n 6 --max-rate 4
    python experiments/census.py --max-n 6 --max-rate 4 --json

The **143 connected unlabeled graphs through six vertices**
currently have **90 proven positive**, **8 proven negative
(P5, P6, C6, K1∨P5, three false-twin P5 expansions and
star-corona(P3))**, and
**45 unresolved** instances. This is an
exhaustive enumeration but NOT an exhaustive classification:
a failed finite rate search or numerical optimisation does not
prove impossibility. See results/S009_ATLAS.md.

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
S009 adds CoronaP3Minor.lean, with the strictly positive algebraic
four-corner minor for the star-corona obstruction. This was imported
and verified at exact PR SHA ed0d02d4 (successful push and PR runs
41188364427 / 41188368166);
the independent-clock event factorisation remains a paper proof.
S008 adds FullPermutationSupport.lean: the actual Mathlib
List.permutations enumerates exactly the nodup lists whose underlying
finset is active, and all members obey the S007 leaf-mass equality.
It is **not yet** the normalization of the full permutation sum or the
pushforward identity to finiteRaceLaw. CI status is tracked in CLAIMS.md.
**S011:** FullPermutationDecomposition.lean proves in Lean that the
actual Mathlib full permutation list decomposes into distinct heads
and all corresponding tail permutations, *with multiplicity one*;
exact Python and imported Lean CI passed at SHA 00fb0afe (run
41195940431). FullPermutationNormalization.lean proves that the weighted `orderMass`
values of **all actual full permutations sum to exactly 1**, for every
positive real rate vector. Both imported Lean and Python CI passed at
exact final PR #10 SHA 1850e94398964fba7e021b29b6a6fa460f8c73c1
(PR run 41196801662), merged as 0e5949b4. The theorem first passed
at SHA a613bb87. The S011 independent Fraction tests
and paper proof establish the finite deletion-consistency and greedy
pushforward statements mathematically; the full formal law-level
pushforward remains open.

**S012 verified Lean advances:** GreedyBlockedErasure.lean proves the
pointwise first-choice residual identity for symmetric neighbour maps:
after accepting a vertex, its later neighbours may be deleted without
changing the final accepted set; scanning nonneighbours is independent
of the seed containing the first vertex. PriorityOutputLaw.lean defines
the weighted full-permutation greedy-output event mass and proves it
is between zero and one for each target using S011 normalization.
C6TVGap.lean formally derives a 4/45 uniform-event deficit from the
existing C6 product bound (pure algebra, not the full stochastic
event-to-TV identification). Full Python+Lean CI verification and SHAs
are in CLAIMS.md. **Weighted restriction and law-level
priorityOutputMass = finiteRaceLaw remain unproved in Lean**; S013
targets those separately. C6's quantitative non-AEGU theorem is a
complete paper result, with exact finite tests, not independently
certified as novel.

**An equivalence to independent exponential clocks and the P6/C6
symbolic event-law formulas have NOT been formalised end-to-end in Lean.** Never report more than the
specific build SHA proves.

**S010 finite-law Lean step:** FiniteLawFuel.lean establishes
strict cardinality decrease afterChoice, fuel independence of
finiteRaceLaw above active.card, and deletion of a blocked vertex from
a complete priority scan. Green Python+Lean CI at final PR SHA 8064bde, Actions run
41193924574 (PR #9 merged as 8c61154), for these imported lemmas; the complete `List.permutations` sum and
pushforward are **still open**. The closure theorem IG-P9/IG-P10
is an informal proof with exact Python checks, not Lean-formalised.

## Navigation
proof/FALSE_TWIN_INVARIANCE.md — S007 structural closure and obstructions;
results/S009_ATLAS.md — new 90/8/45 partial census;
proof/CLIQUE_CORONA.md — all-size constructive clique-corona EGU theorem;
proof/GREEDY_RESIDUAL_IDENTITY.md — S012 deterministic Lean proof;
proof/C6_TV_GAP.md — S012 non-AEGU C6 TV lower bound;
proof/FIVE_VERTEX_ATLAS.md — full n=5 theorem;
proof/SIX_VERTEX_INDEX1.md and results/S006_ATLAS.md — new n=6 witness;
CLAIMS.md — rigorous status ledger;
AGENTS.md — execution and honesty rules;
HANDOVER.md and ROADMAP.md — progress/next work;
sessions/S012.md — installed next session;
PRIOR_ART.md — preliminary literature, not priority certificate.

The separate [Greedy Uniformity on Trees](https://github.com/jfairfaxball-348/Greedy-Uniformity-on-Trees)
(arXiv:2610.02276) is the **equal-rate** predecessor, read-only.
No Inverse Greedy arXiv publication or Palomar registration is claimed.

See also proof/STAR_CORONA_OBSTRUCTION.md for the S009 all-size non-EGU family.
