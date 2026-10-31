# Research roadmap — Inverse Greedy

## S001 — completed 2026-10-30
- [x] Weighted first-choice recurrence, disjoint-union factorisation.
- [x] Multipartite/star, P4 constructions; C6 written obstruction.
- [x] Fraction engine, independent weighted-permutation oracle.
- [x] Lean C6 algebraic identity and passing initial GitHub Actions.

## S002 — 2026-10-30
- [x] Join equivalence EGU(G∨H) iff EGU(G) and EGU(H).
- [x] Explicit rational uniformisation of every finite cograph.
- [x] Strict P5 probability minor: P5 smallest-order non-EGU graph.
- [x] Enumerate all 143 connected unlabeled graphs n≤6;
      62 positive, 2 negative, **79 unresolved**.
- [x] Exact Python tests on 243 P5 rate vectors and connected cographs n≤6.
- [x] Cubic AM-GM SOS lemma verified in Lean CI #9 (59b05ba).
- [ ] C6 six-factor and product inequality Lean formalisation:
      draft attempted, but elaboration timed out. Kept unimported
      to preserve a passing project build; S003 repair task.
- [ ] Full stochastic law/event-to-rational proof in Lean.
- [ ] Classify 79 remaining graph instances with exact certificates.
- [ ] Independent literature/priority certification.

## S003 — executed 2026-10-30
- [x] Proved P6 non-EGU by disjoint triple-race events.
- [x] Derived uniform total-variation gap ≥ 1/25 for P6.
- [x] Exact P6 oracle: all 720 orders, 729 positive integer rate vectors.
- [x] Certified atlas 62 positive / 3 negative / 78 unresolved.
- [x] Repaired C6 six-factor inequality and imported into Lean library;
      CI run #35 at commit 181cda3 verified pure algebraic theorem.
- [x] Compiled the P6 uniform algebraic contradiction at same SHA.
- [ ] Full Lean stochastic event→rational law for C6 and P6.
- [ ] Lean P5 strict minor and full event-to-law connection.
- [ ] Remaining 78 atlas cases and independent novelty audit.

## S004 — executed 2026-10-30
- [x] Strengthened P6 universal TV gap from 1/25 to
      2√(2/5)−6/5≈0.064911 using two disjoint-event deficits.
- [x] Classified six-vertex cone over P5, atlas index 68, as non-EGU
      by join necessity and the P5 strict output probability minor.
- [x] Added exact join identity tests on 729 rate vectors plus
      independent weighted-permutation oracle cases.
- [x] Updated connected atlas to 62 positive / 4 negative / 77 open.
- [x] Introduced a finite weighted-order/greedy-output model and
      first-choice normalisation law in Lean; imported into library,
      with verified core build in CI run #67 (de1b562b).
- [x] Added explicit P6 finite-order event predicates and Lean
      worked-order examples (final PR CI to verify); complete 720-order
      proof is NOT yet Lean checked; Python exhaustive oracle is.
- [ ] Formal equivalence of order-mass law and bounded output-law
      recursion, plus independent exponential clocks.
- [ ] Formal P6 event equivalence, product independence and TV gap
      from output law; formal C6 pair event-law algebra.
- [ ] Lean P5 strict minor; outstanding atlas and priority audit.

## S005 — executed 2026-10-30
- [x] Exact positive witnesses close all seven remaining connected
      five-vertex cases (six rational vectors and one Q(√3)).
- [x] Complete n=5 classification: 20 EGU and only P5 non-EGU.
- [x] Exact Fraction and Q(√3) recursion/permutation oracles verified
      in Python CI #82 at commit 62916d4.
- [x] Lean positivity of individual orderMass/firstChoice terms
      compiled in CI #82 at commit 62916d4.
- [ ] Sum-of-permutations normalisation in Lean.
- [ ] Grouping ordered outcomes into finiteRaceLaw in Lean.
- [ ] Full exponential-clock identification and P6/C6 event laws.
- [ ] Remaining 70 connected six-vertex atlas certificates.
- [ ] Independent novelty/priority certification.

## S006 — executed 2026-10-30
- [x] Merged S005 PR #4 after green final-head CI #87.
- [x] Found exact positive six-vertex atlas index 1 witness (3,6,4,5,3,3)
      and a positive one-parameter rational family; validated by first-choice
      recursion and all 720 priority permutations.
- [x] Updated n≤6 partial atlas to 70 positive / 4 negative / 69 unresolved.
- [x] Added structural Lean induction proving finite head-choice tree mass 1
      at fuel ≥ cardinality (compile status governed by latest Actions SHA).
- [ ] The leaf-by-leaf `orderMass` identity, grouping by `greedyOutput`,
      continuous independent exponential-clock identification and complete
      Lean P6 event laws are separate remaining obligations.
- [ ] Remaining 69 six-vertex certificates and novelty review.

## S007 — executed 2026-10-30
- [x] Proved false-twin contraction theorem (informal): precise law
      equivalence, MIS bijection and strict rate splitting in both directions.
- [x] 19 additional connected six-vertex positive cases: 16 rational
      and 3 Q(√3) lifted rate witnesses from S005, independently checked.
- [x] 3 new connected six-vertex non-EGU cases: atlas indices 4,13,16,
      which contract exactly to the established P5 obstruction.
- [x] Atlas now 89 EGU / 7 non-EGU / 47 unresolved (143 connected n<=6).
- [x] Introduced and imported Lean duplicate-free leaf-level
      first-choice product = orderMass theorem (green CI run 41131451454 at 543cfe9).
- [ ] Explicit full permutation enumeration, normalisation as sum
      over permutations, and pushforward to finiteRaceLaw in Lean.
- [ ] Continuous exponential-clock Lean connection.
- [ ] The remaining 47 six-vertex graph classifications.
- [ ] Independent novelty or publication-priority audit.

## S008 — executed 2026-10-31
- [x] Constructive all-size EGU family: the corona of K_m with one
      private leaf at each clique vertex; leaf/centre rates 1 and
      (m+1)^(1/m)-1, producing m+1 equiprobable maximal sets.
- [x] Exact six-vertex net graph, connected atlas index 8, has rates
      (1,1,1,cuberoot(4)-1,cuberoot(4)-1,cuberoot(4)-1), and all four
      MIS have probability 1/4. Certified by independent exact first-
      choice and all-720-permutation oracles over Q(cuberoot(4)).
- [x] Updated partial connected atlas to 90/7/46.
- [x] Added Lean support characterization for actual List.permutations,
      and reused S007 leaf identity across each supported permutation.
      Mark Lean checked only after successful exact-head CI.
- [ ] Total List.permutations mass = 1 Lean theorem, greedy-output
      pushforward to finiteRaceLaw, and continuous-clock equivalence.
- [ ] Classify 46 remaining connected n=6 cases with certificates;
      independent publication-priority review.

## S009 — executed 2026-10-31
- [x] Proved a **new infinite non-EGU family**, the pendant coronas
      of stars K_(1,m), m>=2, with arbitrary asymmetric positive rates.
      Independent endpoint-pair winners yield a closed-form law,
      and a strictly positive four-corner determinant forbids uniformity.
- [x] Applied the general theorem to connected six-vertex index 3,
      the P3 corona; partial atlas is now 90 positive / 8 negative /
      45 unresolved.
- [x] Exact 729-vector Fraction test, independent full 720-order oracle,
      all-size star-corona formula checks for m=2,3,4.
- [x] Imported algebraic strict minor and shifted-star inequality into Lean;
      verified at final PR SHA ed0d02d4 with green push+PR CI.
- [x] Preserved S006/S007 historical censuses via include_s009=False.
- [ ] Full List.permutations normalisation and greedy pushforward to
      finiteRaceLaw in Lean; independent exponential clock semantics.
- [ ] 45 unresolved n=6 classifications and novelty/priority audit.

- [x] Quantified approximate EGU for every star corona:
      strict nonuniformity for all finite positive rates but
      total-variation infimum zero; exact rate family and
      TV(t) < m/((2^m+1)^2*t).
- [x] Fraction tests of exact TV expression and bound for m=2,3,4.

## S010 — executed 2026-10-31
- [x] Proved exact AEGU (zero infimum TV) closure under disjoint union
      and join, with necessary-and-sufficient factor conditions.
- [x] Constructed explicit new unattained AEGU families C_m ⊔ K2 and
      C_m ∨ K1 (m>=2), deriving precise positive-rate TV identities.
- [x] Independently checked these identities with exact Fraction
      recursion and full 7! weighted permutation oracle on smallest join.
- [x] Added Lean afterChoice cardinality decrease, fuel stability above
      active.card, and blocked-vertex deletion (green imported
      Lean and Python checks at exact final PR SHA 8064bde,
      Actions run 41193924574; merged as 8c61154).
- [x] Installed sessions/S011.md for the next execution workshop.
- [ ] Identify List.permutations leaves uniquely and sum full orderMass
      over all permutations in Lean.
- [ ] Prove weighted greedyOutput pushforward equals finiteRaceLaw in Lean;
      independent continuous Exp-clock bridge remains unproved.
- [ ] 45 six-vertex atlas cases remain unresolved; no novelty certificate.

## S011 — installed
See sessions/S011.md. Finish actual List.permutations decomposition,
normalization and output pushforward; explore additional AEGU boundary
families, keeping unattained approximation distinct from exact EGU.

**Final boss:** classify finite graphs with strictly positive
exponential vertex priorities yielding uniform greedy terminal
maximal independent sets, and characterise the attainable output laws
(including uniform laws in the closure but not the attainable set).
