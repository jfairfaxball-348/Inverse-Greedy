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

## S011 — executed 2026-10-31
- [x] Proved a unique-head decomposition (with exact list multiplicities)
      of actual `List.permutations`, not merely order support; imported
      Lean and green Python+Lean CI at commit 00fb0afe, run 41195940431.
- [x] New complete informal proofs: positive weighted-priority deletion
      consistency for every subset, and pushforward to the first-choice
      greedy MIS recurrence for symmetric irreflexive graphs.
      See proof/PRIORITY_DELETION_CONSISTENCY.md.
- [x] Independent exact `Fraction` regressions across every subset of
      unequal rational 4/5-vertex rate vectors, complete n<=6 permutation
      uniqueness/mass and diverse greedy-law graphs.
- [x] Lean normalisation of the actual complete `List.permutations`
      `orderMass` sum is 1 for all strictly positive real rates, using
      structural head decomposition and induction. Imported Lean+Python
      succeeded at exact final PR #10 SHA 1850e943 (PR run
      41196801662), squash merged as 0e5949b4.
- [ ] Lean weighted deletion restriction and law-level pushforward still
      require formal proof, even though their complete mathematical proofs
      and exact finite tests are available.
- [ ] Continuous independent exponential-clock bridge still open.
- [ ] Boundary search did not yet certify new atlas instances; baseline
      90/8/45 stands.

## S012 — executed 2026-10-31
- [x] Imported Lean theorem giving the deterministic greedy first-choice
      residual identity under symmetric neighbour relations, including
      deletion of every later blocked neighbour and independent scan
      of the surviving suffix (IG-L16).
- [x] Defined the weighted full-priority-permutation greedy-output event
      mass; proved nonnegativity and an upper bound of one for every
      target using S011 structural normalization (IG-L17).
- [x] Derived a strict positive all-rate C6 TV gap 4/45 from the S001
      pair-product inequality: C6 is non-AEGU, unlike star coronas
      with unattained zero infimum (IG-N1b).
- [x] Proved the algebraic 4/45 single-event deficit in Lean (IG-L18),
      without claiming stochastic/TV identification in Lean.
- [x] Proved P5, the order-five smallest non-EGU obstruction, is
      nevertheless **unattained AEGU** with strictly positive
      (1,1,t,1,1) rates as t approaches 0; exact
      TV=t(3t+10)/[4(t+2)(t+4)] < 5t/16. This is a
      new boundary mechanism separate from star coronas.
- [x] Exact Fraction first-choice recursion and full 5! priority-order
      oracle verify the P5 law; pure rational Lean identity and bound
      in P5ApproximateBoundary.lean (CI status in CLAIMS.md).
- [x] Added exact state-machine deletion tests, exact C6 TV checks
      on 729 unequal-rate tuples and two independent weighted order
      oracles; CI verification recorded in CLAIMS.md.
- [ ] Full weighted priority restriction to arbitrary subsets is still
      a **paper proof only**; the Lean law-level equality
      priorityOutputMass = finiteRaceLaw is **not** yet proved.
- [ ] Independent continuous-clock bridge remains open.
- [ ] Six-vertex atlas remains 90/8/45; no novelty certificate.

## S013 — executed 2026-10-31
- [x] Proved the general structural weighted first-head expectation
      identity over **actual** List.permutations, for any real-valued
      first-vertex/tail statistic, not merely normalization (IG-L20).
      Imported Lean and full Python CI green at SHA 5cce19f,
      Actions 41219976009.
- [x] Formalised the first-head event equation and its deterministic
      greedy residual-event reduction, with blocked vertices still
      weighted inside the unfiltered tail (IG-L21; exact-head imported
      Lean status in CLAIMS.md).
- [x] Independent exact Fraction regressions for every nonempty subset
      of a six-vertex rate vector, arbitrary tail-sensitive test
      functions, and conditional filtered tails on several symmetric
      graphs; full suite through tests/test_s013.py.
- [x] Documented exactly where the missing *weighted projection*
      to the retained vertices is required before claiming the complete
      finiteRaceLaw equality.
- [ ] Full arbitrary-subset weighted deletion consistency in Lean.
- [ ] Full `priorityOutputMass = finiteRaceLaw` proof in Lean.
- [ ] Independent Exp-clock ordering bridge in Lean.
- [ ] No new EGU atlas classifications: 90/8/45 remains.

## S014 — executed 2026-10-31
- [x] Defined exact \`List.filter\` projected-order event mass from actual complete weighted permutations.
- [x] Lean formal structural first-head equation separating retained vs discarded first global vertex; initial CI green at 4008362 (run 41223548014).
- [x] Added scalar rate-cancellation algebra and empty-retained-set boundary lemmas; verified with full Python+Lean at exact final PR head 66524262, Actions 41224006146; PR #13 merged as 713e5641.
- [x] New independent unequal-positive-Fraction six-vertex regression for the complete projected law, first retained winner and first-head recurrence.
- [x] Installed S015 for the *actual* Lean event induction and full weighted projection theorem.
- [ ] First retained winner conditional probability as a Lean law theorem, not just a scalar identity.
- [ ] All-target weighted deletion consistency and greedy finiteRaceLaw pushforward in Lean.
- [ ] Independent exponential-clock ordering equivalence; 45 connected six-vertex atlas cases remain.


**Final boss:** classify finite graphs with strictly positive
exponential vertex priorities yielding uniform greedy terminal
maximal independent sets, and characterise the attainable output laws
(including uniform laws in the closure but not the attainable set).

## S015 — executed and merged 2026-11-01 (PR #14, exact-head CI green)
- [x] Added a Lean proof that filtering any actual full permutation to retained ⊆ active gives an actual retained permutation, including correct nodup and underlying finset.
- [x] Derived exact zero mass for every unsupported retained target for arbitrary real rates, and exact mass one for a singleton retained set at positive rates.
- [x] Added exhaustive 7-vertex 128-retained-subset Fraction regression checking the full projected law, support, zero impossible targets and normalization.
- [x] Documented the precise boundary and installed S016.
- [x] Verified final PR #14 head 3583f27d in complete imported Lean and Python/certified census, both green in Actions run 41290187561; merged as fd08c64a.
- [ ] First retained winner law, multi-vertex deletion consistency and complete greedy-output pushforward remain Lean-open.
- [ ] Independent exponential-clock semantics and 45 connected six-vertex atlas cases remain open; 90/8/45 unchanged.
