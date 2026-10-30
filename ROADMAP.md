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

## S006 — installed
See sessions/S006.md. Prioritise structural, machine-checked
bridges between weighted permutations, greedy output law and
independent exponential clocks, alongside the remaining 70 n=6 cases.

**Final boss:** classify finite graphs with strictly positive
exponential vertex priorities yielding uniform greedy terminal
maximal independent sets, and characterise the attainable output laws.
