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

## S003 — installed
See sessions/S003.md. Make C6Product.lean compile, connect
exponential race semantics to output laws, investigate P6 via exact
certificates (not optimizer failure), and reduce atlas unknowns.

**Final boss:** classify finite graphs with strictly positive
exponential vertex priorities yielding uniform greedy terminal
maximal independent sets, and characterise the attainable output laws.
