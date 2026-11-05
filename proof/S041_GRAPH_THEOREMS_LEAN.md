# S041 — the project's graph theorems, Lean-checked for genuine exponential clocks

Date: 2026-11-05. All statements below are Lean theorems about
`RealClockEGU` / `RealClockAEGU`, i.e. about Mathlib's **actual** independent
exponential product measure (via the S041 bridge
`realClockEGU_iff_firstChoiceEGU`), for **all strictly positive real rate
vectors**. Check the exact-head push and PR CI of the S041 PR before calling
them GitHub-verified.

## Infrastructure

| Lean | Content |
|---|---|
| `RaceTerms.lean` | Computable path expansion `raceTerms` of the first-choice recursion, with `finiteRaceLaw_eq_raceValue` (all rates, fuels, active sets). |
| `RationalWitness.lean` | `realClockEGU_of_ratWitness`: kernel-decidable rational witness ⇒ `RealClockEGU`. Checked with `decide +kernel` (kernel reduction, no native code). |
| `GraphOperationsLaw.lean` | Disjoint-union product law, join block law, scaling invariance. |
| `CographEGU.lean` | Relabelling invariance `realClockEGU_congr_equiv`; cotrees. |
| `FalseTwins.lean` | Isolated-vertex deletion, twin-extension law with merged rates. |
| `GeneralFamilies.lean` | Target locality, pendant-pair product formula. |

## Exact EGU theorems

| Claim | Lean theorem |
|---|---|
| IG-P1 complete multipartite graphs are EGU | `Cotree.completeMultipartite_realClockEGU` |
| IG-P2 disjoint union EGU ⟺ both parts EGU | `realClockEGU_union_iff` |
| IG-P3 P4 is EGU (rates `1+√3, 2, 2, 1+√3`) | `atlas4_1_egu` |
| IG-P4 join of nonempty graphs EGU ⟺ both EGU; every cograph EGU | `realClockEGU_join_iff`, `Cotree.realClockEGU`, `IsCograph.realClockEGU` |
| IG-P5 (connected part) the 20 connected five-vertex positives | `atlas5_*_egu` |
| IG-P6 six-vertex atlas index 1 is EGU | `atlas6_1_egu` |
| IG-P7 false-twin extension preserves EGU, both directions | `realClockEGU_twinExtend_iff` |
| IG-P8 every clique corona `K_m ∘ K₁` (m ≥ 1) is EGU | `cliqueCorona_realClockEGU` |
| IG-N1 C6 is not EGU | `c6Nb_not_realClockEGU` |
| IG-N2 P5 is not EGU (strict minor, all rates) | `p5Nb_not_realClockEGU` |
| IG-N3 P6 is not EGU | `p6Nb_not_realClockEGU` |
| IG-N4 the cone `K₁ ∨ P5` is not EGU | `coneP5Nb_not_realClockEGU` |
| IG-N5 every pendant star corona `K_{1,m} ∘ K₁`, m ≥ 2, is not EGU | `starCorona_not_realClockEGU` (m = k+2), `coronaP3Nb_not_realClockEGU` |
| IG-A9 the 90 certified positives and 8 certified negatives of the connected n ≤ 6 atlas | `atlas_n_le_6_certified` (NetworkX labellings) |

## Approximate EGU (total variation)

| Claim | Lean theorem |
|---|---|
| TV dominates disjoint-event deficits | `realClockTV_ge_deficits` |
| IG-N1b C6 TV ≥ 4/45 for all rates; C6 not AEGU | `c6_realClockTV_ge`, `c6_not_realClockAEGU` |
| IG-N2b P5 TV along `(1,1,t,1,1)` is `3/4 − 1/(t+2) − 1/(t+4)`; P5 unattained AEGU | `p5_realClockTV_family`, `p5_unattained_realClockAEGU` |
| IG-N3b P6 TV ≥ 2√(2/5) − 6/5 for all rates | `p6_realClockTV_ge` (Cauchy–Schwarz + case analysis in `p6_tv_analytic`) |
| IG-N6 (m = 2) corona(P3) unattained AEGU along `(1,t,1,1,4t,1)` | `coronaP3_unattained_realClockAEGU` |
| IG-P9 disjoint union AEGU ⟺ both parts AEGU | `realClockAEGU_union_iff` |
| IG-P10 join of nonempty graphs AEGU ⟺ both AEGU | `realClockAEGU_join_iff` (ApproximateJoin.lean) |

## Proof ideas (informal, matching the Lean)

* **Union.** Induction on the first-choice recursion: the first chosen vertex
  lies in one part, and the rate-weighted first step identity
  `Σ_{v∈A∩I} r_v F(A_v, I∖v) = Λ_A F(A, I)` (valid also for `A = ∅`) collapses
  the two sums to `F_G F_H`.
* **Join.** After the first choice, the other side is entirely deleted, so the
  law is `Λ_G/(Λ_G+Λ_H)·F_G` on left targets. EGU ⟸: scale the right rates by
  `c = Λ_G m_H/(Λ_H m_G)` (scale invariance). EGU ⟹: the left law is constant on
  `M(G)` and sums to one.
* **Relabelling.** `finiteRaceLaw` is natural under equivalences preserving the
  neighbour map; MIS families correspond.
* **False twins.** Choosing either twin leaves the other isolated; an isolated
  target vertex can be deleted without changing the law; hence the two twin
  branches add to one branch with the merged rate.
* **Target locality.** The recursion only reads `nb v` for chosen `v ∈ target`.
  For clique coronas the all-leaves target therefore sees only pendant pairs:
  probability `(1+β)^{−m} = 1/(m+1)`; automorphisms swapping pairs equalise the
  other `m` MIS, which then share the remaining mass. For star coronas, targets
  avoiding the hub see corona(P3) plus a disjoint matching; the union law and the
  strict corona(P3) minor give a strict minor for every m ≥ 2.
* **Concrete graphs.** `raceTerms` path lists are certified by `decide +kernel`;
  closed forms by `field_simp; ring`; sign certificates are positive-coefficient
  numerators checked by `positivity`. Rational atlas witnesses are checked in
  exact ℚ arithmetic by kernel reduction; the algebraic √3 witnesses by
  `linear_combination` with `√3² = 3`; atlas index 8 via the clique-corona theorem;
  the false-twin atlas graphs via `realClockEGU_twinExtend_iff` and relabelling.

## Not formalised (and why)

* **IG-N6 for m ≥ 3**: proved informally, not yet in Lean (the family needs the
  full hub analysis of the star-corona recursion).
* **Exhaustiveness**: that the NetworkX atlas lists *every* connected graph of
  order ≤ 6 up to isomorphism, and hence the "all graphs on ≤ 5 vertices" form of
  IG-P5. Every listed graph's status is a Lean theorem; the enumeration is not.
* **Open problems**: the 45 unresolved six-vertex graphs and the classification of
  all EGU graphs (IG-O1, IG-O2) have no proofs to formalise.
* **Novelty** (IG-O4) is a bibliographic question, not a theorem.

Atlas counts unchanged: **90 EGU / 8 non-EGU / 45 unresolved**.
