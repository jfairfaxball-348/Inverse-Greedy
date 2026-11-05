# S041 — genuine real-clock strict-order law and greedy-output pushforward

Date: 2026-11-05. Builds on S035–S039 (merged) and S040 (PR #40, the
generic ENNReal triangular monomial identity). Check the S041 PR's
exact-head push **and** PR CI before describing anything below as
Lean-verified on GitHub; at the time of writing it was verified by a
local full `lake build` of the imported root plus `#print axioms`
(only `propext`, `Classical.choice`, `Quot.sound`).

## Statements

Let `ι` be a finite type, `λ : ι → ℝ` with every `λ_i > 0`, and
`μ = finiteIndependentExp λ` the actual Mathlib product of the
`Exp(λ_i)` laws on `ι → ℝ`.

**(A) Finite-width closed product** (`finiteIndependentExp_strictBin_closedForm`).
For a certified complete order `σ = (σ_0,…,σ_{n-1})` (`CompleteClockOrder`)
and width `δ > 0`, with `q_j = exp(-λ_{σ_j} δ)` and `Q_j = ∏_{l ≥ j} q_l`,

    μ{ ⌈ω_{σ_0}/δ⌉ < ⌈ω_{σ_1}/δ⌉ < ⋯ } = ofReal( ∏_j (1-q_j) q_j^j / (1-Q_j) ).

**(B) Strict-order law** (`finiteIndependentExp_strictClockChamber_orderMass`).

    μ{ ω_{σ_0} < ω_{σ_1} < ⋯ < ω_{σ_{n-1}} } = ofReal(orderMass λ σ)
                                             = ofReal( ∏_j λ_{σ_j} / Σ_{l≥j} λ_{σ_l} ).

**(C) Greedy-output law** (`finiteIndependentExp_realClockGreedyOutput_eq_priorityOutputMass`,
`…_eq_finiteRaceLaw`). Let `clockSortedOrder ω` be the stable merge sort of
`Finset.univ.toList` by clock value and
`realClockGreedyOutput N ω = greedyOutput N (clockSortedOrder ω)`. Every output
event is measurable (`realClockGreedyOutput_event_measurable`) and

    μ{ realClockGreedyOutput N = I } = ofReal(priorityOutputMass λ N univ I)
                                     = ofReal(finiteRaceLaw λ N |ι| univ I)   (N symmetric).

**(D) EGU bridge** (`realClockEGU_iff_firstChoiceEGU`). For symmetric `N`,
the charter definition of EGU with genuine exponential clocks
(`RealClockEGU`) is equivalent to the discrete first-choice-recursion
formulation (`FirstChoiceEGU`), with the same strictly positive rate vector.

## Complete informal proof

*(A).* S035/S038 (merged, Lean): the zero bin is null and the positive bins
`K_i = ⌈ω_i/δ⌉ - 1` have joint law `∏_i (1-q_i) q_i^{k_i}`; the chamber is the
disjoint union of the admissible cylinders, reindexed by gap vectors
`d ∈ ℕ^n` with `k_j = j + Σ_{a≤j} d_a`. Transporting along the certified
equivalence `Fin n ≃ ι` turns the vertex product into the positional
product `∏_j ofReal(1-q_j)·ofReal(q_j)^{k_j}` (nonnegative factors, so
`ofReal` splits exactly). S040's identity gives
`(∏_j c_j q_j^j)·∏_a (∏_{j≥a} q_j)^{d_a}`, and `∏_{j≥a} ofReal q_j = ofReal Q_a`.
In `ENNReal`, `Σ'_{d∈ℕ^n} ∏_a f_a(d_a) = ∏_a Σ'_k f_a(k)` (proved by induction
along `Fin.consEquiv` with `ENNReal.tsum_prod'` and `tsum_mul_left/right`;
no summability side conditions). Each factor is S039's
`Σ'_k (ofReal Q_a)^k = ofReal(1/(1-Q_a))`, with `0<Q_a<1`. Recombining the
nonnegative real factors under `ofReal` gives (A).

*(B).* `Q_j = exp(-Λ_j δ)` with `Λ_j = Σ_{l≥j} λ_{σ_l} > 0`. For `δ>0`,
`(1-q_j) q_j^j/(1-Q_j) = [((1-e^{-λδ})/δ)/((1-e^{-Λδ})/δ)]·q_j^j`, which tends to
`(λ_{σ_j}/Λ_j)·1` as `δ→0⁺` by S030's slope lemma and continuity; a finite
product of limits is the limit of the product. By induction on the list,
`orderMass λ σ = ∏_j λ_{σ_j}/Λ_j`. Squeeze: S033 gives
`bin(δ) ≤ μ(chamber)` and S034 gives
`μ(chamber) ≤ bin(δ) + Σ_{a<b} δ·min(λ_{σ_a},λ_{σ_b})` (distinct positions are
distinct vertices by completeness). Both bounds tend to `ofReal(orderMass)`, and
the middle term is constant, so it equals the limit (`tendsto_nhds_unique`).

*(C).* `clockSortedOrder ω` is a permutation of all vertices and is pairwise
`≤` in clock value (`List.pairwise_mergeSort`). If `ω` is in the strict chamber of
a permutation `σ`, the clocks are injective on `σ`, so both lists are pairwise
`≤` for a relation antisymmetric on their elements, and `List.Perm.eq_of_pairwise`
gives `clockSortedOrder ω = σ` (pointwise, no exceptional set). Hence the chambers
of distinct permutations are disjoint and `U := ⋃_{σ: greedy σ = I} chamber σ` is
contained in the output event `E`. Conversely, if `ω` has no ties then `ω` lies in
the chamber of its own sorted order, so `E ⊆ U ∪ T` with `T` the tie event, which
is null (S022). Thus `μ E = μ U = Σ_σ [greedy σ = I] ofReal(orderMass σ)` by (B),
which is `ofReal(priorityOutputMass)` (nodup permutations, list/finset sum) and,
by S018's proved pushforward, `ofReal(finiteRaceLaw)`. Measurability: the sorted
order is a function of the finite Boolean comparison pattern
`(i,j) ↦ [ω_i ≤ ω_j]`, which is measurable into a finite discrete space.

*(D).* Pointwise in `I`, (C) converts the real-clock statement to the
discrete one; `ofReal` is injective on `[0,∞)`, and both `finiteRaceLaw`
(by S012/S018 nonnegativity) and `1/|M|` are nonnegative.

## Scope and exclusions

* Rates are strictly positive reals, possibly irrational; no zero or limiting rates.
* The exponential **priority times** are the clocks; nothing here concerns
  exponentially distributed MWIS objective weights.
* The Plackett–Luce law for independent exponential races is classical
  probability; the contribution is the *formal* Lean derivation from the actual
  product measure and the formal pushforward to the greedy output. No novelty,
  priority or registry (Palomar) claim is made.
* Graph-specific obstructions/constructions (C6, P5, P6, cographs, coronas, the
  n≤6 atlas) are **not** re-proved here. (D) lets any future Lean theorem about
  `finiteRaceLaw` uniformity transfer verbatim to genuine clocks; existing Lean
  files that formalise only rational identities still do not by themselves
  formalise those graph theorems.
* Not formalised: that `greedyOutput` is always a maximal independent set (exact
  Python check only, `tests/test_s041.py`), or any classification of EGU graphs.
* Atlas unchanged: connected n≤6 **90 EGU / 8 non-EGU / 45 unresolved**.

## Independent checks

`tests/test_s041.py` (exact `Fraction`/`sympy`): the closed product equals an
independent memoryless first-bin recursion for all orders up to four clocks
(including n=0,1); exhaustive strict truncations lie below it within an exact
tail bound; the symbolic `δ→0⁺` limit equals the Plackett–Luce product for small
integer rates; the permutation pushforward equals an independent first-choice
recursion on P3, P4, C5, K1,3, K0, K1, sums to one and is supported on maximal
independent sets. These are finite checks of particular inputs, not proofs.
