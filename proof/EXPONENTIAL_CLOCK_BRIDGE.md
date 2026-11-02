# S019 — Independent exponential clocks and the weighted permutation law

**Status (2026-11-02):** Complete informal measure-theoretic argument
for the bridge; the all-vertex ordered-event theorem is **not**
yet in Lean. The S019 imported two-clock Lean module, when CI-verified,
constructs a genuine continuous product probability space, proves both
exponential marginals and independence. CI results and exact code SHA
must be recorded in `HANDOVER.md`; a successful build is not assumed.

## Setup and definitions

Let `V` be a finite vertex set. For each `v ∈ V` fix a real
rate `λ_v > 0`. On `Ω = ℝ^V` define the product probability
measure
`μ = ⨂_(v ∈ V) expMeasure(λ_v)`,
where Mathlib's `ProbabilityTheory.expMeasure` is a genuine measure
on the real line with density

`f_v(t) = λ_v e^(−λ_v t)` for `t ≥ 0`, and `0` for `t < 0`.

The coordinate projections `T_v(ω) = ω_v` are independent and have
these marginals by the product-measure construction. In particular
this model does **not** define the clocks by the discrete
Plackett–Luce recurrence.

The event for a permutation `π = (π₁, …, π_n)` is

`E_π = { ω : T_(π₁)(ω) < ⋯ < T_(π_n)(ω) }`.

This is a measurable event (finite intersection of strict real
inequalities).

## Theorem (mathematical; Lean bridge still open)

For each complete ordering `π` of `V`,

`μ(E_π) = ∏_(j=1)^n λ_(π_j) / (∑_(k=j)^n λ_(π_k)).`

Every denominator is strictly positive. When `n=0`, there is one
empty ordering and it has mass one.

### Proof

The joint measure has density
`∏_v f_v(t_v)` with respect to ordinary `n`-dimensional
Lebesgue measure. For each ordered chamber `E_π`, this yields

`μ(E_π) = (∏_(j=1)^n λ_(π_j)) ∫_(0<t₁<⋯<t_n)
    exp(−∑_(i=1)^n λ_(π_i)t_i) dt₁⋯dt_n`,

where the integration coordinates have been relabelled by `π`.
Introduce the increments

`u₁=t₁`, `u_j=t_j−t_(j−1)` for `j≥2`.

The triangular map from `(u₁,…,u_n)` to `(t₁,…,t_n)`
has determinant one; it maps the strictly positive orthant
bijectively onto the strict ordered chamber. Further,

`∑_(i=1)^n λ_(π_i)t_i
  = ∑_(j=1)^n (∑_(i=j)^n λ_(π_i)) u_j`.

Put `R_j = ∑_(i=j)^n λ_(π_i)>0`. Tonelli's theorem and
`∫₀∞ exp(−R_j u)du=1/R_j` factor the nonnegative integral,
giving the claimed product. The conventions for `n=0`
and `n=1` produce probability one for the only ordering.

**No ties:** The joint law has a density with respect to
Lebesgue measure and each hyperplane `t_v=t_w` for
`v≠w` has Lebesgue measure zero. A finite union of such
hyperplanes has measure zero. Thus, almost surely, there
is exactly one strict complete arrival ordering.

Consequently the pushforward by measurable finite sorting is
the weighted finite permutation measure with `orderMass`
from `InverseGreedy/FiniteRace.lean` for every full order.
By S018's verified Lean equality
`priorityOutputMass = finiteRaceLaw`, the probability of
every greedy accepted target is the same bounded recursion.

**This final conclusion is an informal theorem until Lean
constructs the full finite-product model, proves ordering
measurability/no ties, computes the event masses, and
combines them with the S018 formal discrete pushforward.**

## Lean obligations

1. **Two-clock model:** define `(expMeasure r).prod (expMeasure s)`,
   show it is a probability measure and that the coordinates
   have exponential marginals and are independent. Exact imported
   CI is necessary to call this Lean-verified.
2. **No ties:** prove the diagonal has measure zero
   (e.g. via non-atomicity of the exponential density and
   `Measure.measure_prod_null`), first for two clocks.
3. **First-arrival event:** prove
   `P(T_r<T_s) = r/(r+s)` directly from the joint measure.
   Merely restating a discrete first-choice formula is insufficient.
4. **Finite product:** instantiate `Measure.pi` over a finite
   indexed type; prove marginals, independence, unique a.s.
   sorting, and each complete ordering event's law.
5. **Pushforward:** establish sorting's event-law identity with
   the exact `orderMass` type and invoke
   `priorityOutputMass_eq_finiteRaceLaw`.
6. Track numerical or exact checks as regression tests **only**;
   none substitute for measure-theoretic Lean proofs.

## Pinned Mathlib interfaces examined

- `Mathlib/Probability/Distributions/Exponential.lean`:
  `expMeasure`, `isProbabilityMeasure_expMeasure`,
  `cdf_expMeasure_eq`.
- `Mathlib/Probability/Independence/Basic.lean`:
  `indepFun_prod` for actual product random variables.
- `Mathlib/MeasureTheory/Measure/Prod.lean`:
  `prod.instIsProbabilityMeasure`, `map_fst_prod`,
  `map_snd_prod`, `measure_prod_null`.
- `Mathlib/Probability/Distributions/Gamma.lean`:
  `gammaMeasure = volume.withDensity (gammaPDF ...)`;
  `expMeasure r = gammaMeasure 1 r`.
- `Mathlib/MeasureTheory/Measure/WithDensity.lean`:
  `withDensity_absolutelyContinuous`, `nullSingletonClass_withDensity`.

Checked against the project's pinned Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`; checking
declaration sources does not imply successful Lean compilation.

No new EGU classification, approximate-EGU claim, or novelty
certificate arises from this probabilistic bridge.
