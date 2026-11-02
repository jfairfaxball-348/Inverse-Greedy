import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# S019: genuine independent exponential clocks (two-clock foundation)

This module constructs a continuous product probability measure, not a
discrete Plackett–Luce distribution declared to be a clock law.

The arrival times are the two coordinate projections. Their marginals are
Mathlib's actual exponential distributions and they are independent.
The probability of one coordinate arriving before the other, the no-tie
statement, and the extension to finite indexed products are separate goals.
-/

open MeasureTheory ProbabilityTheory

namespace InverseGreedy

/-- Joint law of two independent exponential arrival times with rate
parameters `r` and `s`. Strict positivity is needed for it to be
a probability measure, but not for this definition itself. -/
noncomputable def independentExpPair (r s : ℝ) : Measure (ℝ × ℝ) :=
  (expMeasure r).prod (expMeasure s)

/-- Both positive exponential rates give a genuine probability space. -/
theorem independentExpPair_isProbability (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    IsProbabilityMeasure (independentExpPair r s) := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  unfold independentExpPair
  infer_instance

/-- The first clock has the actual rate-`r` exponential distribution. -/
theorem independentExpPair_fst_law (r s : ℝ)
    (hs : 0 < s) :
    Measure.map Prod.fst (independentExpPair r s) = expMeasure r := by
  letI : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  simp [independentExpPair]

/-- The second clock has the actual rate-`s` exponential distribution. -/
theorem independentExpPair_snd_law (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    Measure.map Prod.snd (independentExpPair r s) = expMeasure s := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  simp [independentExpPair]

/-- Under the joint exponential product measure the arrival times
are independent random variables, rather than postulated as such. -/
theorem independentExpPair_indep (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    IndepFun (fun ω : ℝ × ℝ => ω.1) (fun ω : ℝ × ℝ => ω.2)
      (independentExpPair r s) := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  change IndepFun (fun ω : ℝ × ℝ => ω.1) (fun ω : ℝ × ℝ => ω.2)
    ((expMeasure r).prod (expMeasure s))
  exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

/-- The exponential law has zero mass at each individual arrival time.
This follows from the actual density against real Lebesgue measure. -/
theorem expMeasure_point_null (rate x : ℝ) :
    expMeasure rate ({x} : Set ℝ) = 0 := by
  change ((volume : Measure ℝ).withDensity (gammaPDF 1 rate)) {x} = 0
  exact measure_singleton x

/-- Two independent exponential arrival times almost surely do not tie.
This is a genuine product-measure null-diagonal statement. -/
theorem independentExpPair_no_ties (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    independentExpPair r s {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  have hDiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  change (expMeasure r).prod (expMeasure s) {p : ℝ × ℝ | p.1 = p.2} = 0
  apply (Measure.measure_prod_null hDiag).2
  apply Filter.Eventually.of_forall
  intro x
  have hpre : (Prod.mk x) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
    ext y
    simp
  change (expMeasure s) ((Prod.mk x) ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0
  rw [hpre]
  exact expMeasure_point_null s x

end InverseGreedy
