import InverseGreedy.ContinuousRacePartition
import InverseGreedy.FiniteIndependentExp

/-!
# S021: true continuous-rate swap and measurable finite race events

These statements concern the actual exponential product measures, not
the discrete Plackett-Luce priority law. They do not assert the still-open
unequal-rate numerical probability formula or finite chamber masses.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- Swapping two genuinely independent exponential clocks exchanges their
rates in the *continuous product law*. No equal-rate assumption is used. -/
theorem independentExpPair_swap_rates (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    Measure.map Prod.swap (independentExpPair r s) =
      independentExpPair s r := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  unfold independentExpPair
  exact Measure.prod_swap

/-- The chance that the second clock wins a race with rates (r,s)
equals the chance that the first wins the exchanged race (s,r).
This does not assume a Plackett-Luce first-choice probability. -/
theorem independentExpPair_reverse_eq_swapped (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    independentExpPair r s {p : ℝ × ℝ | p.2 < p.1} =
      independentExpPair s r {p : ℝ × ℝ | p.1 < p.2} := by
  have hA : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet
  calc
    independentExpPair r s {p : ℝ × ℝ | p.2 < p.1} =
        (Measure.map Prod.swap (independentExpPair r s))
          {p : ℝ × ℝ | p.1 < p.2} := by
      rw [Measure.map_apply measurable_swap hA]
      rfl
    _ = independentExpPair s r {p : ℝ × ℝ | p.1 < p.2} := by
      rw [independentExpPair_swap_rates r s hr hs]

/-- Every two-coordinate strict clock-comparison event is measurable on
the actual finite product clock space. -/
theorem finiteIndependentExp_lt_measurable {ι : Type*} [Fintype ι]
    (i j : ι) :
    MeasurableSet {ω : ι → ℝ | ω i < ω j} :=
  measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

/-- Every two-coordinate clock-equality event is measurable. -/
theorem finiteIndependentExp_tie_measurable {ι : Type*} [Fintype ι]
    (i j : ι) :
    MeasurableSet {ω : ι → ℝ | ω i = ω j} :=
  measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)

end InverseGreedy
