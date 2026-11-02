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


/-- The event of strictly distinct finite clock times is measurable.
This says nothing yet about the measure of its complement. -/
theorem finiteIndependentExp_pairwise_distinct_measurable
    {ι : Type*} [Fintype ι] :
    MeasurableSet {ω : ι → ℝ | ∀ i j, i ≠ j → ω i ≠ ω j} := by
  have hset :
      {ω : ι → ℝ | ∀ i j, i ≠ j → ω i ≠ ω j} =
        ⋂ i, ⋂ j, {ω : ι → ℝ | i ≠ j → ω i ≠ ω j} := by
    ext ω
    simp
  rw [hset]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases h : i = j
  · simp [h]
  · have heq :
        {ω : ι → ℝ | i ≠ j → ω i ≠ ω j} =
          {ω : ι → ℝ | ω i ≠ ω j} := by
      ext ω
      simp [h]
    rw [heq]
    exact (finiteIndependentExp_tie_measurable i j).compl

/-- For a chosen index, being strictly earlier than every other clock is
a measurable event in the genuine finite continuous probability space. -/
theorem finiteIndependentExp_first_winner_measurable
    {ι : Type*} [Fintype ι] (i : ι) :
    MeasurableSet {ω : ι → ℝ | ∀ j, j ≠ i → ω i < ω j} := by
  have hset :
      {ω : ι → ℝ | ∀ j, j ≠ i → ω i < ω j} =
        ⋂ j, {ω : ι → ℝ | j ≠ i → ω i < ω j} := by
    ext ω
    simp
  rw [hset]
  apply MeasurableSet.iInter
  intro j
  by_cases h : j = i
  · simp [h]
  · simpa [h] using finiteIndependentExp_lt_measurable i j

end InverseGreedy
