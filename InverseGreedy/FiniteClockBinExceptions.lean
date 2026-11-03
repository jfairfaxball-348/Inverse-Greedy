import InverseGreedy.ClockBins

/-!
# S033 companion: zero-bin nullity for every finite exponential family

The right-closed one-based ceiling-bin partition has an exceptional
bin zero, corresponding to nonpositive arrival times. S026 proved
this exceptional cell is null for one exponential clock; the results
below establish that none of the coordinates of an arbitrary finite
independent exponential family occupy bin zero, almost surely.

These statements use Mathlib's genuine continuous independent
exponential product measure, including empty and singleton index
types. No discrete priority permutation law is involved.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- The exceptional zero ceiling bin of any coordinate has zero mass
under the actual finite independent exponential measure. -/
theorem finiteIndependentExp_coordinate_zeroBin_null
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (i : ι) :
    finiteIndependentExp rates
      {ω : ι → ℝ | clockCeilBin δ (ω i) = 0} = 0 := by
  have hcell : MeasurableSet {t : ℝ | clockCeilBin δ t = 0} := by
    rw [clockCeilBin_preimage_zero δ hδ]
    exact measurableSet_Iic
  calc
    finiteIndependentExp rates
        {ω : ι → ℝ | clockCeilBin δ (ω i) = 0} =
      (Measure.map (fun ω : ι → ℝ => ω i) (finiteIndependentExp rates))
        {t : ℝ | clockCeilBin δ t = 0} := by
          rw [Measure.map_apply (measurable_pi_apply i) hcell]
          rfl
    _ = expMeasure (rates i) {t : ℝ | clockCeilBin δ t = 0} := by
      rw [finiteIndependentExp_coordinate_law rates hpos i]
    _ = 0 := expMeasure_clockCeilBin_zero (rates i) δ (hpos i) hδ

/-- The entire union of exceptional zero-bin events is null, including
the empty family (empty union). -/
theorem finiteIndependentExp_any_zeroBin_null
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteIndependentExp rates
      {ω : ι → ℝ | ∃ i, clockCeilBin δ (ω i) = 0} = 0 := by
  have hset :
      {ω : ι → ℝ | ∃ i, clockCeilBin δ (ω i) = 0} =
        ⋃ i, {ω : ι → ℝ | clockCeilBin δ (ω i) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  exact measure_iUnion_null (fun i =>
    finiteIndependentExp_coordinate_zeroBin_null rates hpos δ hδ i)

/-- All actual finite exponential coordinates lie in positive
(one-based) ceiling bins simultaneously, with probability one.
The assertion also holds for the unique empty family. -/
theorem finiteIndependentExp_all_positiveBins_probability_one
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteIndependentExp rates
      {ω : ι → ℝ | ∀ i, clockCeilBin δ (ω i) ≠ 0} = 1 := by
  letI : IsProbabilityMeasure (finiteIndependentExp rates) :=
    finiteIndependentExp_probability rates hpos
  let A : Set (ι → ℝ) :=
    {ω | ∀ i, clockCeilBin δ (ω i) ≠ 0}
  have hA : MeasurableSet A := by
    have hset : A =
        ⋂ i, {ω : ι → ℝ | clockCeilBin δ (ω i) ≠ 0} := by
      ext ω
      simp [A]
    rw [hset]
    apply MeasurableSet.iInter
    intro i
    have hzero : MeasurableSet
        {ω : ι → ℝ | clockCeilBin δ (ω i) = 0} := by
      change MeasurableSet
        ((fun ω : ι → ℝ => clockCeilBin δ (ω i)) ⁻¹' ({0} : Set ℕ))
      exact (finiteIndependentExp_clockCeilBin_measurable δ i)
        (measurableSet_singleton (0 : ℕ))
    simpa only [Set.compl_setOf] using hzero.compl
  have hcompl : Aᶜ =
      {ω : ι → ℝ | ∃ i, clockCeilBin δ (ω i) = 0} := by
    ext ω
    simp [A]
  have hnull : finiteIndependentExp rates Aᶜ = 0 := by
    rw [hcompl]
    exact finiteIndependentExp_any_zeroBin_null rates hpos δ hδ
  have hsum := measure_add_measure_compl (μ := finiteIndependentExp rates) hA
  rw [hnull] at hsum
  simpa [A] using hsum

end InverseGreedy
