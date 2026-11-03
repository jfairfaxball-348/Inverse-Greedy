import InverseGreedy.FiniteClockJointBins
import InverseGreedy.BinnedCollisionBound

/-!
# S033 companion: genuine finite-family bin exceptional events

S032 establishes individual joint positive-bin cylinders. This module
handles the genuine zero-bin exception and transports S029's continuous
two-clock bin-collision bound to arbitrary pairs of coordinates in a
finite independent family. No discrete PL priority law is assumed.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- The one-based ceiling-bin convention has a null zero bin in
every coordinate of an actual independent exponential family. -/
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

/-- The union of all zero-bin exceptional coordinate events is null,
including empty and singleton index types. -/
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

/-- The actual same-bin event for two real clocks is measurable.
The proof uses an explicit countable union of equal integer cells. -/
theorem sameCeilBinEvent_measurable (δ : ℝ) :
    MeasurableSet (sameCeilBinEvent δ) := by
  have hf : Measurable (fun p : ℝ × ℝ => clockCeilBin δ p.1) :=
    (clockCeilBin_measurable δ).comp measurable_fst
  have hg : Measurable (fun p : ℝ × ℝ => clockCeilBin δ p.2) :=
    (clockCeilBin_measurable δ).comp measurable_snd
  have hset : sameCeilBinEvent δ =
      ⋃ k : ℕ, {p : ℝ × ℝ |
        clockCeilBin δ p.1 = k ∧ clockCeilBin δ p.2 = k} := by
    ext p
    simp only [sameCeilBinEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨clockCeilBin δ p.1, rfl, h.symm⟩
    · rintro ⟨k, h₁, h₂⟩
      exact h₁.trans h₂.symm
  rw [hset]
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_singleton.preimage hf).inter
    (measurableSet_singleton.preimage hg)

/-- The two-coordinate collision estimate holds inside *any* finite
independent exponential clock family, not only the two-clock product. -/
theorem finiteIndependentExp_pair_sameBin_le_width_min_rate
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ)
    (i j : ι) (hij : i ≠ j) :
    finiteIndependentExp rates
      {ω : ι → ℝ |
        clockCeilBin δ (ω i) = clockCeilBin δ (ω j)} ≤
      ENNReal.ofReal (δ * min (rates i) (rates j)) := by
  let F : (ι → ℝ) → ℝ × ℝ := fun ω => (ω i, ω j)
  have hF : Measurable F :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  calc
    finiteIndependentExp rates
        {ω : ι → ℝ |
          clockCeilBin δ (ω i) = clockCeilBin δ (ω j)} =
        (Measure.map F (finiteIndependentExp rates))
          (sameCeilBinEvent δ) := by
            rw [Measure.map_apply hF (sameCeilBinEvent_measurable δ)]
            rfl
    _ = independentExpPair (rates i) (rates j) (sameCeilBinEvent δ) := by
      rw [finiteIndependentExp_pair_law rates hpos i j hij]
    _ ≤ ENNReal.ofReal (δ * min (rates i) (rates j)) :=
      independentExpPair_sameCeilBin_le_width_min_rate
        (rates i) (rates j) δ (hpos i) (hpos j) hδ

end InverseGreedy
