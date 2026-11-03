import InverseGreedy.FiniteClockBinChambers

/-!
# S033: measured same-bin pair bound inside any finite exponential family

This transports the S029 genuine two-coordinate collision estimate
through S022's genuine marginal pair-law. It applies with arbitrarily
many other exponential clocks present, without discretely postulating
a weighted order distribution. In combination with a finite union
bound, it controls the error term in the strict chamber sandwich.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- Actual finite-coordinate exponential clock bins coincide with
probability at most bin width times the smaller of the two rates,
for distinct coordinates and all strictly positive rate vectors. -/
theorem finiteIndependentExp_pair_sameCeilBin_le_width_min_rate
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) (i j : ι) (hij : i ≠ j)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteIndependentExp rates
      {ω : ι → ℝ | clockCeilBin δ (ω i) = clockCeilBin δ (ω j)} ≤
      ENNReal.ofReal (δ * min (rates i) (rates j)) := by
  let F : (ι → ℝ) → ℝ × ℝ := fun ω => (ω i, ω j)
  have hF : Measurable F :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hbox : MeasurableSet (sameCeilBinEvent δ) := by
    exact measurableSet_eq_fun
      ((clockCeilBin_measurable δ).comp measurable_fst)
      ((clockCeilBin_measurable δ).comp measurable_snd)
  calc
    finiteIndependentExp rates
        {ω : ι → ℝ | clockCeilBin δ (ω i) = clockCeilBin δ (ω j)} =
        (Measure.map F (finiteIndependentExp rates))
          (sameCeilBinEvent δ) := by
      rw [Measure.map_apply hF hbox]
      rfl
    _ = independentExpPair (rates i) (rates j) (sameCeilBinEvent δ) := by
      rw [finiteIndependentExp_pair_law rates hpos i j hij]
    _ ≤ ENNReal.ofReal (δ * min (rates i) (rates j)) :=
      independentExpPair_sameCeilBin_le_width_min_rate
        (rates i) (rates j) δ (hpos i) (hpos j) hδ

end InverseGreedy
