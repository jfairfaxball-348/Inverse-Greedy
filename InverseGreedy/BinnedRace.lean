import InverseGreedy.ClockBins

/-!
# S027: true two-clock first-bin race cylinders

Every theorem here concerns the genuine Mathlib product measure of two
independent exponential arrival times. In particular, no discrete geometric
priority law is assumed. The strict-bin event is still a countable union of
these cylinders; its infinite sum and the continuous winner ratio are
separate obligations.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- The first exponential clock lies in positive ceiling bin `k+1`,
while the second clock remains beyond that bin's right endpoint. -/
def firstBinSurvivalEvent (δ : ℝ) (k : ℕ) : Set (ℝ × ℝ) :=
  {p | clockCeilBin δ p.1 = k + 1 ∧ ((k : ℝ) + 1) * δ < p.2}

/-- Each genuine first-bin survival cylinder is measurable. -/
theorem firstBinSurvivalEvent_measurable (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    MeasurableSet (firstBinSurvivalEvent δ k) := by
  have hcell : MeasurableSet {t : ℝ | clockCeilBin δ t = k + 1} := by
    rw [clockCeilBin_preimage_succ δ hδ k]
    exact measurableSet_Ioc
  change MeasurableSet
    ({t : ℝ | clockCeilBin δ t = k + 1} ×ˢ
      Set.Ioi (((k : ℝ) + 1) * δ))
  exact hcell.prod measurableSet_Ioi

/-- An exact probability for a nontrivial event of the *true* two-clock
product. It uses the genuine S026 ceiling-bin PMF and S024 survival law. -/
theorem independentExpPair_firstBinSurvival_mass
    (r s δ : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hδ : 0 < δ) (k : ℕ) :
    independentExpPair r s (firstBinSurvivalEvent δ k) =
      ENNReal.ofReal
        ((1 - Real.exp (-(r * δ))) *
          (Real.exp (-(r * δ))) ^ k) *
      ENNReal.ofReal
        (Real.exp (-(s * (((k : ℝ) + 1) * δ)))) := by
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (expMeasure s) :=
    isProbabilityMeasure_expMeasure hs
  have ht : 0 ≤ ((k : ℝ) + 1) * δ := by
    exact mul_nonneg (by positivity) (le_of_lt hδ)
  change (expMeasure r).prod (expMeasure s)
    ({t : ℝ | clockCeilBin δ t = k + 1} ×ˢ
      Set.Ioi (((k : ℝ) + 1) * δ)) = _
  rw [Measure.prod_prod]
  rw [expMeasure_clockCeilBin_succ r δ hr hδ k,
    expMeasure_Ioi_nonnegative s _ hs ht]

/-- A clock that finished its bin before the other clock arrived really
won the continuous race. This implication is exact, including endpoints. -/
theorem firstBinSurvivalEvent_subset_realWinner (δ : ℝ)
    (hδ : 0 < δ) (k : ℕ) :
    firstBinSurvivalEvent δ k ⊆ {p : ℝ × ℝ | p.1 < p.2} := by
  intro p hp
  change clockCeilBin δ p.1 = k + 1 ∧
    ((k : ℝ) + 1) * δ < p.2 at hp
  have hcell :=
    (Set.ext_iff.mp (clockCeilBin_preimage_succ δ hδ k) p.1).mp hp.1
  exact lt_of_le_of_lt hcell.2 hp.2

/-- Corresponding measure-level lower bound under the actual joint law. -/
theorem independentExpPair_firstBinSurvival_le_realWinner
    (r s δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    independentExpPair r s (firstBinSurvivalEvent δ k) ≤
      independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} :=
  measure_mono (firstBinSurvivalEvent_subset_realWinner δ hδ k)

end InverseGreedy
