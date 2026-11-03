import InverseGreedy.FiniteClockChambers

/-!
# S024: exact survival of genuine exponential clocks

These statements concern Mathlib's actual real-valued exponential
probability measure, and its genuine finite product, not a discrete
priority-order law.  They are the first analytic prerequisites for the
geometric-bin argument of S023.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- The CDF of an actual exponential clock, expressed as an ENNReal
measure.  This is the nonnegative-time branch of Mathlib's CDF theorem. -/
theorem expMeasure_Iic_nonnegative (rate t : ℝ)
    (hr : 0 < rate) (ht : 0 ≤ t) :
    expMeasure rate (Set.Iic t) =
      ENNReal.ofReal (1 - Real.exp (-(rate * t))) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hr
  calc
    expMeasure rate (Set.Iic t) =
        ENNReal.ofReal ((cdf (expMeasure rate)) t) :=
      (ofReal_cdf (expMeasure rate) t).symm
    _ = ENNReal.ofReal (1 - Real.exp (-(rate * t))) := by
      rw [cdf_expMeasure_eq hr t, if_pos ht]

/-- The genuine exponential clock puts no mass on the negative-time
lower tail; this is the distinct negative-time branch of its CDF. -/
theorem expMeasure_Iic_negative (rate t : ℝ)
    (hr : 0 < rate) (ht : t < 0) :
    expMeasure rate (Set.Iic t) = 0 := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hr
  calc
    expMeasure rate (Set.Iic t) =
        ENNReal.ofReal ((cdf (expMeasure rate)) t) :=
      (ofReal_cdf (expMeasure rate) t).symm
    _ = 0 := by
      rw [cdf_expMeasure_eq hr t, if_neg (not_le.mpr ht)]
      simp

/-- Exact survival probability from the actual exponential measure
at any nonnegative real time, not from a geometric surrogate. -/
theorem expMeasure_Ioi_nonnegative (rate t : ℝ)
    (hr : 0 < rate) (ht : 0 ≤ t) :
    expMeasure rate (Set.Ioi t) =
      ENNReal.ofReal (Real.exp (-(rate * t))) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hr
  have hle : Real.exp (-(rate * t)) ≤ (1 : ℝ) :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (le_of_lt hr) ht])
  have hsub : 0 ≤ (1 : ℝ) - Real.exp (-(rate * t)) :=
    sub_nonneg.mpr hle
  calc
    expMeasure rate (Set.Ioi t) =
        expMeasure rate ((Set.Iic t)ᶜ) := by rw [Set.compl_Iic]
    _ = 1 - expMeasure rate (Set.Iic t) := by
      rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
    _ = 1 - ENNReal.ofReal (1 - Real.exp (-(rate * t))) := by
      rw [expMeasure_Iic_nonnegative rate t hr ht]
    _ = ENNReal.ofReal (Real.exp (-(rate * t))) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) hsub]
      congr 1
      ring

/-- Exponential clocks have no negative arrival times. -/
theorem expMeasure_negative_time_null (rate : ℝ) (hr : 0 < rate) :
    expMeasure rate (Set.Iio (0 : ℝ)) = 0 := by
  have hzero : expMeasure rate (Set.Iic (0 : ℝ)) = 0 := by
    simpa using expMeasure_Iic_nonnegative rate 0 hr (le_refl 0)
  apply le_antisymm
  · calc
      expMeasure rate (Set.Iio (0 : ℝ)) ≤
          expMeasure rate (Set.Iic (0 : ℝ)) :=
        measure_mono (by intro x hx; exact le_of_lt hx)
      _ = 0 := hzero
  · exact zero_le _

/-- A coordinate of the *genuine finite independent product* retains
the exact exponential survival law (also for a singleton index type). -/
theorem finiteIndependentExp_coordinate_survival {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (i : ι) (t : ℝ) (ht : 0 ≤ t) :
    finiteIndependentExp rates {ω : ι → ℝ | t < ω i} =
      ENNReal.ofReal (Real.exp (-(rates i * t))) := by
  calc
    finiteIndependentExp rates {ω : ι → ℝ | t < ω i} =
        (Measure.map (Function.eval i) (finiteIndependentExp rates))
          (Set.Ioi t) := by
      rw [Measure.map_apply (measurable_pi_apply i) measurableSet_Ioi]
      rfl
    _ = expMeasure (rates i) (Set.Ioi t) := by
      rw [finiteIndependentExp_coordinate_law rates hpos i]
    _ = ENNReal.ofReal (Real.exp (-(rates i * t))) :=
      expMeasure_Ioi_nonnegative (rates i) t (hpos i) ht

end InverseGreedy
