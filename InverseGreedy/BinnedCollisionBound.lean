import InverseGreedy.ContinuousRaceSandwich

/-!
# S029: quantitative true-exponential ceiling-bin collision bound

Starting from S028's exact genuine-product-measure real fraction,
derive a linear-in-bin-width bound. The proof separates elementary
geometric-fraction inequalities from the actual exponential clock
measure and works for arbitrary positive real rates and widths.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

private theorem geometric_collision_fraction_le_first (q t : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((1 - q) * (1 - t)) / (1 - q * t) ≤ 1 - q := by
  have hqt : q * t ≤ t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hq1)) ht0]
  have hden : 0 < 1 - q * t := by linarith
  have hfac : 0 ≤ 1 - q := by linarith
  have hinner : 1 - t ≤ 1 - q * t := by linarith
  exact (div_le_iff₀ hden).mpr
    (mul_le_mul_of_nonneg_left hinner hfac)

/-- The collision probability for two *actual* independent exponential
clocks is bounded by δ times the smaller rate, with no integer-rate or
small-width restriction. This is a measured event, not a binned proxy. -/
theorem independentExpPair_sameCeilBin_le_width_min_rate
    (r s δ : ℝ) (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (sameCeilBinEvent δ) ≤
      ENNReal.ofReal (δ * min r s) := by
  let q : ℝ := Real.exp (-(r * δ))
  let t : ℝ := Real.exp (-(s * δ))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
    nlinarith [mul_pos hr hδ])
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by
    nlinarith [mul_pos hs hδ])
  have hprod : Real.exp (-((r + s) * δ)) = q * t := by
    dsimp [q,t]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmass :
      independentExpPair r s (sameCeilBinEvent δ) =
        ENNReal.ofReal (((1 - q) * (1 - t)) / (1 - q * t)) := by
    simpa only [hprod] using
      independentExpPair_sameCeilBin_realFraction r s δ hr hs hδ
  have hfirst : ((1 - q) * (1 - t)) / (1 - q * t) ≤ r * δ := by
    have hcore := geometric_collision_fraction_le_first q t hq0 hq1 ht0 ht1
    have hlin : 1 - q ≤ r * δ := by
      dsimp [q]
      have he := Real.add_one_le_exp (-(r * δ))
      linarith
    exact le_trans hcore hlin
  have hsecond : ((1 - q) * (1 - t)) / (1 - q * t) ≤ s * δ := by
    have hcore := geometric_collision_fraction_le_first t q ht0 ht1 hq0 hq1
    have hsymmetric :
        ((1 - q) * (1 - t)) / (1 - q * t) ≤ 1 - t := by
      convert hcore using 1 <;> ring
    have hlin : 1 - t ≤ s * δ := by
      dsimp [t]
      have he := Real.add_one_le_exp (-(s * δ))
      linarith
    exact le_trans hsymmetric hlin
  have hreal : ((1 - q) * (1 - t)) / (1 - q * t) ≤ δ * min r s := by
    rcases le_total r s with hrs | hsr
    · rw [min_eq_left hrs, mul_comm δ r]
      exact hfirst
    · rw [min_eq_right hsr, mul_comm δ s]
      exact hsecond
  rw [hmass]
  exact ENNReal.ofReal_le_ofReal hreal

end InverseGreedy
