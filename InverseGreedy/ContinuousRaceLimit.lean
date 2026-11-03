import InverseGreedy.BinnedCollisionBound
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# S030: the small-width analytic exponential-race limit

This module uses differentiability of the real exponential. The functions
are genuine real exponential fractions already proved to be the bin-event
probabilities for the actual independent-clock product measure in S028.
-/

open MeasureTheory ProbabilityTheory Filter
namespace InverseGreedy

/-- The initial slope of the exponential CDF is its positive real rate.
The one-sided limit is stated explicitly for widths approaching zero
from above. -/
theorem exponential_cdf_initial_slope (a : ℝ) :
    Tendsto (fun δ : ℝ => (1 - Real.exp (-(a * δ))) / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  have hlin : HasDerivAt (fun t : ℝ => -(a * t)) (-a) (0 : ℝ) := by
    convert (hasDerivAt_id (0 : ℝ)).mul_const (-a) using 1 <;> ring
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(a * t)))
      (-a) (0 : ℝ) := by
    convert (Real.hasDerivAt_exp (-(a * 0))).comp 0 hlin using 1 <;>
      simp [Real.exp_zero]
  have hderiv : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(a * t)))
      a (0 : ℝ) := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hexp using 1 <;>
      simp [Real.exp_zero]
  have h := hderiv.tendsto_slope_zero_right
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- The true binned-race winner fraction converges to the continuous
rate ratio. This is an analytic theorem over arbitrary positive real
rates, independently of any discrete proxy probability space. -/
theorem continuous_bin_winner_fraction_tendsto (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    Tendsto
      (fun δ : ℝ =>
        ((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
          (1 - Real.exp (-((r + s) * δ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (r / (r + s))) := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hslope :
      Tendsto
        (fun δ : ℝ =>
          ((1 - Real.exp (-(r * δ))) / δ) /
            ((1 - Real.exp (-((r + s) * δ))) / δ))
        (𝓝[>] (0 : ℝ)) (𝓝 (r / (r + s))) :=
    (exponential_cdf_initial_slope r).div
      (exponential_cdf_initial_slope (r + s)) hrs
  have hc : Continuous (fun δ : ℝ => Real.exp (-(s * δ))) := by fun_prop
  have hExp :
      Tendsto (fun δ : ℝ => Real.exp (-(s * δ)))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (hc.continuousAt (0 : ℝ)).tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have hProd := hslope.mul hExp
  have hEq :
      (fun δ : ℝ =>
        (((1 - Real.exp (-(r * δ))) / δ) /
          ((1 - Real.exp (-((r + s) * δ))) / δ)) *
          Real.exp (-(s * δ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ =>
        ((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
          (1 - Real.exp (-((r + s) * δ)))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : 0 < δ := hδ
    have hd : 1 - Real.exp (-((r + s) * δ)) ≠ 0 := by
      have he : Real.exp (-((r + s) * δ)) < 1 :=
        Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos (add_pos hr hs) hδ'])
      linarith
    have hδne : δ ≠ 0 := ne_of_gt hδ'
    field_simp
  have ht := hProd.congr' hEq
  simpa using ht

/-- The same real-analytic limit transported to extended nonnegative
probabilities, with no proxy probability space. -/
theorem continuous_bin_winner_ennreal_tendsto (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    Tendsto
      (fun δ : ℝ => ENNReal.ofReal
        (((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
          (1 - Real.exp (-((r + s) * δ)))))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (r / (r + s)))) :=
  ENNReal.tendsto_ofReal (continuous_bin_winner_fraction_tendsto r s hr hs)

end InverseGreedy
