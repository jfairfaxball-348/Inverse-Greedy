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

/-- Genuine independent exponential clocks have the unequal-rate
winner probability r/(r+s). This is obtained by squeezing the *actual*
product measure between measured ceiling-bin winner and collision events,
using the verified real exponential limit and the O(width) collision bound. -/
theorem independentExpPair_realWinner_rateRatio (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} =
      ENNReal.ofReal (r / (r + s)) := by
  let P : ENNReal := independentExpPair r s {p : ℝ × ℝ | p.1 < p.2}
  let F : ℝ → ENNReal := fun δ =>
    ENNReal.ofReal
      (((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
        (1 - Real.exp (-((r + s) * δ))))
  let C : ℝ → ENNReal := fun δ => ENNReal.ofReal (δ * min r s)
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (r / (r + s)))) :=
    continuous_bin_winner_ennreal_tendsto r s hr hs
  have hrealC :
      Tendsto (fun δ : ℝ => δ * min r s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ => δ * min r s) := by fun_prop
    simpa using
      (hc.continuousAt (0 : ℝ)).tendsto.mono_left nhdsWithin_le_nhds
  have hC : Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [C] using ENNReal.tendsto_ofReal hrealC
  have hFC :
      Tendsto (fun δ : ℝ => F δ + C δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (r / (r + s)))) := by
    simpa using hF.add hC
  have hlo : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), F δ ≤ P := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (independentExpPair_realWinner_fraction_sandwich r s δ
      hr hs hδ).1
  have hhi : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), P ≤ F δ + C δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hm := (independentExpPair_realWinner_bin_sandwich
      r s δ hr hs hδ).2
    have hbin := independentExpPair_strictCeilBinRace_realFraction
      r s δ hr hs hδ
    calc
      P ≤ independentExpPair r s (strictCeilBinRaceEvent δ) +
          independentExpPair r s (sameCeilBinEvent δ) := hm
      _ = F δ + independentExpPair r s (sameCeilBinEvent δ) := by
        rw [hbin]
      _ ≤ F δ + C δ := add_le_add_left
        (independentExpPair_sameCeilBin_le_width_min_rate
          r s δ hr hs hδ) _
  have hpin :
      Tendsto (fun _ : ℝ => P)
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (r / (r + s)))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hF hFC hlo hhi
  have hconst : Tendsto (fun _ : ℝ => P) (𝓝[>] (0 : ℝ)) (𝓝 P) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique hconst hpin

end InverseGreedy
