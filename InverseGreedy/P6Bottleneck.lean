import Mathlib

/-!
# P6: algebraic bottleneck for two independent triple races

This theorem formalises the REAL-INEQUALITY contradiction after the
two event statements in proof/P6_OBSTRUCTION.md have been established.
It does not formalise the exponential race or greedy terminal law.
-/

namespace InverseGreedy

theorem p6_bottleneck_impossible (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hprod : u * v = (1:ℝ)/5)
    (hbound : (2:ℝ)/5 ≤ (1-u)*(1-v)) : False := by
  have hsum : u + v ≤ (4:ℝ)/5 := by nlinarith [hprod, hbound]
  have hnonneg : 0 ≤ u + v := add_nonneg hu hv
  have hsq : (u+v)^2 ≤ ((4:ℝ)/5)^2 := by
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hsum)]
  nlinarith [sq_nonneg (u-v)]



/-- Algebraic core of the quantitative P6 total-variation gap.
The variables u,v are the two independent triple-race probabilities;
δ bounds deviations of the singleton and doubleton output events
from the corresponding 1/5 and 2/5 values. This does not by itself
formalise the stochastic output law or the definition of TV distance. -/
theorem p6_tv_gap_from_race_bounds (u v δ : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hprod : (1:ℝ)/5 - δ ≤ u*v)
    (hcomp : (2:ℝ)/5 - δ ≤ (1-u)*(1-v)) :
    (1:ℝ)/25 ≤ δ := by
  by_contra hg
  have hd : δ < (1:ℝ)/25 := lt_of_not_ge hg
  have hp : (4:ℝ)/25 < u*v := by linarith
  have hc : (9:ℝ)/25 < (1-u)*(1-v) := by linarith
  have hs : (4:ℝ)/5 < u+v := by
    by_contra hn
    have hle : u+v ≤ (4:ℝ)/5 := le_of_not_gt hn
    have hnon : 0 ≤ u+v := add_nonneg hu hv
    have hsq : (u+v)^2 ≤ ((4:ℝ)/5)^2 := by
      nlinarith [mul_nonneg hnon (sub_nonneg.mpr hle)]
    nlinarith [sq_nonneg (u-v)]
  have hcs : (6:ℝ)/5 < (1-u)+(1-v) := by
    by_contra hn
    have hle : (1-u)+(1-v) ≤ (6:ℝ)/5 := le_of_not_gt hn
    have hnon : 0 ≤ (1-u)+(1-v) := by linarith
    have hsq : ((1-u)+(1-v))^2 ≤ ((6:ℝ)/5)^2 := by
      nlinarith [mul_nonneg hnon (sub_nonneg.mpr hle)]
    nlinarith [sq_nonneg ((1-u)-(1-v))]
  linarith

end InverseGreedy
