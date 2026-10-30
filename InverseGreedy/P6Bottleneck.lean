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

end InverseGreedy
