import Mathlib

/-!
# Cubic AM-GM via a polynomial sum-of-squares certificate

One analytic ingredient needed for full formalisation of IG-N1 on C6.
This theorem alone does NOT formalise the random greedy probability
law or the six-factor C6 product inequality.
-/

namespace InverseGreedy

theorem triple_sum_cube_ge_27_mul (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * a * b * c ≤ (a + b + c) ^ 3 := by
  have hs : 0 ≤ a + b + c := by positivity
  have h₁ : 0 ≤ (a + b + c) * (a - b) ^ 2 :=
    mul_nonneg hs (sq_nonneg (a - b))
  have h₂ : 0 ≤ (a + b + c) * (b - c) ^ 2 :=
    mul_nonneg hs (sq_nonneg (b - c))
  have h₃ : 0 ≤ (a + b + c) * (c - a) ^ 2 :=
    mul_nonneg hs (sq_nonneg (c - a))
  have h₄ : 0 ≤ a * (b - c) ^ 2 :=
    mul_nonneg ha (sq_nonneg (b - c))
  have h₅ : 0 ≤ b * (c - a) ^ 2 :=
    mul_nonneg hb (sq_nonneg (c - a))
  have h₆ : 0 ≤ c * (a - b) ^ 2 :=
    mul_nonneg hc (sq_nonneg (a - b))
  -- Twice the difference equals the sum of h₁,h₂,h₃
  -- plus six times the sum of h₄,h₅,h₆.
  nlinarith [h₁, h₂, h₃, h₄, h₅, h₆]

end InverseGreedy
