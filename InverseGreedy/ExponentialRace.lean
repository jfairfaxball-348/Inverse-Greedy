import Mathlib

/-!
# Inverse Greedy: algebraic foundations

The C6 nonuniformity inequality is currently proved on paper, NOT yet Lean
formalised. This file formalises the elementary C6 pair-law identity.
-/

namespace InverseGreedy

theorem c6_pair_probability_algebra (a d A D : ℝ)
    (hTotal : A + D ≠ 0)
    (hEven : A - a + d ≠ 0)
    (hOdd : D - d + a ≠ 0) :
    a / (A + D) * (d / (A - a + d)) +
      d / (A + D) * (a / (D - d + a)) =
      a * d / ((A - a + d) * (D - d + a)) := by
  field_simp [hTotal, hEven, hOdd]
  <;> ring

end InverseGreedy
