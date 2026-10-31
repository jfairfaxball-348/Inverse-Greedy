import Mathlib

/-!
# S012: a positive-rate P5 family approaching exact uniformity

For the five-vertex path at rates (1,1,t,1,1), t>0, the paper proof
computes its four output probabilities via the finite first-choice
recurrence, and their total-variation distance to the uniform four-MIS
law. Here we formalise only the algebraic identity and quantitative
small-t estimate. Identification with the actual greedy probability
law and its exact nonuniformity are separate mathematical results.
-/

namespace InverseGreedy

/-- Pure rational identity behind the P5 symmetric-rate TV formula. -/
theorem p5_boundary_tv_formula (t : ℝ) (ht : 0 < t) :
    (3 : ℝ) / 4 - 1 / (t + 2) - 1 / (t + 4) =
      t * (3*t + 10) / (4 * (t + 2) * (t + 4)) := by
  have h2 : t + 2 ≠ 0 := ne_of_gt (by linarith)
  have h4 : t + 4 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The rational P5 uniformity error is positive for finite t>0. -/
theorem p5_boundary_tv_pos (t : ℝ) (ht : 0 < t) :
    0 < t * (3*t + 10) / (4 * (t + 2) * (t + 4)) := by
  apply div_pos
  · exact mul_pos ht (by linarith)
  · positivity

/-- An explicit positive-rate approach to zero: error < 5t/16.
The limit follows by the ordinary squeeze theorem on paper. -/
theorem p5_boundary_tv_lt_linear (t : ℝ) (ht : 0 < t) :
    t * (3*t + 10) / (4 * (t + 2) * (t + 4)) <
      (5 : ℝ) / 16 * t := by
  have hden : 0 < 4 * (t + 2) * (t + 4) := by positivity
  have ht2 : 0 < t * t := mul_pos ht ht
  have ht3 : 0 < t * (t * t) := mul_pos ht ht2
  apply (div_lt_iff₀ hden).2
  nlinarith

end InverseGreedy
