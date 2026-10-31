import InverseGreedy.FullPermutationSupport

/-!
# S009: strict algebraic minor for the P3 pendant corona

This module kernel-checks the positive rational factorisation
under strictly positive rates. It does NOT prove that the terms
are the independent-clock greedy output probabilities.
The probabilistic event factorisation is proved on paper in
proof/CORONA_P3_OBSTRUCTION.md, and tested independently in Python.
-/

namespace InverseGreedy

/-- Conditional probability that the middle centre loses to the
middle leaf or to end-centre winners of total rate t. -/
noncomputable def coronaP3Survival (b B t : ℝ) : ℝ :=
  (B + t) / (b + B + t)

/-- Exact algebraic factorisation of the four-corner determinant. -/
theorem coronaP3_survival_cross_identity (b B u v : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hu : 0 < u) (hv : 0 < v) :
    coronaP3Survival b B u * coronaP3Survival b B v -
      coronaP3Survival b B 0 * coronaP3Survival b B (u + v) =
      (b * u * v * (2 * B + b + u + v)) /
        ((b + B) * (b + B + u) * (b + B + v) *
          (b + B + u + v)) := by
  have h0 : b + B ≠ 0 := ne_of_gt (add_pos hb hB)
  have h1 : b + B + u ≠ 0 := ne_of_gt (add_pos (add_pos hb hB) hu)
  have h2 : b + B + v ≠ 0 := ne_of_gt (add_pos (add_pos hb hB) hv)
  have h3 : b + B + u + v ≠ 0 :=
    ne_of_gt (add_pos (add_pos (add_pos hb hB) hu) hv)
  unfold coronaP3Survival
  field_simp [h0, h1, h2, h3, add_assoc]
  <;> ring

/-- The conditional middle-centre rejection factor has a strict
log-submodularity-type four-corner inequality. -/
theorem coronaP3_survival_cross_pos (b B u v : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hu : 0 < u) (hv : 0 < v) :
    0 < coronaP3Survival b B u * coronaP3Survival b B v -
      coronaP3Survival b B 0 * coronaP3Survival b B (u + v) := by
  rw [coronaP3_survival_cross_identity b B u v hb hB hu hv]
  positivity

/-- Strict algebraic probability minor for four corner events:
x,y are independent end-centre pair-winning probabilities. -/
theorem coronaP3_strict_minor (x y b B u v : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1)
    (hb : 0 < b) (hB : 0 < B) (hu : 0 < u) (hv : 0 < v) :
    ((x * (1 - y)) * coronaP3Survival b B u) *
        (((1 - x) * y) * coronaP3Survival b B v) >
      (((1 - x) * (1 - y)) * coronaP3Survival b B 0) *
        ((x * y) * coronaP3Survival b B (u + v)) := by
  have hfactor : 0 < x * (1 - x) * y * (1 - y) := by
    have hxx : 0 < 1 - x := by linarith
    have hyy : 0 < 1 - y := by linarith
    positivity
  have hcross := sub_pos.mp
    (coronaP3_survival_cross_pos b B u v hb hB hu hv)
  calc
    ((x * (1 - y)) * coronaP3Survival b B u) *
        (((1 - x) * y) * coronaP3Survival b B v) =
      (x * (1 - x) * y * (1 - y)) *
        (coronaP3Survival b B u * coronaP3Survival b B v) := by ring
    _ > (x * (1 - x) * y * (1 - y)) *
        (coronaP3Survival b B 0 * coronaP3Survival b B (u + v)) :=
      mul_lt_mul_of_pos_left hcross hfactor
    _ = (((1 - x) * (1 - y)) * coronaP3Survival b B 0) *
        ((x * y) * coronaP3Survival b B (u + v)) := by ring

end InverseGreedy
