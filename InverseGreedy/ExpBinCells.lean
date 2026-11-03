import InverseGreedy.ExpSurvival

/-!
# S025: actual exponential mass of geometric bin cells

These theorems compute probabilities of concrete real half-open clock
intervals under Mathlib's genuine exponential measure. No discrete
geometric law or Plackett–Luce priority-order measure is assumed.
The cell event is (k*δ, (k+1)*δ], so endpoint conventions are explicit.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- Genuine exponential mass between two nonnegative time thresholds,
deduced from the actual survival measure rather than a stipulated
geometric distribution. -/
theorem expMeasure_Ioc_nonnegative (rate a b : ℝ)
    (hr : 0 < rate) (ha : 0 ≤ a) (hab : a ≤ b) :
    expMeasure rate (Set.Ioc a b) =
      ENNReal.ofReal
        (Real.exp (-(rate * a)) - Real.exp (-(rate * b))) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hr
  have hset : Set.Ioi a \ Set.Ioi b = Set.Ioc a b := by
    ext x
    simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_lt]
  calc
    expMeasure rate (Set.Ioc a b) =
        expMeasure rate (Set.Ioi a \ Set.Ioi b) := by rw [hset]
    _ = expMeasure rate (Set.Ioi a) - expMeasure rate (Set.Ioi b) := by
      rw [measure_diff measurableSet_Ioi measurableSet_Ioi]
    _ = ENNReal.ofReal
          (Real.exp (-(rate * a)) - Real.exp (-(rate * b))) := by
      rw [expMeasure_Ioi_nonnegative rate a hr ha,
        expMeasure_Ioi_nonnegative rate b hr (le_trans ha hab)]
      rw [← ENNReal.ofReal_sub (Real.exp (-(rate * a)))
        (le_of_lt (Real.exp_pos _))]

/-- Every genuine exponential clock cell has geometric mass. This is
a theorem about *real intervals*, not a separately postulated
natural-number-valued bin random variable. -/
theorem expMeasure_geometric_cell (rate δ : ℝ)
    (hr : 0 < rate) (hδ : 0 < δ) (k : ℕ) :
    expMeasure rate
        (Set.Ioc ((k : ℝ) * δ) (((k : ℝ) + 1) * δ)) =
      ENNReal.ofReal
        ((1 - Real.exp (-(rate * δ))) *
          (Real.exp (-(rate * δ))) ^ k) := by
  have hleft : 0 ≤ (k : ℝ) * δ :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ)
  have hright : (k : ℝ) * δ ≤ ((k : ℝ) + 1) * δ := by
    nlinarith
  rw [expMeasure_Ioc_nonnegative rate _ _ hr hleft hright]
  apply congrArg ENNReal.ofReal
  have hpow (n : ℕ) :
      Real.exp (-(rate * ((n : ℝ) * δ))) =
        (Real.exp (-(rate * δ))) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have heq : -(rate * (((n + 1 : ℕ) : ℝ) * δ)) =
          -(rate * ((n : ℝ) * δ)) + -(rate * δ) := by
        push_cast
        ring
      rw [heq, Real.exp_add, ih, pow_succ]
  have hk : ((k : ℝ) + 1) * δ = (((k + 1 : ℕ) : ℝ) * δ) := by
    push_cast
    ring
  calc
    Real.exp (-(rate * ((k : ℝ) * δ))) -
        Real.exp (-(rate * (((k : ℝ) + 1) * δ))) =
      Real.exp (-(rate * ((k : ℝ) * δ))) -
        Real.exp (-(rate * (((k + 1 : ℕ) : ℝ) * δ))) := by rw [hk]
    _ = (Real.exp (-(rate * δ))) ^ k -
          (Real.exp (-(rate * δ))) ^ (k + 1) := by
      rw [hpow k, hpow (k + 1)]
    _ = (1 - Real.exp (-(rate * δ))) *
          (Real.exp (-(rate * δ))) ^ k := by
      rw [pow_succ]
      ring

end InverseGreedy
