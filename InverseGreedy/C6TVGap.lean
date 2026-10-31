import InverseGreedy.C6Product

/-!
# S012: positive total-variation deficit from the C6 pair-product bound

If three event probabilities have product at most 1/729, then at least
one is at most 1/9. A five-outcome uniform law assigns 1/5 to each,
so the single-event probability deficit is at least 4/45.

This is pure algebra applied to the C6 pair-product formula. The
independent exponential-clock event identification and full total
variation measure have not been formalised in this module.
-/
namespace InverseGreedy

/-- Product of three real numbers bounded by (1/9)^3 forces at least
one of them to be at most 1/9. -/
theorem three_probs_one_small (p q r : ℝ)
    (hproduct : p * q * r ≤ (1 : ℝ) / 729) :
    p ≤ (1 : ℝ) / 9 ∨ q ≤ (1 : ℝ) / 9 ∨
      r ≤ (1 : ℝ) / 9 := by
  by_contra hn
  push_neg at hn
  rcases hn with ⟨hp, hq, hr⟩
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hab : (1 : ℝ) / 9 * ((1 : ℝ) / 9) < p * q := by
    calc
      (1 : ℝ) / 9 * ((1 : ℝ) / 9) <
          p * ((1 : ℝ) / 9) :=
            mul_lt_mul_of_pos_right hp (by norm_num)
      _ < p * q := mul_lt_mul_of_pos_left hq hp0
  have habc : (1 : ℝ) / 9 * ((1 : ℝ) / 9) * ((1 : ℝ) / 9) <
      p * q * r := by
    calc
      (1 : ℝ) / 9 * ((1 : ℝ) / 9) * ((1 : ℝ) / 9) <
          (p * q) * ((1 : ℝ) / 9) :=
            mul_lt_mul_of_pos_right hab (by norm_num)
      _ < p * q * r := mul_lt_mul_of_pos_left hr (mul_pos hp0 hq0)
  norm_num at habc
  linarith

/-- At least one of three C6 pair probabilities has an explicit
deficit relative to the five-element uniform law. -/
theorem three_probs_uniform_deficit (p q r : ℝ)
    (hproduct : p * q * r ≤ (1 : ℝ) / 729) :
    (1 : ℝ) / 5 - p ≥ 4 / 45 ∨
      (1 : ℝ) / 5 - q ≥ 4 / 45 ∨
      (1 : ℝ) / 5 - r ≥ 4 / 45 := by
  rcases three_probs_one_small p q r hproduct with h | h | h
  · left; linarith
  · right; left; linarith
  · right; right; linarith

end InverseGreedy
