import InverseGreedy.FiniteRace

/-!
# S005: positive finite weighted-order laws

These are formal lemmas about the *algebraic* order weights.
They do not yet identify those weights with a product measure on
independent continuous exponential clocks, nor sum all permutation masses.
-/
namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

private theorem nonneg_rate_list_sum (rates : α → ℝ) (order : List α)
    (hrates : ∀ v, 0 < rates v) :
    0 ≤ (order.map rates).sum := by
  induction order with
  | nil => simp
  | cons v tail ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (le_of_lt (hrates v)) ih

/-- Every particular finite priority ordering has positive mass if all rates
are positive. This is not (yet) the total-permutation normalisation theorem. -/
theorem orderMass_pos (rates : α → ℝ) (order : List α)
    (hrates : ∀ v, 0 < rates v) :
    0 < orderMass rates order := by
  induction order with
  | nil => simp [orderMass]
  | cons v tail ih =>
    rw [orderMass_cons]
    exact mul_pos
      (div_pos (hrates v)
        (add_pos_of_pos_of_nonneg (hrates v)
          (nonneg_rate_list_sum rates tail hrates))) ih

/-- The conditional mass at an active vertex is strictly positive. -/
theorem firstChoice_pos_of_mem (rates : α → ℝ) (active : Finset α)
    (v : α) (hv : v ∈ active)
    (hrates : ∀ w ∈ active, 0 < rates w) :
    0 < firstChoice rates active v := by
  unfold firstChoice
  exact div_pos (hrates v hv) (activeRate_pos rates active ⟨v, hv⟩ hrates)

end InverseGreedy
