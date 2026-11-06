import InverseGreedy.ApproximateEGU

/-!
# S042: finite total-variation bound from pointwise mass lower bounds

This lemma is a reusable component for the fast-pair proof of approximate
EGU. It does NOT, on its own, prove the family-wide star-corona AEGU
theorem. That still requires a Lean proof of the hub/leaf first-step lower
bound, and of the exact star-corona MIS cardinality.
-/

open Finset

namespace InverseGreedy

/-- If every maximal independent set receives at least mass `q`, and
`q` is at most the uniform mass, the total-variation distance from
uniform is at most `1 - |MIS| * q`. Uses the *genuine real-clock* law. -/
theorem realClockTV_le_of_pointwise_lower_bound {α : Type*}
    [Fintype α] [DecidableEq α]
    (nb : α → Finset α)
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (hi : ∀ v, v ∉ nb v)
    (r : α → ℝ) (hr : ∀ v, 0 < r v) (q : ℝ)
    (hq : q ≤ 1 / ((maximalIndependentSets nb).card : ℝ))
    (hmin : ∀ I ∈ maximalIndependentSets nb, q ≤ realClockProb nb r I) :
    realClockTV nb r ≤ 1 - ((maximalIndependentSets nb).card : ℝ) * q := by
  rw [realClockTV_eq_negParts nb hs hi r hr]
  have hc : (0 : ℝ) < ((maximalIndependentSets nb).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nb hs hi)
  calc
    (∑ I ∈ maximalIndependentSets nb,
       max 0 (1 / ((maximalIndependentSets nb).card : ℝ) - realClockProb nb r I))
       ≤ ∑ I ∈ maximalIndependentSets nb,
            (1 / ((maximalIndependentSets nb).card : ℝ) - q) := by
            apply Finset.sum_le_sum
            intro I hI
            apply max_le
            · exact sub_nonneg.mpr hq
            · exact sub_le_sub_left (hmin I hI) _
    _ = 1 - ((maximalIndependentSets nb).card : ℝ) * q := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcancel : ((maximalIndependentSets nb).card : ℝ) *
          (1 / ((maximalIndependentSets nb).card : ℝ)) = 1 := by
        field_simp
      calc
        ((maximalIndependentSets nb).card : ℝ) *
            (1 / ((maximalIndependentSets nb).card : ℝ) - q) =
          ((maximalIndependentSets nb).card : ℝ) *
            (1 / ((maximalIndependentSets nb).card : ℝ)) -
          ((maximalIndependentSets nb).card : ℝ) * q := by ring
        _ = _ := by rw [hcancel]

end InverseGreedy
