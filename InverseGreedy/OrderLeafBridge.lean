import InverseGreedy.OrderTreeNormalization

/-!
# S007: identity of a finite priority leaf with its algebraic order mass

A priority leaf is a duplicate-free complete ordered list. At each step,
the active set consists of the as-yet-unread tail including its head.
This module proves (without finite enumeration or positivity assumptions)
that the successive conditional first-choice product of such a leaf is
exactly the previously defined `orderMass`.

NOT proved here: the head/tail decomposition gives *each* permutation
exactly once, summing over all permutations, grouping by greedyOutput,
or comparison to continuous exponential clocks.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Product of conditional first choices along a priority leaf. -/
noncomputable def orderLeafMass (rates : α → ℝ) : List α → ℝ
  | [] => 1
  | v :: tail =>
      firstChoice rates (v :: tail).toFinset v * orderLeafMass rates tail

/-- On a duplicate-free priority leaf, the Finset rate sum is the
usual list sum, so every head denominator has the expected value. -/
theorem activeRate_toFinset_of_nodup (rates : α → ℝ) :
    ∀ order : List α, order.Nodup →
      activeRate rates order.toFinset = (order.map rates).sum := by
  intro order
  induction order with
  | nil =>
      intro _
      simp [activeRate]
  | cons v tail ih =>
      intro hn
      rcases List.nodup_cons.mp hn with ⟨hnot, htail⟩
      have hv : v ∉ tail.toFinset := by simpa using hnot
      calc
        activeRate rates (v :: tail).toFinset =
            rates v + activeRate rates tail.toFinset := by
              simp [activeRate, hv]
        _ = rates v + (tail.map rates).sum := by rw [ih htail]
        _ = ((v :: tail).map rates).sum := by simp

/-- The finite head-choice probability along every duplicate-free
priority leaf agrees exactly with `orderMass`. This closes the
leaf-product identity, but NOT the permutation enumeration/pushforward. -/
theorem orderLeafMass_eq_orderMass (rates : α → ℝ) :
    ∀ order : List α, order.Nodup →
      orderLeafMass rates order = orderMass rates order := by
  intro order
  induction order with
  | nil =>
      intro _
      rfl
  | cons v tail ih =>
      intro hn
      have ht : tail.Nodup := (List.nodup_cons.mp hn).2
      calc
        orderLeafMass rates (v :: tail) =
            firstChoice rates (v :: tail).toFinset v *
              orderLeafMass rates tail := rfl
        _ = (rates v / (rates v + (tail.map rates).sum)) *
              orderMass rates tail := by
                rw [ih ht]
                rw [show firstChoice rates (v :: tail).toFinset v =
                    rates v / (rates v + (tail.map rates).sum) by
                  change rates v / activeRate rates (v :: tail).toFinset =
                    rates v / (rates v + (tail.map rates).sum)
                  rw [activeRate_toFinset_of_nodup rates (v :: tail) hn]
                  simp]
        _ = orderMass rates (v :: tail) :=
          (orderMass_cons rates v tail).symm

end InverseGreedy
