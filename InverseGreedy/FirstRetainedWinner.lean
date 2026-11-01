import InverseGreedy.ProjectionSupport

/-!
# S016: first retained winner as an actual weighted permutation event

The event uses Mathlib's actual complete priority permutations. The
first-head equation explicitly accounts for all globally first vertices:
a retained vertex decides the event immediately; a discarded vertex
passes the same event to the complete conditional tail law.

The theorem here is a law-level recurrence. It does not by itself assert
the closed-form retained-winner marginal or full subset deletion
consistency, and it does not involve independent exponential clocks.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Mass that the first member of `retained` in a complete weighted
priority permutation of `active` is `winner`. The event is false
if no retained vertex is present. -/
noncomputable def firstRetainedMass (rates : α → ℝ)
    (active retained : Finset α) (winner : α) : ℝ :=
  ((active.toList.permutations).map (fun order =>
    if (order.filter (fun v => v ∈ retained)).head? = some winner
    then orderMass rates order else (0 : ℝ))).sum

/-- Exact first-head equation for the first-retained-winner event.
The normalization of conditional tails is proved using the actual
full-permutation normalization theorem (S011), not postulated. -/
theorem firstRetainedMass_head (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v)
    (active retained : Finset α) (winner : α)
    (he : active ≠ ∅) :
    firstRetainedMass rates active retained winner =
      (active.toList.map (fun v =>
        firstChoice rates active v *
          (if v ∈ retained then
            if v = winner then (1 : ℝ) else 0
          else firstRetainedMass rates (active.erase v) retained winner))).sum := by
  classical
  unfold firstRetainedMass
  rw [full_priority_weighted_head_event rates active he
    (fun order => (order.filter (fun v => v ∈ retained)).head? = some winner)]
  congr 1
  apply List.map_congr_left
  intro v hv
  by_cases hret : v ∈ retained
  · by_cases hwin : v = winner
    · subst winner
      simp [hret, full_priority_orderMass_sum_one rates hrates (active.erase v)]
    · simp [hret, hwin]
  · simp [hret]

/-- When nothing is retained, no first-retained winner exists.
This is a genuine zero-event identity for any rates. -/
theorem firstRetainedMass_empty (rates : α → ℝ)
    (active : Finset α) (winner : α) :
    firstRetainedMass rates active ∅ winner = 0 := by
  classical
  simp [firstRetainedMass]

/-- At an empty active set the event has zero mass, regardless of
the purported retained vertices. -/
theorem firstRetainedMass_empty_active (rates : α → ℝ)
    (retained : Finset α) (winner : α) :
    firstRetainedMass rates ∅ retained winner = 0 := by
  classical
  simp [firstRetainedMass]

end InverseGreedy
