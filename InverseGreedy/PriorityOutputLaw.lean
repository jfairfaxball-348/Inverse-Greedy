import InverseGreedy.GreedyBlockedErasure

/-!
# S012: weighted greedy-output event law as a pushforward

This is the actual weighted List.permutations distribution, grouped by
greedyOutput. Total order mass is known to be one (S011). Here we prove
each target event has mass between zero and one. The more demanding
identity with finiteRaceLaw remains a separate unproved Lean obligation.
-/
namespace InverseGreedy
variable {α : Type*} [DecidableEq α]

/-- Exact mass of the terminal greedy output target when full weighted
priority permutations are enumerated. No clock semantics assumed. -/
noncomputable def priorityOutputMass (rates : α → ℝ)
    (neighbours : α → Finset α) (active target : Finset α) : ℝ :=
  ((active.toList.permutations).map (fun order =>
    if greedyOutput neighbours order = target
    then orderMass rates order else 0)).sum

/-- Every target event has nonnegative mass at strictly positive rates. -/
theorem priorityOutputMass_nonneg (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v)
    (neighbours : α → Finset α) (active target : Finset α) :
    0 ≤ priorityOutputMass rates neighbours active target := by
  have h : ∀ xs : List (List α),
      0 ≤ (xs.map (fun order =>
        if greedyOutput neighbours order = target
        then orderMass rates order else 0)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons order tail ih =>
        simp only [List.map_cons, List.sum_cons]
        have hp : 0 ≤
            (if greedyOutput neighbours order = target
              then orderMass rates order else (0 : ℝ)) := by
          split_ifs
          · exact le_of_lt (orderMass_pos rates order hrates)
          · exact le_refl _
        exact add_nonneg hp ih
  exact h _

/-- The event mass never exceeds one: it is bounded termwise by the
complete, structurally normalised weighted priority-order law. -/
theorem priorityOutputMass_le_one (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v)
    (neighbours : α → Finset α) (active target : Finset α) :
    priorityOutputMass rates neighbours active target ≤ 1 := by
  have h : ∀ xs : List (List α),
      (xs.map (fun order =>
        if greedyOutput neighbours order = target
        then orderMass rates order else 0)).sum ≤
      (xs.map (orderMass rates)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons order tail ih =>
        simp only [List.map_cons, List.sum_cons]
        have hp : (if greedyOutput neighbours order = target
            then orderMass rates order else (0 : ℝ)) ≤
            orderMass rates order := by
          split_ifs
          · exact le_refl _
          · exact le_of_lt (orderMass_pos rates order hrates)
        exact add_le_add hp ih
  calc
    priorityOutputMass rates neighbours active target ≤
        ((active.toList.permutations).map (orderMass rates)).sum := h _
    _ = 1 := full_priority_orderMass_sum_one rates hrates active

end InverseGreedy
