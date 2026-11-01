import InverseGreedy.ProjectedOrderLaw

/-!
# S015: exact support of weighted projected-order events

Filtering an actual full permutation to a retained subset gives an
actual complete permutation of the retained set, not a spurious order.
This yields zero mass for every impossible projected target and the
complete singleton-retained law (mass one at the unique possible order).
These results are law-level facts, but do NOT prove arbitrary-subset
deletion consistency or the greedy finiteRaceLaw pushforward.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Every projection of an actual complete priority order onto a subset
is an actual complete permutation of that subset. -/
theorem filtered_full_order_is_retained_permutation
    (active retained : Finset α) (hsub : retained ⊆ active)
    (order : List α) (horder : order ∈ active.toList.permutations) :
    order.filter (fun w => w ∈ retained) ∈ retained.toList.permutations := by
  classical
  obtain ⟨hnodup, hset⟩ :=
    (mem_full_priority_permutations_iff active order).mp horder
  apply (mem_full_priority_permutations_iff retained _).mpr
  constructor
  · exact hnodup.filter _
  · ext w
    simp only [List.mem_toFinset, List.mem_filter]
    constructor
    · exact And.right
    · intro hw
      have ha : w ∈ order.toFinset := by
        rw [hset]
        exact hsub hw
      exact ⟨by simpa using ha, hw⟩

/-- An impossible retained target order has exactly zero mass,
irrespective of rates. This excludes repeated, missing or extraneous
vertices without appealing to numerical tests. -/
theorem projectedOrderMass_zero_of_not_perm (rates : α → ℝ)
    (active retained : Finset α) (hsub : retained ⊆ active)
    (target : List α) (hnot : target ∉ retained.toList.permutations) :
    projectedOrderMass rates active retained target = 0 := by
  classical
  have hnone : ∀ order ∈ active.toList.permutations,
      order.filter (fun w => w ∈ retained) ≠ target := by
    intro order ho heq
    apply hnot
    rw [← heq]
    exact filtered_full_order_is_retained_permutation active retained
      hsub order ho
  unfold projectedOrderMass
  have hmap :
      (active.toList.permutations.map (fun order =>
        if order.filter (fun w => w ∈ retained) = target
        then orderMass rates order else (0 : ℝ))) =
      (active.toList.permutations.map (fun _ => (0 : ℝ))) := by
    apply List.map_congr_left
    intro order ho
    simp [hnone order ho]
  rw [hmap]
  simp

/-- A singleton retained subset has a deterministic projected
priority order. Its exact mass is one at all strictly positive rates. -/
theorem projectedOrderMass_singleton (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v)
    (active : Finset α) (v : α) (hv : v ∈ active) :
    projectedOrderMass rates active {v} [v] = 1 := by
  classical
  have hsub : ({v} : Finset α) ⊆ active :=
    Finset.singleton_subset_iff.mpr hv
  have hsingle : ∀ order ∈ active.toList.permutations,
      order.filter (fun w => w ∈ ({v} : Finset α)) = [v] := by
    intro order ho
    have hp := filtered_full_order_is_retained_permutation
      active ({v} : Finset α) hsub order ho
    simpa using hp
  unfold projectedOrderMass
  have hmap :
      (active.toList.permutations.map (fun order =>
        if order.filter (fun w => w ∈ ({v} : Finset α)) = [v]
        then orderMass rates order else (0 : ℝ))) =
      (active.toList.permutations.map (orderMass rates)) := by
    apply List.map_congr_left
    intro order ho
    simp [hsingle order ho]
  rw [hmap]
  exact full_priority_orderMass_sum_one rates hrates active

end InverseGreedy
