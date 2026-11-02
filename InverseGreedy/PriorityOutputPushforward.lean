import InverseGreedy.PriorityProjectionEvent

/-!
# S018: exact discrete greedy-output pushforward

The law of greedyOutput under genuine complete weighted permutations
equals the bounded finite first-choice recursion on symmetric finite
neighbour maps. Only discrete size-biased ordering is involved;
independent continuous exponential clocks remain separate.
-/
namespace InverseGreedy
variable {α : Type*} [DecidableEq α]

/-- The first-head tail event is precisely the intrinsic greedy
output event on the residual active set. This uses weighted projection
and a pointwise proof that the first selected vertex is absent from
the residual output. -/
theorem priority_filtered_tail_event_eq
    (rates : α → ℝ) (hrates : ∀ w, 0 < rates w)
    (neighbours : α → Finset α)
    (active target : Finset α) (v : α) (hv : v ∈ active) :
    (((active.erase v).toList.permutations).map (fun tail =>
      if insert v (greedyOutput neighbours
          (tail.filter (fun w => w ∉ neighbours v))) = target
      then orderMass rates tail else (0 : ℝ))).sum =
    if v ∈ target then
      priorityOutputMass rates neighbours
        (afterChoice neighbours active v) (target.erase v)
    else 0 := by
  classical
  let kept := afterChoice neighbours active v
  have hsub : kept ⊆ active.erase v :=
    afterChoice_subset_erase neighbours active v
  have hprojection :=
    weighted_priority_filtered_greedy_event
      rates hrates neighbours (active.erase v) kept
      (target.erase v) hsub
  have hevent (tail : List α)
      (htail : tail ∈ (active.erase v).toList.permutations) :
      (insert v (greedyOutput neighbours
        (tail.filter (fun w => w ∉ neighbours v))) = target) ↔
        (v ∈ target ∧
          greedyOutput neighbours
            (tail.filter (fun w => w ∈ kept)) = target.erase v) := by
    have hset :=
      ((mem_full_priority_permutations_iff (active.erase v) tail).mp htail).2
    have htail_sub : tail.toFinset ⊆ active.erase v := by
      rw [hset]
    have hfilter :
        tail.filter (fun w => w ∉ neighbours v) =
          tail.filter (fun w => w ∈ kept) :=
      residual_filter_eq_afterChoice neighbours active v tail htail_sub
    have hnot_tail : v ∉ tail := by
      intro hmem
      have hm : v ∈ tail.toFinset := by simpa using hmem
      rw [hset] at hm
      simp at hm
    have hnot_output :
        v ∉ greedyOutput neighbours
          (tail.filter (fun w => w ∈ kept)) := by
      intro hmem
      have hm := greedyOutput_subset_vertices neighbours
        (tail.filter (fun w => w ∈ kept)) hmem
      have hmemfilter : v ∈ tail.filter (fun w => w ∈ kept) := by
        simpa using hm
      exact hnot_tail (List.mem_filter.mp hmemfilter).1
    rw [hfilter]
    constructor
    · intro heq
      constructor
      · rw [← heq]
        simp
      · rw [← heq]
        simp [hnot_output]
    · rintro ⟨hvt, hrest⟩
      rw [hrest]
      exact Finset.insert_erase hvt
  by_cases hvt : v ∈ target
  · simp only [if_pos hvt]
    calc
      _ = (((active.erase v).toList.permutations).map (fun tail =>
            if greedyOutput neighbours
                (tail.filter (fun w => w ∈ kept)) = target.erase v
            then orderMass rates tail else (0 : ℝ))).sum := by
              congr 1
              apply List.map_congr_left
              intro tail ht
              simpa [hevent tail ht, hvt]
      _ = priorityOutputMass rates neighbours kept (target.erase v) :=
        hprojection
  · simp only [if_neg hvt]
    have hmap :
        (((active.erase v).toList.permutations).map (fun tail =>
          if insert v (greedyOutput neighbours
            (tail.filter (fun w => w ∉ neighbours v))) = target
          then orderMass rates tail else (0 : ℝ))) =
          ((active.erase v).toList.permutations).map
            (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro tail ht
      simpa [hevent tail ht, hvt]
    rw [hmap]
    simp

/-- First-choice recursion of the actual weighted full-permutation
greedy output law, with all deleted neighbour priorities integrated out
using S017's exact full retained-order theorem. -/
theorem priorityOutputMass_first_choice
    (rates : α → ℝ) (hrates : ∀ v, 0 < rates v)
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (active target : Finset α) (he : active ≠ ∅) :
    priorityOutputMass rates neighbours active target =
      ∑ v ∈ active,
        if v ∈ target then
          firstChoice rates active v *
            priorityOutputMass rates neighbours
              (afterChoice neighbours active v) (target.erase v)
        else 0 := by
  classical
  rw [priorityOutputMass_head_residual rates neighbours hSymm
    active target he]
  have hmap :
      (active.toList.map (fun v =>
        firstChoice rates active v *
          (((active.erase v).toList.permutations).map (fun tail =>
            if insert v (greedyOutput neighbours
                  (tail.filter (fun w => w ∉ neighbours v))) = target
            then orderMass rates tail else (0 : ℝ))).sum)).sum =
      (active.toList.map (fun v =>
        if v ∈ target then
          firstChoice rates active v *
            priorityOutputMass rates neighbours
              (afterChoice neighbours active v) (target.erase v)
        else 0)).sum := by
    congr 1
    apply List.map_congr_left
    intro v hv
    rw [priority_filtered_tail_event_eq rates hrates neighbours
      active target v (Finset.mem_toList.mp hv)]
    by_cases hvt : v ∈ target <;> simp [hvt]
  rw [hmap]
  simp only [Finset.sum_map_toList]

/-- Main S018 discrete pushforward theorem. Every target, including
impossible targets, has exactly the same full-permutation greedy mass
as in the bounded finite first-arrival recursion. The symmetry
assumption is used for deterministic blocked-neighbour deletion.
Strict positivity is used for S017 weighted deletion consistency. -/
theorem priorityOutputMass_eq_finiteRaceLaw
    (rates : α → ℝ) (hrates : ∀ v, 0 < rates v)
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (active target : Finset α) :
    priorityOutputMass rates neighbours active target =
      finiteRaceLaw rates neighbours active.card active target := by
  have h : ∀ fuel : ℕ, ∀ active target : Finset α,
      active.card ≤ fuel →
      priorityOutputMass rates neighbours active target =
        finiteRaceLaw rates neighbours fuel active target := by
    intro fuel
    induction fuel with
    | zero =>
        intro active target hcard
        have ha : active = ∅ :=
          Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
        subst active
        simp [priorityOutputMass, finiteRaceLaw, greedyOutput, orderMass, eq_comm]
    | succ fuel ih =>
        intro active target hcard
        by_cases he : active = ∅
        · subst active
          simp [priorityOutputMass, finiteRaceLaw, greedyOutput, orderMass, eq_comm]
        · rw [priorityOutputMass_first_choice rates hrates
            neighbours hSymm active target he]
          rw [finiteRaceLaw_step rates neighbours fuel active target he]
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hvt : v ∈ target
          · simp only [if_pos hvt]
            congr 1
            exact ih (afterChoice neighbours active v) (target.erase v)
              (by
                have hs := afterChoice_card_lt neighbours active v hv
                omega)
          · simp [hvt]
  exact h active.card active target (le_refl _)

end InverseGreedy
