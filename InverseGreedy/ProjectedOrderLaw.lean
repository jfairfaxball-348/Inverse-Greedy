import InverseGreedy.PriorityHeadEvents

/-!
# S014: exact projected weighted order event and first-head equation

`projectedOrderMass` measures an actual full-priority-order event
after filtering the order to a retained subset. Its structural
head equation separates a retained first vertex from a discarded
first vertex. This is a law-level identity over Mathlib's actual
`List.permutations`; it is **not yet** the deletion-consistency
theorem equating the projected law to `orderMass` on the retained
subset. No independent exponential clocks occur in this file.
-/

namespace InverseGreedy
variable {α : Type*} [DecidableEq α]

noncomputable def projectedOrderMass (rates : α → ℝ)
    (active retained : Finset α) (target : List α) : ℝ :=
  ((active.toList.permutations).map (fun order =>
    if order.filter (fun w => w ∈ retained) = target
    then orderMass rates order else (0 : ℝ))).sum

/-- The exact weighted projection event law on full permutations
satisfies a head recursion. If the first global winner is retained,
it must match the first requested retained vertex; if discarded,
the requested retained order is unchanged. No stochastic limit,
deletion-consistency assumption, or factorial enumeration is used. -/
theorem projectedOrderMass_head
    (rates : α → ℝ) (active retained : Finset α)
    (target : List α) (he : active ≠ ∅) :
    projectedOrderMass rates active retained target =
      (active.toList.map (fun v =>
        firstChoice rates active v *
          (if v ∈ retained then
            match target with
            | [] => (0 : ℝ)
            | w :: suffix =>
                if v = w then
                  projectedOrderMass rates (active.erase v) retained suffix
                else 0
          else projectedOrderMass rates (active.erase v) retained target))).sum := by
  classical
  unfold projectedOrderMass
  rw [full_priority_weighted_head_event rates active he
    (fun order => order.filter (fun w => w ∈ retained) = target)]
  congr 1
  apply List.map_congr_left
  intro v hv
  congr 1
  by_cases h : v ∈ retained
  · cases target with
    | nil =>
        simp [h]
    | cons w suffix =>
        by_cases heq : v = w
        · subst w
          simp [h]
        · simp [h, heq]
  · simp [h]


/-- The scalar cancellation at the heart of the first-retained-winner
induction. The first retained vertex can win immediately, or all
first-overall discarded winners can be summed before it wins. This
algebraic identity alone does not prove the probabilistic marginal. -/
theorem retained_first_rate_cancellation
    (retainedRate discardedRate winnerRate : ℝ)
    (hret : retainedRate ≠ 0)
    (htotal : retainedRate + discardedRate ≠ 0) :
    winnerRate / (retainedRate + discardedRate) +
      discardedRate / (retainedRate + discardedRate) *
        (winnerRate / retainedRate) = winnerRate / retainedRate := by
  field_simp
  ring

end InverseGreedy
