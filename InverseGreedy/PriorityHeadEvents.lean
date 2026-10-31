import InverseGreedy.PriorityHeadConditioning

/-!
# S013: first-choice recursion of the weighted priority event law

The head decomposition can be applied to *any* event of an entire
priority ordering. Applying it to the greedy terminal event and the
deterministic S012 first-residual identity gives a genuine first-step
equation for actual permutation masses.

The residual **tail still contains the blocked vertices** and has to
be filtered inside the event. Replacing its weighted sum by the
weighted law of the induced residual graph requires the outstanding
general weighted-deletion consistency theorem. No such replacement
is claimed here; neither is continuous-clock equivalence.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- A genuine event, not merely a normalizing constant, splits
over all possible first priority winners with their conditional
first-choice weights. The underlying enumeration is Mathlib's actual
List.permutations and contains each order exactly once. -/
theorem full_priority_weighted_head_event
    (rates : α → ℝ) (active : Finset α)
    (he : active ≠ ∅) (event : List α → Prop) :
    ((active.toList.permutations).map (fun order =>
      if event order then orderMass rates order else (0 : ℝ))).sum =
    (active.toList.map (fun v =>
      firstChoice rates active v *
        (((active.erase v).toList.permutations).map
          (fun tail => if event (v :: tail)
            then orderMass rates tail else (0 : ℝ))).sum)).sum := by
  classical
  have hnil : ([] : List α) ∉ active.toList.permutations := by
    intro hmem
    have hset :=
      ((mem_full_priority_permutations_iff active []).mp hmem).2
    have hempty : active = ∅ := by simpa using hset.symm
    exact he hempty
  calc
    ((active.toList.permutations).map (fun order =>
        if event order then orderMass rates order else (0 : ℝ))).sum =
      ((active.toList.permutations).map (fun order =>
        match order with
        | [] => (0 : ℝ)
        | v :: tail => orderMass rates (v :: tail) *
            (if event (v :: tail) then (1 : ℝ) else 0))).sum := by
          congr 1
          apply List.map_congr_left
          intro order hmem
          cases order with
          | nil => exact (hnil hmem).elim
          | cons v tail =>
              by_cases h : event (v :: tail) <;> simp [h]
    _ = (active.toList.map (fun v =>
        firstChoice rates active v *
          (((active.erase v).toList.permutations).map
            (fun tail => orderMass rates tail *
              (if event (v :: tail) then (1 : ℝ) else 0))).sum)).sum :=
        full_priority_weighted_head_sum rates active he
          (fun v tail => if event (v :: tail) then (1 : ℝ) else 0)
    _ = (active.toList.map (fun v =>
        firstChoice rates active v *
          (((active.erase v).toList.permutations).map
            (fun tail => if event (v :: tail)
              then orderMass rates tail else (0 : ℝ))).sum)).sum := by
          simp only [mul_ite, mul_one, mul_zero]

/-- Genuine first-head equation for the distribution of the greedy
terminal output. This holds for arbitrary neighbour maps; it has
not yet erased any blocked vertices. -/
theorem priorityOutputMass_head_event
    (rates : α → ℝ) (neighbours : α → Finset α)
    (active target : Finset α) (he : active ≠ ∅) :
    priorityOutputMass rates neighbours active target =
    (active.toList.map (fun v =>
      firstChoice rates active v *
        (((active.erase v).toList.permutations).map (fun tail =>
          if greedyOutput neighbours (v :: tail) = target
          then orderMass rates tail else (0 : ℝ))).sum)).sum := by
  unfold priorityOutputMass
  exact full_priority_weighted_head_event rates active he
    (fun order => greedyOutput neighbours order = target)

/-- In a symmetric graph, conditioning on the first winner reduces
every greedy event to the accepted first vertex plus a scan on the
filtered tail. The weights are still those of the *unfiltered*
tail; the law-level weighted projection remains to be proved. -/
theorem priorityOutputMass_head_residual
    (rates : α → ℝ) (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (active target : Finset α) (he : active ≠ ∅) :
    priorityOutputMass rates neighbours active target =
    (active.toList.map (fun v =>
      firstChoice rates active v *
        (((active.erase v).toList.permutations).map (fun tail =>
          if insert v (greedyOutput neighbours
                (tail.filter (fun w => w ∉ neighbours v))) = target
          then orderMass rates tail else (0 : ℝ))).sum)).sum := by
  rw [priorityOutputMass_head_event rates neighbours active target he]
  simp only [greedyOutput_first_residual neighbours hSymm]

end InverseGreedy
