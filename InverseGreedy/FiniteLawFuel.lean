import InverseGreedy.FullPermutationSupport

/-!
# S010: Fuel invariance and deletion consistency in the finite greedy model

The bounded finiteRaceLaw has a technical fuel argument. As soon as fuel
covers the active cardinality, adding fuel does not change the output
mass of ANY target, at ANY real rates. This result is entirely
combinatorial and does not need the exponential-clock interpretation.

A vertex already blocked by a previously accepted neighbour can be
removed from the priority list without changing greedyOutput.
These lemmas are prerequisites, not a claim that the weighted
permutation pushforward is already proved.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- After choosing v, every surviving active vertex was already
active and differs from v. No graph hypotheses are needed. -/
theorem afterChoice_subset_erase (neighbours : α → Finset α)
    (active : Finset α) (v : α) :
    afterChoice neighbours active v ⊆ active.erase v := by
  intro w hw
  simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_erase] at hw ⊢
  exact ⟨(fun h => hw.2 (Or.inl h)), hw.1⟩

/-- Every genuine selection strictly decreases active cardinality. -/
theorem afterChoice_card_lt (neighbours : α → Finset α)
    (active : Finset α) (v : α) (hv : v ∈ active) :
    (afterChoice neighbours active v).card < active.card := by
  have hle : (afterChoice neighbours active v).card ≤
      (active.erase v).card :=
    Finset.card_le_card (afterChoice_subset_erase neighbours active v)
  have herase := Finset.card_erase_add_one hv
  omega

/-- One extra unit of fuel does not change the weighted terminal
event law whenever the active set has at most `fuel` vertices.
This is for every proposed terminal set, including impossible ones. -/
theorem finiteRaceLaw_fuel_step_stable (rates : α → ℝ)
    (neighbours : α → Finset α) :
    ∀ fuel (active target : Finset α), active.card ≤ fuel →
      finiteRaceLaw rates neighbours (fuel + 1) active target =
        finiteRaceLaw rates neighbours fuel active target := by
  intro fuel
  induction fuel with
  | zero =>
      intro active target hcard
      have he : active = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      subst active
      simp [finiteRaceLaw]
  | succ fuel ih =>
      intro active target hcard
      by_cases he : active = ∅
      · simp [finiteRaceLaw, he]
      · have hsmall : ∀ v ∈ active,
            (afterChoice neighbours active v).card ≤ fuel := by
          intro v hv
          have hlt := afterChoice_card_lt neighbours active v hv
          omega
        rw [finiteRaceLaw_step rates neighbours (fuel + 1) active target he]
        rw [finiteRaceLaw_step rates neighbours fuel active target he]
        apply Finset.sum_congr rfl
        intro v hv
        split_ifs with htarget
        · rw [ih (afterChoice neighbours active v)
            (target.erase v) (hsmall v hv)]
        · rfl

/-- All sufficiently large fuel values define the same target law.
No probability or positivity assumptions are necessary. -/
theorem finiteRaceLaw_fuel_eq_card (rates : α → ℝ)
    (neighbours : α → Finset α) (fuel : Nat)
    (active target : Finset α) (hbound : active.card ≤ fuel) :
    finiteRaceLaw rates neighbours fuel active target =
      finiteRaceLaw rates neighbours active.card active target := by
  have h : ∀ extra : Nat,
      finiteRaceLaw rates neighbours (active.card + extra) active target =
        finiteRaceLaw rates neighbours active.card active target := by
    intro extra
    induction extra with
    | zero => simp
    | succ k ih =>
        rw [show active.card + (k + 1) = (active.card + k) + 1 by omega]
        rw [finiteRaceLaw_fuel_step_stable rates neighbours
          (active.card + k) active target (by omega)]
        exact ih
  calc
    finiteRaceLaw rates neighbours fuel active target =
      finiteRaceLaw rates neighbours
        (active.card + (fuel - active.card)) active target := by
          rw [Nat.add_sub_of_le hbound]
    _ = finiteRaceLaw rates neighbours active.card active target :=
      h (fuel - active.card)

/-- A vertex already blocked by the current accepted set is rejected. -/
theorem greedyAccept_blocked (neighbours : α → Finset α)
    (accepted : Finset α) (v : α)
    (hblocked : (neighbours v ∩ accepted).Nonempty) :
    greedyAccept neighbours accepted v = accepted := by
  simp [greedyAccept, hblocked]

/-- A blocked vertex may be deleted from any priority list, provided
its blocker was accepted during the preceding front. This is the
local skip law needed to relate full scans to active-set deletions. -/
theorem greedyOutput_skip_blocked (neighbours : α → Finset α)
    (front suffix : List α) (v : α)
    (hblocked : (neighbours v ∩
      front.foldl (greedyAccept neighbours) ∅).Nonempty) :
    greedyOutput neighbours (front ++ v :: suffix) =
      greedyOutput neighbours (front ++ suffix) := by
  unfold greedyOutput
  simp only [List.foldl_append, List.foldl_cons]
  rw [greedyAccept_blocked neighbours _ v hblocked]

end InverseGreedy
