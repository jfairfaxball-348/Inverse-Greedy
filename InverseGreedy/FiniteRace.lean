import Mathlib

/-!
# Finite weighted races and the greedy output map

All rates used to interpret this model probabilistically are strictly
positive. `orderMass` is the size-biased-permutation mass, and
`finiteRaceLaw` is the bounded first-arrival recursion. Neither
construction alone proves an equivalence with independent Exp clocks.
-/
namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Normalising rate of the currently active finite vertex set. -/
def activeRate (rates : α → ℝ) (active : Finset α) : ℝ :=
  ∑ v ∈ active, rates v

/-- First-choice law for a strictly positive finite rate vector. -/
noncomputable def firstChoice (rates : α → ℝ) (active : Finset α) (v : α) : ℝ :=
  rates v / activeRate rates active

/-- The active rate is positive when the active set is nonempty. -/
theorem activeRate_pos (rates : α → ℝ) (active : Finset α)
    (hactive : active.Nonempty)
    (hrates : ∀ v ∈ active, 0 < rates v) :
    0 < activeRate rates active := by
  unfold activeRate
  exact Finset.sum_pos (fun v hv => hrates v hv) hactive

/-- The weighted first-choice masses form a probability distribution. -/
theorem firstChoice_sum_one (rates : α → ℝ) (active : Finset α)
    (hactive : active.Nonempty)
    (hrates : ∀ v ∈ active, 0 < rates v) :
    (∑ v ∈ active, firstChoice rates active v) = 1 := by
  have ht := activeRate_pos rates active hactive hrates
  change (∑ v ∈ active, rates v / activeRate rates active) = 1
  rw [← Finset.sum_div]
  change activeRate rates active / activeRate rates active = 1
  exact div_self (ne_of_gt ht)

/-- Exact probability weight of an ordered list of distinct vertices,
obtained by taking successive choices proportional to remaining rates.
For an empty list its weight is one. -/
noncomputable def orderMass (rates : α → ℝ) : List α → ℝ
  | [] => 1
  | v :: tail =>
      (rates v / (rates v + (tail.map rates).sum)) * orderMass rates tail

theorem orderMass_cons (rates : α → ℝ) (v : α) (tail : List α) :
    orderMass rates (v :: tail) =
      (rates v / (rates v + (tail.map rates).sum)) * orderMass rates tail := rfl

theorem orderMass_nil (rates : α → ℝ) : orderMass rates [] = 1 := rfl

/-- Greedy acceptance step from the set of already accepted vertices. -/
def greedyAccept (neighbours : α → Finset α) (accepted : Finset α)
    (v : α) : Finset α :=
  if (neighbours v ∩ accepted).Nonempty then accepted else insert v accepted

/-- Output of the sequential greedy scan of a finite priority list. -/
def greedyOutput (neighbours : α → Finset α) (order : List α) : Finset α :=
  order.foldl (greedyAccept neighbours) ∅

/-- Delete the selected vertex and its neighbours from the active set. -/
def afterChoice (neighbours : α → Finset α) (active : Finset α)
    (v : α) : Finset α :=
  active \ insert v (neighbours v)

/-- Recursive exact event mass for a proposed greedy terminal output.
The fuel bounds the number of active selections. With fuel `active.card`,
all branches terminate before fuel is exhausted. -/
noncomputable def finiteRaceLaw (rates : α → ℝ)
    (neighbours : α → Finset α) : Nat → Finset α → Finset α → ℝ
  | 0, active, target => if active = ∅ ∧ target = ∅ then 1 else 0
  | fuel + 1, active, target =>
      if active = ∅ then (if target = ∅ then 1 else 0)
      else ∑ v ∈ active,
        if v ∈ target then
          firstChoice rates active v *
            finiteRaceLaw rates neighbours fuel
              (afterChoice neighbours active v) (target.erase v)
        else 0

/-- First-choice equation, a proved unfolding of the finite weighted
recursive law. -/
theorem finiteRaceLaw_step (rates : α → ℝ)
    (neighbours : α → Finset α) (fuel : Nat)
    (active target : Finset α) (hactive : active ≠ ∅) :
    finiteRaceLaw rates neighbours (fuel + 1) active target =
      ∑ v ∈ active,
        if v ∈ target then
          firstChoice rates active v *
            finiteRaceLaw rates neighbours fuel
              (afterChoice neighbours active v) (target.erase v)
        else 0 := by
  simp [finiteRaceLaw, hactive]

/-- On the empty active set the sole possible terminal output is empty. -/
theorem finiteRaceLaw_empty (rates : α → ℝ)
    (neighbours : α → Finset α) (fuel : Nat) :
    finiteRaceLaw rates neighbours (fuel + 1) ∅ ∅ = 1 := by
  simp [finiteRaceLaw]

end InverseGreedy
