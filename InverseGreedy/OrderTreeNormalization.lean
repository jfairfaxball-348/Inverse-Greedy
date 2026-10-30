import InverseGreedy.OrderMassBridge

/-!
# S006: structural normalisation of the finite weighted-order tree

Every node chooses its first vertex proportionally to its strictly positive
rate and removes that vertex. The resulting tree enumerates complete
size-biased priority orders by successive head choices. This theorem
normalises the *recursive tree mass*, without a factorial-size `decide`
and without appealing to an exponential random-variable model.

The additional claim identifying each tree leaf with `orderMass` of
the corresponding permutation, and the pushforward to `finiteRaceLaw`,
are separate obligations (not claimed here).
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Total leaf mass of the head-choice decomposition tree, with a
fuel bound. In a complete tree, fuel is at least the active cardinality. -/
noncomputable def orderTreeMass (rates : α → ℝ) :
    Nat → Finset α → ℝ
  | 0, active => if active = ∅ then 1 else 0
  | fuel + 1, active =>
      if active = ∅ then 1
      else ∑ v ∈ active,
        firstChoice rates active v *
          orderTreeMass rates fuel (active.erase v)

/-- Every complete head-choice tree has total leaf mass exactly one.
The proof uses card-decreasing induction and first-choice normalisation;
it is uniform in the vertex set and requires no permutation enumeration. -/
theorem orderTreeMass_normalized (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v) :
    ∀ fuel (active : Finset α), active.card ≤ fuel →
      orderTreeMass rates fuel active = 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro active hcard
      have he : active = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      simp [orderTreeMass, he]
  | succ fuel ih =>
      intro active hcard
      by_cases he : active = ∅
      · simp [orderTreeMass, he]
      · have hne : active.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
        rw [orderTreeMass]
        simp only [he, ↓reduceIte]
        calc
          (∑ v ∈ active,
              firstChoice rates active v *
                orderTreeMass rates fuel (active.erase v)) =
              ∑ v ∈ active, firstChoice rates active v := by
                apply Finset.sum_congr rfl
                intro v hv
                have hsmall : (active.erase v).card ≤ fuel := by
                  have hs := Finset.card_erase_add_one hv
                  omega
                rw [ih (active.erase v) hsmall, mul_one]
          _ = 1 := firstChoice_sum_one rates active hne
            (by intro v hv; exact hrates v)

/-- The card-bounded total priority-order mass is one. -/
theorem orderTreeMass_card (rates : α → ℝ) (active : Finset α)
    (hrates : ∀ v, 0 < rates v) :
    orderTreeMass rates active.card active = 1 :=
  orderTreeMass_normalized rates hrates active.card active (le_refl _)

end InverseGreedy
