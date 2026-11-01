import InverseGreedy.FirstRetainedWinner

/-!
# S016: close the actual first-retained-winner marginal by induction

The weighted first-head recursion from S016 is combined with the
fixed-point identity for proportional rates. The only probability
normalization input is the S011 full-permutation theorem.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

private theorem first_retained_fixed_point (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v)
    (active retained : Finset α) (winner : α)
    (hsub : retained ⊆ active) (hret : retained.Nonempty)
    (hw : winner ∈ retained) :
    (active.toList.map (fun v => firstChoice rates active v *
      (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
       else firstChoice rates retained winner))).sum =
       firstChoice rates retained winner := by
  classical
  let C : ℝ := firstChoice rates retained winner
  let Ra : ℝ := activeRate rates active
  let Rr : ℝ := activeRate rates retained
  have hactive : active.Nonempty := hret.mono hsub
  have hRa : 0 < Ra := activeRate_pos rates active hactive
    (by intro v hv; exact hrates v)
  have hRr : 0 < Rr := activeRate_pos rates retained hret
    (by intro v hv; exact hrates v)
  have hwa : winner ∈ active := hsub hw
  have hwin : (∑ v ∈ active, if v = winner then rates v else (0 : ℝ)) =
      rates winner := by
    simp [hwa]
  have hfilter : active.filter (fun v => v ∈ retained) = retained := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hv
      exact ⟨hsub hv, hv⟩
  have hkept : (∑ v ∈ active, if v ∈ retained then rates v else (0 : ℝ)) =
      Rr := by
    rw [← Finset.sum_filter, hfilter]
    rfl
  have hpoint : ∀ v ∈ active,
      rates v *
        (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
         else C) =
      (if v = winner then rates v else 0) + C * rates v -
        C * (if v ∈ retained then rates v else 0) := by
    intro v hv
    by_cases hvr : v ∈ retained
    · by_cases heq : v = winner <;> simp [hvr, heq] <;> ring
    · have hneq : v ≠ winner := by
        intro heq
        subst v
        exact hvr hw
      simp [hvr, hneq] <;> ring
  have hnumer :
      (∑ v ∈ active, rates v *
        (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
         else C)) = rates winner + C * Ra - C * Rr := by
    calc
      _ = (∑ v ∈ active,
          (if v = winner then rates v else 0) + C * rates v -
          C * (if v ∈ retained then rates v else 0)) := by
            apply Finset.sum_congr rfl
            exact hpoint
      _ = (∑ v ∈ active, if v = winner then rates v else 0) +
          C * (∑ v ∈ active, rates v) -
          C * (∑ v ∈ active, if v ∈ retained then rates v else 0) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum]
      _ = rates winner + C * Ra - C * Rr := by
            rw [hwin, hkept]
            rfl
  have hscaled :
      (active.toList.map (fun v => firstChoice rates active v *
         (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
          else C))).sum =
        (∑ v ∈ active, rates v *
          (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
           else C)) / Ra := by
    simp only [Finset.sum_map_toList, firstChoice]
    change (∑ v ∈ active, rates v / Ra *
      (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
       else C)) = _
    calc
      _ = (∑ v ∈ active, (rates v *
          (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
           else C)) / Ra) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = _ := by rw [Finset.sum_div]
  change (active.toList.map (fun v => firstChoice rates active v *
    (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
     else C))).sum = C
  rw [hscaled, hnumer]
  dsimp [C, firstChoice]
  have hnRa : Ra ≠ 0 := ne_of_gt hRa
  have hnRr : Rr ≠ 0 := ne_of_gt hRr
  field_simp
  <;> ring

/-- Actual full-permutation first-retained-winner mass equals the
intrinsic proportional first choice on the retained subset, for
every finite active set and arbitrary strictly positive real rates.
This is NOT the complete ordered-subsequence law. -/
theorem firstRetainedMass_eq_firstChoice (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v) :
    ∀ (active retained : Finset α) (winner : α),
      retained ⊆ active → retained.Nonempty → winner ∈ retained →
      firstRetainedMass rates active retained winner =
        firstChoice rates retained winner := by
  have h : ∀ (fuel : ℕ) (active retained : Finset α) (winner : α),
      active.card ≤ fuel → retained ⊆ active → retained.Nonempty →
      winner ∈ retained →
      firstRetainedMass rates active retained winner =
        firstChoice rates retained winner := by
    intro fuel
    induction fuel with
    | zero =>
        intro active retained winner hcard hsub hret hw
        have hactive : active.Nonempty := hret.mono hsub
        have hp := Finset.card_pos.mpr hactive
        omega
    | succ fuel ih =>
        intro active retained winner hcard hsub hret hw
        have hactive : active.Nonempty := hret.mono hsub
        have he : active ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hactive
        rw [firstRetainedMass_head rates hrates active retained winner he]
        calc
          _ = (active.toList.map (fun v => firstChoice rates active v *
            (if v ∈ retained then (if v = winner then (1 : ℝ) else 0)
             else firstChoice rates retained winner))).sum := by
                congr 1
                apply List.map_congr_left
                intro v hv
                by_cases hvr : v ∈ retained
                · simp [hvr]
                · simp only [hvr, ite_false]
                  congr 1
                  have hva : v ∈ active := Finset.mem_toList.mp hv
                  have hsube : retained ⊆ active.erase v := by
                    intro w hwr
                    apply Finset.mem_erase.mpr
                    constructor
                    · intro heq
                      subst w
                      exact hvr hwr
                    · exact hsub hwr
                  have hsmaller : (active.erase v).card ≤ fuel := by
                    have her := Finset.card_erase_add_one hva
                    omega
                  exact ih (active.erase v) retained winner hsmaller
                    hsube hret hw
          _ = firstChoice rates retained winner :=
                first_retained_fixed_point rates hrates active retained winner
                  hsub hret hw
  intro active retained winner hsub hret hw
  exact h active.card active retained winner (le_refl _) hsub hret hw

end InverseGreedy
