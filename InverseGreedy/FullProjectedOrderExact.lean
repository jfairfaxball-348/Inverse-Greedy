import InverseGreedy.FirstRetainedExact

/-!
# S017: full weighted deletion consistency for actual priority permutations

The projected law is a sum over complete Mathlib List.permutations,
not an abstract recursive law. Induction on the active-cardinality
proves its equality with the intrinsic size-biased retained order mass.

This is a discrete law theorem. It does not identify independent
continuous exponential clocks or prove the greedy-output pushforward.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

private theorem sum_map_mul_right (xs : List α) (f : α → ℝ) (c : ℝ) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- Erasing a vertex absent from the active priority permutation has no
effect on the retained subsequence event. -/
theorem projectedOrderMass_erase_irrelevant (rates : α → ℝ)
    (active retained : Finset α) (target : List α) (v : α)
    (hv : v ∉ active) :
    projectedOrderMass rates active retained target =
      projectedOrderMass rates active (retained.erase v) target := by
  classical
  have hfilter : ∀ xs : List α, v ∉ xs →
      xs.filter (fun w => w ∈ retained) =
        xs.filter (fun w => w ∈ retained.erase v) := by
    intro xs
    induction xs with
    | nil =>
        intro _
        rfl
    | cons x xs ih =>
        intro hnot
        have hx : x ≠ v := by
          intro heq
          apply hnot
          simp [heq]
        have htail : v ∉ xs := by
          intro hm
          apply hnot
          simp [hm]
        simp [List.filter_cons, Finset.mem_erase, hx, ih htail]
  unfold projectedOrderMass
  congr 1
  apply List.map_congr_left
  intro order ho
  have hset := ((mem_full_priority_permutations_iff active order).mp ho).2
  have hnot : v ∉ order := by
    intro hm
    apply hv
    rw [← hset]
    simpa using hm
  rw [hfilter order hnot]

/-- A complete nonempty retained order has a complete tail after its
first entry is removed from the retained set. -/
private theorem retained_tail_permutation (retained : Finset α)
    (w : α) (suffix : List α)
    (ht : (w :: suffix) ∈ retained.toList.permutations) :
    w ∈ retained ∧
      suffix ∈ (retained.erase w).toList.permutations := by
  classical
  obtain ⟨hnodup, hset⟩ :=
    (mem_full_priority_permutations_iff retained (w :: suffix)).mp ht
  have hw : w ∈ retained := by
    rw [← hset]
    simp
  have htail :
      suffix ∈ (retained.erase w).toList.permutations := by
    apply (mem_full_priority_permutations_iff (retained.erase w) suffix).mpr
    constructor
    · exact (List.nodup_cons.mp hnodup).2
    · have hnot : w ∉ suffix.toFinset := by
        simpa using (List.nodup_cons.mp hnodup).1
      have hs : insert w suffix.toFinset = retained := by
        simpa using hset
      calc
        suffix.toFinset = (insert w suffix.toFinset).erase w := by
          simp [hnot]
        _ = retained.erase w := by rw [hs]
  exact ⟨hw, htail⟩

/-- Every full retained permutation has exactly the intrinsic
Plackett–Luce mass. This is the all-positive-real, arbitrary-subset
weighted projection theorem over actual complete permutations. -/
theorem projectedOrderMass_eq_orderMass (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v) :
    ∀ (active retained : Finset α) (target : List α),
      retained ⊆ active →
      target ∈ retained.toList.permutations →
      projectedOrderMass rates active retained target =
        orderMass rates target := by
  have h : ∀ fuel : ℕ, ∀ (active retained : Finset α) (target : List α),
      active.card ≤ fuel → retained ⊆ active →
      target ∈ retained.toList.permutations →
      projectedOrderMass rates active retained target =
        orderMass rates target := by
    intro fuel
    induction fuel with
    | zero =>
        intro active retained target hcard hsub ht
        have ha : active = ∅ :=
          Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
        have hr : retained = ∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro v hv
          have := hsub hv
          simp [ha] at this
        have hnil : target = [] := by
          obtain ⟨_, hset⟩ :=
            (mem_full_priority_permutations_iff retained target).mp ht
          cases target with
          | nil => rfl
          | cons w suffix =>
              have hw : w ∈ retained := by
                rw [← hset]
                simp
              simp [hr] at hw
        subst active
        subst retained
        subst target
        simp [projectedOrderMass, orderMass]
    | succ fuel ih =>
        intro active retained target hcard hsub ht
        by_cases hret : retained = ∅
        · subst retained
          have hnil : target = [] := by
            obtain ⟨_, hset⟩ :=
              (mem_full_priority_permutations_iff (∅ : Finset α) target).mp ht
            cases target with
            | nil => rfl
            | cons w suffix =>
                have hw : w ∈ (∅ : Finset α) := by
                  rw [← hset]
                  simp
                simp at hw
          subst target
          simpa [orderMass] using
            (projectedOrderMass_empty_retained rates hrates active)
        · have hretne : retained.Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr hret
          have ha : active ≠ ∅ := by
            intro he
            have hz : retained = ∅ := by
              apply Finset.eq_empty_iff_forall_not_mem.mpr
              intro v hv
              have := hsub hv
              simp [he] at this
            exact hret hz
          cases target with
          | nil =>
              have hset :=
                ((mem_full_priority_permutations_iff retained []).mp ht).2
              have hz : retained = ∅ := by simpa using hset.symm
              exact (hret hz).elim
          | cons w suffix =>
              have htarget : (w :: suffix) ∈ retained.toList.permutations := ht
              obtain ⟨hw, htail⟩ :=
                retained_tail_permutation retained w suffix htarget
              have hsmaller (v : α) (hv : v ∈ active) :
                  (active.erase v).card ≤ fuel := by
                have hc := Finset.card_erase_add_one hv
                omega
              have hsub_w : retained.erase w ⊆ active.erase w := by
                intro x hx
                obtain ⟨hxne, hxr⟩ := Finset.mem_erase.mp hx
                exact Finset.mem_erase.mpr ⟨hxne, hsub hxr⟩
              have hkept :
                  projectedOrderMass rates (active.erase w) retained suffix =
                    orderMass rates suffix := by
                calc
                  projectedOrderMass rates (active.erase w) retained suffix =
                      projectedOrderMass rates (active.erase w)
                        (retained.erase w) suffix :=
                        projectedOrderMass_erase_irrelevant rates
                          (active.erase w) retained suffix w (by simp)
                  _ = orderMass rates suffix :=
                    ih (active.erase w) (retained.erase w) suffix
                      (hsmaller w (hsub hw)) hsub_w htail
              have hdiscard (v : α) (hva : v ∈ active)
                  (hvr : v ∉ retained) :
                  projectedOrderMass rates (active.erase v) retained
                    (w :: suffix) = orderMass rates (w :: suffix) := by
                have hsub_v : retained ⊆ active.erase v := by
                  intro x hx
                  apply Finset.mem_erase.mpr
                  constructor
                  · intro heq
                    subst x
                    exact hvr hx
                  · exact hsub hx
                exact ih (active.erase v) retained (w :: suffix)
                  (hsmaller v hva) hsub_v htarget
              have horder :
                  orderMass rates (w :: suffix) =
                    firstChoice rates retained w * orderMass rates suffix :=
                orderMass_cons_full_tail rates retained w hw suffix htail
              have hreduce :
                  (active.toList.map (fun v => firstChoice rates active v *
                    (if v ∈ retained then
                      if v = w then
                        projectedOrderMass rates (active.erase v) retained suffix
                      else 0
                    else projectedOrderMass rates (active.erase v) retained
                      (w :: suffix)))).sum =
                  (active.toList.map (fun v =>
                    (firstChoice rates active v *
                      (if v ∈ retained then
                        (if v = w then (1 : ℝ) else 0)
                      else firstChoice rates retained w)) *
                        orderMass rates suffix)).sum := by
                congr 1
                apply List.map_congr_left
                intro v hv
                have hva : v ∈ active := Finset.mem_toList.mp hv
                by_cases hvr : v ∈ retained
                · by_cases heq : v = w
                  · subst v
                    simp [hw, hkept]
                  · simp [hvr, heq]
                · simp only [hvr, ite_false]
                  rw [hdiscard v hva hvr, horder]
                  ring
              calc
                projectedOrderMass rates active retained (w :: suffix) =
                    (active.toList.map (fun v =>
                      firstChoice rates active v *
                        (if v ∈ retained then
                          if v = w then
                            projectedOrderMass rates (active.erase v)
                              retained suffix
                          else 0
                        else projectedOrderMass rates (active.erase v)
                          retained (w :: suffix)))).sum :=
                      projectedOrderMass_head rates active retained
                        (w :: suffix) ha
                _ = (active.toList.map (fun v =>
                    (firstChoice rates active v *
                      (if v ∈ retained then
                        (if v = w then (1 : ℝ) else 0)
                      else firstChoice rates retained w)) *
                        orderMass rates suffix)).sum := hreduce
                _ = (active.toList.map (fun v =>
                    firstChoice rates active v *
                      (if v ∈ retained then
                        (if v = w then (1 : ℝ) else 0)
                      else firstChoice rates retained w))).sum *
                        orderMass rates suffix :=
                  sum_map_mul_right active.toList
                    (fun v => firstChoice rates active v *
                      (if v ∈ retained then
                        (if v = w then (1 : ℝ) else 0)
                      else firstChoice rates retained w))
                    (orderMass rates suffix)
                _ = firstChoice rates retained w * orderMass rates suffix := by
                    rw [first_retained_fixed_point rates hrates
                      active retained w hsub hretne hw]
                _ = orderMass rates (w :: suffix) := horder.symm
  intro active retained target hsub ht
  exact h active.card active retained target (le_refl _) hsub ht

end InverseGreedy
