import InverseGreedy.RealClockGreedyMIS

/-!
# S041: exact laws of disjoint unions and joins; EGU closure (IG-P2, IG-P4)

On the sum type `α ⊕ β` we define the disjoint union and the join of two
neighbour maps. For strictly positive rates we prove, for the first-choice
recursion (hence, by the S041 bridge, for genuine exponential clocks):

* union: `P(I ⊔ J) = P_G(I) · P_H(J)`;
* join: `P(I ⊔ ∅) = Λ_G/(Λ_G+Λ_H) · P_G(I)` and symmetrically;
* scaling all rates by `c > 0` leaves the law unchanged;
* the maximal independent sets of a union are the products, and of a join
  (both sides nonempty) the disjoint union of the two families;
* `RealClockEGU (union) ↔ RealClockEGU G ∧ RealClockEGU H` and the same for
  joins of nonempty graphs.
-/

open Finset
namespace InverseGreedy

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Disjoint union of two neighbour maps. -/
def unionNb (nG : α → Finset α) (nH : β → Finset β) : α ⊕ β → Finset (α ⊕ β)
  | Sum.inl a => (nG a).disjSum ∅
  | Sum.inr b => (∅ : Finset α).disjSum (nH b)

/-- Join of two neighbour maps: every left vertex is adjacent to every
right vertex. -/
def joinNb [Fintype α] [Fintype β] (nG : α → Finset α) (nH : β → Finset β) :
    α ⊕ β → Finset (α ⊕ β)
  | Sum.inl a => (nG a).disjSum Finset.univ
  | Sum.inr b => (Finset.univ : Finset α).disjSum (nH b)

/-- Rates on a sum type. -/
def sumRates (rG : α → ℝ) (rH : β → ℝ) : α ⊕ β → ℝ := Sum.elim rG rH

omit [DecidableEq α] [DecidableEq β] in
theorem sumRates_pos {rG : α → ℝ} {rH : β → ℝ} (hG : ∀ a, 0 < rG a)
    (hH : ∀ b, 0 < rH b) : ∀ x, 0 < sumRates rG rH x
  | Sum.inl a => hG a
  | Sum.inr b => hH b

omit [DecidableEq α] [DecidableEq β] in
theorem activeRate_disjSum (rG : α → ℝ) (rH : β → ℝ) (A : Finset α) (B : Finset β) :
    activeRate (sumRates rG rH) (A.disjSum B) = activeRate rG A + activeRate rH B := by
  simp [activeRate, Finset.sum_disjSum, sumRates]

theorem activeRate_nonneg {γ : Type*} (r : γ → ℝ) (hr : ∀ v, 0 < r v) (A : Finset γ) :
    0 ≤ activeRate r A :=
  Finset.sum_nonneg (fun v _ => (hr v).le)

theorem activeRate_pos_of_nonempty {γ : Type*} (r : γ → ℝ) (hr : ∀ v, 0 < r v)
    (A : Finset γ) (hA : A ≠ ∅) : 0 < activeRate r A :=
  Finset.sum_pos (fun v _ => hr v) (Finset.nonempty_iff_ne_empty.mpr hA)

theorem disjSum_erase_inl (I : Finset α) (J : Finset β) (a : α) :
    (I.disjSum J).erase (Sum.inl a) = (I.erase a).disjSum J := by
  ext x; cases x <;> simp

theorem disjSum_erase_inr (I : Finset α) (J : Finset β) (b : β) :
    (I.disjSum J).erase (Sum.inr b) = I.disjSum (J.erase b) := by
  ext x; cases x <;> simp

theorem afterChoice_union_inl (nG : α → Finset α) (nH : β → Finset β)
    (A : Finset α) (B : Finset β) (a : α) :
    afterChoice (unionNb nG nH) (A.disjSum B) (Sum.inl a) =
      (afterChoice nG A a).disjSum B := by
  ext x; cases x <;> simp [afterChoice, unionNb]

theorem afterChoice_union_inr (nG : α → Finset α) (nH : β → Finset β)
    (A : Finset α) (B : Finset β) (b : β) :
    afterChoice (unionNb nG nH) (A.disjSum B) (Sum.inr b) =
      A.disjSum (afterChoice nH B b) := by
  ext x; cases x <;> simp [afterChoice, unionNb]

theorem afterChoice_join_inl [Fintype α] [Fintype β] (nG : α → Finset α)
    (nH : β → Finset β) (A : Finset α) (B : Finset β) (a : α) :
    afterChoice (joinNb nG nH) (A.disjSum B) (Sum.inl a) =
      (afterChoice nG A a).disjSum ∅ := by
  ext x; cases x <;> simp [afterChoice, joinNb]

theorem afterChoice_join_inr [Fintype α] [Fintype β] (nG : α → Finset α)
    (nH : β → Finset β) (A : Finset α) (B : Finset β) (b : β) :
    afterChoice (joinNb nG nH) (A.disjSum B) (Sum.inr b) =
      (∅ : Finset α).disjSum (afterChoice nH B b) := by
  ext x; cases x <;> simp [afterChoice, joinNb]

/-- Rate-weighted first-step identity, valid also for the empty active set. -/
theorem weighted_first_step {γ : Type*} [DecidableEq γ] (r : γ → ℝ)
    (hr : ∀ v, 0 < r v) (nb : γ → Finset γ) (A T : Finset γ) :
    (∑ v ∈ A, if v ∈ T then
        r v * finiteRaceLaw r nb (afterChoice nb A v).card
          (afterChoice nb A v) (T.erase v) else 0) =
      activeRate r A * finiteRaceLaw r nb A.card A T := by
  by_cases hA : A = ∅
  · subst hA; simp [activeRate]
  · obtain ⟨k, hk⟩ : ∃ k, A.card = k + 1 :=
      ⟨A.card - 1, by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA); omega⟩
    rw [hk, finiteRaceLaw_step r nb k A T hA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hlt := afterChoice_card_lt nb A v hv
    have hfuel : finiteRaceLaw r nb k (afterChoice nb A v) (T.erase v) =
        finiteRaceLaw r nb (afterChoice nb A v).card (afterChoice nb A v) (T.erase v) :=
      finiteRaceLaw_fuel_eq_card r nb k _ _ (by omega)
    have hpos := activeRate_pos_of_nonempty r hr A hA
    split_ifs
    · rw [hfuel, firstChoice]
      field_simp
    · simp

/-- **Union law.** -/
theorem finiteRaceLaw_union (rG : α → ℝ) (rH : β → ℝ)
    (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b)
    (nG : α → Finset α) (nH : β → Finset β) :
    ∀ (fuel : ℕ) (A : Finset α) (B : Finset β) (I : Finset α) (J : Finset β),
      A.card + B.card ≤ fuel →
      finiteRaceLaw (sumRates rG rH) (unionNb nG nH) fuel (A.disjSum B) (I.disjSum J) =
        finiteRaceLaw rG nG A.card A I * finiteRaceLaw rH nH B.card B J
  | 0, A, B, I, J, h => by
      have hA : A = ∅ := Finset.card_eq_zero.mp (by omega)
      have hB : B = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hA; subst hB
      by_cases hI : I = ∅ <;> by_cases hJ : J = ∅ <;>
        simp [finiteRaceLaw, hI, hJ]
  | fuel + 1, A, B, I, J, h => by
      by_cases hAB : A = ∅ ∧ B = ∅
      · obtain ⟨hA, hB⟩ := hAB
        subst hA; subst hB
        by_cases hI : I = ∅ <;> by_cases hJ : J = ∅ <;>
          simp [finiteRaceLaw, hI, hJ]
      · have hne : A.disjSum B ≠ ∅ := by
          rw [Ne, Finset.disjSum_eq_empty]; exact hAB
        have hΛ : 0 < activeRate rG A + activeRate rH B := by
          by_cases hA : A = ∅
          · have hB : B ≠ ∅ := fun hB => hAB ⟨hA, hB⟩
            have := activeRate_pos_of_nonempty rH hH B hB
            have := activeRate_nonneg rG hG A
            linarith
          · have := activeRate_pos_of_nonempty rG hG A hA
            have := activeRate_nonneg rH hH B
            linarith
        rw [finiteRaceLaw_step _ _ fuel _ _ hne, Finset.sum_disjSum]
        have hleft : ∀ a ∈ A,
            (if Sum.inl a ∈ I.disjSum J then
              firstChoice (sumRates rG rH) (A.disjSum B) (Sum.inl a) *
                finiteRaceLaw (sumRates rG rH) (unionNb nG nH) fuel
                  (afterChoice (unionNb nG nH) (A.disjSum B) (Sum.inl a))
                  ((I.disjSum J).erase (Sum.inl a)) else 0) =
            (finiteRaceLaw rH nH B.card B J / (activeRate rG A + activeRate rH B)) *
              (if a ∈ I then rG a * finiteRaceLaw rG nG (afterChoice nG A a).card
                (afterChoice nG A a) (I.erase a) else 0) := by
          intro a ha
          rw [afterChoice_union_inl, disjSum_erase_inl,
            finiteRaceLaw_union rG rH hG hH nG nH fuel _ B _ J
              (by have := afterChoice_card_lt nG A a ha; omega)]
          simp only [Finset.inl_mem_disjSum]
          split_ifs
          · rw [firstChoice, activeRate_disjSum]
            simp only [sumRates, Sum.elim_inl]
            field_simp
          · simp
        have hright : ∀ b ∈ B,
            (if Sum.inr b ∈ I.disjSum J then
              firstChoice (sumRates rG rH) (A.disjSum B) (Sum.inr b) *
                finiteRaceLaw (sumRates rG rH) (unionNb nG nH) fuel
                  (afterChoice (unionNb nG nH) (A.disjSum B) (Sum.inr b))
                  ((I.disjSum J).erase (Sum.inr b)) else 0) =
            (finiteRaceLaw rG nG A.card A I / (activeRate rG A + activeRate rH B)) *
              (if b ∈ J then rH b * finiteRaceLaw rH nH (afterChoice nH B b).card
                (afterChoice nH B b) (J.erase b) else 0) := by
          intro b hb
          rw [afterChoice_union_inr, disjSum_erase_inr,
            finiteRaceLaw_union rG rH hG hH nG nH fuel A _ I _
              (by have := afterChoice_card_lt nH B b hb; omega)]
          simp only [Finset.inr_mem_disjSum]
          split_ifs
          · rw [firstChoice, activeRate_disjSum]
            simp only [sumRates, Sum.elim_inr]
            field_simp
          · simp
        rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright,
          ← Finset.mul_sum, ← Finset.mul_sum,
          weighted_first_step rG hG nG A I, weighted_first_step rH hH nH B J]
        field_simp

/-- The join restricted to an empty right side runs exactly the left law. -/
theorem finiteRaceLaw_join_left_only [Fintype α] [Fintype β] (r : α ⊕ β → ℝ)
    (nG : α → Finset α) (nH : β → Finset β) :
    ∀ (fuel : ℕ) (A : Finset α) (I : Finset α) (J : Finset β), A.card ≤ fuel →
      finiteRaceLaw r (joinNb nG nH) fuel (A.disjSum ∅) (I.disjSum J) =
        finiteRaceLaw (fun a => r (Sum.inl a)) nG A.card A I *
          (if J = ∅ then 1 else 0)
  | 0, A, I, J, h => by
      have hA : A = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hA
      by_cases hI : I = ∅ <;> by_cases hJ : J = ∅ <;> simp [finiteRaceLaw, hI, hJ]
  | fuel + 1, A, I, J, h => by
      by_cases hA : A = ∅
      · subst hA
        by_cases hI : I = ∅ <;> by_cases hJ : J = ∅ <;> simp [finiteRaceLaw, hI, hJ]
      · have hne : A.disjSum (∅ : Finset β) ≠ ∅ := by
          rw [Ne, Finset.disjSum_eq_empty]; tauto
        obtain ⟨k, hk⟩ : ∃ k, A.card = k + 1 :=
          ⟨A.card - 1, by
            have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA); omega⟩
        rw [finiteRaceLaw_step _ _ fuel _ _ hne, Finset.sum_disjSum, hk,
          finiteRaceLaw_step _ _ k _ _ hA, Finset.sum_mul]
        simp only [Finset.sum_empty, add_zero]
        apply Finset.sum_congr rfl
        intro a ha
        have hlt := afterChoice_card_lt nG A a ha
        rw [afterChoice_join_inl, disjSum_erase_inl,
          finiteRaceLaw_join_left_only r nG nH fuel _ _ J (by omega),
          finiteRaceLaw_fuel_eq_card _ nG k _ _ (by omega)]
        simp only [Finset.inl_mem_disjSum]
        split_ifs <;>
          simp [firstChoice, activeRate, mul_comm]

/-- The join restricted to an empty left side runs exactly the right law. -/
theorem finiteRaceLaw_join_right_only [Fintype α] [Fintype β] (r : α ⊕ β → ℝ)
    (nG : α → Finset α) (nH : β → Finset β) :
    ∀ (fuel : ℕ) (B : Finset β) (I : Finset α) (J : Finset β), B.card ≤ fuel →
      finiteRaceLaw r (joinNb nG nH) fuel ((∅ : Finset α).disjSum B) (I.disjSum J) =
        (if I = ∅ then 1 else 0) *
          finiteRaceLaw (fun b => r (Sum.inr b)) nH B.card B J
  | 0, B, I, J, h => by
      have hB : B = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hB
      by_cases hI : I = ∅ <;> by_cases hJ : J = ∅ <;> simp [finiteRaceLaw, hI, hJ]
  | fuel + 1, B, I, J, h => by
      by_cases hB : B = ∅
      · subst hB
        by_cases hI : I = ∅ <;> by_cases hJ : J = ∅ <;> simp [finiteRaceLaw, hI, hJ]
      · have hne : (∅ : Finset α).disjSum B ≠ ∅ := by
          rw [Ne, Finset.disjSum_eq_empty]; tauto
        obtain ⟨k, hk⟩ : ∃ k, B.card = k + 1 :=
          ⟨B.card - 1, by
            have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB); omega⟩
        rw [finiteRaceLaw_step _ _ fuel _ _ hne, Finset.sum_disjSum, hk,
          finiteRaceLaw_step _ _ k _ _ hB, Finset.mul_sum]
        simp only [Finset.sum_empty, zero_add]
        apply Finset.sum_congr rfl
        intro b hb
        have hlt := afterChoice_card_lt nH B b hb
        rw [afterChoice_join_inr, disjSum_erase_inr,
          finiteRaceLaw_join_right_only r nG nH fuel _ I _ (by omega),
          finiteRaceLaw_fuel_eq_card _ nH k _ _ (by omega)]
        simp only [Finset.inr_mem_disjSum]
        split_ifs <;>
          simp [firstChoice, activeRate, mul_comm]

/-- **Join law** from nonempty active sets on both sides. -/
theorem finiteRaceLaw_join [Fintype α] [Fintype β] (rG : α → ℝ) (rH : β → ℝ)
    (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b)
    (nG : α → Finset α) (nH : β → Finset β)
    (fuel : ℕ) (A : Finset α) (B : Finset β) (hA : A ≠ ∅) (hB : B ≠ ∅)
    (hfuel : A.card + B.card ≤ fuel + 1) (I : Finset α) (J : Finset β) :
    finiteRaceLaw (sumRates rG rH) (joinNb nG nH) (fuel + 1) (A.disjSum B) (I.disjSum J) =
      activeRate rG A / (activeRate rG A + activeRate rH B) *
          (finiteRaceLaw rG nG A.card A I * (if J = ∅ then 1 else 0)) +
        activeRate rH B / (activeRate rG A + activeRate rH B) *
          ((if I = ∅ then 1 else 0) * finiteRaceLaw rH nH B.card B J) := by
  have hne : A.disjSum B ≠ ∅ := by rw [Ne, Finset.disjSum_eq_empty]; tauto
  have hΛA := activeRate_pos_of_nonempty rG hG A hA
  have hΛB := activeRate_pos_of_nonempty rH hH B hB
  rw [finiteRaceLaw_step _ _ fuel _ _ hne, Finset.sum_disjSum]
  have hleft : ∀ a ∈ A,
      (if Sum.inl a ∈ I.disjSum J then
        firstChoice (sumRates rG rH) (A.disjSum B) (Sum.inl a) *
          finiteRaceLaw (sumRates rG rH) (joinNb nG nH) fuel
            (afterChoice (joinNb nG nH) (A.disjSum B) (Sum.inl a))
            ((I.disjSum J).erase (Sum.inl a)) else 0) =
      ((if J = ∅ then 1 else 0) / (activeRate rG A + activeRate rH B)) *
        (if a ∈ I then rG a * finiteRaceLaw rG nG (afterChoice nG A a).card
          (afterChoice nG A a) (I.erase a) else 0) := by
    intro a ha
    have hBpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB)
    rw [afterChoice_join_inl, disjSum_erase_inl,
      finiteRaceLaw_join_left_only _ nG nH fuel _ _ J
        (by have := afterChoice_card_lt nG A a ha; omega)]
    simp only [Finset.inl_mem_disjSum]
    split_ifs
    · rw [firstChoice, activeRate_disjSum]
      simp only [sumRates, Sum.elim_inl]
      field_simp
    all_goals simp
  have hright : ∀ b ∈ B,
      (if Sum.inr b ∈ I.disjSum J then
        firstChoice (sumRates rG rH) (A.disjSum B) (Sum.inr b) *
          finiteRaceLaw (sumRates rG rH) (joinNb nG nH) fuel
            (afterChoice (joinNb nG nH) (A.disjSum B) (Sum.inr b))
            ((I.disjSum J).erase (Sum.inr b)) else 0) =
      ((if I = ∅ then 1 else 0) / (activeRate rG A + activeRate rH B)) *
        (if b ∈ J then rH b * finiteRaceLaw rH nH (afterChoice nH B b).card
          (afterChoice nH B b) (J.erase b) else 0) := by
    intro b hb
    have hApos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA)
    rw [afterChoice_join_inr, disjSum_erase_inr,
      finiteRaceLaw_join_right_only _ nG nH fuel _ I _
        (by have := afterChoice_card_lt nH B b hb; omega)]
    simp only [Finset.inr_mem_disjSum]
    split_ifs
    · rw [firstChoice, activeRate_disjSum]
      simp only [sumRates, Sum.elim_inr]
      field_simp
    all_goals simp
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright,
    ← Finset.mul_sum, ← Finset.mul_sum,
    weighted_first_step rG hG nG A I, weighted_first_step rH hH nH B J]
  field_simp

/-- Global scaling of all rates leaves the first-choice law unchanged. -/
theorem finiteRaceLaw_scale {γ : Type*} [DecidableEq γ] (r : γ → ℝ) (c : ℝ) (hc : 0 < c)
    (nb : γ → Finset γ) :
    ∀ (fuel : ℕ) (A T : Finset γ),
      finiteRaceLaw (fun v => c * r v) nb fuel A T = finiteRaceLaw r nb fuel A T
  | 0, A, T => by simp [finiteRaceLaw]
  | fuel + 1, A, T => by
      by_cases hA : A = ∅
      · simp [finiteRaceLaw, hA]
      · rw [finiteRaceLaw_step _ _ fuel _ _ hA, finiteRaceLaw_step _ _ fuel _ _ hA]
        apply Finset.sum_congr rfl
        intro v _
        rw [finiteRaceLaw_scale r c hc nb fuel]
        congr 2
        simp only [firstChoice, activeRate, ← Finset.mul_sum]
        rw [mul_div_mul_left _ _ (ne_of_gt hc)]

end InverseGreedy
