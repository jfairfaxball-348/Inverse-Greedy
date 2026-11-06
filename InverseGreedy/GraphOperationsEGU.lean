import InverseGreedy.GraphOperationsLaw

/-!
# S041: EGU is closed under disjoint union and join, in both directions

IG-P2 and IG-P4 (join part) as theorems about genuine exponential clocks:
for symmetric irreflexive neighbour maps,

* `RealClockEGU (unionNb nG nH) ↔ RealClockEGU nG ∧ RealClockEGU nH`;
* `RealClockEGU (joinNb nG nH) ↔ RealClockEGU nG ∧ RealClockEGU nH`
  for nonempty vertex types.
-/

open Finset
namespace InverseGreedy

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The first-choice output law sums to one over maximal independent sets. -/
theorem finiteRaceLaw_sum_MIS {γ : Type*} [Fintype γ] [DecidableEq γ]
    (r : γ → ℝ) (hr : ∀ v, 0 < r v) (nb : γ → Finset γ)
    (hSymm : ∀ x y, y ∈ nb x → x ∈ nb y) (hIrr : ∀ v, v ∉ nb v) :
    ∑ I ∈ maximalIndependentSets nb,
      finiteRaceLaw r nb (Fintype.card γ) Finset.univ I = 1 := by
  have h := finiteIndependentExp_realClockGreedyOutput_sum_MIS r hr nb hSymm hIrr
  simp only [finiteIndependentExp_realClockGreedyOutput_eq_finiteRaceLaw r hr nb hSymm]
    at h
  have hnn : ∀ I ∈ maximalIndependentSets nb,
      0 ≤ finiteRaceLaw r nb (Fintype.card γ) Finset.univ I := by
    intro I _
    rw [← Finset.card_univ, ← priorityOutputMass_eq_finiteRaceLaw r hr nb hSymm]
    exact priorityOutputMass_nonneg r hr nb _ _
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ENNReal.ofReal_eq_one] at h
  exact h

theorem finiteRaceLaw_nonneg {γ : Type*} [Fintype γ] [DecidableEq γ]
    (r : γ → ℝ) (hr : ∀ v, 0 < r v) (nb : γ → Finset γ)
    (hSymm : ∀ x y, y ∈ nb x → x ∈ nb y) (I : Finset γ) :
    0 ≤ finiteRaceLaw r nb (Fintype.card γ) Finset.univ I := by
  rw [← Finset.card_univ, ← priorityOutputMass_eq_finiteRaceLaw r hr nb hSymm]
  exact priorityOutputMass_nonneg r hr nb _ _

/-- The MIS family of a nonempty graph is nonempty and avoids `∅`. -/
theorem maximalIndependentSets_nonempty {γ : Type*} [Fintype γ] [DecidableEq γ]
    (nb : γ → Finset γ) (hSymm : ∀ x y, y ∈ nb x → x ∈ nb y)
    (hIrr : ∀ v, v ∉ nb v) : (maximalIndependentSets nb).Nonempty := by
  have h := finiteRaceLaw_sum_MIS (fun _ => (1 : ℝ)) (fun _ => one_pos) nb hSymm hIrr
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  rw [hne, Finset.sum_empty] at h
  exact zero_ne_one h

theorem empty_not_isMIS {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (nb : γ → Finset γ) : ¬ IsMaximalIndependentSet nb ∅ := by
  rintro ⟨_, hdom⟩
  obtain ⟨u, hu, _⟩ := hdom (Classical.arbitrary γ) (Finset.notMem_empty _)
  exact Finset.notMem_empty u hu

/-! ### symmetry and irreflexivity of the operations -/

omit [DecidableEq α] [DecidableEq β] in
theorem unionNb_symm {nG : α → Finset α} {nH : β → Finset β}
    (hG : ∀ x y, y ∈ nG x → x ∈ nG y) (hH : ∀ x y, y ∈ nH x → x ∈ nH y) :
    ∀ x y, y ∈ unionNb nG nH x → x ∈ unionNb nG nH y := by
  rintro (a | b) (a' | b') h <;> simp_all [unionNb]

omit [DecidableEq α] [DecidableEq β] in
theorem unionNb_irrefl {nG : α → Finset α} {nH : β → Finset β}
    (hG : ∀ v, v ∉ nG v) (hH : ∀ v, v ∉ nH v) : ∀ v, v ∉ unionNb nG nH v := by
  rintro (a | b) <;> simp_all [unionNb]

omit [DecidableEq α] [DecidableEq β] in
theorem joinNb_symm [Fintype α] [Fintype β] {nG : α → Finset α} {nH : β → Finset β}
    (hG : ∀ x y, y ∈ nG x → x ∈ nG y) (hH : ∀ x y, y ∈ nH x → x ∈ nH y) :
    ∀ x y, y ∈ joinNb nG nH x → x ∈ joinNb nG nH y := by
  rintro (a | b) (a' | b') h <;> simp_all [joinNb]

omit [DecidableEq α] [DecidableEq β] in
theorem joinNb_irrefl [Fintype α] [Fintype β] {nG : α → Finset α} {nH : β → Finset β}
    (hG : ∀ v, v ∉ nG v) (hH : ∀ v, v ∉ nH v) : ∀ v, v ∉ joinNb nG nH v := by
  rintro (a | b) <;> simp_all [joinNb]

/-! ### maximal independent sets -/

omit [DecidableEq α] [DecidableEq β] in
theorem isMIS_union_iff [Fintype α] [Fintype β] (nG : α → Finset α) (nH : β → Finset β)
    (K : Finset (α ⊕ β)) :
    IsMaximalIndependentSet (unionNb nG nH) K ↔
      IsMaximalIndependentSet nG K.toLeft ∧ IsMaximalIndependentSet nH K.toRight := by
  simp only [IsMaximalIndependentSet, IsIndependentSet, Sum.forall, Sum.exists,
    unionNb, Finset.mem_toLeft, Finset.mem_toRight, Finset.inl_mem_disjSum,
    Finset.inr_mem_disjSum, Finset.notMem_empty, not_false_eq_true, implies_true,
    and_true, true_and, and_false, exists_false, or_false, false_or]
  tauto

theorem isMIS_join_iff [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (nG : α → Finset α) (nH : β → Finset β) (K : Finset (α ⊕ β)) :
    IsMaximalIndependentSet (joinNb nG nH) K ↔
      (IsMaximalIndependentSet nG K.toLeft ∧ K.toRight = ∅) ∨
        (K.toLeft = ∅ ∧ IsMaximalIndependentSet nH K.toRight) := by
  have hl := empty_not_isMIS nG
  have hr := empty_not_isMIS nH
  constructor
  · rintro ⟨hind, hdom⟩
    have hsplit : K.toLeft = ∅ ∨ K.toRight = ∅ := by
      by_contra hc
      push Not at hc
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
      exact hind _ (Finset.mem_toLeft.mp ha) _ (Finset.mem_toRight.mp hb)
        (by simp [joinNb])
    rcases hsplit with hL | hR
    · right
      refine ⟨hL, ?_, ?_⟩
      · intro u hu v hv
        have := hind (Sum.inr u) (Finset.mem_toRight.mp hu) (Sum.inr v)
          (Finset.mem_toRight.mp hv)
        simpa [joinNb] using this
      · intro v hv
        obtain ⟨u, hu, huv⟩ := hdom (Sum.inr v) (fun h => hv (Finset.mem_toRight.mpr h))
        rcases u with a | b
        · exact absurd (Finset.mem_toLeft.mpr hu) (by rw [hL]; exact Finset.notMem_empty _)
        · exact ⟨b, Finset.mem_toRight.mpr hu, by simpa [joinNb] using huv⟩
    · left
      refine ⟨⟨?_, ?_⟩, hR⟩
      · intro u hu v hv
        have := hind (Sum.inl u) (Finset.mem_toLeft.mp hu) (Sum.inl v)
          (Finset.mem_toLeft.mp hv)
        simpa [joinNb] using this
      · intro v hv
        obtain ⟨u, hu, huv⟩ := hdom (Sum.inl v) (fun h => hv (Finset.mem_toLeft.mpr h))
        rcases u with a | b
        · exact ⟨a, Finset.mem_toLeft.mpr hu, by simpa [joinNb] using huv⟩
        · exact absurd (Finset.mem_toRight.mpr hu) (by rw [hR]; exact Finset.notMem_empty _)
  · rintro (⟨⟨hind, hdom⟩, hR⟩ | ⟨hL, ⟨hind, hdom⟩⟩)
    · have hne : K.toLeft.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        exact hl (h0 ▸ ⟨hind, hdom⟩)
      obtain ⟨a0, ha0⟩ := hne
      refine ⟨?_, ?_⟩
      · rintro (a | b) hu (a' | b') hv
        · simpa [joinNb] using hind a (Finset.mem_toLeft.mpr hu) a'
            (Finset.mem_toLeft.mpr hv)
        · exact absurd (Finset.mem_toRight.mpr hv) (by rw [hR]; exact Finset.notMem_empty _)
        · exact absurd (Finset.mem_toRight.mpr hu) (by rw [hR]; exact Finset.notMem_empty _)
        · exact absurd (Finset.mem_toRight.mpr hu) (by rw [hR]; exact Finset.notMem_empty _)
      · rintro (a | b) hv
        · obtain ⟨u, hu, huv⟩ := hdom a (fun h => hv (Finset.mem_toLeft.mp h))
          exact ⟨Sum.inl u, Finset.mem_toLeft.mp hu, by simpa [joinNb] using huv⟩
        · exact ⟨Sum.inl a0, Finset.mem_toLeft.mp ha0, by simp [joinNb]⟩
    · have hne : K.toRight.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        exact hr (h0 ▸ ⟨hind, hdom⟩)
      obtain ⟨b0, hb0⟩ := hne
      refine ⟨?_, ?_⟩
      · rintro (a | b) hu (a' | b') hv
        · exact absurd (Finset.mem_toLeft.mpr hu) (by rw [hL]; exact Finset.notMem_empty _)
        · exact absurd (Finset.mem_toLeft.mpr hu) (by rw [hL]; exact Finset.notMem_empty _)
        · exact absurd (Finset.mem_toLeft.mpr hv) (by rw [hL]; exact Finset.notMem_empty _)
        · simpa [joinNb] using hind b (Finset.mem_toRight.mpr hu) b'
            (Finset.mem_toRight.mpr hv)
      · rintro (a | b) hv
        · exact ⟨Sum.inr b0, Finset.mem_toRight.mp hb0, by simp [joinNb]⟩
        · obtain ⟨u, hu, huv⟩ := hdom b (fun h => hv (Finset.mem_toRight.mp h))
          exact ⟨Sum.inr u, Finset.mem_toRight.mp hu, by simpa [joinNb] using huv⟩

theorem maximalIndependentSets_union_eq [Fintype α] [Fintype β]
    (nG : α → Finset α) (nH : β → Finset β) :
    maximalIndependentSets (unionNb nG nH) =
      (maximalIndependentSets nG ×ˢ maximalIndependentSets nH).image
        (fun p => p.1.disjSum p.2) := by
  ext K
  simp only [mem_maximalIndependentSets, Finset.mem_image, Finset.mem_product, Prod.exists]
  rw [isMIS_union_iff]
  constructor
  · intro h
    exact ⟨K.toLeft, K.toRight, h, Finset.toLeft_disjSum_toRight⟩
  · rintro ⟨I, J, ⟨hI, hJ⟩, rfl⟩
    simpa using And.intro hI hJ

theorem maximalIndependentSets_union_card [Fintype α] [Fintype β]
    (nG : α → Finset α) (nH : β → Finset β) :
    (maximalIndependentSets (unionNb nG nH)).card =
      (maximalIndependentSets nG).card * (maximalIndependentSets nH).card := by
  rw [maximalIndependentSets_union_eq, Finset.card_image_of_injective, Finset.card_product]
  rintro ⟨I, J⟩ ⟨I', J'⟩ h
  simp only [Finset.disjSum_inj] at h
  rw [h.1, h.2]

theorem maximalIndependentSets_join_card [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (nG : α → Finset α) (nH : β → Finset β) :
    (maximalIndependentSets (joinNb nG nH)).card =
      (maximalIndependentSets nG).card + (maximalIndependentSets nH).card := by
  have heq : maximalIndependentSets (joinNb nG nH) =
      (maximalIndependentSets nG).image (fun I => I.disjSum (∅ : Finset β)) ∪
        (maximalIndependentSets nH).image (fun J => (∅ : Finset α).disjSum J) := by
    ext K
    simp only [mem_maximalIndependentSets, Finset.mem_union, Finset.mem_image]
    rw [isMIS_join_iff]
    constructor
    · rintro (⟨h, hR⟩ | ⟨hL, h⟩)
      · left; exact ⟨K.toLeft, h, by rw [← hR, Finset.toLeft_disjSum_toRight]⟩
      · right; exact ⟨K.toRight, h, by rw [← hL, Finset.toLeft_disjSum_toRight]⟩
    · rintro (⟨I, h, rfl⟩ | ⟨J, h, rfl⟩)
      · left
        simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
        exact ⟨h, trivial⟩
      · right
        simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
        exact ⟨trivial, h⟩
  rw [heq, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective]
  · intro J J' h; simpa using h
  · intro I I' h; simpa using h
  · rw [Finset.disjoint_left]
    intro K hK hK'
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨J, hJ, hIJ⟩ := Finset.mem_image.mp hK'
    simp only [Finset.disjSum_inj] at hIJ
    rw [mem_maximalIndependentSets] at hI
    exact empty_not_isMIS nG (hIJ.1 ▸ hI)

/-! ### EGU closure theorems -/

omit [DecidableEq α] [DecidableEq β] in
theorem sumRates_comp (r : α ⊕ β → ℝ) :
    sumRates (fun a => r (Sum.inl a)) (fun b => r (Sum.inr b)) = r := by
  funext x; cases x <;> rfl

theorem finiteRaceLaw_union_univ [Fintype α] [Fintype β] (rG : α → ℝ) (rH : β → ℝ)
    (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b)
    (nG : α → Finset α) (nH : β → Finset β) (I : Finset α) (J : Finset β) :
    finiteRaceLaw (sumRates rG rH) (unionNb nG nH) (Fintype.card (α ⊕ β))
        Finset.univ (I.disjSum J) =
      finiteRaceLaw rG nG (Fintype.card α) Finset.univ I *
        finiteRaceLaw rH nH (Fintype.card β) Finset.univ J := by
  rw [← Finset.univ_disjSum_univ, finiteRaceLaw_union rG rH hG hH nG nH _ _ _ _ _
    (by simp [Fintype.card_sum]), Finset.card_univ, Finset.card_univ]

theorem finiteRaceLaw_join_univ_left [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (rG : α → ℝ) (rH : β → ℝ) (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b)
    (nG : α → Finset α) (nH : β → Finset β) (I : Finset α) (hI : I ≠ ∅) :
    finiteRaceLaw (sumRates rG rH) (joinNb nG nH) (Fintype.card (α ⊕ β))
        Finset.univ (I.disjSum ∅) =
      activeRate rG Finset.univ / (activeRate rG Finset.univ + activeRate rH Finset.univ) *
        finiteRaceLaw rG nG (Fintype.card α) Finset.univ I := by
  have hα : 0 < Fintype.card α := Fintype.card_pos
  have hβ : 0 < Fintype.card β := Fintype.card_pos
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card (α ⊕ β) = k + 1 :=
    ⟨Fintype.card (α ⊕ β) - 1, by rw [Fintype.card_sum]; omega⟩
  rw [← Finset.univ_disjSum_univ, hk, finiteRaceLaw_join rG rH hG hH nG nH k _ _
    (Finset.univ_nonempty.ne_empty) (Finset.univ_nonempty.ne_empty)
    (by rw [Finset.card_univ, Finset.card_univ, ← Fintype.card_sum, hk])]
  simp [hI, Finset.card_univ]

theorem finiteRaceLaw_join_univ_right [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (rG : α → ℝ) (rH : β → ℝ) (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b)
    (nG : α → Finset α) (nH : β → Finset β) (J : Finset β) (hJ : J ≠ ∅) :
    finiteRaceLaw (sumRates rG rH) (joinNb nG nH) (Fintype.card (α ⊕ β))
        Finset.univ ((∅ : Finset α).disjSum J) =
      activeRate rH Finset.univ / (activeRate rG Finset.univ + activeRate rH Finset.univ) *
        finiteRaceLaw rH nH (Fintype.card β) Finset.univ J := by
  have hα : 0 < Fintype.card α := Fintype.card_pos
  have hβ : 0 < Fintype.card β := Fintype.card_pos
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card (α ⊕ β) = k + 1 :=
    ⟨Fintype.card (α ⊕ β) - 1, by rw [Fintype.card_sum]; omega⟩
  rw [← Finset.univ_disjSum_univ, hk, finiteRaceLaw_join rG rH hG hH nG nH k _ _
    (Finset.univ_nonempty.ne_empty) (Finset.univ_nonempty.ne_empty)
    (by rw [Finset.card_univ, Finset.card_univ, ← Fintype.card_sum, hk])]
  simp [hJ, Finset.card_univ]

/-- **IG-P2 (Lean, genuine clocks).** A disjoint union is EGU iff both parts are. -/
theorem realClockEGU_union_iff [Fintype α] [Fintype β]
    (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v) :
    RealClockEGU (unionNb nG nH) ↔ RealClockEGU nG ∧ RealClockEGU nH := by
  rw [realClockEGU_iff_firstChoiceEGU _ (unionNb_symm hGs hHs),
    realClockEGU_iff_firstChoiceEGU _ hGs, realClockEGU_iff_firstChoiceEGU _ hHs]
  set mG := (maximalIndependentSets nG).card
  set mH := (maximalIndependentSets nH).card
  constructor
  · rintro ⟨r, hr, hu⟩
    set rG : α → ℝ := fun a => r (Sum.inl a)
    set rH : β → ℝ := fun b => r (Sum.inr b)
    have hrG : ∀ a, 0 < rG a := fun a => hr _
    have hrH : ∀ b, 0 < rH b := fun b => hr _
    have hprod : ∀ I ∈ maximalIndependentSets nG, ∀ J ∈ maximalIndependentSets nH,
        finiteRaceLaw rG nG (Fintype.card α) Finset.univ I *
          finiteRaceLaw rH nH (Fintype.card β) Finset.univ J = 1 / ((mG : ℝ) * mH) := by
      intro I hI J hJ
      have hK : I.disjSum J ∈ maximalIndependentSets (unionNb nG nH) := by
        rw [maximalIndependentSets_union_eq]
        exact Finset.mem_image.mpr ⟨(I, J), Finset.mem_product.mpr ⟨hI, hJ⟩, rfl⟩
      have := hu _ hK
      rw [← sumRates_comp r, finiteRaceLaw_union_univ rG rH hrG hrH,
        maximalIndependentSets_union_card] at this
      rw [this]; push_cast; ring
    have hsG := finiteRaceLaw_sum_MIS rG hrG nG hGs hGi
    have hsH := finiteRaceLaw_sum_MIS rH hrH nH hHs hHi
    obtain ⟨I0, hI0⟩ := maximalIndependentSets_nonempty nG hGs hGi
    obtain ⟨J0, hJ0⟩ := maximalIndependentSets_nonempty nH hHs hHi
    have hmG : (0 : ℝ) < mG := by exact_mod_cast Finset.card_pos.mpr ⟨I0, hI0⟩
    have hmH : (0 : ℝ) < mH := by exact_mod_cast Finset.card_pos.mpr ⟨J0, hJ0⟩
    -- the J0-marginal
    have hJ0val : finiteRaceLaw rH nH (Fintype.card β) Finset.univ J0 = 1 / mH := by
      have hsum : (∑ I ∈ maximalIndependentSets nG,
          finiteRaceLaw rG nG (Fintype.card α) Finset.univ I) *
            finiteRaceLaw rH nH (Fintype.card β) Finset.univ J0 =
          mG * (1 / ((mG : ℝ) * mH)) := by
        rw [Finset.sum_mul, Finset.sum_congr rfl (fun I hI => hprod I hI J0 hJ0),
          Finset.sum_const, nsmul_eq_mul]
      rw [hsG, one_mul] at hsum
      rw [hsum]; field_simp
    have hI0val : finiteRaceLaw rG nG (Fintype.card α) Finset.univ I0 = 1 / mG := by
      have hsum : finiteRaceLaw rG nG (Fintype.card α) Finset.univ I0 *
          (∑ J ∈ maximalIndependentSets nH,
            finiteRaceLaw rH nH (Fintype.card β) Finset.univ J) =
          mH * (1 / ((mG : ℝ) * mH)) := by
        rw [Finset.mul_sum, Finset.sum_congr rfl (fun J hJ => hprod I0 hI0 J hJ),
          Finset.sum_const, nsmul_eq_mul]
      rw [hsH, mul_one] at hsum
      rw [hsum]; field_simp
    refine ⟨⟨rG, hrG, fun I hI => ?_⟩, ⟨rH, hrH, fun J hJ => ?_⟩⟩
    · have h := hprod I hI J0 hJ0
      rw [hJ0val] at h
      change _ = 1 / (mG : ℝ)
      rw [eq_div_iff hmG.ne']
      field_simp at h
      linarith
    · have h := hprod I0 hI0 J hJ
      rw [hI0val] at h
      change _ = 1 / (mH : ℝ)
      rw [eq_div_iff hmH.ne']
      field_simp at h
      linarith
  · rintro ⟨⟨rG, hrG, huG⟩, ⟨rH, hrH, huH⟩⟩
    refine ⟨sumRates rG rH, sumRates_pos hrG hrH, fun K hK => ?_⟩
    have hK' := hK
    rw [maximalIndependentSets_union_eq] at hK'
    obtain ⟨⟨I, J⟩, hIJ, rfl⟩ := Finset.mem_image.mp hK'
    obtain ⟨hI, hJ⟩ := Finset.mem_product.mp hIJ
    rw [finiteRaceLaw_union_univ rG rH hrG hrH, huG I hI, huH J hJ,
      maximalIndependentSets_union_card]
    push_cast; ring

/-- **IG-P4, join part (Lean, genuine clocks).** The join of two nonempty
graphs is EGU iff both factors are. -/
theorem realClockEGU_join_iff [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v) :
    RealClockEGU (joinNb nG nH) ↔ RealClockEGU nG ∧ RealClockEGU nH := by
  rw [realClockEGU_iff_firstChoiceEGU _ (joinNb_symm hGs hHs),
    realClockEGU_iff_firstChoiceEGU _ hGs, realClockEGU_iff_firstChoiceEGU _ hHs]
  set mG := (maximalIndependentSets nG).card with hmG_def
  set mH := (maximalIndependentSets nH).card with hmH_def
  clear_value mG mH
  have hmG : (0 : ℝ) < mG := by
    obtain ⟨I0, hI0⟩ := maximalIndependentSets_nonempty nG hGs hGi
    rw [hmG_def]; exact_mod_cast Finset.card_pos.mpr ⟨I0, hI0⟩
  have hmH : (0 : ℝ) < mH := by
    obtain ⟨J0, hJ0⟩ := maximalIndependentSets_nonempty nH hHs hHi
    rw [hmH_def]; exact_mod_cast Finset.card_pos.mpr ⟨J0, hJ0⟩
  have hIne : ∀ I ∈ maximalIndependentSets nG, I ≠ ∅ := by
    intro I hI h0
    rw [mem_maximalIndependentSets, h0] at hI
    exact empty_not_isMIS nG hI
  have hJne : ∀ J ∈ maximalIndependentSets nH, J ≠ ∅ := by
    intro J hJ h0
    rw [mem_maximalIndependentSets, h0] at hJ
    exact empty_not_isMIS nH hJ
  have hmemL : ∀ I ∈ maximalIndependentSets nG,
      I.disjSum (∅ : Finset β) ∈ maximalIndependentSets (joinNb nG nH) := by
    intro I hI
    rw [mem_maximalIndependentSets, isMIS_join_iff]
    left
    rw [mem_maximalIndependentSets] at hI
    simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
    exact ⟨hI, trivial⟩
  have hmemR : ∀ J ∈ maximalIndependentSets nH,
      (∅ : Finset α).disjSum J ∈ maximalIndependentSets (joinNb nG nH) := by
    intro J hJ
    rw [mem_maximalIndependentSets, isMIS_join_iff]
    right
    rw [mem_maximalIndependentSets] at hJ
    simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
    exact ⟨trivial, hJ⟩
  constructor
  · rintro ⟨r, hr, hu⟩
    set rG : α → ℝ := fun a => r (Sum.inl a)
    set rH : β → ℝ := fun b => r (Sum.inr b)
    have hrG : ∀ a, 0 < rG a := fun a => hr _
    have hrH : ∀ b, 0 < rH b := fun b => hr _
    have hΛG := activeRate_pos_of_nonempty rG hrG Finset.univ Finset.univ_nonempty.ne_empty
    have hΛH := activeRate_pos_of_nonempty rH hrH Finset.univ Finset.univ_nonempty.ne_empty
    rw [maximalIndependentSets_join_card, ← hmG_def, ← hmH_def] at hu
    refine ⟨⟨rG, hrG, fun I hI => ?_⟩, ⟨rH, hrH, fun J hJ => ?_⟩⟩
    · have hall : ∀ I' ∈ maximalIndependentSets nG,
          finiteRaceLaw rG nG (Fintype.card α) Finset.univ I' =
            (activeRate rG Finset.univ + activeRate rH Finset.univ) /
              (activeRate rG Finset.univ * ((mG : ℝ) + mH)) := by
        intro I' hI'
        have h := hu _ (hmemL I' hI')
        rw [← sumRates_comp r, finiteRaceLaw_join_univ_left rG rH hrG hrH nG nH I'
          (hIne I' hI')] at h
        push_cast at h
        field_simp at h ⊢
        linarith
      have hs := finiteRaceLaw_sum_MIS rG hrG nG hGs hGi
      rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, ← hmG_def] at hs
      rw [← hmG_def]
      rw [hall I hI]
      field_simp at hs ⊢
      linarith
    · have hall : ∀ J' ∈ maximalIndependentSets nH,
          finiteRaceLaw rH nH (Fintype.card β) Finset.univ J' =
            (activeRate rG Finset.univ + activeRate rH Finset.univ) /
              (activeRate rH Finset.univ * ((mG : ℝ) + mH)) := by
        intro J' hJ'
        have h := hu _ (hmemR J' hJ')
        rw [← sumRates_comp r, finiteRaceLaw_join_univ_right rG rH hrG hrH nG nH J'
          (hJne J' hJ')] at h
        push_cast at h
        field_simp at h ⊢
        linarith
      have hs := finiteRaceLaw_sum_MIS rH hrH nH hHs hHi
      rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, ← hmH_def] at hs
      rw [← hmH_def]
      rw [hall J hJ]
      field_simp at hs ⊢
      linarith
  · rintro ⟨⟨rG, hrG, huG⟩, ⟨rH, hrH, huH⟩⟩
    have hΛG := activeRate_pos_of_nonempty rG hrG Finset.univ Finset.univ_nonempty.ne_empty
    have hΛH := activeRate_pos_of_nonempty rH hrH Finset.univ Finset.univ_nonempty.ne_empty
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ,
        c = activeRate rG Finset.univ * mH / (activeRate rH Finset.univ * mG) := ⟨_, rfl⟩
    have hc : 0 < c := by rw [hc_def]; positivity
    have hrH' : ∀ b, 0 < (fun b => c * rH b) b := fun b => mul_pos hc (hrH b)
    have hΛH' : activeRate (fun b => c * rH b) Finset.univ =
        c * activeRate rH Finset.univ := by
      change ∑ v ∈ Finset.univ, c * rH v = c * ∑ v ∈ Finset.univ, rH v
      rw [Finset.mul_sum]
    refine ⟨sumRates rG (fun b => c * rH b), sumRates_pos hrG hrH', fun K hK => ?_⟩
    have hK' := hK
    rw [mem_maximalIndependentSets, isMIS_join_iff] at hK'
    rw [maximalIndependentSets_join_card, ← hmG_def, ← hmH_def]
    push_cast
    rcases hK' with ⟨hI, hR⟩ | ⟨hL, hJ⟩
    · have hKeq : K = K.toLeft.disjSum ∅ := by rw [← hR, Finset.toLeft_disjSum_toRight]
      have hIm : K.toLeft ∈ maximalIndependentSets nG := (mem_maximalIndependentSets _ _).mpr hI
      rw [hKeq, finiteRaceLaw_join_univ_left rG (fun b => c * rH b) hrG hrH' nG nH _ (hIne _ hIm),
        huG _ hIm, hΛH', hc_def, ← hmG_def]
      field_simp
    · have hKeq : K = (∅ : Finset α).disjSum K.toRight := by
        rw [← hL, Finset.toLeft_disjSum_toRight]
      have hJm : K.toRight ∈ maximalIndependentSets nH := (mem_maximalIndependentSets _ _).mpr hJ
      rw [hKeq, finiteRaceLaw_join_univ_right rG (fun b => c * rH b) hrG hrH' nG nH _ (hJne _ hJm),
        finiteRaceLaw_scale rH c hc nH, huH _ hJm, hΛH', hc_def, ← hmH_def]
      field_simp

end InverseGreedy
