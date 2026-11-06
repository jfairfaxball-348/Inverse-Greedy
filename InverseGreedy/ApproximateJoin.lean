import InverseGreedy.ApproximateEGU

/-!
# S041: approximate EGU is closed under joins (IG-P10)

For nonempty finite graphs with symmetric irreflexive neighbour maps,
`RealClockAEGU (joinNb nG nH) ↔ RealClockAEGU nG ∧ RealClockAEGU nH`,
for genuine exponential clocks, even when no infimum is attained.

With `λ = Λ_G/(Λ_G+Λ_H)` the join law is `λ·P_G` on left MIS and `(1-λ)·P_H`
on right MIS. (⇐) rescaling the right rates makes `λ = m_G/m`, and then the
join TV is `λ·TV_G + (1-λ)·TV_H`. (⇒) small join TV forces `λ ≈ m_G/m`, and
then `TV_G ≤ (4m/m_G)·TV_join`.
-/

open Finset
namespace InverseGreedy

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [Nonempty α] [Nonempty β]

theorem maximalIndependentSets_join_eq (nG : α → Finset α) (nH : β → Finset β) :
    maximalIndependentSets (joinNb nG nH) =
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

/-- The join TV as two weighted block sums. -/
theorem realClockTV_join_eq (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v)
    (rG : α → ℝ) (rH : β → ℝ) (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b) :
    realClockTV (joinNb nG nH) (sumRates rG rH) =
      (1 / 2) * (∑ I ∈ maximalIndependentSets nG,
          |activeRate rG Finset.univ / (activeRate rG Finset.univ + activeRate rH Finset.univ) *
              realClockProb nG rG I -
            1 / (((maximalIndependentSets nG).card + (maximalIndependentSets nH).card : ℕ) : ℝ)| +
        ∑ J ∈ maximalIndependentSets nH,
          |activeRate rH Finset.univ / (activeRate rG Finset.univ + activeRate rH Finset.univ) *
              realClockProb nH rH J -
            1 / (((maximalIndependentSets nG).card + (maximalIndependentSets nH).card : ℕ) : ℝ)|) := by
  unfold realClockTV
  rw [maximalIndependentSets_join_card, maximalIndependentSets_join_eq,
    Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro K hK hK'
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨J, hJ, hIJ⟩ := Finset.mem_image.mp hK'
      simp only [Finset.disjSum_inj] at hIJ
      rw [mem_maximalIndependentSets] at hI
      exact empty_not_isMIS nG (hIJ.1 ▸ hI)),
    Finset.sum_image (fun I _ I' _ h => by simpa using h),
    Finset.sum_image (fun J _ J' _ h => by simpa using h)]
  congr 2
  · apply Finset.sum_congr rfl
    intro I hI
    have hIne : I ≠ ∅ := by
      intro h0; rw [mem_maximalIndependentSets, h0] at hI; exact empty_not_isMIS nG hI
    rw [realClockProb_eq _ (joinNb_symm hGs hHs) _ (sumRates_pos hG hH),
      finiteRaceLaw_join_univ_left rG rH hG hH nG nH I hIne, realClockProb_eq nG hGs rG hG]
  · apply Finset.sum_congr rfl
    intro J hJ
    have hJne : J ≠ ∅ := by
      intro h0; rw [mem_maximalIndependentSets, h0] at hJ; exact empty_not_isMIS nH hJ
    rw [realClockProb_eq _ (joinNb_symm hGs hHs) _ (sumRates_pos hG hH),
      finiteRaceLaw_join_univ_right rG rH hG hH nG nH J hJne, realClockProb_eq nH hHs rH hH]

/-- Scaling the rates does not change the TV. -/
theorem realClockTV_scale {γ : Type*} [Fintype γ] [DecidableEq γ] (nb : γ → Finset γ)
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (r : γ → ℝ) (hr : ∀ v, 0 < r v) (c : ℝ) (hc : 0 < c) :
    realClockTV nb (fun v => c * r v) = realClockTV nb r := by
  unfold realClockTV
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  rw [realClockProb_eq nb hs _ (fun v => mul_pos hc (hr v)), realClockProb_eq nb hs r hr,
    finiteRaceLaw_scale r c hc nb]

/-- Key estimate for (⇒): a block's TV is controlled by the join TV. -/
private theorem block_tv_bound {ι : Type*} (S : Finset ι) (p : ι → ℝ) (lam m k : ℝ)
    (hk : 0 < k) (hm : 0 < m) (hS : (S.card : ℝ) = k) (hp : ∑ i ∈ S, p i = 1)
    (hlam : 0 < lam) (D : ℝ) (hD : ∑ i ∈ S, |lam * p i - 1 / m| ≤ D)
    (hsmall : D ≤ k / (2 * m)) :
    (1 / 2) * ∑ i ∈ S, |p i - 1 / k| ≤ 2 * m / k * D := by
  have hsum : |lam - k / m| ≤ D := by
    have : lam - k / m = ∑ i ∈ S, (lam * p i - 1 / m) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp, Finset.sum_const, nsmul_eq_mul, hS]
      ring
    rw [this]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hD
  have hlam_lb : k / (2 * m) ≤ lam := by
    have := neg_abs_le (lam - k / m)
    have h2 : k / (2 * m) = k / m - k / (2 * m) := by field_simp; ring
    linarith
  have hpt : ∀ i ∈ S, |p i - 1 / k| ≤ (|lam * p i - 1 / m| + |1 / m - lam / k|) / lam := by
    intro i _
    rw [le_div_iff₀ hlam]
    calc |p i - 1 / k| * lam = |lam * p i - lam / k| := by
          rw [← abs_of_pos hlam, ← abs_mul, abs_of_pos hlam]; congr 1; field_simp
      _ = |(lam * p i - 1 / m) + (1 / m - lam / k)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hconst : (S.card : ℝ) * |1 / m - lam / k| = |k / m - lam| := by
    rw [hS, ← abs_of_pos hk, ← abs_mul, abs_of_pos hk]; congr 1; field_simp
  calc (1 / 2) * ∑ i ∈ S, |p i - 1 / k|
      ≤ (1 / 2) * ∑ i ∈ S, (|lam * p i - 1 / m| + |1 / m - lam / k|) / lam := by
        gcongr with i hi; exact hpt i hi
    _ = (1 / 2) * ((∑ i ∈ S, |lam * p i - 1 / m|) + S.card * |1 / m - lam / k|) / lam := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (1 / 2) * (D + D) / lam := by
        rw [hconst, abs_sub_comm]
        gcongr
    _ = D / lam := by ring
    _ ≤ D / (k / (2 * m)) := by
        apply div_le_div_of_nonneg_left (le_trans (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD)
          (by positivity) hlam_lb
    _ = 2 * m / k * D := by field_simp

/-- **IG-P10 (Lean, genuine clocks).** The join of two nonempty graphs is
approximately EGU iff both factors are. -/
theorem realClockAEGU_join_iff (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v) :
    RealClockAEGU (joinNb nG nH) ↔ RealClockAEGU nG ∧ RealClockAEGU nH := by
  set mG : ℝ := ((maximalIndependentSets nG).card : ℝ) with hmGdef
  set mH : ℝ := ((maximalIndependentSets nH).card : ℝ) with hmHdef
  have hmG : 0 < mG := by
    rw [hmGdef]; exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nG hGs hGi)
  have hmH : 0 < mH := by
    rw [hmHdef]; exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nH hHs hHi)
  have hcast : (((maximalIndependentSets nG).card + (maximalIndependentSets nH).card : ℕ) : ℝ) =
      mG + mH := by rw [hmGdef, hmHdef]; push_cast; ring
  have hprobG : ∀ (rG : α → ℝ), (∀ a, 0 < rG a) →
      ∑ I ∈ maximalIndependentSets nG, realClockProb nG rG I = 1 := by
    intro rG hG
    rw [Finset.sum_congr rfl (fun I _ => realClockProb_eq nG hGs rG hG I)]
    exact finiteRaceLaw_sum_MIS rG hG nG hGs hGi
  have hprobH : ∀ (rH : β → ℝ), (∀ b, 0 < rH b) →
      ∑ J ∈ maximalIndependentSets nH, realClockProb nH rH J = 1 := by
    intro rH hH
    rw [Finset.sum_congr rfl (fun J _ => realClockProb_eq nH hHs rH hH J)]
    exact finiteRaceLaw_sum_MIS rH hH nH hHs hHi
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · set δ : ℝ := min (mG / (4 * (mG + mH))) (ε * mG / (8 * (mG + mH))) with hδ
      have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
      obtain ⟨r, hr, hlt⟩ := h δ hδ0
      refine ⟨fun a => r (Sum.inl a), fun a => hr _, ?_⟩
      have hJ := realClockTV_join_eq nG nH hGs hHs hGi hHi _ _
        (fun a => hr (Sum.inl a)) (fun b => hr (Sum.inr b))
      rw [sumRates_comp, hcast] at hJ
      set ΛG := activeRate (fun a => r (Sum.inl a)) Finset.univ
      set ΛH := activeRate (fun b => r (Sum.inr b)) Finset.univ
      have hΛG : 0 < ΛG := activeRate_pos_of_nonempty _ (fun a => hr _) _ Finset.univ_nonempty.ne_empty
      have hΛH : 0 < ΛH := activeRate_pos_of_nonempty _ (fun b => hr _) _ Finset.univ_nonempty.ne_empty
      have hnn2 := Finset.sum_nonneg (fun J (_ : J ∈ maximalIndependentSets nH) =>
        abs_nonneg (ΛH / (ΛG + ΛH) * realClockProb nH (fun b => r (Sum.inr b)) J - 1 / (mG + mH)))
      have hD : ∑ I ∈ maximalIndependentSets nG,
          |ΛG / (ΛG + ΛH) * realClockProb nG (fun a => r (Sum.inl a)) I - 1 / (mG + mH)| ≤
            2 * δ := by linarith
      have hb := block_tv_bound _ _ _ (mG + mH) mG hmG (by positivity) hmGdef.symm
        (hprobG _ (fun a => hr _)) (by positivity) (2 * δ) hD (by
          have := min_le_left (mG / (4 * (mG + mH))) (ε * mG / (8 * (mG + mH)))
          rw [← hδ] at this
          have h2 : mG / (2 * (mG + mH)) = 2 * (mG / (4 * (mG + mH))) := by field_simp; ring
          linarith)
      unfold realClockTV
      rw [← hmGdef]
      have h3 := min_le_right (mG / (4 * (mG + mH))) (ε * mG / (8 * (mG + mH)))
      rw [← hδ] at h3
      have h4 : 2 * (mG + mH) / mG * (2 * δ) ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hmG]
        have : δ * (8 * (mG + mH)) ≤ ε * mG := by
          rw [le_div_iff₀ (by positivity)] at h3; linarith
        nlinarith
      linarith
    · set δ : ℝ := min (mH / (4 * (mG + mH))) (ε * mH / (8 * (mG + mH))) with hδ
      have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
      obtain ⟨r, hr, hlt⟩ := h δ hδ0
      refine ⟨fun b => r (Sum.inr b), fun b => hr _, ?_⟩
      have hJ := realClockTV_join_eq nG nH hGs hHs hGi hHi _ _
        (fun a => hr (Sum.inl a)) (fun b => hr (Sum.inr b))
      rw [sumRates_comp, hcast] at hJ
      set ΛG := activeRate (fun a => r (Sum.inl a)) Finset.univ
      set ΛH := activeRate (fun b => r (Sum.inr b)) Finset.univ
      have hΛG : 0 < ΛG := activeRate_pos_of_nonempty _ (fun a => hr _) _ Finset.univ_nonempty.ne_empty
      have hΛH : 0 < ΛH := activeRate_pos_of_nonempty _ (fun b => hr _) _ Finset.univ_nonempty.ne_empty
      have hnn1 := Finset.sum_nonneg (fun I (_ : I ∈ maximalIndependentSets nG) =>
        abs_nonneg (ΛG / (ΛG + ΛH) * realClockProb nG (fun a => r (Sum.inl a)) I - 1 / (mG + mH)))
      have hD : ∑ J ∈ maximalIndependentSets nH,
          |ΛH / (ΛG + ΛH) * realClockProb nH (fun b => r (Sum.inr b)) J - 1 / (mG + mH)| ≤
            2 * δ := by linarith
      have hb := block_tv_bound _ _ _ (mG + mH) mH hmH (by positivity) hmHdef.symm
        (hprobH _ (fun b => hr _)) (by positivity) (2 * δ) hD (by
          have := min_le_left (mH / (4 * (mG + mH))) (ε * mH / (8 * (mG + mH)))
          rw [← hδ] at this
          have h2 : mH / (2 * (mG + mH)) = 2 * (mH / (4 * (mG + mH))) := by field_simp; ring
          linarith)
      unfold realClockTV
      rw [← hmHdef]
      have h3 := min_le_right (mH / (4 * (mG + mH))) (ε * mH / (8 * (mG + mH)))
      rw [← hδ] at h3
      have h4 : 2 * (mG + mH) / mH * (2 * δ) ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hmH]
        have : δ * (8 * (mG + mH)) ≤ ε * mH := by
          rw [le_div_iff₀ (by positivity)] at h3; linarith
        nlinarith
      linarith
  · rintro ⟨hG, hH⟩ ε hε
    obtain ⟨rG, hrG, hltG⟩ := hG ε hε
    obtain ⟨rH, hrH, hltH⟩ := hH ε hε
    have hΛG := activeRate_pos_of_nonempty rG hrG Finset.univ Finset.univ_nonempty.ne_empty
    have hΛH := activeRate_pos_of_nonempty rH hrH Finset.univ Finset.univ_nonempty.ne_empty
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
        c = activeRate rG Finset.univ * mH / (activeRate rH Finset.univ * mG) := ⟨_, rfl⟩
    have hc : 0 < c := by rw [hcdef]; positivity
    have hrH' : ∀ b, 0 < (fun b => c * rH b) b := fun b => mul_pos hc (hrH b)
    have hΛH' : activeRate (fun b => c * rH b) Finset.univ = c * activeRate rH Finset.univ := by
      change ∑ v ∈ Finset.univ, c * rH v = c * ∑ v ∈ Finset.univ, rH v
      rw [Finset.mul_sum]
    refine ⟨sumRates rG (fun b => c * rH b), sumRates_pos hrG hrH', ?_⟩
    rw [realClockTV_join_eq nG nH hGs hHs hGi hHi rG _ hrG hrH', hcast, hΛH']
    have hlamG : activeRate rG Finset.univ / (activeRate rG Finset.univ + c * activeRate rH Finset.univ)
        = mG / (mG + mH) := by rw [hcdef]; field_simp
    have hlamH : c * activeRate rH Finset.univ /
        (activeRate rG Finset.univ + c * activeRate rH Finset.univ) = mH / (mG + mH) := by
      rw [hcdef]; field_simp
    rw [hlamG, hlamH]
    have hscale : ∀ J, realClockProb nH (fun b => c * rH b) J = realClockProb nH rH J := by
      intro J
      rw [realClockProb_eq nH hHs _ hrH', realClockProb_eq nH hHs rH hrH, finiteRaceLaw_scale rH c hc nH]
    simp only [hscale]
    have hGsum : ∑ I ∈ maximalIndependentSets nG,
        |mG / (mG + mH) * realClockProb nG rG I - 1 / (mG + mH)| =
        mG / (mG + mH) * ∑ I ∈ maximalIndependentSets nG, |realClockProb nG rG I - 1 / mG| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro I _
      rw [← abs_of_pos (show 0 < mG / (mG + mH) by positivity), ← abs_mul,
        abs_of_pos (show 0 < mG / (mG + mH) by positivity)]
      congr 1; field_simp
    have hHsum : ∑ J ∈ maximalIndependentSets nH,
        |mH / (mG + mH) * realClockProb nH rH J - 1 / (mG + mH)| =
        mH / (mG + mH) * ∑ J ∈ maximalIndependentSets nH, |realClockProb nH rH J - 1 / mH| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro J _
      rw [← abs_of_pos (show 0 < mH / (mG + mH) by positivity), ← abs_mul,
        abs_of_pos (show 0 < mH / (mG + mH) by positivity)]
      congr 1; field_simp
    rw [hGsum, hHsum]
    unfold realClockTV at hltG hltH
    rw [← hmGdef] at hltG
    rw [← hmHdef] at hltH
    have hw : mG / (mG + mH) + mH / (mG + mH) = 1 := by field_simp
    have hnnG := Finset.sum_nonneg (fun I (_ : I ∈ maximalIndependentSets nG) =>
      abs_nonneg (realClockProb nG rG I - 1 / mG))
    have hnnH := Finset.sum_nonneg (fun J (_ : J ∈ maximalIndependentSets nH) =>
      abs_nonneg (realClockProb nH rH J - 1 / mH))
    have ha : 0 < mG / (mG + mH) := by positivity
    have hb : 0 < mH / (mG + mH) := by positivity
    nlinarith

end InverseGreedy
