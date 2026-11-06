import InverseGreedy.SmallGraphObstructions
import InverseGreedy.GraphOperationsEGU
import InverseGreedy.C6TVGap
import InverseGreedy.P5ApproximateBoundary

/-!
# S041: approximate EGU and total-variation gaps for genuine clocks

`realClockTV nb r` is the total-variation distance between the genuine
exponential-clock greedy output law and the uniform law on the maximal
independent sets (non-MIS outputs have probability zero, see
`finiteIndependentExp_realClockGreedyOutput_nonMIS`). `RealClockAEGU`
means the infimum over strictly positive rates is zero.

* `realClockTV_ge_deficits`: TV dominates the sum of the deficits of two
  disjoint MIS events;
* IG-N1b: C6 has TV ≥ 4/45 for every positive rate vector, hence is not AEGU;
* IG-N2b: P5 is AEGU but not EGU (explicit family, exact TV formula);
* IG-N3b: P6 has TV ≥ 2√(2/5) − 6/5 for every positive rate vector;
* IG-N6 (m = 2): corona(P3) is AEGU but not EGU (explicit family);
* IG-P9: a disjoint union is AEGU iff both parts are.
-/

open Finset MeasureTheory
namespace InverseGreedy

section TV

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Output probability of a target under genuine exponential clocks. -/
noncomputable def realClockProb (nb : α → Finset α) (r : α → ℝ) (I : Finset α) : ℝ :=
  (finiteIndependentExp r {ω : α → ℝ | realClockGreedyOutput nb ω = I}).toReal

theorem realClockProb_eq (nb : α → Finset α) (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (r : α → ℝ) (hr : ∀ v, 0 < r v) (I : Finset α) :
    realClockProb nb r I = finiteRaceLaw r nb (Fintype.card α) Finset.univ I := by
  unfold realClockProb
  rw [finiteIndependentExp_realClockGreedyOutput_eq_finiteRaceLaw r hr nb hs I,
    ENNReal.toReal_ofReal (finiteRaceLaw_nonneg r hr nb hs I)]

/-- Total variation between the genuine output law and the uniform law on
the maximal independent sets. -/
noncomputable def realClockTV (nb : α → Finset α) (r : α → ℝ) : ℝ :=
  (1 / 2) * ∑ I ∈ maximalIndependentSets nb,
    |realClockProb nb r I - 1 / ((maximalIndependentSets nb).card : ℝ)|

/-- Approximate EGU: uniformity is approached by strictly positive rates. -/
def RealClockAEGU (nb : α → Finset α) : Prop :=
  ∀ ε > 0, ∃ r : α → ℝ, (∀ v, 0 < r v) ∧ realClockTV nb r < ε

private theorem abs_eq_add_two_negPart (y : ℝ) : |y| = y + 2 * max 0 (-y) := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring

private theorem sum_max_zero_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    max 0 (∑ i ∈ s, a i) ≤ ∑ i ∈ s, max 0 (a i) :=
  max_le (Finset.sum_nonneg (fun i _ => le_max_left _ _))
    (Finset.sum_le_sum (fun i _ => le_max_right _ _))

/-- TV equals the total negative part of the deviations. -/
theorem realClockTV_eq_negParts (nb : α → Finset α) (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (hi : ∀ v, v ∉ nb v) (r : α → ℝ) (hr : ∀ v, 0 < r v) :
    realClockTV nb r = ∑ I ∈ maximalIndependentSets nb,
      max 0 (1 / ((maximalIndependentSets nb).card : ℝ) - realClockProb nb r I) := by
  have hm : (0 : ℝ) < (maximalIndependentSets nb).card := by
    exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nb hs hi)
  have hsum : ∑ I ∈ maximalIndependentSets nb,
      (realClockProb nb r I - 1 / ((maximalIndependentSets nb).card : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_congr rfl (fun I _ => realClockProb_eq nb hs r hr I),
      finiteRaceLaw_sum_MIS r hr nb hs hi, Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring
  unfold realClockTV
  simp only [abs_eq_add_two_negPart, Finset.sum_add_distrib, hsum, zero_add, ← Finset.mul_sum]
  simp only [neg_sub]
  ring

/-- **Deficit lower bound.** -/
theorem realClockTV_ge_deficits (nb : α → Finset α) (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (hi : ∀ v, v ∉ nb v) (r : α → ℝ) (hr : ∀ v, 0 < r v)
    (E F : Finset (Finset α)) (hE : E ⊆ maximalIndependentSets nb)
    (hF : F ⊆ maximalIndependentSets nb) (hEF : Disjoint E F) :
    max 0 (E.card / ((maximalIndependentSets nb).card : ℝ) -
        ∑ I ∈ E, realClockProb nb r I) +
      max 0 (F.card / ((maximalIndependentSets nb).card : ℝ) -
        ∑ I ∈ F, realClockProb nb r I) ≤ realClockTV nb r := by
  rw [realClockTV_eq_negParts nb hs hi r hr]
  set m : ℝ := ((maximalIndependentSets nb).card : ℝ)
  have hE' : E.card / m - ∑ I ∈ E, realClockProb nb r I =
      ∑ I ∈ E, (1 / m - realClockProb nb r I) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have hF' : F.card / m - ∑ I ∈ F, realClockProb nb r I =
      ∑ I ∈ F, (1 / m - realClockProb nb r I) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  rw [hE', hF']
  calc
    _ ≤ ∑ I ∈ E, max 0 (1 / m - realClockProb nb r I) +
          ∑ I ∈ F, max 0 (1 / m - realClockProb nb r I) :=
      add_le_add (sum_max_zero_ge _ _) (sum_max_zero_ge _ _)
    _ = ∑ I ∈ E ∪ F, max 0 (1 / m - realClockProb nb r I) :=
      (Finset.sum_union hEF).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hE hF)
      (fun _ _ _ => le_max_left _ _)

theorem realClockTV_nonneg (nb : α → Finset α) (r : α → ℝ) : 0 ≤ realClockTV nb r := by
  unfold realClockTV
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- EGU implies AEGU (zero TV at the witness). -/
theorem RealClockEGU.aegu (nb : α → Finset α) (h : RealClockEGU nb) : RealClockAEGU nb := by
  obtain ⟨r, hr, hu⟩ := h
  intro ε hε
  refine ⟨r, hr, ?_⟩
  have h0 : realClockTV nb r = 0 := by
    unfold realClockTV
    rw [Finset.sum_eq_zero (fun I hI => by
      rw [realClockProb, hu I hI, ENNReal.toReal_ofReal (by positivity), sub_self, abs_zero]),
      mul_zero]
  rw [h0]; exact hε

end TV

/-! ### C6: uniform TV gap -/

theorem c6_realClockTV_ge (r : Fin 6 → ℝ) (hr : ∀ v, 0 < r v) :
    (4 : ℝ) / 45 ≤ realClockTV c6Nb r := by
  have hprob : ∀ I, realClockProb c6Nb r I = finiteRaceLaw r c6Nb 6 Finset.univ I := by
    intro I; rw [realClockProb_eq c6Nb c6Nb_symm r hr I, Fintype.card_fin]
  have hprod := c6_opposite_pair_product_le (r 0) (r 2) (r 4) (r 3) (r 5) (r 1)
    (hr 0) (hr 2) (hr 4) (hr 3) (hr 5) (hr 1)
  have hdef := three_probs_uniform_deficit _ _ _ hprod
  have hbound : ∀ I ∈ maximalIndependentSets c6Nb,
      (1 : ℝ) / 5 - finiteRaceLaw r c6Nb 6 Finset.univ I ≥ 4 / 45 →
      (4 : ℝ) / 45 ≤ realClockTV c6Nb r := by
    intro I hI hI'
    have := realClockTV_ge_deficits c6Nb c6Nb_symm c6Nb_irrefl r hr {I} ∅
      (Finset.singleton_subset_iff.mpr hI) (Finset.empty_subset _) (Finset.disjoint_empty_right _)
    simp only [Finset.card_singleton, Finset.sum_singleton, Finset.card_empty, Nat.cast_zero,
      zero_div, Finset.sum_empty, sub_zero, max_self, add_zero, c6Nb_mis_card,
      Nat.cast_ofNat, hprob] at this
    have hm : (4 : ℝ) / 45 ≤ max 0 (1 / 5 - finiteRaceLaw r c6Nb 6 Finset.univ I) :=
      le_max_of_le_right hI'
    linarith
  rcases hdef with h | h | h
  · exact hbound _ c6Nb_mis_03 (by rw [c6Nb_law_03 r hr]; exact h)
  · exact hbound _ c6Nb_mis_25 (by rw [c6Nb_law_25 r hr]; exact h)
  · exact hbound _ c6Nb_mis_14 (by rw [c6Nb_law_14 r hr]; exact h)

/-- **IG-N1b (Lean, genuine clocks).** C6 is not even approximately EGU. -/
theorem c6_not_realClockAEGU : ¬ RealClockAEGU c6Nb := by
  intro h
  obtain ⟨r, hr, hlt⟩ := h (4 / 45) (by norm_num)
  linarith [c6_realClockTV_ge r hr]

/-! ### P5: unattained approximate EGU -/

theorem p5Nb_mis_eq : maximalIndependentSets p5Nb = {{0, 2, 4}, {0, 3}, {1, 3}, {1, 4}} := by
  decide +kernel

/-- Exact TV along the explicit family `(1,1,t,1,1)`. -/
theorem p5_realClockTV_family (t : ℝ) (ht : 0 < t) :
    realClockTV p5Nb ![1, 1, t, 1, 1] = 3 / 4 - 1 / (t + 2) - 1 / (t + 4) := by
  obtain ⟨r, hrdef⟩ : ∃ r : Fin 5 → ℝ, r = ![1, 1, t, 1, 1] := ⟨_, rfl⟩
  rw [← hrdef]
  have e0 : r 0 = 1 := by rw [hrdef]; rfl
  have e1 : r 1 = 1 := by rw [hrdef]; rfl
  have e2 : r 2 = t := by rw [hrdef]; rfl
  have e3 : r 3 = 1 := by rw [hrdef]; rfl
  have e4 : r 4 = 1 := by rw [hrdef]; rfl
  have hr : ∀ v, 0 < r v := by
    intro v; rw [hrdef]; fin_cases v <;> simp [ht]
  have hprob : ∀ I, realClockProb p5Nb r I = finiteRaceLaw r p5Nb 5 Finset.univ I := by
    intro I; rw [realClockProb_eq p5Nb p5Nb_symm r hr I, Fintype.card_fin]
  rw [realClockTV_eq_negParts p5Nb p5Nb_symm p5Nb_irrefl r hr, p5Nb_mis_eq]
  have hsum := finiteRaceLaw_sum_MIS r hr p5Nb p5Nb_symm p5Nb_irrefl
  rw [p5Nb_mis_eq, Fintype.card_fin] at hsum
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum ⊢
  simp only [hprob]
  rw [show ({{0, 2, 4}, {0, 3}, {1, 3}, {1, 4}} : Finset (Finset (Fin 5))).card = 4 by decide]
  rw [p5Nb_law_03 r hr, p5Nb_law_13 r hr, p5Nb_law_14 r hr] at hsum ⊢
  rw [e0, e1, e2, e3, e4] at hsum ⊢
  have h03 : (1 : ℝ) * 1 / ((1 + 1) * (t + 1 + 1)) = 1 / (2 * (t + 2)) := by
    field_simp; ring
  have h13 : (1 : ℝ) * 1 * (1 + 1 + 1 + 1) / ((1 + 1) * (1 + 1) * (1 + 1 + t + 1 + 1)) =
      1 / (t + 4) := by
    field_simp; ring
  have h14 : (1 : ℝ) * 1 / ((1 + 1) * (1 + 1 + t)) = 1 / (2 * (t + 2)) := by
    field_simp; ring
  rw [h03, h13, h14] at hsum ⊢
  have hp024 : finiteRaceLaw r p5Nb 5 Finset.univ {0, 2, 4} =
      1 - 1 / (t + 2) - 1 / (t + 4) := by
    have : 1 / (2 * (t + 2)) + 1 / (2 * (t + 2)) = 1 / (t + 2) := by field_simp; ring
    linarith
  rw [hp024]
  have ht2 : 1 / (2 * (t + 2)) < 1 / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have ht4 : 1 / (t + 4) < 1 / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hpos := p5_boundary_tv_pos t ht
  rw [← p5_boundary_tv_formula t ht] at hpos
  have hn024 : (1 : ℝ) / ((4 : ℕ) : ℝ) - (1 - 1 / (t + 2) - 1 / (t + 4)) ≤ 0 := by
    push_cast; linarith
  have hn03 : 0 ≤ (1 : ℝ) / ((4 : ℕ) : ℝ) - 1 / (2 * (t + 2)) := by push_cast; linarith
  have hn13 : 0 ≤ (1 : ℝ) / ((4 : ℕ) : ℝ) - 1 / (t + 4) := by push_cast; linarith
  rw [max_eq_left hn024, max_eq_right hn03, max_eq_right hn13]
  push_cast
  field_simp
  ring

/-- **IG-N2b (Lean, genuine clocks).** P5 is approximately EGU, but not EGU. -/
theorem p5_unattained_realClockAEGU : RealClockAEGU p5Nb ∧ ¬ RealClockEGU p5Nb := by
  refine ⟨fun ε hε => ?_, p5Nb_not_realClockEGU⟩
  set t : ℝ := min 1 ε with htdef
  have ht : 0 < t := lt_min one_pos hε
  have hr : ∀ v, 0 < (![1, 1, t, 1, 1] : Fin 5 → ℝ) v := by
    intro v; fin_cases v <;> simp [ht]
  refine ⟨_, hr, ?_⟩
  rw [p5_realClockTV_family t ht, p5_boundary_tv_formula t ht]
  have hlin := p5_boundary_tv_lt_linear t ht
  have : t ≤ ε := min_le_right _ _
  nlinarith

/-! ### P6: sharp TV gap -/

/-- One-variable analytic core of IG-N3b. -/
theorem p6_tv_analytic (u v : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    2 * Real.sqrt (2 / 5) - 6 / 5 ≤
      max 0 (1 / 5 - u * v) + max 0 (2 / 5 - (1 - u) * (1 - v)) := by
  have hp0 : 0 ≤ u * v := mul_nonneg hu hv
  have hq0 : 0 ≤ (1 - u) * (1 - v) := mul_nonneg (by linarith) (by linarith)
  obtain ⟨x, hxdef⟩ : ∃ x, x = Real.sqrt (u * v) := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, y = Real.sqrt ((1 - u) * (1 - v)) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := by rw [hydef]; exact Real.sqrt_nonneg _
  have hx2 : x ^ 2 = u * v := by rw [hxdef]; exact Real.sq_sqrt hp0
  have hy2 : y ^ 2 = (1 - u) * (1 - v) := by rw [hydef]; exact Real.sq_sqrt hq0
  have hX0 : 0 ≤ u * (1 - v) := mul_nonneg hu (by linarith)
  have hY0 : 0 ≤ v * (1 - u) := mul_nonneg hv (by linarith)
  obtain ⟨a, hadef⟩ : ∃ a, a = Real.sqrt (u * (1 - v)) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = Real.sqrt (v * (1 - u)) := ⟨_, rfl⟩
  have ha2 : a ^ 2 = u * (1 - v) := by rw [hadef]; exact Real.sq_sqrt hX0
  have hb2 : b ^ 2 = v * (1 - u) := by rw [hbdef]; exact Real.sq_sqrt hY0
  have hxy_eq : x * y = a * b := by
    rw [hxdef, hydef, hadef, hbdef, ← Real.sqrt_mul hp0, ← Real.sqrt_mul hX0]
    congr 1; ring
  have hamgm : 2 * (x * y) ≤ u * (1 - v) + v * (1 - u) := by
    rw [hxy_eq, ← ha2, ← hb2]; nlinarith [sq_nonneg (a - b)]
  have hsq : (x + y) ^ 2 ≤ 1 := by
    have : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by ring
    rw [this, hx2, hy2]; linarith
  have hxy : x + y ≤ 1 := by
    by_contra hc; push Not at hc
    have : (1 : ℝ) ^ 2 < (x + y) ^ 2 := pow_lt_pow_left₀ hc zero_le_one (by norm_num)
    rw [one_pow] at this; linarith
  have hq' : (1 - u) * (1 - v) ≤ (1 - x) ^ 2 := by
    rw [← hy2]; exact pow_le_pow_left₀ hy0 (by linarith) 2
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (2 / 5) := ⟨_, rfl⟩
  rw [← hsdef]
  have hs2 : s ^ 2 = 2 / 5 := by rw [hsdef]; exact Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hsl : 3 / 5 < s := by
    by_contra hc; push Not at hc
    have : s ^ 2 ≤ (3 / 5) ^ 2 := pow_le_pow_left₀ hs0 hc 2
    have h9 : ((3 : ℝ) / 5) ^ 2 = 9 / 25 := by norm_num
    linarith
  have hs1 : s < 1 := by
    by_contra hc; push Not at hc
    have : (1 : ℝ) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ zero_le_one hc 2
    rw [one_pow] at this; linarith
  have hm1 := le_max_left (0 : ℝ) (1 / 5 - u * v)
  have hm2 := le_max_right (0 : ℝ) (1 / 5 - u * v)
  have hm3 := le_max_left (0 : ℝ) (2 / 5 - (1 - u) * (1 - v))
  have hm4 := le_max_right (0 : ℝ) (2 / 5 - (1 - u) * (1 - v))
  rcases le_total x (1 - s) with hxa | hxa
  · have hpx : x ^ 2 ≤ (1 - s) ^ 2 := pow_le_pow_left₀ hx0 hxa 2
    have hexp : (1 - s) ^ 2 = 7 / 5 - 2 * s := by linear_combination hs2
    linarith
  · by_cases hb : u * v ≤ 1 / 5
    · have hxs : x ≤ s := by
        by_contra hc; push Not at hc
        have : s ^ 2 < x ^ 2 := pow_lt_pow_left₀ hc hs0 (by norm_num)
        linarith
      have hprod : 0 ≤ (x - (1 - s)) * (s - x) := mul_nonneg (by linarith) (by linarith)
      have hquad : -(2 / 5) + 2 * x - 2 * x ^ 2 - (2 * s - 6 / 5) = 2 * ((x - (1 - s)) * (s - x)) := by
        linear_combination (-2 : ℝ) * hs2
      have hexp : (1 - x) ^ 2 = 1 - 2 * x + x ^ 2 := by ring
      linarith
    · push Not at hb
      obtain ⟨c, hcdef⟩ : ∃ c, c = Real.sqrt (1 / 5) := ⟨_, rfl⟩
      have hc2 : c ^ 2 = 1 / 5 := by rw [hcdef]; exact Real.sq_sqrt (by norm_num)
      have hc0 : 0 ≤ c := by rw [hcdef]; exact Real.sqrt_nonneg _
      have hcl : 2 / 5 ≤ c := by
        by_contra hc; push Not at hc
        have : c ^ 2 < (2 / 5) ^ 2 := pow_lt_pow_left₀ hc hc0 (by norm_num)
        have h4 : ((2 : ℝ) / 5) ^ 2 = 4 / 25 := by norm_num
        linarith
      have hc1 : c ≤ 1 := by
        by_contra hc; push Not at hc
        have : (1 : ℝ) ^ 2 < c ^ 2 := pow_lt_pow_left₀ hc zero_le_one (by norm_num)
        rw [one_pow] at this; linarith
      have hsc : s ≤ c + 1 / 5 := by
        by_contra hc; push Not at hc
        have h1 : (c + 1 / 5) ^ 2 < s ^ 2 := pow_lt_pow_left₀ hc (by linarith) (by norm_num)
        have h2 : (c + 1 / 5) ^ 2 = c ^ 2 + 2 / 5 * c + 1 / 25 := by ring
        linarith
      have hxc : c < x := by
        by_contra hcx; push Not at hcx
        have : x ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hx0 hcx 2
        linarith
      have hx1 : x ≤ 1 := by linarith
      have hmono : (1 - x) ^ 2 ≤ (1 - c) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hexp : (1 - c) ^ 2 = 6 / 5 - 2 * c := by linear_combination hc2
      linarith

/-- **IG-N3b (Lean, genuine clocks).** -/
theorem p6_realClockTV_ge (r : Fin 6 → ℝ) (hr : ∀ v, 0 < r v) :
    2 * Real.sqrt (2 / 5) - 6 / 5 ≤ realClockTV p6Nb r := by
  have hprob : ∀ I, realClockProb p6Nb r I = finiteRaceLaw r p6Nb 6 Finset.univ I := by
    intro I; rw [realClockProb_eq p6Nb p6Nb_symm r hr I, Fintype.card_fin]
  have hdef := realClockTV_ge_deficits p6Nb p6Nb_symm p6Nb_irrefl r hr {{1, 4}}
    {{0, 2, 5}, {0, 3, 5}} (by
      intro I hI; rw [Finset.mem_singleton] at hI; rw [hI]; exact p6Nb_mis_14)
    (by
      intro I hI
      rcases Finset.mem_insert.mp hI with rfl | hI
      · exact p6Nb_mis_025
      · rw [Finset.mem_singleton] at hI; rw [hI]; exact p6Nb_mis_035)
    (by decide)
  have hsF : ∑ I ∈ ({{0, 2, 5}, {0, 3, 5}} : Finset (Finset (Fin 6))), realClockProb p6Nb r I =
      realClockProb p6Nb r {0, 2, 5} + realClockProb p6Nb r {0, 3, 5} := by
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Finset.card_singleton, Finset.sum_singleton, hsF,
    show ({{0, 2, 5}, {0, 3, 5}} : Finset (Finset (Fin 6))).card = 2 by decide,
    p6Nb_mis_card, hprob, hprob, hprob, p6Nb_law_14 r hr] at hdef
  have hb := p6Nb_endpoint_bound r hr
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2
  have h3 := hr 3; have h4 := hr 4; have h5 := hr 5
  obtain ⟨u, hudef⟩ : ∃ u, u = r 1 / (r 0 + r 1 + r 2) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, v = r 4 / (r 3 + r 4 + r 5) := ⟨_, rfl⟩
  rw [← hudef, ← hvdef] at hdef hb
  have hu : 0 ≤ u := by rw [hudef]; positivity
  have hv : 0 ≤ v := by rw [hvdef]; positivity
  have hu1 : u ≤ 1 := by rw [hudef, div_le_one (by positivity)]; linarith
  have hv1 : v ≤ 1 := by rw [hvdef, div_le_one (by positivity)]; linarith
  have han := p6_tv_analytic u v hu hu1 hv hv1
  have hmono : max 0 (2 / 5 - (1 - u) * (1 - v)) ≤
      max 0 ((2 : ℝ) / 5 - (finiteRaceLaw r p6Nb 6 Finset.univ {0, 2, 5} +
        finiteRaceLaw r p6Nb 6 Finset.univ {0, 3, 5})) :=
    max_le_max (le_refl _) (by linarith)
  norm_num at hdef
  linarith

/-! ### corona(P3): unattained approximate EGU (IG-N6, m = 2) -/

theorem coronaP3Nb_mis_eq :
    maximalIndependentSets coronaP3Nb = {{3, 4, 5}, {0, 4, 5}, {2, 3, 4}, {0, 2, 4}, {1, 3, 5}} := by
  decide +kernel

/-- **IG-N6, m = 2 (Lean, genuine clocks).** The corona of P3 is
approximately EGU but not EGU: along rates `(1,t,1,1,4t,1)`, TV < 2/(25 t). -/
theorem coronaP3_unattained_realClockAEGU :
    RealClockAEGU coronaP3Nb ∧ ¬ RealClockEGU coronaP3Nb := by
  refine ⟨fun ε hε => ?_, coronaP3Nb_not_realClockEGU⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = 1 / ε := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; positivity
  obtain ⟨r, hrdef⟩ : ∃ r : Fin 6 → ℝ, r = ![1, t, 1, 1, 4 * t, 1] := ⟨_, rfl⟩
  have e0 : r 0 = 1 := by rw [hrdef]; rfl
  have e1 : r 1 = t := by rw [hrdef]; rfl
  have e2 : r 2 = 1 := by rw [hrdef]; rfl
  have e3 : r 3 = 1 := by rw [hrdef]; rfl
  have e4 : r 4 = 4 * t := by rw [hrdef]; rfl
  have e5 : r 5 = 1 := by rw [hrdef]; rfl
  have hr : ∀ v, 0 < r v := by
    intro v; rw [hrdef]; fin_cases v <;> simp [ht]
  refine ⟨r, hr, ?_⟩
  have hprob : ∀ I, realClockProb coronaP3Nb r I = finiteRaceLaw r coronaP3Nb 6 Finset.univ I := by
    intro I; rw [realClockProb_eq coronaP3Nb coronaP3Nb_symm r hr I, Fintype.card_fin]
  have hsum := finiteRaceLaw_sum_MIS r hr coronaP3Nb coronaP3Nb_symm coronaP3Nb_irrefl
  rw [realClockTV_eq_negParts coronaP3Nb coronaP3Nb_symm coronaP3Nb_irrefl r hr,
    coronaP3Nb_mis_eq]
  rw [coronaP3Nb_mis_eq, Fintype.card_fin] at hsum
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum ⊢
  simp only [hprob]
  rw [show ({{3, 4, 5}, {0, 4, 5}, {2, 3, 4}, {0, 2, 4}, {1, 3, 5}} :
    Finset (Finset (Fin 6))).card = 5 by decide]
  rw [coronaP3Nb_law_345 r hr, coronaP3Nb_law_045 r hr, coronaP3Nb_law_234 r hr,
    coronaP3Nb_law_024 r hr] at hsum ⊢
  simp only [coronaP3Survival] at hsum ⊢
  rw [e0, e1, e2, e3, e4, e5] at hsum ⊢
  obtain ⟨P, hPdef⟩ : ∃ P, P = finiteRaceLaw r coronaP3Nb 6 Finset.univ {1, 3, 5} := ⟨_, rfl⟩
  rw [← hPdef] at hsum ⊢
  have e0' : (1 - 1 / (1 + 1)) * (1 - 1 / (1 + 1)) * ((4 * t + 0) / (t + 4 * t + 0)) =
      (1 : ℝ) / 5 := by field_simp; ring
  have ea : 1 / (1 + 1) * (1 - 1 / (1 + 1)) * ((4 * t + (1 + 1)) / (t + 4 * t + (1 + 1))) =
      (1 : ℝ) / 5 + 1 / (10 * (5 * t + 2)) := by field_simp; ring
  have ec : (1 - 1 / (1 + 1)) * (1 / (1 + 1)) * ((4 * t + (1 + 1)) / (t + 4 * t + (1 + 1))) =
      (1 : ℝ) / 5 + 1 / (10 * (5 * t + 2)) := by field_simp; ring
  have eac : 1 / (1 + 1) * (1 / (1 + 1)) *
      ((4 * t + (1 + 1 + (1 + 1))) / (t + 4 * t + (1 + 1 + (1 + 1)))) =
      (1 : ℝ) / 5 + 1 / (5 * (5 * t + 4)) := by field_simp; ring
  rw [e0', ea, ec, eac] at hsum ⊢
  have hA : 0 < 1 / (10 * (5 * t + 2)) := by positivity
  have hB : 0 < 1 / (5 * (5 * t + 4)) := by positivity
  have hP : P = 1 / 5 - 2 * (1 / (10 * (5 * t + 2))) - 1 / (5 * (5 * t + 4)) := by linarith
  rw [hP]
  push_cast
  have n0 : (1 : ℝ) / 5 - 1 / 5 ≤ 0 := by norm_num
  have na : (1 : ℝ) / 5 - (1 / 5 + 1 / (10 * (5 * t + 2))) ≤ 0 := by linarith
  have nac : (1 : ℝ) / 5 - (1 / 5 + 1 / (5 * (5 * t + 4))) ≤ 0 := by linarith
  have nP : 0 ≤ (1 : ℝ) / 5 - (1 / 5 - 2 * (1 / (10 * (5 * t + 2))) - 1 / (5 * (5 * t + 4))) := by
    linarith
  rw [max_eq_left n0, max_eq_left na, max_eq_left nac, max_eq_right nP]
  have hbound : 2 * (1 / (10 * (5 * t + 2))) + 1 / (5 * (5 * t + 4)) < 1 / t := by
    have h1 : 1 / (10 * (5 * t + 2)) < 1 / (25 * t) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h2 : 1 / (5 * (5 * t + 4)) < 1 / (25 * t) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h3 : 3 * (1 / (25 * t)) < 1 / t := by
      rw [show 3 * (1 / (25 * t)) = 3 / (25 * t) by ring,
        div_lt_div_iff₀ (by positivity) ht]; nlinarith
    linarith
  have : 1 / t = ε := by rw [htdef]; field_simp
  linarith

/-! ### AEGU closure under disjoint union (IG-P9) -/

section UnionAEGU

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem realClockTV_union_eq_sum (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (rG : α → ℝ) (rH : β → ℝ) (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b) :
    realClockTV (unionNb nG nH) (sumRates rG rH) =
      (1 / 2) * ∑ I ∈ maximalIndependentSets nG, ∑ J ∈ maximalIndependentSets nH,
        |realClockProb nG rG I * realClockProb nH rH J -
          1 / ((maximalIndependentSets nG).card : ℝ) *
            (1 / ((maximalIndependentSets nH).card : ℝ))| := by
  unfold realClockTV
  rw [maximalIndependentSets_union_card, maximalIndependentSets_union_eq,
    Finset.sum_image (by
      rintro ⟨I, J⟩ _ ⟨I', J'⟩ _ h
      simp only [Finset.disjSum_inj] at h; rw [h.1, h.2]), Finset.sum_product]
  congr 1
  apply Finset.sum_congr rfl; intro I _
  apply Finset.sum_congr rfl; intro J _
  rw [realClockProb_eq _ (unionNb_symm hGs hHs) _ (sumRates_pos hG hH),
    finiteRaceLaw_union_univ rG rH hG hH, realClockProb_eq nG hGs rG hG,
    realClockProb_eq nH hHs rH hH]
  push_cast
  rw [one_div_mul_one_div]

theorem realClockTV_union_le (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v)
    (rG : α → ℝ) (rH : β → ℝ) (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b) :
    realClockTV (unionNb nG nH) (sumRates rG rH) ≤ realClockTV nG rG + realClockTV nH rH := by
  rw [realClockTV_union_eq_sum nG nH hGs hHs rG rH hG hH]
  set mG : ℝ := ((maximalIndependentSets nG).card : ℝ) with hmGdef
  set mH : ℝ := ((maximalIndependentSets nH).card : ℝ) with hmHdef
  clear_value mG mH
  have hmG : 0 < mG := by
    rw [hmGdef]; exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nG hGs hGi)
  have hmH : 0 < mH := by
    rw [hmHdef]; exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nH hHs hHi)
  have hq : ∀ J, 0 ≤ realClockProb nH rH J := fun J => ENNReal.toReal_nonneg
  have hsumH : ∑ J ∈ maximalIndependentSets nH, realClockProb nH rH J = 1 := by
    rw [Finset.sum_congr rfl (fun J _ => realClockProb_eq nH hHs rH hH J)]
    exact finiteRaceLaw_sum_MIS rH hH nH hHs hHi
  have hpt : ∀ I J, |realClockProb nG rG I * realClockProb nH rH J - 1 / mG * (1 / mH)| ≤
      |realClockProb nG rG I - 1 / mG| * realClockProb nH rH J +
        1 / mG * |realClockProb nH rH J - 1 / mH| := by
    intro I J
    have : realClockProb nG rG I * realClockProb nH rH J - 1 / mG * (1 / mH) =
        (realClockProb nG rG I - 1 / mG) * realClockProb nH rH J +
          1 / mG * (realClockProb nH rH J - 1 / mH) := by ring
    rw [this]
    calc _ ≤ |(realClockProb nG rG I - 1 / mG) * realClockProb nH rH J| +
          |1 / mG * (realClockProb nH rH J - 1 / mH)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hq J), abs_of_pos (one_div_pos.mpr hmG)]
  calc (1 / 2) * ∑ I ∈ maximalIndependentSets nG, ∑ J ∈ maximalIndependentSets nH,
        |realClockProb nG rG I * realClockProb nH rH J - 1 / mG * (1 / mH)|
      ≤ (1 / 2) * ∑ I ∈ maximalIndependentSets nG, ∑ J ∈ maximalIndependentSets nH,
        (|realClockProb nG rG I - 1 / mG| * realClockProb nH rH J +
          1 / mG * |realClockProb nH rH J - 1 / mH|) := by
        gcongr with I _ J _; exact hpt I J
    _ = realClockTV nG rG + realClockTV nH rH := by
        unfold realClockTV
        rw [← hmGdef, ← hmHdef]
        have inner : ∀ I ∈ maximalIndependentSets nG,
            ∑ J ∈ maximalIndependentSets nH,
              (|realClockProb nG rG I - 1 / mG| * realClockProb nH rH J +
                1 / mG * |realClockProb nH rH J - 1 / mH|) =
            |realClockProb nG rG I - 1 / mG| +
              1 / mG * ∑ J ∈ maximalIndependentSets nH, |realClockProb nH rH J - 1 / mH| := by
          intro I _
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumH, mul_one, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl inner, Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul, ← hmGdef]
        have hcancel : mG * (1 / mG * ∑ J ∈ maximalIndependentSets nH,
            |realClockProb nH rH J - 1 / mH|) =
            ∑ J ∈ maximalIndependentSets nH, |realClockProb nH rH J - 1 / mH| := by
          rw [← mul_assoc, mul_one_div_cancel hmG.ne', one_mul]
        rw [hcancel]
        ring

theorem realClockTV_le_union_left (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v)
    (rG : α → ℝ) (rH : β → ℝ) (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b) :
    realClockTV nG rG ≤ realClockTV (unionNb nG nH) (sumRates rG rH) := by
  rw [realClockTV_union_eq_sum nG nH hGs hHs rG rH hG hH]
  unfold realClockTV
  set mH : ℝ := ((maximalIndependentSets nH).card : ℝ) with hmHdef
  clear_value mH
  have hmH : 0 < mH := by
    rw [hmHdef]; exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nH hHs hHi)
  have hsumH : ∑ J ∈ maximalIndependentSets nH, realClockProb nH rH J = 1 := by
    rw [Finset.sum_congr rfl (fun J _ => realClockProb_eq nH hHs rH hH J)]
    exact finiteRaceLaw_sum_MIS rH hH nH hHs hHi
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro I _
  have : realClockProb nG rG I - 1 / ((maximalIndependentSets nG).card : ℝ) =
      ∑ J ∈ maximalIndependentSets nH, (realClockProb nG rG I * realClockProb nH rH J -
        1 / ((maximalIndependentSets nG).card : ℝ) * (1 / mH)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumH, Finset.sum_const, nsmul_eq_mul,
      ← hmHdef]
    field_simp
  rw [this]
  exact Finset.abs_sum_le_sum_abs _ _

theorem realClockTV_le_union_right (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v)
    (rG : α → ℝ) (rH : β → ℝ) (hG : ∀ a, 0 < rG a) (hH : ∀ b, 0 < rH b) :
    realClockTV nH rH ≤ realClockTV (unionNb nG nH) (sumRates rG rH) := by
  rw [realClockTV_union_eq_sum nG nH hGs hHs rG rH hG hH, Finset.sum_comm]
  unfold realClockTV
  set mG : ℝ := ((maximalIndependentSets nG).card : ℝ) with hmGdef
  clear_value mG
  have hmG : 0 < mG := by
    rw [hmGdef]; exact_mod_cast Finset.card_pos.mpr (maximalIndependentSets_nonempty nG hGs hGi)
  have hsumG : ∑ I ∈ maximalIndependentSets nG, realClockProb nG rG I = 1 := by
    rw [Finset.sum_congr rfl (fun I _ => realClockProb_eq nG hGs rG hG I)]
    exact finiteRaceLaw_sum_MIS rG hG nG hGs hGi
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro J _
  have : realClockProb nH rH J - 1 / ((maximalIndependentSets nH).card : ℝ) =
      ∑ I ∈ maximalIndependentSets nG, (realClockProb nG rG I * realClockProb nH rH J -
        1 / mG * (1 / ((maximalIndependentSets nH).card : ℝ))) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsumG, Finset.sum_const, nsmul_eq_mul,
      ← hmGdef]
    field_simp
  rw [this]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **IG-P9 (Lean, genuine clocks).** A disjoint union is AEGU iff both parts are. -/
theorem realClockAEGU_union_iff (nG : α → Finset α) (nH : β → Finset β)
    (hGs : ∀ x y, y ∈ nG x → x ∈ nG y) (hHs : ∀ x y, y ∈ nH x → x ∈ nH y)
    (hGi : ∀ v, v ∉ nG v) (hHi : ∀ v, v ∉ nH v) :
    RealClockAEGU (unionNb nG nH) ↔ RealClockAEGU nG ∧ RealClockAEGU nH := by
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨r, hr, hlt⟩ := h ε hε
      refine ⟨fun a => r (Sum.inl a), fun a => hr _, ?_⟩
      have := realClockTV_le_union_left nG nH hGs hHs hGi hHi _ _
        (fun a => hr (Sum.inl a)) (fun b => hr (Sum.inr b))
      rw [sumRates_comp] at this
      linarith
    · obtain ⟨r, hr, hlt⟩ := h ε hε
      refine ⟨fun b => r (Sum.inr b), fun b => hr _, ?_⟩
      have := realClockTV_le_union_right nG nH hGs hHs hGi hHi _ _
        (fun a => hr (Sum.inl a)) (fun b => hr (Sum.inr b))
      rw [sumRates_comp] at this
      linarith
  · rintro ⟨hG, hH⟩ ε hε
    obtain ⟨rG, hrG, hltG⟩ := hG (ε / 2) (by positivity)
    obtain ⟨rH, hrH, hltH⟩ := hH (ε / 2) (by positivity)
    refine ⟨sumRates rG rH, sumRates_pos hrG hrH, ?_⟩
    have := realClockTV_union_le nG nH hGs hHs hGi hHi rG rH hrG hrH
    linarith

end UnionAEGU

end InverseGreedy
