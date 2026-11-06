import InverseGreedy.CographEGU
import InverseGreedy.SmallGraphObstructions

/-!
# S041: infinite families — clique coronas (IG-P8) and star coronas (IG-N5)

Two general tools:
* **target locality** `finiteRaceLaw_congr_target`: the first-choice law of a
  target set only depends on the neighbourhoods of target vertices;
* **pendant pairs** `finiteRaceLaw_pendant_leaves`: if each leaf `inl i` has
  the single neighbour `inr i`, the probability of accepting all leaves of a
  block of pairs is `∏ rᵢ/(rᵢ + sᵢ)`.

Consequences, for genuine exponential clocks:
* every clique corona `K_m ∘ K₁` (m ≥ 1) is EGU, with leaf rate 1 and clique
  rate `(m+1)^(1/m) - 1`;
* every pendant star corona `K_{1,m} ∘ K₁` with `m ≥ 2` is not EGU.
-/

open Finset
namespace InverseGreedy

/-- **Target locality.** -/
theorem finiteRaceLaw_congr_target {γ : Type*} [DecidableEq γ] (r : γ → ℝ)
    (nb1 nb2 : γ → Finset γ) :
    ∀ (fuel : ℕ) (A T : Finset γ), (∀ v ∈ T, nb1 v = nb2 v) →
      finiteRaceLaw r nb1 fuel A T = finiteRaceLaw r nb2 fuel A T
  | 0, A, T, _ => by simp [finiteRaceLaw]
  | fuel + 1, A, T, h => by
      by_cases hA : A = ∅
      · simp [finiteRaceLaw, hA]
      · rw [finiteRaceLaw_step _ _ fuel _ _ hA, finiteRaceLaw_step _ _ fuel _ _ hA]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs with hv
        · have hafter : afterChoice nb1 A v = afterChoice nb2 A v := by
            simp [afterChoice, h v hv]
          rw [hafter, finiteRaceLaw_congr_target r nb1 nb2 fuel _ _
            (fun w hw => h w (Finset.mem_of_mem_erase hw))]
        · rfl

/-- **Pendant pairs.** -/
theorem finiteRaceLaw_pendant_leaves {β : Type*} [DecidableEq β]
    (r : β ⊕ β → ℝ) (hr : ∀ v, 0 < r v) (nb : β ⊕ β → Finset (β ⊕ β))
    (hleaf : ∀ i, nb (Sum.inl i) = (∅ : Finset β).disjSum {i}) :
    ∀ (fuel : ℕ) (S : Finset β), 2 * S.card ≤ fuel →
      finiteRaceLaw r nb fuel (S.disjSum S) (S.disjSum ∅) =
        ∏ i ∈ S, r (Sum.inl i) / (r (Sum.inl i) + r (Sum.inr i))
  | 0, S, h => by
      have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hS; simp [finiteRaceLaw]
  | fuel + 1, S, h => by
      by_cases hS : S = ∅
      · subst hS; simp [finiteRaceLaw]
      · have hne : S.disjSum S ≠ ∅ := by rw [Ne, Finset.disjSum_eq_empty]; tauto
        rw [finiteRaceLaw_step _ _ fuel _ _ hne, Finset.sum_disjSum]
        simp only [Finset.inr_mem_disjSum, Finset.notMem_empty, if_false,
          Finset.sum_const_zero, add_zero, Finset.inl_mem_disjSum]
        set f : β → ℝ := fun i => r (Sum.inl i) / (r (Sum.inl i) + r (Sum.inr i)) with hf
        have hΛ : activeRate r (S.disjSum S) =
            ∑ j ∈ S, (r (Sum.inl j) + r (Sum.inr j)) := by
          simp [activeRate, Finset.sum_disjSum, Finset.sum_add_distrib]
        have hΛpos : 0 < ∑ j ∈ S, (r (Sum.inl j) + r (Sum.inr j)) :=
          Finset.sum_pos (fun j _ => add_pos (hr _) (hr _))
            (Finset.nonempty_iff_ne_empty.mpr hS)
        have hterm : ∀ i ∈ S,
            (if i ∈ S then firstChoice r (S.disjSum S) (Sum.inl i) *
              finiteRaceLaw r nb fuel (afterChoice nb (S.disjSum S) (Sum.inl i))
                ((S.disjSum ∅).erase (Sum.inl i)) else 0) =
            (r (Sum.inl i) + r (Sum.inr i)) / (∑ j ∈ S, (r (Sum.inl j) + r (Sum.inr j))) *
              ∏ j ∈ S, f j := by
          intro i hi
          have hafter : afterChoice nb (S.disjSum S) (Sum.inl i) =
              (S.erase i).disjSum (S.erase i) := by
            ext x; cases x <;> simp [afterChoice, hleaf, and_comm]
          have hcard : (S.erase i).card + 1 = S.card := Finset.card_erase_add_one hi
          rw [if_pos hi, hafter, disjSum_erase_inl,
            finiteRaceLaw_pendant_leaves r hr nb hleaf fuel (S.erase i) (by omega),
            firstChoice, hΛ, ← Finset.mul_prod_erase S f hi]
          have h1 := hr (Sum.inl i)
          have h2 := hr (Sum.inr i)
          simp only [hf]
          field_simp
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_div,
          div_self hΛpos.ne', one_mul]

/-! ### clique coronas -/

/-- Clique corona `K_m ∘ K₁`: leaves `inl i` (pendant at `inr i`), centres
`inr i` forming a clique. -/
def cliqueCoronaNb (m : ℕ) : Fin m ⊕ Fin m → Finset (Fin m ⊕ Fin m)
  | Sum.inl i => (∅ : Finset (Fin m)).disjSum {i}
  | Sum.inr i => ({i} : Finset (Fin m)).disjSum (Finset.univ.erase i)

theorem cliqueCoronaNb_symm (m : ℕ) :
    ∀ x y, y ∈ cliqueCoronaNb m x → x ∈ cliqueCoronaNb m y := by
  rintro (i | i) (j | j) h <;> simp_all [cliqueCoronaNb, eq_comm]

theorem cliqueCoronaNb_irrefl (m : ℕ) : ∀ v, v ∉ cliqueCoronaNb m v := by
  rintro (i | i) <;> simp [cliqueCoronaNb]

theorem cliqueCorona_isMIS_iff (m : ℕ) (K : Finset (Fin m ⊕ Fin m)) :
    IsMaximalIndependentSet (cliqueCoronaNb m) K ↔
      K = Finset.univ.disjSum ∅ ∨ ∃ c, K = (Finset.univ.erase c).disjSum {c} := by
  constructor
  · rintro ⟨hind, hdom⟩
    have hLC : ∀ i, Sum.inl i ∈ K → Sum.inr i ∉ K := by
      intro i hl hr'
      exact hind _ hl _ hr' (by simp [cliqueCoronaNb])
    have hCC : ∀ i j, Sum.inr i ∈ K → Sum.inr j ∈ K → i = j := by
      intro i j hi hj
      by_contra hij
      exact hind _ hi _ hj (by simp [cliqueCoronaNb, Ne.symm hij])
    have hcover : ∀ i, Sum.inl i ∉ K → Sum.inr i ∈ K := by
      intro i hl
      obtain ⟨u, hu, hiu⟩ := hdom _ hl
      rcases u with j | j
      · simp [cliqueCoronaNb] at hiu
      · simp only [cliqueCoronaNb, Finset.inl_mem_disjSum, Finset.mem_singleton] at hiu
        rw [hiu]; exact hu
    by_cases hc : ∃ c, Sum.inr c ∈ K
    · obtain ⟨c, hcK⟩ := hc
      right
      refine ⟨c, ?_⟩
      ext x
      rcases x with i | i
      · simp only [Finset.inl_mem_disjSum, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hi hic; subst hic; exact hLC _ hi hcK
        · intro hic
          by_contra hi
          exact hic (hCC _ _ (hcover i hi) hcK)
      · simp only [Finset.inr_mem_disjSum, Finset.mem_singleton]
        constructor
        · intro hi; exact hCC _ _ hi hcK
        · rintro rfl; exact hcK
    · left
      push Not at hc
      ext x
      rcases x with i | i
      · simp only [Finset.inl_mem_disjSum, Finset.mem_univ, iff_true]
        by_contra hi
        exact hc i (hcover i hi)
      · simp only [Finset.inr_mem_disjSum, Finset.notMem_empty, iff_false]
        exact hc i
  · rintro (rfl | ⟨c, rfl⟩)
    · refine ⟨?_, ?_⟩
      · rintro (i | i) hu (j | j) hv <;> simp_all [cliqueCoronaNb]
      · rintro (i | i) hv
        · simp at hv
        · exact ⟨Sum.inl i, by simp, by simp [cliqueCoronaNb]⟩
    · refine ⟨?_, ?_⟩
      · rintro (i | i) hu (j | j) hv <;> simp_all [cliqueCoronaNb, eq_comm]
      · rintro (i | i) hv
        · simp only [Finset.inl_mem_disjSum, Finset.mem_erase, Finset.mem_univ, and_true,
            not_not] at hv
          subst hv
          exact ⟨Sum.inr i, by simp, by simp [cliqueCoronaNb]⟩
        · simp only [Finset.inr_mem_disjSum, Finset.mem_singleton] at hv
          exact ⟨Sum.inr c, by simp, by simpa [cliqueCoronaNb] using hv⟩

/-- The clique-corona rate vector: leaves `1`, centres `β`. -/
noncomputable def cliqueCoronaRates (m : ℕ) (β : ℝ) : Fin m ⊕ Fin m → ℝ :=
  sumRates (fun _ => 1) (fun _ => β)

/-- **IG-P8 (Lean, genuine clocks).** Every clique corona is EGU. -/
theorem cliqueCorona_realClockEGU (m : ℕ) (hm : 0 < m) :
    RealClockEGU (cliqueCoronaNb m) := by
  set β : ℝ := ((m : ℝ) + 1) ^ ((m : ℕ)⁻¹ : ℝ) - 1 with hβdef
  have hβpow : (1 + β) ^ m = (m : ℝ) + 1 := by
    rw [hβdef, add_sub_cancel]
    exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hβ : 0 < β := by
    by_contra hneg
    push Not at hneg
    have h1 : 1 + β ≤ 1 := by linarith
    have h0 : 0 ≤ 1 + β := by
      rw [hβdef, add_sub_cancel]; positivity
    have : (1 + β) ^ m ≤ 1 := pow_le_one₀ h0 h1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set r := cliqueCoronaRates m β with hrdef
  have hr : ∀ v, 0 < r v := by
    rintro (i | i)
    · simp [hrdef, cliqueCoronaRates, sumRates]
    · simpa [hrdef, cliqueCoronaRates, sumRates] using hβ
  set nb := cliqueCoronaNb m
  have hs := cliqueCoronaNb_symm m
  have hi := cliqueCoronaNb_irrefl m
  have hfuel : Fintype.card (Fin m ⊕ Fin m) = 2 * (Finset.univ : Finset (Fin m)).card := by
    simp [Fintype.card_sum]; ring
  have huniv : (Finset.univ : Finset (Fin m ⊕ Fin m)) = Finset.univ.disjSum Finset.univ :=
    Finset.univ_disjSum_univ.symm
  -- probability of the all-leaves set
  have hL : finiteRaceLaw r nb (Fintype.card (Fin m ⊕ Fin m)) Finset.univ
      (Finset.univ.disjSum ∅) = 1 / ((m : ℝ) + 1) := by
    rw [huniv, finiteRaceLaw_pendant_leaves r hr nb (fun i => rfl) _ _ (by rw [hfuel])]
    simp only [hrdef, cliqueCoronaRates, sumRates, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [div_pow, one_pow, add_comm 1 β, add_comm β 1, hβpow]
  -- symmetry of the centre sets
  have hsym : ∀ c d : Fin m,
      finiteRaceLaw r nb (Fintype.card (Fin m ⊕ Fin m)) Finset.univ
          ((Finset.univ.erase c).disjSum {c}) =
        finiteRaceLaw r nb (Fintype.card (Fin m ⊕ Fin m)) Finset.univ
          ((Finset.univ.erase d).disjSum {d}) := by
    intro c d
    let σ : Equiv.Perm (Fin m) := Equiv.swap c d
    let e : Fin m ⊕ Fin m ≃ Fin m ⊕ Fin m := Equiv.sumCongr σ σ
    have hnb : ∀ a, nb (e a) = (nb a).map e.toEmbedding := by
      rintro (i | i)
      · ext x; rcases x with j | j <;> simp [nb, e, cliqueCoronaNb, σ, Equiv.swap_apply_eq_iff]
      · ext x; rcases x with j | j <;>
          simp [nb, e, cliqueCoronaNb, σ, Equiv.swap_apply_eq_iff]
    have hre : (fun a => r (e a)) = r := by
      funext a; rcases a with i | i <;> simp [hrdef, cliqueCoronaRates, sumRates, e]
    have hmapU : (Finset.univ : Finset (Fin m ⊕ Fin m)).map e.toEmbedding = Finset.univ := by
      simp
    have hmapT : ((Finset.univ.erase c).disjSum {c}).map e.toEmbedding =
        (Finset.univ.erase d).disjSum ({d} : Finset (Fin m)) := by
      ext x; rcases x with j | j <;>
        simp [e, σ, Finset.mem_map_equiv, Equiv.swap_apply_eq_iff]
    have := finiteRaceLaw_map_equiv e nb nb hnb r (Fintype.card (Fin m ⊕ Fin m))
      Finset.univ ((Finset.univ.erase c).disjSum {c})
    rw [hmapU, hmapT, hre] at this
    exact this.symm
  -- the MIS family
  have hM : maximalIndependentSets nb =
      insert (Finset.univ.disjSum ∅)
        (Finset.univ.image (fun c : Fin m => (Finset.univ.erase c).disjSum {c})) := by
    ext K
    rw [mem_maximalIndependentSets, cliqueCorona_isMIS_iff]
    simp [eq_comm]
  have hLnot : Finset.univ.disjSum ∅ ∉
      Finset.univ.image (fun c : Fin m => (Finset.univ.erase c).disjSum ({c} : Finset (Fin m))) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro c h
    have := congrArg (fun K => Sum.inr c ∈ K) h
    simp at this
  have hinj : Function.Injective (fun c : Fin m => (Finset.univ.erase c).disjSum ({c} : Finset (Fin m))) := by
    intro c d h
    have := congrArg (fun K => Sum.inr c ∈ K) h
    simpa using this
  have hcard : (maximalIndependentSets nb).card = m + 1 := by
    rw [hM, Finset.card_insert_of_notMem hLnot, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  rw [realClockEGU_iff_firstChoiceEGU _ hs]
  refine ⟨r, hr, ?_⟩
  -- value of each centre set
  obtain ⟨c0⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hsum := finiteRaceLaw_sum_MIS r hr nb hs hi
  rw [hM, Finset.sum_insert hLnot, Finset.sum_image (fun c _ d _ h => hinj h), hL,
    Finset.sum_congr rfl (fun c _ => hsym c c0), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc0 : finiteRaceLaw r nb (Fintype.card (Fin m ⊕ Fin m)) Finset.univ
      ((Finset.univ.erase c0).disjSum {c0}) = 1 / ((m : ℝ) + 1) := by
    field_simp at hsum ⊢
    nlinarith
  intro K hK
  rw [hcard]
  push_cast
  rw [hM] at hK
  rcases Finset.mem_insert.mp hK with rfl | hK'
  · exact hL
  · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hK'
    rw [hsym c c0, hc0]

/-! ### star coronas -/

/-- Pendant star corona `K_{1,k+2} ∘ K₁`: on `Fin 6` the corona of P3 (hub `1`
with leaf `4`; spokes `0, 2` with leaves `3, 5`), plus `k` further spokes
`inr (inr j)` at the hub, each with its own leaf `inr (inl j)`. -/
def starCoronaNb (k : ℕ) : Fin 6 ⊕ (Fin k ⊕ Fin k) → Finset (Fin 6 ⊕ (Fin k ⊕ Fin k))
  | Sum.inl a => (coronaP3Nb a).disjSum
      (if a = 1 then (∅ : Finset (Fin k)).disjSum Finset.univ else ∅)
  | Sum.inr (Sum.inl j) => (∅ : Finset (Fin 6)).disjSum ((∅ : Finset (Fin k)).disjSum {j})
  | Sum.inr (Sum.inr j) => ({1} : Finset (Fin 6)).disjSum (({j} : Finset (Fin k)).disjSum ∅)

/-- `k` disjoint edges `inl j — inr j`. -/
def matchingNb (k : ℕ) : Fin k ⊕ Fin k → Finset (Fin k ⊕ Fin k)
  | Sum.inl j => (∅ : Finset (Fin k)).disjSum {j}
  | Sum.inr j => ({j} : Finset (Fin k)).disjSum ∅

theorem starCoronaNb_symm (k : ℕ) :
    ∀ x y, y ∈ starCoronaNb k x → x ∈ starCoronaNb k y := by
  rintro (a | j | j) (b | j' | j') h
  · simp only [starCoronaNb, Finset.inl_mem_disjSum] at h ⊢
    exact coronaP3Nb_symm a b h
  · by_cases ha : a = 1 <;> simp_all [starCoronaNb]
  · by_cases ha : a = 1 <;> simp_all [starCoronaNb]
  · simp [starCoronaNb] at h
  · simp_all [starCoronaNb]
  · simp_all [starCoronaNb]
  · simp_all [starCoronaNb]
  · simp_all [starCoronaNb]
  · simp_all [starCoronaNb]

theorem starCorona_isMIS_of (k : ℕ) (S : Finset (Fin 6))
    (hS : IsMaximalIndependentSet coronaP3Nb S) (h1 : (1 : Fin 6) ∉ S) :
    IsMaximalIndependentSet (starCoronaNb k)
      (S.disjSum ((Finset.univ : Finset (Fin k)).disjSum ∅)) := by
  obtain ⟨hind, hdom⟩ := hS
  constructor
  · rintro (a | j | j) hu (b | j' | j') hv
    · simp only [Finset.inl_mem_disjSum] at hu hv
      simpa [starCoronaNb] using hind a hu b hv
    · simp only [Finset.inl_mem_disjSum] at hu
      have ha : a ≠ 1 := fun h => h1 (h ▸ hu)
      simp [starCoronaNb, ha]
    · simp at hv
    · simp [starCoronaNb]
    · simp [starCoronaNb]
    · simp at hv
    · simp at hu
    · simp at hu
    · simp at hu
  · rintro (a | j | j) hv
    · simp only [Finset.inl_mem_disjSum] at hv
      obtain ⟨u, hu, hau⟩ := hdom a hv
      exact ⟨Sum.inl u, by simpa using hu, by simp [starCoronaNb, hau]⟩
    · simp at hv
    · exact ⟨Sum.inr (Sum.inl j), by simp, by simp [starCoronaNb]⟩

/-- Star-corona output probabilities factor through corona(P3) and the
extra pendant edges, for targets avoiding the hub. -/
theorem starCorona_law_factor (k : ℕ) (r : Fin 6 ⊕ (Fin k ⊕ Fin k) → ℝ)
    (hr : ∀ v, 0 < r v) (S : Finset (Fin 6)) (h1 : (1 : Fin 6) ∉ S) :
    finiteRaceLaw r (starCoronaNb k) (Fintype.card (Fin 6 ⊕ (Fin k ⊕ Fin k))) Finset.univ
        (S.disjSum ((Finset.univ : Finset (Fin k)).disjSum ∅)) =
      finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ S *
        ∏ j : Fin k, r (Sum.inr (Sum.inl j)) /
          (r (Sum.inr (Sum.inl j)) + r (Sum.inr (Sum.inr j))) := by
  have hloc : ∀ v ∈ S.disjSum ((Finset.univ : Finset (Fin k)).disjSum ∅),
      starCoronaNb k v = unionNb coronaP3Nb (matchingNb k) v := by
    rintro (a | j | j) hv
    · simp only [Finset.inl_mem_disjSum] at hv
      have ha : a ≠ 1 := fun h => h1 (h ▸ hv)
      simp [starCoronaNb, unionNb, ha]
    · rfl
    · simp at hv
  rw [finiteRaceLaw_congr_target r _ _ _ _ _ hloc, ← sumRates_comp r,
    finiteRaceLaw_union_univ _ _ (fun a => hr _) (fun x => hr _), Fintype.card_fin]
  congr 1
  rw [← Finset.univ_disjSum_univ,
    finiteRaceLaw_pendant_leaves _ (fun x => hr _) (matchingNb k) (fun j => rfl) _ _
      (by simp [Fintype.card_sum]; omega)]
  rfl

/-- **IG-N5 (Lean, genuine clocks), all m ≥ 2.** No pendant star corona
`K_{1,m} ∘ K₁` with at least two spokes is EGU. -/
theorem starCorona_not_realClockEGU (k : ℕ) : ¬ RealClockEGU (starCoronaNb k) := by
  intro h
  rw [realClockEGU_iff_firstChoiceEGU _ (starCoronaNb_symm k)] at h
  obtain ⟨r, hr, hu⟩ := h
  set c : ℝ := ∏ j : Fin k, r (Sum.inr (Sum.inl j)) /
    (r (Sum.inr (Sum.inl j)) + r (Sum.inr (Sum.inr j))) with hc
  have hcpos : 0 < c :=
    Finset.prod_pos (fun j _ => div_pos (hr _) (add_pos (hr _) (hr _)))
  have hmis : ∀ S : Finset (Fin 6), IsMaximalIndependentSet coronaP3Nb S → (1 : Fin 6) ∉ S →
      S.disjSum ((Finset.univ : Finset (Fin k)).disjSum ∅) ∈
        maximalIndependentSets (starCoronaNb k) := fun S hS h1 =>
    (mem_maximalIndependentSets _ _).mpr (starCorona_isMIS_of k S hS h1)
  have m345 := hmis {3, 4, 5} (by decide) (by decide)
  have m024 := hmis {0, 2, 4} (by decide) (by decide)
  have m045 := hmis {0, 4, 5} (by decide) (by decide)
  have m234 := hmis {2, 3, 4} (by decide) (by decide)
  have e345 := hu _ m345
  have e024 := hu _ m024
  have e045 := hu _ m045
  have e234 := hu _ m234
  rw [starCorona_law_factor k r hr _ (by decide)] at e345 e024 e045 e234
  have hminor := coronaP3Nb_strict_minor (fun a => r (Sum.inl a)) (fun a => hr _)
  have hc2 : 0 < c * c := mul_pos hcpos hcpos
  have key := mul_lt_mul_of_pos_right hminor hc2
  have l1 : finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {3, 4, 5} *
      finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {0, 2, 4} * (c * c) =
      (finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {3, 4, 5} * c) *
      (finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {0, 2, 4} * c) := by ring
  have l2 : finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {0, 4, 5} *
      finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {2, 3, 4} * (c * c) =
      (finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {0, 4, 5} * c) *
      (finiteRaceLaw (fun a => r (Sum.inl a)) coronaP3Nb 6 Finset.univ {2, 3, 4} * c) := by ring
  rw [l1, l2, e345, e024, e045, e234] at key
  exact lt_irrefl _ key

end InverseGreedy
