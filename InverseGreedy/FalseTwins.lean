import InverseGreedy.CographEGU

/-!
# S041: false-twin invariance (IG-P7) for genuine exponential clocks

`twinExtend nb w` adds to a graph on `β` a new vertex `none` that is a
*false twin* of `some w` (same open neighbourhood, nonadjacent). We prove:

* `finiteRaceLaw_isolated`: an isolated active target vertex can be deleted;
* `finiteRaceLaw_twinExtend`: the law of the twin extension, on lifted targets,
  equals the law of the original graph with the twins' rates added;
* `realClockEGU_twinExtend_iff`: the twin extension is EGU iff the original is.
-/

open Finset
namespace InverseGreedy

section Isolated

variable {γ : Type*} [DecidableEq γ]

theorem finiteRaceLaw_empty_active (r : γ → ℝ) (nb : γ → Finset γ) (fuel : ℕ)
    (T : Finset γ) :
    finiteRaceLaw r nb fuel ∅ T = if T = ∅ then 1 else 0 := by
  cases fuel <;> simp [finiteRaceLaw]

/-- **Isolated vertex deletion.** -/
theorem finiteRaceLaw_isolated (r : γ → ℝ) (hr : ∀ v, 0 < r v) (nb : γ → Finset γ)
    (z : γ) :
    ∀ (fuel : ℕ) (A T : Finset γ), A.card ≤ fuel → z ∈ A → z ∈ T →
      (∀ v ∈ A, z ∉ nb v) → (∀ v ∈ nb z, v ∉ A) →
      finiteRaceLaw r nb fuel A T = finiteRaceLaw r nb fuel (A.erase z) (T.erase z)
  | 0, A, T, h, hz, _, _, _ => by
      have : A = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [this] at hz; simp at hz
  | fuel + 1, A, T, h, hzA, hzT, hiso1, hiso2 => by
      have hA : A ≠ ∅ := Finset.ne_empty_of_mem hzA
      have hcardE : (A.erase z).card + 1 = A.card := Finset.card_erase_add_one hzA
      rw [finiteRaceLaw_step _ _ fuel _ _ hA, ← Finset.add_sum_erase _ _ hzA]
      have hafterz : afterChoice nb A z = A.erase z := by
        ext x
        simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hx, hn⟩; exact ⟨fun h => hn (Or.inl h), hx⟩
        · rintro ⟨hne, hx⟩
          exact ⟨hx, fun h => h.elim hne (fun hm => hiso2 x hm hx)⟩
      rw [if_pos hzT, hafterz]
      -- remaining terms
      have hrest : ∀ v ∈ A.erase z,
          (if v ∈ T then firstChoice r A v *
              finiteRaceLaw r nb fuel (afterChoice nb A v) (T.erase v) else 0) =
            activeRate r (A.erase z) / activeRate r A *
              (if v ∈ T.erase z then firstChoice r (A.erase z) v *
                finiteRaceLaw r nb fuel (afterChoice nb (A.erase z) v)
                  ((T.erase z).erase v) else 0) := by
        intro v hv
        have hvz : v ≠ z := Finset.ne_of_mem_erase hv
        have hvA : v ∈ A := Finset.mem_of_mem_erase hv
        have hΛ' : 0 < activeRate r (A.erase z) :=
          activeRate_pos_of_nonempty r hr _ (Finset.ne_empty_of_mem hv)
        have hzafter : z ∈ afterChoice nb A v := by
          simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert]
          exact ⟨hzA, fun h => h.elim (fun h' => hvz h'.symm) (hiso1 v hvA)⟩
        have hcardv := afterChoice_card_lt nb A v hvA
        have hIH := finiteRaceLaw_isolated r hr nb z fuel (afterChoice nb A v) (T.erase v)
          (by omega) hzafter (Finset.mem_erase.mpr ⟨hvz.symm, hzT⟩)
          (fun x hx => hiso1 x (Finset.mem_sdiff.mp hx).1)
          (fun x hx hxa => hiso2 x hx (Finset.mem_sdiff.mp hxa).1)
        have hset : (afterChoice nb A v).erase z = afterChoice nb (A.erase z) v := by
          ext x; simp [afterChoice]; tauto
        have hset2 : (T.erase v).erase z = (T.erase z).erase v := Finset.erase_right_comm
        simp only [Finset.mem_erase, hvz, ne_eq, not_false_eq_true, true_and]
        split_ifs
        · rw [hIH, hset, hset2, firstChoice, firstChoice]
          field_simp
        · simp
      rw [Finset.sum_congr rfl hrest, ← Finset.mul_sum]
      have hstable : finiteRaceLaw r nb fuel (A.erase z) (T.erase z) =
          finiteRaceLaw r nb (fuel + 1) (A.erase z) (T.erase z) :=
        (finiteRaceLaw_fuel_step_stable r nb fuel _ _ (by omega)).symm
      by_cases hE : A.erase z = ∅
      · rw [hE] at hstable ⊢
        simp only [Finset.sum_empty, mul_zero, add_zero, firstChoice]
        have hAz : A = {z} := by
          rw [← Finset.insert_erase hzA, hE]; rfl
        rw [hAz]
        simp only [activeRate, Finset.sum_singleton, div_self (hr z).ne', one_mul]
        rw [finiteRaceLaw_empty_active, finiteRaceLaw_empty_active]
      · rw [← finiteRaceLaw_step _ _ fuel _ _ hE, ← hstable, firstChoice]
        have hsplit : activeRate r A = r z + activeRate r (A.erase z) := by
          unfold activeRate; rw [← Finset.add_sum_erase _ _ hzA]
        have hΛ : 0 < activeRate r A := activeRate_pos_of_nonempty r hr A hA
        rw [hsplit] at hΛ ⊢
        field_simp

end Isolated

section Twin

variable {β : Type*} [DecidableEq β]

/-- Add a false twin `none` of `some w`. -/
def twinExtend (nb : β → Finset β) (w : β) : Option β → Finset (Option β)
  | some v => (nb v).map Function.Embedding.some ∪ (if w ∈ nb v then {none} else ∅)
  | none => (nb w).map Function.Embedding.some


theorem mem_twinExtend_some_some (nb : β → Finset β) (w x y : β) :
    some y ∈ twinExtend nb w (some x) ↔ y ∈ nb x := by
  show some y ∈ (nb x).map Function.Embedding.some ∪ (if w ∈ nb x then {none} else ∅) ↔ _
  split_ifs <;> simp

theorem mem_twinExtend_some_none (nb : β → Finset β) (w x : β) :
    none ∈ twinExtend nb w (some x) ↔ w ∈ nb x := by
  show none ∈ (nb x).map Function.Embedding.some ∪ (if w ∈ nb x then {none} else ∅) ↔ _
  split_ifs with h <;> simp [h]

theorem mem_twinExtend_none_some (nb : β → Finset β) (w y : β) :
    some y ∈ twinExtend nb w none ↔ y ∈ nb w := by
  simp [twinExtend]

theorem none_notMem_twinExtend_none (nb : β → Finset β) (w : β) :
    none ∉ twinExtend nb w none := by
  simp [twinExtend]

/-- Lift a vertex set: `w` is duplicated to `{some w, none}`. -/
def twinLift (w : β) (S : Finset β) : Finset (Option β) :=
  S.map Function.Embedding.some ∪ (if w ∈ S then {none} else ∅)

/-- Merge the twins' rates. -/
def twinMergeRates (w : β) (r : Option β → ℝ) : β → ℝ :=
  fun v => r (some v) + (if v = w then r none else 0)

theorem mem_twinLift_some (w : β) (S : Finset β) (v : β) :
    some v ∈ twinLift w S ↔ v ∈ S := by
  unfold twinLift; split_ifs <;> simp

theorem mem_twinLift_none (w : β) (S : Finset β) : none ∈ twinLift w S ↔ w ∈ S := by
  unfold twinLift; split_ifs with h <;> simp [h]

theorem activeRate_twinLift (w : β) (r : Option β → ℝ) (S : Finset β) :
    activeRate r (twinLift w S) = activeRate (twinMergeRates w r) S := by
  unfold activeRate twinLift twinMergeRates
  rw [Finset.sum_union (by
      rw [Finset.disjoint_left]; intro x hx hx'
      split_ifs at hx' <;> simp_all)]
  rw [Finset.sum_map, Finset.sum_add_distrib]
  congr 1
  split_ifs with hw
  · simp [Finset.sum_ite_eq', hw]
  · simp only [Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro v hv
    simp [show v ≠ w from fun h => hw (h ▸ hv)]

end Twin

section TwinLaw

variable {β : Type*} [DecidableEq β]

theorem twinLift_eq_empty (w : β) (S : Finset β) : twinLift w S = ∅ ↔ S = ∅ := by
  constructor
  · intro h
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    have := (mem_twinLift_some w S v).mpr hv
    rw [h] at this; simp at this
  · rintro rfl; simp [twinLift]

theorem twinLift_of_notMem (w : β) (S : Finset β) (hw : w ∉ S) :
    twinLift w S = S.map Function.Embedding.some := by
  simp [twinLift, hw]

theorem twinLift_erase_some (w : β) (S : Finset β) (v : β) (hv : v ≠ w) :
    (twinLift w S).erase (some v) = twinLift w (S.erase v) := by
  ext x; rcases x with _ | y
  · simp [mem_twinLift_none, Ne.symm hv]
  · simp [mem_twinLift_some]

theorem afterChoice_twin_some (nb : β → Finset β) (w : β) (A : Finset β) (v : β)
    (hv : v ≠ w) :
    afterChoice (twinExtend nb w) (twinLift w A) (some v) =
      twinLift w (afterChoice nb A v) := by
  ext x; rcases x with _ | y
  · simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert, mem_twinLift_none,
      twinExtend, Finset.mem_union, Finset.mem_map, Function.Embedding.some_apply,
      reduceCtorEq, and_false, exists_false, false_or]
    by_cases h : w ∈ nb v <;> simp [h, Ne.symm hv]
  · simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert, mem_twinLift_some,
      twinExtend, Finset.mem_union, Finset.mem_map, Function.Embedding.some_apply,
      Option.some.injEq, exists_eq_right]
    by_cases h : w ∈ nb v <;> simp [h]

/-- **Twin law.** For symmetric `nb` with `w ∉ nb w`. -/
theorem finiteRaceLaw_twinExtend (nb : β → Finset β)
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (w : β) (hw : w ∉ nb w)
    (r : Option β → ℝ) (hr : ∀ v, 0 < r v) :
    ∀ (fuel : ℕ) (A T : Finset β), (twinLift w A).card ≤ fuel →
      finiteRaceLaw r (twinExtend nb w) fuel (twinLift w A) (twinLift w T) =
        finiteRaceLaw (twinMergeRates w r) nb A.card A T
  | 0, A, T, h => by
      have hA : A = ∅ := (twinLift_eq_empty w A).mp (Finset.card_eq_zero.mp (by omega))
      subst hA
      simp only [twinLift_eq_empty, Finset.card_empty]
      rw [show twinLift w (∅ : Finset β) = ∅ from (twinLift_eq_empty w ∅).mpr rfl]
      simp [finiteRaceLaw, twinLift_eq_empty]
  | fuel + 1, A, T, h => by
      by_cases hA : A = ∅
      · subst hA
        rw [show twinLift w (∅ : Finset β) = ∅ from (twinLift_eq_empty w ∅).mpr rfl,
          finiteRaceLaw_empty_active, Finset.card_empty, finiteRaceLaw_empty_active]
        simp only [twinLift_eq_empty]
      have hAne : twinLift w A ≠ ∅ := fun h' => hA ((twinLift_eq_empty w A).mp h')
      obtain ⟨k, hk⟩ : ∃ k, A.card = k + 1 :=
        ⟨A.card - 1, by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA); omega⟩
      have hcardA : A.card ≤ (twinLift w A).card := by
        rw [twinLift, Finset.card_union_of_disjoint (by
          rw [Finset.disjoint_left]; intro x hx hx'
          split_ifs at hx' <;> simp_all)]
        simp
      have hΛ := activeRate_twinLift w r A
      set r' := twinMergeRates w r with hr'
      have hr'pos : ∀ v, 0 < r' v := by
        intro v; simp only [hr', twinMergeRates]
        split_ifs
        · exact add_pos (hr _) (hr _)
        · simpa using hr (some v)
      -- the merged-side term for each vertex
      set G : β → ℝ := fun v => if v ∈ T then firstChoice r' A v *
        finiteRaceLaw r' nb k (afterChoice nb A v) (T.erase v) else 0 with hG
      have hRHS : finiteRaceLaw r' nb A.card A T = ∑ v ∈ A, G v := by
        rw [hk, finiteRaceLaw_step _ _ k _ _ hA]
      -- common tool: IH normalised to fuel k on the merged side
      have hIH : ∀ (B U : Finset β), (twinLift w B).card ≤ fuel → B.card ≤ k →
          finiteRaceLaw r (twinExtend nb w) fuel (twinLift w B) (twinLift w U) =
            finiteRaceLaw r' nb k B U := by
        intro B U hB hBk
        rw [finiteRaceLaw_twinExtend nb hs w hw r hr fuel B U hB,
          finiteRaceLaw_fuel_eq_card r' nb k B U hBk]
      have hsome : ∀ v ∈ A, v ≠ w →
          (if some v ∈ twinLift w T then firstChoice r (twinLift w A) (some v) *
            finiteRaceLaw r (twinExtend nb w) fuel
              (afterChoice (twinExtend nb w) (twinLift w A) (some v))
              ((twinLift w T).erase (some v)) else 0) = G v := by
        intro v hv hvw
        have hlt := afterChoice_card_lt nb A v hv
        simp only [mem_twinLift_some]
        rw [afterChoice_twin_some nb w A v hvw, twinLift_erase_some w T v hvw]
        simp only [hG]
        split_ifs
        · rw [hIH _ _ ?_ (by omega), firstChoice, firstChoice, hΛ]
          · simp [hr', twinMergeRates, hvw]
          · have hsub : twinLift w (afterChoice nb A v) ⊆ (twinLift w A).erase (some v) := by
              rw [twinLift_erase_some w A v hvw]
              intro x hx
              rcases x with _ | y
              · rw [mem_twinLift_none] at hx ⊢
                exact afterChoice_subset_erase _ _ _ hx
              · rw [mem_twinLift_some] at hx ⊢
                exact afterChoice_subset_erase _ _ _ hx
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem ((mem_twinLift_some w A v).mpr hv)] at this
            omega
        · rfl
      -- the two twin terms
      have htwins : w ∈ A →
          (if some w ∈ twinLift w T then firstChoice r (twinLift w A) (some w) *
            finiteRaceLaw r (twinExtend nb w) fuel
              (afterChoice (twinExtend nb w) (twinLift w A) (some w))
              ((twinLift w T).erase (some w)) else 0) +
          (if none ∈ twinLift w T then firstChoice r (twinLift w A) none *
            finiteRaceLaw r (twinExtend nb w) fuel
              (afterChoice (twinExtend nb w) (twinLift w A) none)
              ((twinLift w T).erase none) else 0) = G w := by
        intro hwA
        obtain ⟨A', hA'⟩ : ∃ A', A' = afterChoice nb A w := ⟨_, rfl⟩
        have hwA' : w ∉ A' := by simp [hA', afterChoice]
        have hlt : A'.card < A.card := hA' ▸ afterChoice_card_lt nb A w hwA
        have htl : (twinLift w A).card = A.card + 1 := by
          rw [twinLift, Finset.card_union_of_disjoint (by
            rw [Finset.disjoint_left]; intro x hx hx'
            split_ifs at hx' <;> simp_all)]
          simp [hwA]
        have htl' : (twinLift w A').card = A'.card := by
          rw [twinLift_of_notMem w A' hwA', Finset.card_map]
        have hA'card : (twinLift w A').card ≤ fuel := by omega
        have hiso_none : ∀ x ∈ insert none (twinLift w A'), none ∉ twinExtend nb w x := by
          rintro (_ | y) hx
          · simp [twinExtend]
          · have hy : y ∈ A' := by
              rw [Finset.mem_insert, mem_twinLift_some] at hx; simpa using hx
            have hyn : y ∉ nb w := by
              simp only [hA', afterChoice, Finset.mem_sdiff, Finset.mem_insert] at hy; tauto
            simp only [twinExtend, Finset.mem_union, Finset.mem_map, reduceCtorEq,
              Function.Embedding.some_apply, and_false, exists_false, false_or]
            split_ifs with hwy
            · exact absurd (hs y w hwy) hyn
            · simp
        by_cases hwT : w ∈ T
        · rw [if_pos ((mem_twinLift_some w T w).mpr hwT), if_pos ((mem_twinLift_none w T).mpr hwT)]
          -- branch some w
          have hafter1 : afterChoice (twinExtend nb w) (twinLift w A) (some w) =
              insert none (twinLift w A') := by
            ext x; rcases x with _ | y
            · simp [afterChoice, twinExtend, mem_twinLift_none, hwA, hw, hwA']
            · simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert, mem_twinLift_some,
                twinExtend, Finset.mem_union, Finset.mem_map, Function.Embedding.some_apply,
                Option.some.injEq, exists_eq_right, reduceCtorEq, false_or, hA']
              simp [hw]
          have htarget1 : (twinLift w T).erase (some w) = insert none (twinLift w (T.erase w)) := by
            ext x; rcases x with _ | y
            · simp [mem_twinLift_none, hwT]
            · simp [mem_twinLift_some]
          -- branch none
          have hafter2 : afterChoice (twinExtend nb w) (twinLift w A) none =
              insert (some w) (twinLift w A') := by
            ext x; rcases x with _ | y
            · simp [afterChoice, twinExtend, mem_twinLift_none, hwA']
            · simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert, mem_twinLift_some,
                twinExtend, Finset.mem_map, Function.Embedding.some_apply,
                Option.some.injEq, exists_eq_right, reduceCtorEq, false_or, hA']
              by_cases hyw : y = w
              · subst hyw; simp [hwA, hw]
              · simp [hyw]
          have htarget2 : (twinLift w T).erase none = insert (some w) (twinLift w (T.erase w)) := by
            ext x; rcases x with _ | y
            · simp [mem_twinLift_none]
            · by_cases hyw : y = w
              · subst hyw; simp [mem_twinLift_some, hwT]
              · simp [mem_twinLift_some, hyw]
          have hiso_some : ∀ x ∈ insert (some w) (twinLift w A'),
              some w ∉ twinExtend nb w x := by
            rintro (_ | y) hx
            · simp [twinExtend, hw]
            · have hy : y = w ∨ y ∈ A' := by
                rw [Finset.mem_insert, mem_twinLift_some] at hx; simpa using hx
              simp only [twinExtend, Finset.mem_union, Finset.mem_map,
                Function.Embedding.some_apply, Option.some.injEq, exists_eq_right]
              rcases hy with rfl | hy
              · simp [hw]
              · have hyn : y ∉ nb w := by
                  simp only [hA', afterChoice, Finset.mem_sdiff, Finset.mem_insert] at hy; tauto
                intro hc
                rcases hc with hc | hc
                · exact hyn (hs y w hc)
                · split_ifs at hc <;> simp at hc
          rw [hafter1, htarget1, hafter2, htarget2,
            finiteRaceLaw_isolated r hr _ none fuel _ _ (by
              rw [Finset.card_insert_of_notMem (by
                rw [mem_twinLift_none]; exact hwA')]; omega)
              (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _) hiso_none (by
                intro v hv hvA
                simp only [twinExtend, Finset.mem_map, Function.Embedding.some_apply] at hv
                obtain ⟨y, hy, rfl⟩ := hv
                rw [Finset.mem_insert, mem_twinLift_some] at hvA
                simp only [reduceCtorEq, false_or] at hvA
                simp only [hA', afterChoice, Finset.mem_sdiff, Finset.mem_insert] at hvA
                exact hvA.2 (Or.inr hy)),
            finiteRaceLaw_isolated r hr _ (some w) fuel _ _ (by
              rw [Finset.card_insert_of_notMem (by
                rw [mem_twinLift_some]; exact hwA')]; omega)
              (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _) hiso_some (by
                intro v hv hvA
                simp only [twinExtend, Finset.mem_union, Finset.mem_map,
                  Function.Embedding.some_apply, hw, if_false, Finset.notMem_empty,
                  or_false] at hv
                obtain ⟨y, hy, rfl⟩ := hv
                rw [Finset.mem_insert, mem_twinLift_some] at hvA
                rcases hvA with hvA | hvA
                · simp only [Option.some.injEq] at hvA; subst hvA; exact hw hy
                · simp only [hA', afterChoice, Finset.mem_sdiff, Finset.mem_insert] at hvA
                  exact hvA.2 (Or.inr hy))]
          rw [Finset.erase_insert (by rw [mem_twinLift_none]; exact hwA'),
            Finset.erase_insert (by rw [mem_twinLift_none]; simp),
            Finset.erase_insert (by rw [mem_twinLift_some]; exact hwA'),
            Finset.erase_insert (by rw [mem_twinLift_some]; simp),
            hIH _ _ hA'card (by omega)]
          simp only [hG, if_pos hwT, firstChoice, hΛ]
          simp only [hr', twinMergeRates, if_true]
          rw [← hA']
          ring
        · simp [mem_twinLift_some, mem_twinLift_none, hG, hwT]
      -- assemble
      rw [hRHS, finiteRaceLaw_step _ _ fuel _ _ hAne]
      have hsplit : ∀ (f : Option β → ℝ), ∑ x ∈ twinLift w A, f x =
          ∑ v ∈ A, f (some v) + (if w ∈ A then f none else 0) := by
        intro f
        unfold twinLift
        rw [Finset.sum_union (by
          rw [Finset.disjoint_left]; intro x hx hx'
          split_ifs at hx' <;> simp_all), Finset.sum_map]
        split_ifs <;> simp
      rw [hsplit]
      by_cases hwA : w ∈ A
      · rw [if_pos hwA, ← Finset.add_sum_erase _ _ hwA, ← Finset.add_sum_erase _ G hwA]
        have ht := htwins hwA
        have hs2 : ∑ x ∈ A.erase w, (if some x ∈ twinLift w T then
            firstChoice r (twinLift w A) (some x) *
              finiteRaceLaw r (twinExtend nb w) fuel
                (afterChoice (twinExtend nb w) (twinLift w A) (some x))
                ((twinLift w T).erase (some x)) else 0) = ∑ x ∈ A.erase w, G x :=
          Finset.sum_congr rfl (fun v hv =>
            hsome v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv))
        linarith
      · rw [if_neg hwA, add_zero]
        apply Finset.sum_congr rfl
        intro v hv
        exact hsome v hv (fun h => hwA (h ▸ hv))

end TwinLaw

section TwinEGU

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem twinExtend_symm (nb : β → Finset β) (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (w : β) :
    ∀ x y, y ∈ twinExtend nb w x → x ∈ twinExtend nb w y := by
  rintro (_ | x) (_ | y) h
  · exact absurd h (none_notMem_twinExtend_none nb w)
  · rw [mem_twinExtend_none_some] at h; rw [mem_twinExtend_some_none]; exact hs _ _ h
  · rw [mem_twinExtend_some_none] at h; rw [mem_twinExtend_none_some]; exact hs _ _ h
  · rw [mem_twinExtend_some_some] at h ⊢; exact hs _ _ h

theorem twinExtend_irrefl (nb : β → Finset β) (hi : ∀ v, v ∉ nb v) (w : β) :
    ∀ v, v ∉ twinExtend nb w v := by
  rintro (_ | v)
  · exact none_notMem_twinExtend_none nb w
  · rw [mem_twinExtend_some_some]; exact hi v

theorem univ_eq_twinLift (w : β) :
    (Finset.univ : Finset (Option β)) = twinLift w Finset.univ := by
  ext x; rcases x with _ | y <;> simp [mem_twinLift_some, mem_twinLift_none]

omit [Fintype β] in
theorem twinLift_injective (w : β) : Function.Injective (twinLift w) := by
  intro S S' h
  ext v
  rw [← mem_twinLift_some w S v, ← mem_twinLift_some w S' v, h]

theorem isMIS_twinExtend_iff (nb : β → Finset β) (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (w : β) (hw : w ∉ nb w) (K : Finset (Option β)) :
    IsMaximalIndependentSet (twinExtend nb w) K ↔
      ∃ T, IsMaximalIndependentSet nb T ∧ K = twinLift w T := by
  have hnb_some := mem_twinExtend_some_some nb w
  have hnb_none_of := mem_twinExtend_some_none nb w
  have hnone_some := mem_twinExtend_none_some nb w
  have hnone_none := none_notMem_twinExtend_none nb w
  constructor
  · rintro ⟨hind, hdom⟩
    set T := Finset.univ.filter (fun v => some v ∈ K) with hT
    have hmemT : ∀ v, v ∈ T ↔ some v ∈ K := by intro v; simp [hT]
    have htw : none ∈ K ↔ some w ∈ K := by
      constructor
      · intro hn
        by_contra hsw
        obtain ⟨u, hu, hwu⟩ := hdom _ hsw
        rcases u with _ | y
        · exact hw ((hnone_some w).mp hwu)
        · have : w ∈ nb y := (hnb_some y w).mp hwu
          exact hind _ hu _ hn ((hnb_none_of y).mpr this)
      · intro hsw
        by_contra hn
        obtain ⟨u, hu, hnu⟩ := hdom _ hn
        rcases u with _ | y
        · exact hn hu
        · have hwy : w ∈ nb y := (hnb_none_of y).mp hnu
          exact hind _ hsw _ hu ((hnb_some w y).mpr (hs _ _ hwy))
    refine ⟨T, ⟨?_, ?_⟩, ?_⟩
    · intro u hu v hv huv
      exact hind _ ((hmemT u).mp hu) _ ((hmemT v).mp hv) ((hnb_some u v).mpr huv)
    · intro v hv
      obtain ⟨u, hu, hvu⟩ := hdom (some v) (fun h => hv ((hmemT v).mpr h))
      rcases u with _ | y
      · exact ⟨w, (hmemT w).mpr (htw.mp hu), (hnone_some v).mp hvu⟩
      · exact ⟨y, (hmemT y).mpr hu, (hnb_some y v).mp hvu⟩
    · ext x; rcases x with _ | y
      · rw [mem_twinLift_none, hmemT, htw]
      · rw [mem_twinLift_some, hmemT]
  · rintro ⟨T, ⟨hind, hdom⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro (_ | x) hx (_ | y) hy
      · exact hnone_none
      · rw [mem_twinLift_none] at hx; rw [mem_twinLift_some] at hy
        rw [hnone_some]; exact hind _ hx _ hy
      · rw [mem_twinLift_some] at hx; rw [mem_twinLift_none] at hy
        rw [hnb_none_of]; exact hind _ hx _ hy
      · rw [mem_twinLift_some] at hx hy
        rw [hnb_some]; exact hind _ hx _ hy
    · rintro (_ | v) hv
      · rw [mem_twinLift_none] at hv
        obtain ⟨u, hu, hwu⟩ := hdom w hv
        exact ⟨some u, (mem_twinLift_some w T u).mpr hu, (hnb_none_of u).mpr hwu⟩
      · rw [mem_twinLift_some] at hv
        obtain ⟨u, hu, hvu⟩ := hdom v hv
        exact ⟨some u, (mem_twinLift_some w T u).mpr hu, (hnb_some u v).mpr hvu⟩

theorem maximalIndependentSets_twinExtend (nb : β → Finset β)
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (w : β) (hw : w ∉ nb w) :
    maximalIndependentSets (twinExtend nb w) =
      (maximalIndependentSets nb).map ⟨twinLift w, twinLift_injective w⟩ := by
  ext K
  simp only [mem_maximalIndependentSets, Finset.mem_map, Function.Embedding.coeFn_mk]
  rw [isMIS_twinExtend_iff nb hs w hw]
  constructor
  · rintro ⟨T, hT, rfl⟩; exact ⟨T, hT, rfl⟩
  · rintro ⟨T, hT, rfl⟩; exact ⟨T, hT, rfl⟩

/-- **IG-P7 (Lean, genuine clocks).** Adding a false twin preserves EGU
in both directions. -/
theorem realClockEGU_twinExtend_iff (nb : β → Finset β)
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (hi : ∀ v, v ∉ nb v) (w : β) :
    RealClockEGU (twinExtend nb w) ↔ RealClockEGU nb := by
  rw [realClockEGU_iff_firstChoiceEGU _ (twinExtend_symm nb hs w),
    realClockEGU_iff_firstChoiceEGU _ hs]
  have hM := maximalIndependentSets_twinExtend nb hs w (hi w)
  have hcard : (maximalIndependentSets (twinExtend nb w)).card =
      (maximalIndependentSets nb).card := by rw [hM, Finset.card_map]
  have hfuel : (twinLift w (Finset.univ : Finset β)).card ≤ Fintype.card (Option β) := by
    rw [← univ_eq_twinLift]; simp
  have hlaw : ∀ (r : Option β → ℝ), (∀ v, 0 < r v) → ∀ T : Finset β,
      finiteRaceLaw r (twinExtend nb w) (Fintype.card (Option β)) Finset.univ (twinLift w T) =
        finiteRaceLaw (twinMergeRates w r) nb (Fintype.card β) Finset.univ T := by
    intro r hr T
    rw [univ_eq_twinLift w, finiteRaceLaw_twinExtend nb hs w (hi w) r hr _ _ _ hfuel,
      Finset.card_univ]
  constructor
  · rintro ⟨r, hr, hu⟩
    refine ⟨twinMergeRates w r, fun v => ?_, fun T hT => ?_⟩
    · simp only [twinMergeRates]
      split_ifs
      · exact add_pos (hr _) (hr _)
      · simpa using hr (some v)
    · have hK : twinLift w T ∈ maximalIndependentSets (twinExtend nb w) := by
        rw [hM]; exact Finset.mem_map_of_mem _ hT
      rw [← hlaw r hr T, hu _ hK, hcard]
  · rintro ⟨r', hr', hu⟩
    let r : Option β → ℝ := fun x => match x with
      | none => r' w / 2
      | some v => if v = w then r' w / 2 else r' v
    have hr : ∀ x, 0 < r x := by
      rintro (_ | v)
      · exact half_pos (hr' w)
      · simp only [r]; split_ifs
        · exact half_pos (hr' w)
        · exact hr' v
    have hmerge : twinMergeRates w r = r' := by
      funext v
      simp only [twinMergeRates, r]
      by_cases hv : v = w
      · subst hv; simp
      · simp [hv]
    refine ⟨r, hr, fun K hK => ?_⟩
    rw [hM] at hK
    obtain ⟨T, hT, rfl⟩ := Finset.mem_map.mp hK
    simp only [Function.Embedding.coeFn_mk]
    rw [hlaw r hr T, hmerge, hu T hT, hcard]

end TwinEGU

end InverseGreedy
