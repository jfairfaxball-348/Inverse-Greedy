import InverseGreedy.GraphOperationsEGU

/-!
# S041: relabelling invariance, cographs and complete multipartite graphs

* `realClockEGU_congr_equiv`: EGU is invariant under graph isomorphism.
* `Cotree`: finite cographs built from single vertices by disjoint union
  and join; **every cotree graph is EGU under genuine exponential clocks**
  (IG-P4, cograph part), hence every graph isomorphic to one is EGU.
* `Cotree.completeMultipartite`: complete multipartite graphs (joins of
  edgeless parts) are EGU (IG-P1). Edgeless graphs are EGU.
-/

open Finset
namespace InverseGreedy

section Iso

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem finiteRaceLaw_map_equiv (e : α ≃ β) (nbα : α → Finset α) (nbβ : β → Finset β)
    (hnb : ∀ a, nbβ (e a) = (nbα a).map e.toEmbedding) (r : β → ℝ) :
    ∀ (fuel : ℕ) (A T : Finset α),
      finiteRaceLaw r nbβ fuel (A.map e.toEmbedding) (T.map e.toEmbedding) =
        finiteRaceLaw (fun a => r (e a)) nbα fuel A T
  | 0, A, T => by simp [finiteRaceLaw]
  | fuel + 1, A, T => by
      by_cases hA : A = ∅
      · subst hA; simp [finiteRaceLaw]
      · have hA' : A.map e.toEmbedding ≠ ∅ := by simpa using hA
        rw [finiteRaceLaw_step _ _ fuel _ _ hA', finiteRaceLaw_step _ _ fuel _ _ hA,
          Finset.sum_map]
        apply Finset.sum_congr rfl
        intro a _
        have hafter : afterChoice nbβ (A.map e.toEmbedding) (e a) =
            (afterChoice nbα A a).map e.toEmbedding := by
          ext x
          obtain ⟨y, rfl⟩ := e.surjective x
          simp [afterChoice, hnb]
        have herase : (T.map e.toEmbedding).erase (e a) =
            (T.erase a).map e.toEmbedding := by
          ext x
          obtain ⟨y, rfl⟩ := e.surjective x
          simp
        simp only [Equiv.toEmbedding_apply]
        rw [hafter, herase, finiteRaceLaw_map_equiv e nbα nbβ hnb r fuel]
        simp [firstChoice, activeRate, Finset.sum_map]

theorem isMIS_map_equiv_iff [Fintype α] [Fintype β] (e : α ≃ β) (nbα : α → Finset α)
    (nbβ : β → Finset β) (hnb : ∀ a, nbβ (e a) = (nbα a).map e.toEmbedding)
    (I : Finset α) :
    IsMaximalIndependentSet nbβ (I.map e.toEmbedding) ↔ IsMaximalIndependentSet nbα I := by
  have hmem : ∀ (S : Finset α) (a : α), e a ∈ S.map e.toEmbedding ↔ a ∈ S := by
    intro S a; simp
  constructor
  · rintro ⟨hind, hdom⟩
    refine ⟨fun u hu v hv huv => ?_, fun v hv => ?_⟩
    · have h := hind (e u) ((hmem I u).mpr hu) (e v) ((hmem I v).mpr hv)
      rw [hnb, hmem] at h
      exact h huv
    · obtain ⟨x, hx, hvx⟩ := hdom (e v) (fun h => hv ((hmem I v).mp h))
      obtain ⟨u, rfl⟩ := e.surjective x
      rw [hnb, hmem] at hvx
      exact ⟨u, (hmem I u).mp hx, hvx⟩
  · rintro ⟨hind, hdom⟩
    refine ⟨fun x hx y hy hxy => ?_, fun y hy => ?_⟩
    · obtain ⟨u, rfl⟩ := e.surjective x
      obtain ⟨v, rfl⟩ := e.surjective y
      rw [hnb, hmem] at hxy
      exact hind u ((hmem I u).mp hx) v ((hmem I v).mp hy) hxy
    · obtain ⟨v, rfl⟩ := e.surjective y
      obtain ⟨u, hu, huv⟩ := hdom v (fun h => hy ((hmem I v).mpr h))
      exact ⟨e u, (hmem I u).mpr hu, by rw [hnb, hmem]; exact huv⟩

theorem maximalIndependentSets_map_equiv [Fintype α] [Fintype β] (e : α ≃ β)
    (nbα : α → Finset α) (nbβ : β → Finset β)
    (hnb : ∀ a, nbβ (e a) = (nbα a).map e.toEmbedding) :
    maximalIndependentSets nbβ =
      (maximalIndependentSets nbα).map (Finset.mapEmbedding e.toEmbedding).toEmbedding := by
  ext K
  simp only [Finset.mem_map, mem_maximalIndependentSets, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply]
  constructor
  · intro hK
    refine ⟨K.map e.symm.toEmbedding, ?_, ?_⟩
    · rw [← isMIS_map_equiv_iff e nbα nbβ hnb]
      simpa [Finset.map_map] using hK
    · simp [Finset.map_map]
  · rintro ⟨I, hI, rfl⟩
    exact (isMIS_map_equiv_iff e nbα nbβ hnb I).mpr hI

/-- **EGU is a graph invariant** (genuine clocks): isomorphic neighbour maps
are simultaneously EGU or not. -/
theorem realClockEGU_congr_equiv [Fintype α] [Fintype β] (e : α ≃ β)
    (nbα : α → Finset α) (nbβ : β → Finset β)
    (hnb : ∀ a, nbβ (e a) = (nbα a).map e.toEmbedding)
    (hsα : ∀ x y, y ∈ nbα x → x ∈ nbα y) (hsβ : ∀ x y, y ∈ nbβ x → x ∈ nbβ y) :
    RealClockEGU nbα ↔ RealClockEGU nbβ := by
  rw [realClockEGU_iff_firstChoiceEGU _ hsα, realClockEGU_iff_firstChoiceEGU _ hsβ]
  have hcard : (maximalIndependentSets nbβ).card = (maximalIndependentSets nbα).card := by
    rw [maximalIndependentSets_map_equiv e nbα nbβ hnb, Finset.card_map]
  have huniv : (Finset.univ : Finset β) = (Finset.univ : Finset α).map e.toEmbedding := by
    simp
  have hfc : Fintype.card β = Fintype.card α := (Fintype.card_congr e).symm
  constructor
  · rintro ⟨r, hr, hu⟩
    refine ⟨fun b => r (e.symm b), fun b => hr _, fun K hK => ?_⟩
    rw [maximalIndependentSets_map_equiv e nbα nbβ hnb] at hK
    obtain ⟨I, hI, rfl⟩ := Finset.mem_map.mp hK
    simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
    rw [huniv, hfc, finiteRaceLaw_map_equiv e nbα nbβ hnb, hcard]
    simpa using hu I hI
  · rintro ⟨r, hr, hu⟩
    refine ⟨fun a => r (e a), fun a => hr _, fun I hI => ?_⟩
    have hK : I.map e.toEmbedding ∈ maximalIndependentSets nbβ := by
      rw [mem_maximalIndependentSets, isMIS_map_equiv_iff e nbα nbβ hnb]
      exact (mem_maximalIndependentSets _ _).mp hI
    have := hu _ hK
    rw [huniv, hfc, finiteRaceLaw_map_equiv e nbα nbβ hnb, hcard] at this
    exact this

end Iso

/-! ### edgeless graphs -/

/-- An edgeless graph on a nonempty finite type is EGU: its only maximal
independent set is the whole vertex set. -/
theorem realClockEGU_edgeless {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ] :
    RealClockEGU (fun _ : γ => (∅ : Finset γ)) := by
  have hs : ∀ x y : γ, y ∈ (fun _ : γ => (∅ : Finset γ)) x →
      x ∈ (fun _ : γ => (∅ : Finset γ)) y := by
    simp
  have hi : ∀ v : γ, v ∉ (fun _ : γ => (∅ : Finset γ)) v := by simp
  have hM : maximalIndependentSets (fun _ : γ => (∅ : Finset γ)) = {Finset.univ} := by
    ext I
    simp only [mem_maximalIndependentSets, Finset.mem_singleton, IsMaximalIndependentSet,
      IsIndependentSet, Finset.notMem_empty, not_false_eq_true, implies_true, true_and,
      and_false, exists_false]
    constructor
    · intro h
      ext v
      simp only [Finset.mem_univ, iff_true]
      by_contra hv
      exact h v hv
    · rintro rfl v hv
      exact hv (Finset.mem_univ v)
  rw [realClockEGU_iff_firstChoiceEGU _ hs]
  refine ⟨fun _ => 1, fun _ => one_pos, fun I hI => ?_⟩
  have hsum := finiteRaceLaw_sum_MIS (fun _ => (1 : ℝ)) (fun _ => one_pos) _ hs hi
  rw [hM, Finset.sum_singleton] at hsum
  rw [hM, Finset.mem_singleton] at hI
  rw [hI, hsum, hM, Finset.card_singleton]
  norm_num

/-! ### cotrees -/

/-- Cotrees: single vertices closed under disjoint union and join. -/
inductive Cotree
  | leaf : Cotree
  | union : Cotree → Cotree → Cotree
  | join : Cotree → Cotree → Cotree

namespace Cotree

/-- Vertex type of a cotree. -/
def V : Cotree → Type
  | leaf => Unit
  | union s t => s.V ⊕ t.V
  | join s t => s.V ⊕ t.V

instance instFintype : (t : Cotree) → Fintype t.V
  | leaf => inferInstanceAs (Fintype Unit)
  | union s t => @instFintypeSum s.V t.V (instFintype s) (instFintype t)
  | join s t => @instFintypeSum s.V t.V (instFintype s) (instFintype t)

instance instDecidableEq : (t : Cotree) → DecidableEq t.V
  | leaf => inferInstanceAs (DecidableEq Unit)
  | union s t => @instDecidableEqSum s.V t.V (instDecidableEq s) (instDecidableEq t)
  | join s t => @instDecidableEqSum s.V t.V (instDecidableEq s) (instDecidableEq t)

instance instNonempty : (t : Cotree) → Nonempty t.V
  | leaf => ⟨()⟩
  | union s _ => ⟨Sum.inl (Classical.choice (instNonempty s))⟩
  | join s _ => ⟨Sum.inl (Classical.choice (instNonempty s))⟩

/-- Neighbour map of a cotree graph. -/
def nb : (t : Cotree) → t.V → Finset t.V
  | leaf => fun _ => ∅
  | union s t => unionNb s.nb t.nb
  | join s t => joinNb s.nb t.nb

theorem nb_symm : (t : Cotree) → ∀ x y, y ∈ t.nb x → x ∈ t.nb y
  | leaf => by intro x y h; simp [nb] at h
  | union s t => unionNb_symm (nb_symm s) (nb_symm t)
  | join s t => joinNb_symm (nb_symm s) (nb_symm t)

theorem nb_irrefl : (t : Cotree) → ∀ v, v ∉ t.nb v
  | leaf => by intro v; simp [nb]
  | union s t => unionNb_irrefl (nb_irrefl s) (nb_irrefl t)
  | join s t => joinNb_irrefl (nb_irrefl s) (nb_irrefl t)

/-- **IG-P4, cograph part (Lean, genuine clocks).** Every cotree graph is
EGU for some strictly positive real rate vector. -/
theorem realClockEGU : (t : Cotree) → RealClockEGU t.nb
  | leaf => realClockEGU_edgeless (γ := Unit)
  | union s t =>
      (realClockEGU_union_iff s.nb t.nb (nb_symm s) (nb_symm t) (nb_irrefl s)
        (nb_irrefl t)).mpr ⟨realClockEGU s, realClockEGU t⟩
  | join s t =>
      (realClockEGU_join_iff s.nb t.nb (nb_symm s) (nb_symm t) (nb_irrefl s)
        (nb_irrefl t)).mpr ⟨realClockEGU s, realClockEGU t⟩

/-- An edgeless cotree on `n + 1` vertices. -/
def edgeless : ℕ → Cotree
  | 0 => leaf
  | n + 1 => union leaf (edgeless n)

/-- Complete multipartite cotree with parts of sizes `p+1, q+1, …`. -/
def completeMultipartite (p : ℕ) : List ℕ → Cotree
  | [] => edgeless p
  | q :: ps => join (edgeless p) (completeMultipartite q ps)

/-- **IG-P1 (Lean, genuine clocks).** Complete multipartite graphs are EGU. -/
theorem completeMultipartite_realClockEGU (p : ℕ) (ps : List ℕ) :
    RealClockEGU (completeMultipartite p ps).nb :=
  realClockEGU _

end Cotree

/-- A neighbour map is a cograph if it is isomorphic to a cotree graph. -/
def IsCograph {α : Type*} (nb : α → Finset α) : Prop :=
  ∃ (t : Cotree) (e : t.V ≃ α), ∀ v, nb (e v) = (t.nb v).map e.toEmbedding

/-- **Every finite cograph is EGU under genuine exponential clocks.** -/
theorem IsCograph.realClockEGU {α : Type*} [Fintype α] [DecidableEq α]
    {nb : α → Finset α} (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (h : IsCograph nb) :
    RealClockEGU nb := by
  obtain ⟨t, e, he⟩ := h
  exact (realClockEGU_congr_equiv e t.nb nb he (Cotree.nb_symm t) hs).mp
    (Cotree.realClockEGU t)

end InverseGreedy
