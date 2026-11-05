import InverseGreedy.AtlasCertificates

/-!
# S041: Boolean edge-vector encoding of graphs and kernel-cheap certificates

A graph on `Fin n` with `m = n(n-1)/2` possible edges is encoded by an edge
vector `f : Fin m → Bool` through explicit pair/rank tables. `allBool m P`
enumerates all `2^m` vectors by structural recursion (cheap kernel
reduction, unlike `Finset.powerset`), with soundness `allBool_sound`.
`nbOf_fOf` shows every symmetric irreflexive neighbour map is decoded from
its own edge vector, so statements about all graphs on `Fin n` reduce to a
single kernel-checked Boolean computation. `IsoCheckB` is a Boolean
isomorphism certificate; `realClockEGU_iff_of_isoCheckB` converts it into
EGU equivalence via `realClockEGU_congr_equiv`.
-/

namespace InverseGreedy

/-- Exhaustive Boolean check over all edge vectors of length `m`. -/
def allBool : (m : ℕ) → ((Fin m → Bool) → Bool) → Bool
  | 0, P => P Fin.elim0
  | m + 1, P => allBool m (fun f => P (Fin.cons false f)) && allBool m (fun f => P (Fin.cons true f))

theorem allBool_sound : ∀ (m : ℕ) (P : (Fin m → Bool) → Bool), allBool m P = true →
    ∀ f, P f = true
  | 0, P, h, f => by
      have : f = Fin.elim0 := funext (fun i => Fin.elim0 i)
      rw [this]; exact h
  | m + 1, P, h, f => by
      simp only [allBool, Bool.and_eq_true] at h
      rw [← Fin.cons_self_tail f]
      cases hf : f 0
      · exact allBool_sound m _ h.1 (Fin.tail f)
      · exact allBool_sound m _ h.2 (Fin.tail f)

variable {n m : ℕ}

/-- Adjacency read from an edge vector through a rank table. -/
def adjOf (rank : Fin n → Fin n → Fin m) (f : Fin m → Bool) (i j : Fin n) : Bool :=
  if i < j then f (rank i j) else if j < i then f (rank j i) else false

/-- Neighbour map of an edge vector. -/
def nbOf (rank : Fin n → Fin n → Fin m) (f : Fin m → Bool) : Fin n → Finset (Fin n) :=
  fun i => Finset.univ.filter (fun j => adjOf rank f i j = true)

/-- Edge vector of a neighbour map through a pair table. -/
def fOf (pair : Fin m → Fin n × Fin n) (nb : Fin n → Finset (Fin n)) : Fin m → Bool :=
  fun r => decide ((pair r).2 ∈ nb (pair r).1)

theorem nbOf_fOf (rank : Fin n → Fin n → Fin m) (pair : Fin m → Fin n × Fin n)
    (hrank : ∀ i j, i < j → pair (rank i j) = (i, j))
    (nb : Fin n → Finset (Fin n)) (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (hi : ∀ v, v ∉ nb v) :
    nbOf rank (fOf pair nb) = nb := by
  funext i
  ext j
  simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold adjOf fOf
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h, hrank i j h]; simp
  · subst h; simp [hi]
  · rw [if_neg (not_lt.mpr h.le), if_pos h, hrank j i h]
    simp only [decide_eq_true_eq]
    exact ⟨hs _ _, hs _ _⟩

theorem nbOf_symm (rank : Fin n → Fin n → Fin m) (f : Fin m → Bool) :
    ∀ x y, y ∈ nbOf rank f x → x ∈ nbOf rank f y := by
  intro x y h
  simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  unfold adjOf at h ⊢
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · rw [if_pos hxy] at h; rw [if_neg (not_lt.mpr hxy.le), if_pos hxy]; exact h
  · subst hxy; simp at h
  · rw [if_neg (not_lt.mpr hxy.le), if_pos hxy] at h; rw [if_pos hxy]; exact h

/-- Boolean isomorphism certificate between two edge vectors. -/
def IsoCheckB (rank : Fin n → Fin n → Fin m) (f h : Fin m → Bool) (σ τ : Fin n → Fin n) : Bool :=
  (List.finRange n).all (fun x => τ (σ x) == x) &&
  (List.finRange n).all (fun y => σ (τ y) == y) &&
  (List.finRange n).all (fun i => (List.finRange n).all (fun j =>
    adjOf rank f i j == adjOf rank h (σ i) (σ j)))

theorem realClockEGU_iff_of_isoCheckB (rank : Fin n → Fin n → Fin m) (f h : Fin m → Bool)
    (σ τ : Fin n → Fin n) (hc : IsoCheckB rank f h σ τ = true) :
    RealClockEGU (nbOf rank f) ↔ RealClockEGU (nbOf rank h) := by
  simp only [IsoCheckB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at hc
  obtain ⟨⟨hl, hr⟩, hadj⟩ := hc
  let e : Fin n ≃ Fin n := ⟨σ, τ, hl, hr⟩
  have hnb : ∀ a, nbOf rank h (e a) = (nbOf rank f a).map e.toEmbedding := by
    intro a
    ext b
    obtain ⟨c, rfl⟩ : ∃ c, b = σ c := ⟨τ b, (hr b).symm⟩
    simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    change adjOf rank h (σ a) (σ c) = true ↔ ∃ x, adjOf rank f a x = true ∧ σ x = σ c
    constructor
    · intro hh; exact ⟨c, by rw [hadj]; exact hh, rfl⟩
    · rintro ⟨x, hx, hxc⟩
      have : x = c := by rw [← hl x, hxc, hl c]
      subst this; rw [← hadj]; exact hx
  exact realClockEGU_congr_equiv e _ _ hnb (nbOf_symm rank f) (nbOf_symm rank h)

/-- The decoded graph of a certificate's target is the stated isomorphic copy. -/
theorem iso_of_isoCheckB (rank : Fin n → Fin n → Fin m) (f h : Fin m → Bool)
    (σ τ : Fin n → Fin n) (hc : IsoCheckB rank f h σ τ = true) :
    ∃ e : Fin n ≃ Fin n, ∀ a, nbOf rank h (e a) = (nbOf rank f a).map e.toEmbedding := by
  simp only [IsoCheckB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at hc
  obtain ⟨⟨hl, hr⟩, hadj⟩ := hc
  refine ⟨⟨σ, τ, hl, hr⟩, fun a => ?_⟩
  ext b
  obtain ⟨c, rfl⟩ : ∃ c, b = σ c := ⟨τ b, (hr b).symm⟩
  simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.toEmbedding_apply]
  change adjOf rank h (σ a) (σ c) = true ↔ ∃ x, adjOf rank f a x = true ∧ σ x = σ c
  constructor
  · intro hh; exact ⟨c, by rw [hadj]; exact hh, rfl⟩
  · rintro ⟨x, hx, hxc⟩
    have : x = c := by rw [← hl x, hxc, hl c]
    subst this; rw [← hadj]; exact hx

end InverseGreedy
