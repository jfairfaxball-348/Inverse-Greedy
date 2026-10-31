import InverseGreedy.FiniteLawFuel

/-!
# S011: exact head decomposition of the actual permutation list

Every full priority order has exactly one head and exactly one tail
permutation of the remaining active vertices. Crucially this is an
equivalence of duplicate-free *lists of orders* (not just support
membership): each order is enumerated with multiplicity one.
This is a discrete combinatorial bridge and says nothing about
independent continuous exponential clocks.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- The recursive head-and-tail enumeration, retaining the empty
permutation as a single leaf. -/
def headSplitOrders (active : Finset α) : List (List α) :=
  if active = ∅ then [[]]
  else active.toList.flatMap (fun v =>
    ((active.erase v).toList.permutations.map (List.cons v)))

/-- A head-tail enumeration has exactly the support of the actual
Mathlib `List.permutations` enumeration. -/
theorem mem_headSplitOrders_iff (active : Finset α) (order : List α) :
    order ∈ headSplitOrders active ↔
      order ∈ active.toList.permutations := by
  by_cases he : active = ∅
  · subst active
    simp [headSplitOrders]
  · rw [mem_full_priority_permutations_iff]
    constructor
    · intro h
      simp only [headSplitOrders, if_neg he] at h
      rcases List.mem_flatMap.mp h with ⟨v, hv, hm⟩
      rcases List.mem_map.mp hm with ⟨tail, ht, hcons⟩
      subst order
      have hvactive : v ∈ active := Finset.mem_toList.mp hv
      obtain ⟨htnodup, htset⟩ :=
        (mem_full_priority_permutations_iff (active.erase v) tail).mp ht
      have hvnot : v ∉ tail.toFinset := by
        rw [htset]
        simp
      constructor
      · exact List.nodup_cons.mpr ⟨by simpa using hvnot, htnodup⟩
      · simpa [List.toFinset_cons, htset] using
          (Finset.insert_erase hvactive)
    · intro h
      rcases h with ⟨hnodup, hset⟩
      cases order with
      | nil =>
          have hempty : active = ∅ := by
            simpa using hset.symm
          exact (he hempty).elim
      | cons v tail =>
          have hvactive : v ∈ active := by
            have hv : v ∈ (v :: tail).toFinset := by simp
            rwa [hset] at hv
          obtain ⟨hvnot, htnodup⟩ := List.nodup_cons.mp hnodup
          have hvnotset : v ∉ tail.toFinset := by simpa using hvnot
          have htset : tail.toFinset = active.erase v := by
            calc
              tail.toFinset = (insert v tail.toFinset).erase v := by
                simp [hvnotset]
              _ = (v :: tail).toFinset.erase v := by
                simp [List.toFinset_cons]
              _ = active.erase v := congrArg (fun s : Finset α => s.erase v) hset
          have ht : tail ∈ (active.erase v).toList.permutations :=
            (mem_full_priority_permutations_iff (active.erase v) tail).mpr
              ⟨htnodup, htset⟩
          simp only [headSplitOrders, if_neg he]
          apply List.mem_flatMap.mpr
          refine ⟨v, Finset.mem_toList.mpr hvactive, ?_⟩
          exact List.mem_map.mpr ⟨tail, ht, rfl⟩

/-- There are no repeated orders in the head-tail enumeration,
including when the active set is empty. -/
theorem headSplitOrders_nodup (active : Finset α) :
    (headSplitOrders active).Nodup := by
  by_cases he : active = ∅
  · subst active
    simp [headSplitOrders]
  · simp only [headSplitOrders, if_neg he]
    rw [List.nodup_flatMap]
    constructor
    · intro v hv
      exact (List.nodup_permutations (active.erase v).toList
        (Finset.nodup_toList _)).map
        (fun _ _ h => (List.cons.inj h).2)
    · apply (Finset.nodup_toList active).imp
      intro v w hne
      apply List.disjoint_left.mpr
      intro order hleft
      rcases List.mem_map.mp hleft with ⟨tail, ht, hcons⟩
      subst order
      intro hright
      rcases List.mem_map.mp hright with ⟨tail', ht', heq⟩
      exact hne ((List.cons.inj heq).1)

/-- Actual `List.permutations` decomposes by unique head and
permutations of the erased active set, with exact multiplicity. -/
theorem full_priority_permutations_head_decomposition (active : Finset α) :
    active.toList.permutations.Perm (headSplitOrders active) := by
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_permutations active.toList (Finset.nodup_toList active))
    (headSplitOrders_nodup active)).2
  intro order
  exact (mem_headSplitOrders_iff active order).symm

end InverseGreedy
