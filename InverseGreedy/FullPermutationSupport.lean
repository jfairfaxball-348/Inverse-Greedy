import InverseGreedy.OrderLeafBridge

/-!
# S008: support of the complete finite priority-permutation law

A full priority ordering of a finite active vertex set is exactly a
duplicate-free list whose underlying finset is the active set.
This uses Mathlib's actual `List.permutations`, not a factorial
`decide` computation. Combining with S007 gives the correct
leaf probability for every member of that support.

This file does NOT yet prove that the permutation weights sum to one,
their greedy pushforward is `finiteRaceLaw`, or an exponential-clock
measure equivalence.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Membership in the actual list of permutations is equivalent to
having each active vertex once, with no extra vertices. -/
theorem mem_full_priority_permutations_iff (active : Finset α)
    (order : List α) :
    order ∈ active.toList.permutations ↔
      order.Nodup ∧ order.toFinset = active := by
  constructor
  · intro hmem
    have hperm : order.Perm active.toList := List.mem_permutations.mp hmem
    have hnodup : order.Nodup :=
      hperm.nodup_iff.mpr (Finset.nodup_toList active)
    have hset : order.toFinset = (active.toList).toFinset :=
      List.toFinset_eq_of_perm order active.toList hperm
    exact ⟨hnodup, by simpa using hset⟩
  · rintro ⟨hnodup, hset⟩
    apply List.mem_permutations.mpr
    have hset' : order.toFinset = (active.toList).toFinset := by
      simpa using hset
    exact List.perm_of_nodup_nodup_toFinset_eq
      hnodup (Finset.nodup_toList active) hset'

/-- On each and every full permutation, the S007 finite choice-leaf
product is exactly the corresponding order mass. -/
theorem full_priority_leaf_mass_eq_orderMass (rates : α → ℝ)
    (active : Finset α) (order : List α)
    (hmem : order ∈ active.toList.permutations) :
    orderLeafMass rates order = orderMass rates order := by
  exact orderLeafMass_eq_orderMass rates order
    ((mem_full_priority_permutations_iff active order).mp hmem).1

end InverseGreedy
