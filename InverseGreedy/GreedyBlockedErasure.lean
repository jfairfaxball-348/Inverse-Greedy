import InverseGreedy.FullPermutationNormalization

namespace InverseGreedy
variable {α : Type*} [DecidableEq α]

theorem greedyAccept_extensive (neighbours : α → Finset α)
    (accepted : Finset α) (w : α) :
    accepted ⊆ greedyAccept neighbours accepted w := by
  intro x hx
  by_cases h : (neighbours w ∩ accepted).Nonempty
  · simpa [greedyAccept, h] using hx
  · simp only [greedyAccept, h, ↓reduceIte, Finset.mem_insert]
    exact Or.inr hx

theorem greedyScan_preserves_mem (neighbours : α → Finset α)
    (suffix : List α) (accepted : Finset α) (v : α)
    (hv : v ∈ accepted) :
    v ∈ suffix.foldl (greedyAccept neighbours) accepted := by
  induction suffix generalizing accepted with
  | nil => simpa using hv
  | cons w tail ih =>
      simp only [List.foldl_cons]
      exact ih _ ((greedyAccept_extensive neighbours accepted w) hv)

end InverseGreedy
