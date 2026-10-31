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

/-- With symmetric adjacency, a vertex already accepted permanently
rejects all its later neighbours. Filtering those neighbours out does
not change the accepted set at the end of the scan. -/
theorem greedyScan_erase_neighbors
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (v : α) (suffix : List α) (accepted : Finset α)
    (hv : v ∈ accepted) :
    suffix.foldl (greedyAccept neighbours) accepted =
      (suffix.filter (fun w => w ∉ neighbours v)).foldl
        (greedyAccept neighbours) accepted := by
  induction suffix generalizing accepted with
  | nil => rfl
  | cons w tail ih =>
      by_cases hw : w ∈ neighbours v
      · have hblocked : (neighbours w ∩ accepted).Nonempty := by
          refine ⟨v, ?_⟩
          simp only [Finset.mem_inter]
          exact ⟨hSymm v w hw, hv⟩
        have hreject := greedyAccept_blocked neighbours accepted w hblocked
        calc
          (w :: tail).foldl (greedyAccept neighbours) accepted =
              tail.foldl (greedyAccept neighbours) accepted := by
                simp [hreject]
          _ = (tail.filter (fun x => x ∉ neighbours v)).foldl
                (greedyAccept neighbours) accepted := ih accepted hv
          _ = ((w :: tail).filter (fun x => x ∉ neighbours v)).foldl
                (greedyAccept neighbours) accepted := by simp [hw]
      · have hv' : v ∈ greedyAccept neighbours accepted w :=
          (greedyAccept_extensive neighbours accepted w) hv
        calc
          (w :: tail).foldl (greedyAccept neighbours) accepted =
              tail.foldl (greedyAccept neighbours)
                (greedyAccept neighbours accepted w) := rfl
          _ = (tail.filter (fun x => x ∉ neighbours v)).foldl
                (greedyAccept neighbours)
                (greedyAccept neighbours accepted w) := ih _ hv'
          _ = ((w :: tail).filter (fun x => x ∉ neighbours v)).foldl
                (greedyAccept neighbours) accepted := by simp [hw]

/-- Pointwise deletion after the first accepted vertex; no probabilistic
assumptions or clock calculations are used. -/
theorem greedyOutput_first_erase_neighbors
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (v : α) (suffix : List α) :
    greedyOutput neighbours (v :: suffix) =
      (suffix.filter (fun w => w ∉ neighbours v)).foldl
        (greedyAccept neighbours) ({v} : Finset α) := by
  have hstart : greedyAccept neighbours ∅ v = ({v} : Finset α) := by
    simp [greedyAccept]
  unfold greedyOutput
  simp only [List.foldl_cons, hstart]
  exact greedyScan_erase_neighbors neighbours hSymm v suffix {v} (by simp)

end InverseGreedy
