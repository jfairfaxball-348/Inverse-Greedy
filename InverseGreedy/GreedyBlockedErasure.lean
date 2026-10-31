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

/-- A fixed vertex with no adjacency to the scanned vertex does not
change its accept/reject decision or interfere with that step. -/
theorem greedyAccept_insert_separate
    (neighbours : α → Finset α)
    (accepted : Finset α) (v w : α)
    (hsep : v ∉ neighbours w) :
    greedyAccept neighbours (insert v accepted) w =
      insert v (greedyAccept neighbours accepted w) := by
  have hinter : neighbours w ∩ insert v accepted =
      neighbours w ∩ accepted := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, (rfl | hxa)⟩
      · exact (hsep hx).elim
      · exact ⟨hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨hx, Or.inr hxa⟩
  by_cases hb : (neighbours w ∩ accepted).Nonempty
  · simp [greedyAccept, hinter, hb]
  · simp [greedyAccept, hinter, hb, Finset.insert_comm]

/-- A nonadjacent sentinel commutes with a complete greedy scan. -/
theorem greedyScan_insert_separate
    (neighbours : α → Finset α)
    (v : α) (suffix : List α) (accepted : Finset α)
    (hsep : ∀ w ∈ suffix, v ∉ neighbours w) :
    suffix.foldl (greedyAccept neighbours) (insert v accepted) =
      insert v (suffix.foldl (greedyAccept neighbours) accepted) := by
  induction suffix generalizing accepted with
  | nil => rfl
  | cons w tail ih =>
      have hw : v ∉ neighbours w := hsep w (by simp)
      have ht : ∀ x ∈ tail, v ∉ neighbours x := by
        intro x hx
        exact hsep x (by simp [hx])
      simp only [List.foldl_cons]
      rw [greedyAccept_insert_separate neighbours accepted v w hw]
      exact ih _ ht

/-- The first greedy vertex is accepted, its neighbours are irrelevant,
and its accepted status does not alter later decisions on the residual
vertex list. In particular this is the exact deterministic reduction
needed for the first-choice recurrence. -/
theorem greedyOutput_first_residual
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (v : α) (suffix : List α) :
    greedyOutput neighbours (v :: suffix) =
      insert v (greedyOutput neighbours
        (suffix.filter (fun w => w ∉ neighbours v))) := by
  let kept := suffix.filter (fun w => w ∉ neighbours v)
  have hs : ∀ w ∈ kept, v ∉ neighbours w := by
    intro w hw hvw
    have hn : w ∉ neighbours v := by
      have hm : w ∈ suffix ∧ w ∉ neighbours v := by
        simpa [kept] using hw
      exact hm.2
    exact hn (hSymm w v hvw)
  calc
    greedyOutput neighbours (v :: suffix) =
        kept.foldl (greedyAccept neighbours) ({v} : Finset α) := by
          exact greedyOutput_first_erase_neighbors neighbours hSymm v suffix
    _ = insert v (kept.foldl (greedyAccept neighbours) ∅) := by
          exact greedyScan_insert_separate neighbours v kept ∅ hs
    _ = insert v (greedyOutput neighbours kept) := rfl

end InverseGreedy
