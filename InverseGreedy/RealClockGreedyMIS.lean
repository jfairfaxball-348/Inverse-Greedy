import InverseGreedy.RealClockGreedyLaw

/-!
# S041: the real-clock greedy output is always a maximal independent set

For a symmetric, irreflexive neighbour map, the sequential greedy scan of
any list containing every vertex returns a maximal independent set
(pointwise, for every list, not almost surely). Consequently, under
genuine independent exponential clocks with strictly positive rates, the
real-clock greedy output law is a probability distribution supported on
`maximalIndependentSets`: non-MIS targets have probability zero and the
MIS probabilities sum to one. This makes the `RealClockEGU` condition the
statement that the output law is *exactly* uniform on the MIS family.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- One greedy step preserves independence. -/
theorem greedyAccept_independent (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (hIrr : ∀ v, v ∉ neighbours v)
    (acc : Finset α) (hacc : IsIndependentSet neighbours acc) (w : α) :
    IsIndependentSet neighbours (greedyAccept neighbours acc w) := by
  by_cases h : (neighbours w ∩ acc).Nonempty
  · simpa [greedyAccept, h] using hacc
  · have hdisj : ∀ x ∈ acc, x ∉ neighbours w := by
      intro x hx hxw
      exact h ⟨x, Finset.mem_inter.mpr ⟨hxw, hx⟩⟩
    simp only [greedyAccept, h, ↓reduceIte]
    intro u hu v hv
    rcases Finset.mem_insert.mp hu with rfl | hu'
    · rcases Finset.mem_insert.mp hv with rfl | hv'
      · exact hIrr _
      · exact hdisj v hv'
    · rcases Finset.mem_insert.mp hv with rfl | hv'
      · intro hvu
        exact hdisj u hu' (hSymm u v hvu)
      · exact hacc u hu' v hv'

/-- The whole greedy scan preserves independence. -/
theorem greedyScan_independent (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (hIrr : ∀ v, v ∉ neighbours v) :
    ∀ (l : List α) (acc : Finset α), IsIndependentSet neighbours acc →
      IsIndependentSet neighbours (l.foldl (greedyAccept neighbours) acc)
  | [], _, h => h
  | w :: l, acc, h => by
      simp only [List.foldl_cons]
      exact greedyScan_independent neighbours hSymm hIrr l _
        (greedyAccept_independent neighbours hSymm hIrr acc h w)

/-- Every scanned vertex ends up accepted or has an accepted neighbour. -/
theorem greedyScan_dominates (neighbours : α → Finset α) :
    ∀ (l : List α) (acc : Finset α) (v : α), v ∈ l →
      v ∈ l.foldl (greedyAccept neighbours) acc ∨
        ∃ u ∈ l.foldl (greedyAccept neighbours) acc, u ∈ neighbours v
  | [], _, _, hv => absurd hv (List.not_mem_nil)
  | w :: l, acc, v, hv => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hv with rfl | hv'
      · by_cases h : (neighbours v ∩ acc).Nonempty
        · right
          obtain ⟨u, hu⟩ := id h
          refine ⟨u, greedyScan_preserves_mem neighbours l _ u ?_,
            (Finset.mem_inter.mp hu).1⟩
          simpa [greedyAccept, h] using (Finset.mem_inter.mp hu).2
        · left
          apply greedyScan_preserves_mem neighbours l _ v
          simp [greedyAccept, h]
      · exact greedyScan_dominates neighbours l _ v hv'

/-- The greedy output of any list containing every vertex is a maximal
independent set, for symmetric irreflexive neighbour maps. -/
theorem greedyOutput_isMaximalIndependentSet (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (hIrr : ∀ v, v ∉ neighbours v)
    (order : List α) (hall : ∀ v, v ∈ order) :
    IsMaximalIndependentSet neighbours (greedyOutput neighbours order) := by
  constructor
  · exact greedyScan_independent neighbours hSymm hIrr order ∅
      (by intro u hu; simp at hu)
  · intro v hv
    rcases greedyScan_dominates neighbours order ∅ v (hall v) with h | ⟨u, hu, huv⟩
    · exact absurd h hv
    · exact ⟨u, hu, hSymm v u huv⟩

/-- Every realised real-clock greedy output is a maximal independent set. -/
theorem realClockGreedyOutput_isMaximalIndependentSet [Fintype α]
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (hIrr : ∀ v, v ∉ neighbours v) (ω : α → ℝ) :
    IsMaximalIndependentSet neighbours (realClockGreedyOutput neighbours ω) := by
  apply greedyOutput_isMaximalIndependentSet neighbours hSymm hIrr
  intro v
  have hperm := List.mem_permutations.mp (clockSortedOrder_mem_permutations ω)
  exact hperm.symm.subset (Finset.mem_toList.mpr (Finset.mem_univ v))

theorem realClockGreedyOutput_mem_maximalIndependentSets [Fintype α]
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (hIrr : ∀ v, v ∉ neighbours v) (ω : α → ℝ) :
    realClockGreedyOutput neighbours ω ∈ maximalIndependentSets neighbours := by
  rw [mem_maximalIndependentSets]
  exact realClockGreedyOutput_isMaximalIndependentSet neighbours hSymm hIrr ω

/-- Targets that are not maximal independent sets have probability zero
(no rate hypothesis needed). -/
theorem finiteIndependentExp_realClockGreedyOutput_nonMIS [Fintype α]
    (rates : α → ℝ) (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (hIrr : ∀ v, v ∉ neighbours v) (target : Finset α)
    (hnot : target ∉ maximalIndependentSets neighbours) :
    finiteIndependentExp rates
        {ω : α → ℝ | realClockGreedyOutput neighbours ω = target} = 0 := by
  have hempty :
      {ω : α → ℝ | realClockGreedyOutput neighbours ω = target} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hnot (h ▸ realClockGreedyOutput_mem_maximalIndependentSets
      neighbours hSymm hIrr ω)
  rw [hempty, measure_empty]

/-- **The real-clock greedy output law is a probability distribution on
the maximal independent sets.** -/
theorem finiteIndependentExp_realClockGreedyOutput_sum_MIS [Fintype α]
    (rates : α → ℝ) (hpos : ∀ i, 0 < rates i)
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (hIrr : ∀ v, v ∉ neighbours v) :
    ∑ I ∈ maximalIndependentSets neighbours,
        finiteIndependentExp rates
          {ω : α → ℝ | realClockGreedyOutput neighbours ω = I} = 1 := by
  have : IsProbabilityMeasure (finiteIndependentExp rates) :=
    finiteIndependentExp_probability rates hpos
  have hdisj : ((maximalIndependentSets neighbours : Finset (Finset α)) :
      Set (Finset α)).PairwiseDisjoint
        (fun I => {ω : α → ℝ | realClockGreedyOutput neighbours ω = I}) := by
    intro I _ J _ hIJ
    apply Set.disjoint_left.mpr
    intro ω h1 h2
    exact hIJ (h1.symm.trans h2)
  have hcover :
      (⋃ I ∈ maximalIndependentSets neighbours,
        {ω : α → ℝ | realClockGreedyOutput neighbours ω = I}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨_, realClockGreedyOutput_mem_maximalIndependentSets
      neighbours hSymm hIrr ω, rfl⟩
  rw [← measure_biUnion_finset hdisj
    (fun I _ => realClockGreedyOutput_event_measurable neighbours I),
    hcover, measure_univ]

end InverseGreedy
