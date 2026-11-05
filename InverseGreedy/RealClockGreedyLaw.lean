import InverseGreedy.FiniteClockOrderLaw
import InverseGreedy.PriorityOutputPushforward

/-!
# S041: the genuine real-clock greedy output and its exact law

Vertices of a finite type carry independent real exponential clocks
(Mathlib's actual product measure). The realised priority order is the
*stable merge sort* of all vertices by clock value (ties, a null event,
are broken by the fixed enumeration `Finset.univ.toList`). The greedy
output is the sequential greedy scan of that sorted list.

Proved here, for strictly positive real rates:
* the realised order and every output event are measurable;
* on each strict chamber the sorted order is that chamber's order;
* the law of the real-clock greedy output is exactly the discrete
  full-permutation pushforward `priorityOutputMass`, and hence (for
  symmetric neighbour maps) the first-choice recursion `finiteRaceLaw`;
* the charter's EGU property, stated with genuine exponential clocks, is
  equivalent to its discrete first-choice-recursion formulation.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

variable {α : Type*}

/-- All pairwise clock comparisons, as a finite Boolean pattern. -/
noncomputable def clockComparisonPattern (ω : α → ℝ) : α → α → Bool :=
  fun i j => decide (ω i ≤ ω j)

/-- The realised priority order: a stable sort of all vertices by clock
value. It depends on the clocks only through the comparison pattern. -/
noncomputable def clockSortedOrder [Fintype α] (ω : α → ℝ) : List α :=
  (Finset.univ : Finset α).toList.mergeSort (clockComparisonPattern ω)

/-- Greedy output of genuine real arrival clocks. -/
noncomputable def realClockGreedyOutput [Fintype α] [DecidableEq α] (neighbours : α → Finset α)
    (ω : α → ℝ) : Finset α :=
  greedyOutput neighbours (clockSortedOrder ω)

/-- The comparison pattern is a measurable map into a finite discrete space. -/
theorem clockComparisonPattern_measurable :
    Measurable (clockComparisonPattern : (α → ℝ) → α → α → Bool) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_to_countable'
  intro b
  have hle : MeasurableSet {ω : α → ℝ | ω i ≤ ω j} :=
    measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  cases b with
  | true =>
      convert hle using 1
      ext ω
      simp [clockComparisonPattern]
  | false =>
      convert hle.compl using 1
      ext ω
      simp [clockComparisonPattern]

/-- Every event determined by the realised clock order is measurable. -/
theorem clockSortedOrder_preimage_measurable [Fintype α] [DecidableEq α] (S : Set (List α)) :
    MeasurableSet {ω : α → ℝ | clockSortedOrder ω ∈ S} := by
  change MeasurableSet (clockComparisonPattern ⁻¹'
    {p : α → α → Bool |
      (Finset.univ : Finset α).toList.mergeSort p ∈ S})
  exact clockComparisonPattern_measurable MeasurableSet.of_discrete

/-- Each real-clock greedy output event is measurable. -/
theorem realClockGreedyOutput_event_measurable [Fintype α] [DecidableEq α]
    (neighbours : α → Finset α) (target : Finset α) :
    MeasurableSet {ω : α → ℝ | realClockGreedyOutput neighbours ω = target} :=
  clockSortedOrder_preimage_measurable
    {order : List α | greedyOutput neighbours order = target}

/-- The realised order is always a complete permutation of the vertices. -/
theorem clockSortedOrder_mem_permutations [Fintype α] (ω : α → ℝ) :
    clockSortedOrder ω ∈ (Finset.univ : Finset α).toList.permutations :=
  List.mem_permutations.mpr (List.mergeSort_perm _ _)

/-- The realised order is weakly increasing in clock value. -/
theorem clockSortedOrder_pairwise_le [Fintype α] (ω : α → ℝ) :
    (clockSortedOrder ω).Pairwise (fun i j => ω i ≤ ω j) := by
  have h := List.pairwise_mergeSort (le := clockComparisonPattern ω)
    (fun a b c hab hbc => by
      simp only [clockComparisonPattern, decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      simp only [clockComparisonPattern, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _)
    (Finset.univ : Finset α).toList
  unfold clockSortedOrder
  simpa [clockComparisonPattern] using h

/-- A strict chamber of a list makes the clocks injective on its entries. -/
theorem strictClockChamber_clock_injective {order : List α}
    {ω : α → ℝ} (hω : ω ∈ strictClockChamber order) {a b : α}
    (ha : a ∈ order) (hb : b ∈ order) (hab : ω a = ω b) : a = b := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hb
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · have := hω ⟨p, hp⟩ ⟨q, hq⟩ hpq
    exact absurd hab (ne_of_lt this)
  · subst hpq
    rfl
  · have := hω ⟨q, hq⟩ ⟨p, hp⟩ hpq
    exact absurd hab.symm (ne_of_lt this)

/-- A strict chamber is the same as strict pairwise increase of the list. -/
theorem strictClockChamber_iff_pairwise (order : List α) (ω : α → ℝ) :
    ω ∈ strictClockChamber order ↔
      order.Pairwise (fun i j => ω i < ω j) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro hω i j hi hj hij
    exact hω ⟨i, hi⟩ ⟨j, hj⟩ hij
  · intro h a b hab
    exact h a.val b.val a.isLt b.isLt hab

/-- On the strict chamber of any complete permutation the realised
sorted order is exactly that permutation (no null-set exception). -/
theorem clockSortedOrder_eq_of_mem_strictClockChamber [Fintype α]
    (order : List α)
    (hperm : order ∈ (Finset.univ : Finset α).toList.permutations)
    (ω : α → ℝ) (hω : ω ∈ strictClockChamber order) :
    clockSortedOrder ω = order := by
  have hstrict := (strictClockChamber_iff_pairwise order ω).mp hω
  have hsortperm : List.Perm (clockSortedOrder ω) order :=
    (List.mem_permutations.mp (clockSortedOrder_mem_permutations ω)).trans
      (List.mem_permutations.mp hperm).symm
  apply List.Perm.eq_of_pairwise (le := fun i j => ω i ≤ ω j)
  · intro a b ha hb hab hba
    exact strictClockChamber_clock_injective hω (hsortperm.subset ha) hb
      (le_antisymm hab hba)
  · exact clockSortedOrder_pairwise_le ω
  · exact hstrict.imp (fun h => le_of_lt h)
  · exact hsortperm

/-- Without ties the clocks lie in the strict chamber of their own
realised sorted order. -/
theorem mem_strictClockChamber_clockSortedOrder [Fintype α] (ω : α → ℝ)
    (hnotie : ∀ i j, i ≠ j → ω i ≠ ω j) :
    ω ∈ strictClockChamber (clockSortedOrder ω) := by
  rw [strictClockChamber_iff_pairwise]
  have hnodup : (clockSortedOrder ω).Nodup :=
    (List.mem_permutations.mp (clockSortedOrder_mem_permutations ω)).nodup_iff.mpr
      (Finset.nodup_toList _)
  have hle := clockSortedOrder_pairwise_le ω
  have hne := hnodup
  rw [List.Nodup] at hne
  exact (hle.and hne).imp (fun h => lt_of_le_of_ne h.1 (hnotie _ _ h.2))

/-- Every complete permutation of the vertices is a certified complete
clock order in the sense of S038. -/
def completeClockOrderOfPermutation [Fintype α] [DecidableEq α] (order : List α)
    (hperm : order ∈ (Finset.univ : Finset α).toList.permutations) :
    CompleteClockOrder order where
  index := List.Nodup.getEquivOfForallMemList order
    ((mem_full_priority_permutations_iff Finset.univ order).mp hperm).1
    (fun x => by
      have hset :=
        ((mem_full_priority_permutations_iff Finset.univ order).mp hperm).2
      have : x ∈ order.toFinset := by rw [hset]; exact Finset.mem_univ x
      exact List.mem_toFinset.mp this)
  agrees := fun j => by simp

/-- The real-clock strict-order law, phrased for full permutations. -/
theorem finiteIndependentExp_strictClockChamber_permutation [Fintype α] [DecidableEq α]
    (rates : α → ℝ) (hpos : ∀ i, 0 < rates i) (order : List α)
    (hperm : order ∈ (Finset.univ : Finset α).toList.permutations) :
    finiteIndependentExp rates (strictClockChamber order) =
      ENNReal.ofReal (orderMass rates order) :=
  finiteIndependentExp_strictClockChamber_orderMass rates hpos order
    (completeClockOrderOfPermutation order hperm)

/-- **S041 main theorem: genuine real-clock greedy-output law.**
For every finite vertex type, neighbour map and target set, and every
strictly positive real rate vector, the actual independent exponential
probability that the sorted-clock greedy scan outputs `target` equals
the full-permutation weighted pushforward `priorityOutputMass`. -/
theorem finiteIndependentExp_realClockGreedyOutput_eq_priorityOutputMass
    [Fintype α] [DecidableEq α]
    (rates : α → ℝ) (hpos : ∀ i, 0 < rates i)
    (neighbours : α → Finset α) (target : Finset α) :
    finiteIndependentExp rates
        {ω : α → ℝ | realClockGreedyOutput neighbours ω = target} =
      ENNReal.ofReal
        (priorityOutputMass rates neighbours Finset.univ target) := by
  classical
  let μ := finiteIndependentExp rates
  let perms := (Finset.univ : Finset α).toList.permutations
  let S : Finset (List α) :=
    perms.toFinset.filter (fun order => greedyOutput neighbours order = target)
  let E : Set (α → ℝ) :=
    {ω | realClockGreedyOutput neighbours ω = target}
  let U : Set (α → ℝ) := ⋃ order ∈ S, strictClockChamber order
  let T : Set (α → ℝ) := {ω | ∃ i j, i ≠ j ∧ ω i = ω j}
  have hSperm : ∀ order ∈ S, order ∈ perms := by
    intro order h
    exact List.mem_toFinset.mp (Finset.mem_filter.mp h).1
  have hUE : U ⊆ E := by
    intro ω hω
    obtain ⟨order, horder, hmem⟩ := Set.mem_iUnion₂.mp hω
    change greedyOutput neighbours (clockSortedOrder ω) = target
    rw [clockSortedOrder_eq_of_mem_strictClockChamber order
      (hSperm order horder) ω hmem]
    exact (Finset.mem_filter.mp horder).2
  have hEU : E ⊆ U ∪ T := by
    intro ω hω
    by_cases hnotie : ∀ i j, i ≠ j → ω i ≠ ω j
    · left
      apply Set.mem_iUnion₂.mpr
      refine ⟨clockSortedOrder ω, ?_,
        mem_strictClockChamber_clockSortedOrder ω hnotie⟩
      apply Finset.mem_filter.mpr
      exact ⟨List.mem_toFinset.mpr (clockSortedOrder_mem_permutations ω), hω⟩
    · right
      push Not at hnotie
      exact hnotie
  have hT : μ T = 0 := finiteIndependentExp_any_tie_null rates hpos
  have hEqU : μ E = μ U := by
    apply le_antisymm
    · calc
        μ E ≤ μ (U ∪ T) := measure_mono hEU
        _ ≤ μ U + μ T := measure_union_le _ _
        _ = μ U := by rw [hT, add_zero]
    · exact measure_mono hUE
  have hdisj : (S : Set (List α)).PairwiseDisjoint strictClockChamber := by
    intro σ hσ τ hτ hne
    apply Set.disjoint_left.mpr
    intro ω h1 h2
    apply hne
    calc
      σ = clockSortedOrder ω :=
        (clockSortedOrder_eq_of_mem_strictClockChamber σ
          (hSperm σ hσ) ω h1).symm
      _ = τ := clockSortedOrder_eq_of_mem_strictClockChamber τ
          (hSperm τ hτ) ω h2
  have hU : μ U = ∑ order ∈ S, μ (strictClockChamber order) :=
    measure_biUnion_finset hdisj
      (fun order _ => strictClockChamber_measurable order)
  have hnodup : perms.Nodup :=
    List.nodup_permutations _ (Finset.nodup_toList _)
  have hmass :
      priorityOutputMass rates neighbours Finset.univ target =
        ∑ order ∈ S, orderMass rates order := by
    unfold priorityOutputMass
    rw [Finset.sum_filter]
    exact (List.sum_toFinset _ hnodup).symm
  change μ E = _
  rw [hEqU, hU, hmass,
    ENNReal.ofReal_sum_of_nonneg (fun order _ =>
      (orderMass_pos rates order hpos).le)]
  apply Finset.sum_congr rfl
  intro order horder
  exact finiteIndependentExp_strictClockChamber_permutation rates hpos order
    (hSperm order horder)

/-- The genuine real-clock greedy law equals the discrete first-choice
recursion of S018 whenever the neighbour map is symmetric. -/
theorem finiteIndependentExp_realClockGreedyOutput_eq_finiteRaceLaw
    [Fintype α] [DecidableEq α]
    (rates : α → ℝ) (hpos : ∀ i, 0 < rates i)
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y)
    (target : Finset α) :
    finiteIndependentExp rates
        {ω : α → ℝ | realClockGreedyOutput neighbours ω = target} =
      ENNReal.ofReal
        (finiteRaceLaw rates neighbours (Fintype.card α) Finset.univ target) := by
  rw [finiteIndependentExp_realClockGreedyOutput_eq_priorityOutputMass
    rates hpos neighbours target,
    priorityOutputMass_eq_finiteRaceLaw rates hpos neighbours hSymm,
    Finset.card_univ]

/-- Independence of a vertex set for a neighbour map. -/
def IsIndependentSet (neighbours : α → Finset α) (I : Finset α) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, v ∉ neighbours u

/-- Maximal independent sets: independent, and every outside vertex is
adjacent to (a neighbour of) some member. -/
def IsMaximalIndependentSet (neighbours : α → Finset α) (I : Finset α) : Prop :=
  IsIndependentSet neighbours I ∧ ∀ v, v ∉ I → ∃ u ∈ I, v ∈ neighbours u

/-- The finite family of maximal independent sets. -/
noncomputable def maximalIndependentSets [Fintype α] (neighbours : α → Finset α) :
    Finset (Finset α) := by
  classical
  exact (Finset.univ : Finset (Finset α)).filter
    (IsMaximalIndependentSet neighbours)

/-- The charter's EGU property with *genuine* independent exponential
clocks and strictly positive real rates. -/
def RealClockEGU [Fintype α] [DecidableEq α] (neighbours : α → Finset α) : Prop :=
  ∃ rates : α → ℝ, (∀ v, 0 < rates v) ∧
    ∀ I ∈ maximalIndependentSets neighbours,
      finiteIndependentExp rates
          {ω : α → ℝ | realClockGreedyOutput neighbours ω = I} =
        ENNReal.ofReal (1 / ((maximalIndependentSets neighbours).card : ℝ))

/-- The same property for the discrete first-choice recursion. -/
def FirstChoiceEGU [Fintype α] [DecidableEq α] (neighbours : α → Finset α) : Prop :=
  ∃ rates : α → ℝ, (∀ v, 0 < rates v) ∧
    ∀ I ∈ maximalIndependentSets neighbours,
      finiteRaceLaw rates neighbours (Fintype.card α) Finset.univ I =
        1 / ((maximalIndependentSets neighbours).card : ℝ)

/-- **Bridge theorem.** For symmetric neighbour maps, EGU defined by
genuine real exponential clocks is equivalent to EGU defined by the
discrete first-choice recursion used throughout the project. -/
theorem realClockEGU_iff_firstChoiceEGU [Fintype α] [DecidableEq α]
    (neighbours : α → Finset α)
    (hSymm : ∀ x y, y ∈ neighbours x → x ∈ neighbours y) :
    RealClockEGU neighbours ↔ FirstChoiceEGU neighbours := by
  have hkey : ∀ rates : α → ℝ, (∀ v, 0 < rates v) → ∀ I : Finset α,
      (finiteIndependentExp rates
          {ω : α → ℝ | realClockGreedyOutput neighbours ω = I} =
        ENNReal.ofReal (1 / ((maximalIndependentSets neighbours).card : ℝ))) ↔
      (finiteRaceLaw rates neighbours (Fintype.card α) Finset.univ I =
        1 / ((maximalIndependentSets neighbours).card : ℝ)) := by
    intro rates hpos I
    rw [finiteIndependentExp_realClockGreedyOutput_eq_finiteRaceLaw
      rates hpos neighbours hSymm I]
    have hnonneg :
        0 ≤ finiteRaceLaw rates neighbours (Fintype.card α) Finset.univ I := by
      rw [← Finset.card_univ,
        ← priorityOutputMass_eq_finiteRaceLaw rates hpos neighbours hSymm]
      exact priorityOutputMass_nonneg rates hpos neighbours _ _
    have hc : 0 ≤ 1 / ((maximalIndependentSets neighbours).card : ℝ) := by
      positivity
    exact ENNReal.ofReal_eq_ofReal_iff hnonneg hc
  constructor
  · rintro ⟨rates, hpos, h⟩
    exact ⟨rates, hpos, fun I hI => (hkey rates hpos I).mp (h I hI)⟩
  · rintro ⟨rates, hpos, h⟩
    exact ⟨rates, hpos, fun I hI => (hkey rates hpos I).mpr (h I hI)⟩

end InverseGreedy
