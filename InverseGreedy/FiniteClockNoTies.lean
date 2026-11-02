import InverseGreedy.ContinuousRaceSwap

/-!
# S022: two selected coordinates of genuine finite exponential products

This is a statement about Mathlib's actual independent real exponential
clock space, not a surrogate weighted-permutation distribution.
-/

open MeasureTheory ProbabilityTheory

namespace InverseGreedy

/-- Any pair of distinct coordinates of the genuine finite exponential
clock product has exactly the prescribed independent two-clock law. -/
theorem finiteIndependentExp_pair_law {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (i j : ι) (hij : i ≠ j) :
    Measure.map (fun ω : ι → ℝ => (ω i, ω j))
      (finiteIndependentExp rates) =
      independentExpPair (rates i) (rates j) := by
  letI : IsProbabilityMeasure (finiteIndependentExp rates) :=
    finiteIndependentExp_probability rates hpos
  have hind : IndepFun (fun ω : ι → ℝ => ω i)
      (fun ω : ι → ℝ => ω j) (finiteIndependentExp rates) :=
    (finiteIndependentExp_coordinates_independent rates hpos).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
  simpa only [finiteIndependentExp_coordinate_law rates hpos i,
    finiteIndependentExp_coordinate_law rates hpos j, independentExpPair] using hmap

/-- Two different clocks in a finite real exponential family cannot tie
except on a null event, for arbitrary positive real rates. -/
theorem finiteIndependentExp_pair_tie_null {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (i j : ι) (hij : i ≠ j) :
    finiteIndependentExp rates {ω : ι → ℝ | ω i = ω j} = 0 := by
  let F : (ι → ℝ) → ℝ × ℝ := fun ω => (ω i, ω j)
  have hF : Measurable F :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hDiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  calc
    finiteIndependentExp rates {ω : ι → ℝ | ω i = ω j} =
        (Measure.map F (finiteIndependentExp rates))
          {p : ℝ × ℝ | p.1 = p.2} := by
      rw [Measure.map_apply hF hDiag]
      rfl
    _ = independentExpPair (rates i) (rates j)
          {p : ℝ × ℝ | p.1 = p.2} := by
      rw [finiteIndependentExp_pair_law rates hpos i j hij]
    _ = 0 := independentExpPair_no_ties (rates i) (rates j)
        (hpos i) (hpos j)

/-- The union of all distinct-coordinate clock ties has zero probability,
including empty and singleton index types. -/
theorem finiteIndependentExp_any_tie_null {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i) :
    finiteIndependentExp rates
      {ω : ι → ℝ | ∃ i j, i ≠ j ∧ ω i = ω j} = 0 := by
  have hset :
      {ω : ι → ℝ | ∃ i j, i ≠ j ∧ ω i = ω j} =
        ⋃ i, ⋃ j, {ω : ι → ℝ | i ≠ j ∧ ω i = ω j} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using
      (finiteIndependentExp_pair_tie_null rates hpos i j hij)

/-- Genuine finite exponential clocks are pairwise distinct almost surely.
No assumption of two or more vertices is required. -/
theorem finiteIndependentExp_pairwise_distinct_probability_one
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i) :
    finiteIndependentExp rates
      {ω : ι → ℝ | ∀ i j, i ≠ j → ω i ≠ ω j} = 1 := by
  letI : IsProbabilityMeasure (finiteIndependentExp rates) :=
    finiteIndependentExp_probability rates hpos
  let A : Set (ι → ℝ) :=
    {ω | ∀ i j, i ≠ j → ω i ≠ ω j}
  have hA : MeasurableSet A :=
    finiteIndependentExp_pairwise_distinct_measurable
  have hcompl : Aᶜ =
      {ω : ι → ℝ | ∃ i j, i ≠ j ∧ ω i = ω j} := by
    ext ω
    simp [A]
  have hnull : finiteIndependentExp rates Aᶜ = 0 := by
    rw [hcompl]
    exact finiteIndependentExp_any_tie_null rates hpos
  have hsum := measure_add_measure_compl hA
  rw [hnull] at hsum
  simpa [A] using hsum

end InverseGreedy
