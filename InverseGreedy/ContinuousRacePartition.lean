import InverseGreedy.IndependentExpPair

/-!
# S020 genuine continuous two-clock race
The joint law here is the Mathlib exponential product measure.
-/
open MeasureTheory ProbabilityTheory
namespace InverseGreedy

theorem independentExpPair_strict_winners_sum (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} +
      independentExpPair r s {p : ℝ × ℝ | p.2 < p.1} = 1 := by
  let μ : Measure (ℝ × ℝ) := independentExpPair r s
  letI : IsProbabilityMeasure μ := independentExpPair_isProbability r s hr hs
  let A : Set (ℝ × ℝ) := {p | p.1 < p.2}
  let B : Set (ℝ × ℝ) := {p | p.2 < p.1}
  let D : Set (ℝ × ℝ) := {p | p.1 = p.2}
  have hB : MeasurableSet B :=
    (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hD : MeasurableSet D :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro p hA hB
    change p.1 < p.2 at hA
    change p.2 < p.1 at hB
    exact (lt_asymm hA hB)
  have hABD : Disjoint (A ∪ B) D := by
    apply Set.disjoint_left.mpr
    intro p hAB hD
    rcases hAB with hA | hB
    · exact (ne_of_lt hA) hD
    · exact (ne_of_gt hB) hD
  have hcover : (A ∪ B) ∪ D = Set.univ := by
    ext p
    simp only [A, B, D, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hnull : μ D = 0 := independentExpPair_no_ties r s hr hs
  change μ A + μ B = 1
  calc
    μ A + μ B = μ (A ∪ B) := (measure_union hAB hB).symm
    _ = μ ((A ∪ B) ∪ D) := by rw [measure_union hABD hD, hnull, add_zero]
    _ = 1 := by rw [hcover, measure_univ]

theorem independentExpPair_equal_rates_swap (r : ℝ) (hr : 0 < r) :
    Measure.map Prod.swap (independentExpPair r r) =
      independentExpPair r r := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  unfold independentExpPair
  exact Measure.prod_swap

theorem independentExpPair_equal_rates_symmetry (r : ℝ) (hr : 0 < r) :
    independentExpPair r r {p : ℝ × ℝ | p.1 < p.2} =
      independentExpPair r r {p : ℝ × ℝ | p.2 < p.1} := by
  let μ : Measure (ℝ × ℝ) := independentExpPair r r
  let A : Set (ℝ × ℝ) := {p | p.1 < p.2}
  let B : Set (ℝ × ℝ) := {p | p.2 < p.1}
  have hA : MeasurableSet A :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hswap : Measure.map Prod.swap μ = μ :=
    independentExpPair_equal_rates_swap r hr
  change μ A = μ B
  calc
    μ A = (Measure.map Prod.swap μ) A := by rw [hswap]
    _ = μ (Prod.swap ⁻¹' A) := Measure.map_apply measurable_swap hA
    _ = μ B := by rfl

theorem independentExpPair_equal_rates_balanced (r : ℝ) (hr : 0 < r) :
    independentExpPair r r {p : ℝ × ℝ | p.1 < p.2} +
      independentExpPair r r {p : ℝ × ℝ | p.1 < p.2} = 1 := by
  have hsum := independentExpPair_strict_winners_sum r r hr hr
  rw [← independentExpPair_equal_rates_symmetry r hr] at hsum
  exact hsum

end InverseGreedy
