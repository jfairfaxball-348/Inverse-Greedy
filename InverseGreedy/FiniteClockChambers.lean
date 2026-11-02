import InverseGreedy.FiniteClockNoTies

/-!
# S023: measurable strict sorting chambers of genuine finite real clocks

A strict chamber records all comparisons between positions of a proposed
finite list. This is a *set in the real product sample space*, rather than
a discrete priority law. The list need not be a permutation for the
measurability result; later chamber probability theorems must additionally
require that it enumerates the complete finite index type.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- The event that the real clocks appear in the exact strict order
specified by the positions of a list. -/
def strictClockChamber {ι : Type*} (order : List ι) : Set (ι → ℝ) :=
  {ω | ∀ a b : Fin order.length, a < b →
    ω (order[a]) < ω (order[b])}

/-- Every strict sorting chamber is measurable in the actual finite
real-clock sample space. This holds without assuming any probability law,
rate positivity, pairwise distinctness, or completeness of the list. -/
theorem strictClockChamber_measurable {ι : Type*} [Fintype ι]
    (order : List ι) : MeasurableSet (strictClockChamber order) := by
  have hset :
      strictClockChamber order =
        ⋂ a : Fin order.length, ⋂ b : Fin order.length,
          {ω : ι → ℝ | a < b → ω (order[a]) < ω (order[b])} := by
    ext ω
    simp only [strictClockChamber, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  by_cases hab : a < b
  · simpa [hab] using
      (finiteIndependentExp_lt_measurable (order[a]) (order[b]))
  · simp [hab]

end InverseGreedy
