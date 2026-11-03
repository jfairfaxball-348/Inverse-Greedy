import InverseGreedy.FiniteClockJointBins
import InverseGreedy.BinnedCollisionBound

/-!
# S033: the genuine finite-clock strict-bin / real-chamber sandwich

The events below live on the actual real-clock sample space. They do
not postulate the Plackett-Luce permutation distribution. The ordered
bin event is a subset of the ordered real-clock chamber, and the
difference lies within a finite list of same-bin collisions.

This is only the deterministic and measure-theoretic *sandwich*,
not the geometric multiple-series evaluation or the zero-width limit.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- Strict order of the actual ceiling bins of a proposed list. -/
def strictClockBinChamber {ι : Type*} (δ : ℝ) (order : List ι) :
    Set (ι → ℝ) :=
  {ω | ∀ a b : Fin order.length, a < b →
    clockCeilBin δ (ω (order[a])) <
      clockCeilBin δ (ω (order[b]))}

/-- Any two positions of a proposed order collide in the same real-clock bin. -/
def clockBinCollisionOnList {ι : Type*} (δ : ℝ) (order : List ι) :
    Set (ι → ℝ) :=
  {ω | ∃ a b : Fin order.length, a < b ∧
    clockCeilBin δ (ω (order[a])) =
      clockCeilBin δ (ω (order[b]))}

/-- Strictly increasing actual bins force strictly increasing actual clocks.
No positive-rate assumption and no completeness assumption are required. -/
theorem strictClockBinChamber_subset_strictClockChamber
    {ι : Type*} (δ : ℝ) (hδ : 0 < δ) (order : List ι) :
    strictClockBinChamber δ order ⊆ strictClockChamber order := by
  intro ω hω a b hab
  have hbins : clockCeilBin δ (ω (order[a])) <
      clockCeilBin δ (ω (order[b])) := hω a b hab
  by_contra hnot
  have hreverse : ω (order[b]) ≤ ω (order[a]) :=
    le_of_not_gt hnot
  have hmono := clockCeilBin_mono δ hδ hreverse
  omega

/-- The only obstruction to matching strict real and strict bin orders
is the collision of two bins in the proposed finite list. -/
theorem strictClockChamber_subset_bin_union_collision
    {ι : Type*} (δ : ℝ) (hδ : 0 < δ) (order : List ι) :
    strictClockChamber order ⊆
      strictClockBinChamber δ order ∪ clockBinCollisionOnList δ order := by
  intro ω hω
  by_cases hb : ω ∈ strictClockBinChamber δ order
  · exact Or.inl hb
  · right
    change ¬ (∀ a b : Fin order.length, a < b →
      clockCeilBin δ (ω (order[a])) <
        clockCeilBin δ (ω (order[b]))) at hb
    push_neg at hb
    obtain ⟨a, b, hab, hnot⟩ := hb
    have hle : clockCeilBin δ (ω (order[a])) ≤
        clockCeilBin δ (ω (order[b])) :=
      clockCeilBin_mono δ hδ (le_of_lt (hω a b hab))
    have heq : clockCeilBin δ (ω (order[a])) =
        clockCeilBin δ (ω (order[b])) :=
      le_antisymm hle (le_of_not_gt hnot)
    exact ⟨a, b, hab, heq⟩

/-- True-measure sandwich; the error term is an actual clock-bin
collision event, not a surrogate discrete permutation law. -/
theorem finiteIndependentExp_strictChamber_bin_sandwich
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι) :
    finiteIndependentExp rates (strictClockBinChamber δ order) ≤
      finiteIndependentExp rates (strictClockChamber order) ∧
    finiteIndependentExp rates (strictClockChamber order) ≤
      finiteIndependentExp rates (strictClockBinChamber δ order) +
        finiteIndependentExp rates (clockBinCollisionOnList δ order) := by
  constructor
  · exact measure_mono
      (strictClockBinChamber_subset_strictClockChamber δ hδ order)
  · calc
      finiteIndependentExp rates (strictClockChamber order) ≤
          finiteIndependentExp rates
            (strictClockBinChamber δ order ∪ clockBinCollisionOnList δ order) :=
        measure_mono (strictClockChamber_subset_bin_union_collision δ hδ order)
      _ ≤ finiteIndependentExp rates (strictClockBinChamber δ order) +
            finiteIndependentExp rates (clockBinCollisionOnList δ order) :=
        measure_union_le _ _

end InverseGreedy
