import InverseGreedy.ClockBins
import InverseGreedy.FiniteClockPairOrder

/-!
# S032: genuine joint ceiling-bin law and exact two-list chambers

The full finite family of positive-rate real exponential clocks has an
explicit *joint*, rather than merely pairwise, geometric-bin probability.
This uses Mathlib's actual product measure on real clocks and
`Measure.pi_pi`. It is an essential ingredient for a future finite
strict-bin chamber calculation, but it does NOT evaluate arbitrary
strict real-clock permutation chambers.

The two-item strict real chamber is exactly the existing genuine
pair-comparison event. Repeated entries make any strict chamber empty.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- Each specified simultaneous ceiling-bin assignment has exactly the
product of its genuine one-clock geometric probabilities, for every finite
index type, including the empty type. No discrete ordering law is used. -/
theorem finiteIndependentExp_all_clockCeilBin_joint
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (bins : ι → ℕ) :
    finiteIndependentExp rates
        {ω : ι → ℝ | ∀ i, clockCeilBin δ (ω i) = bins i + 1} =
      ∏ i : ι, ENNReal.ofReal
        ((1 - Real.exp (-(rates i * δ))) *
          (Real.exp (-(rates i * δ))) ^ (bins i)) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (rates i)) :=
    fun i => isProbabilityMeasure_expMeasure (hpos i)
  let cells : ι → Set ℝ :=
    fun i => {t : ℝ | clockCeilBin δ t = bins i + 1}
  have hevent :
      {ω : ι → ℝ | ∀ i, clockCeilBin δ (ω i) = bins i + 1} =
        Set.univ.pi cells := by
    ext ω
    simp [cells, Set.mem_pi]
  calc
    finiteIndependentExp rates
        {ω : ι → ℝ | ∀ i, clockCeilBin δ (ω i) = bins i + 1} =
        (Measure.pi (fun i => expMeasure (rates i))) (Set.univ.pi cells) := by
          rw [hevent]
          rfl
    _ = ∏ i : ι, (expMeasure (rates i)) (cells i) :=
      Measure.pi_pi (fun i => expMeasure (rates i)) cells
    _ = ∏ i : ι, ENNReal.ofReal
        ((1 - Real.exp (-(rates i * δ))) *
          (Real.exp (-(rates i * δ))) ^ (bins i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact expMeasure_clockCeilBin_succ (rates i) δ (hpos i) hδ (bins i)

/-- A two-item strict clock chamber imposes exactly one inequality. -/
theorem strictClockChamber_pair {ι : Type*} (i j : ι) :
    strictClockChamber [i, j] = {ω : ι → ℝ | ω i < ω j} := by
  ext ω
  change (∀ a b : Fin 2, a < b →
    ω ([i, j][a]) < ω ([i, j][b])) ↔ ω i < ω j
  constructor
  · intro h
    simpa using h ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  · intro hij a b hab
    fin_cases a <;> fin_cases b <;> simp_all

/-- The genuine measured probability of a two-item chamber is the
unequal-rate exponential race ratio, independently of other clocks. -/
theorem finiteIndependentExp_pair_chamber_mass
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (i j : ι) (hij : i ≠ j) :
    finiteIndependentExp rates (strictClockChamber [i, j]) =
      ENNReal.ofReal (rates i / (rates i + rates j)) := by
  rw [strictClockChamber_pair]
  exact finiteIndependentExp_pair_lt_rateRatio rates hpos i j hij

/-- Any strict proposed order which reuses an index at two different
positions defines the empty real-clock event, regardless of rates. -/
theorem strictClockChamber_eq_empty_of_repeated
    {ι : Type*} (order : List ι)
    (a b : Fin order.length) (hab : a < b)
    (heq : order[a] = order[b]) :
    strictClockChamber order = ∅ := by
  ext ω
  constructor
  · intro hω
    have hlt := hω a b hab
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)
  · simp

/-- Accordingly, any product probability of a repeated-index strict
chamber is zero, even when its rates are not positive. -/
theorem finiteIndependentExp_repeated_chamber_zero
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (order : List ι) (a b : Fin order.length) (hab : a < b)
    (heq : order[a] = order[b]) :
    finiteIndependentExp rates (strictClockChamber order) = 0 := by
  rw [strictClockChamber_eq_empty_of_repeated order a b hab heq]
  simp

end InverseGreedy
