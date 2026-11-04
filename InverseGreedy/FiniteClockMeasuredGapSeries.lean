import InverseGreedy.FiniteClockCompleteOrder

/-!
# S038: reindex S035's *genuine measured* chamber series by finite gaps

This starts with the actual finite independent exponential probability
measure proved in S035, not with an assumed discrete Plackett--Luce law.
Completeness of the list is witnessed by `CompleteClockOrder`.

Only the countable change of variables is proved here: evaluation of the
multiple geometric series, the zero-width limit and measured sorting law
remain separate obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical
namespace InverseGreedy

/-- The S032 joint geometric positive-bin mass, as a standalone
expression in the original clock-coordinate assignment. -/
noncomputable def finiteExpPositiveBinMonomial
    {ι : Type*} [Fintype ι] (rates : ι → ℝ) (δ : ℝ)
    (bins : ι → ℕ) : ENNReal :=
  ∏ i : ι, ENNReal.ofReal
    ((1 - Real.exp (-(rates i * δ))) *
      (Real.exp (-(rates i * δ))) ^ (bins i))

/-- Genuine measured positive-bin chamber probability, reindexed by
S037 gap vectors through an explicit complete vertex enumeration.
This equality includes `Fin 0` and `Fin 1` and still uses the real
independent exponential probability measure on its left. -/
theorem finiteIndependentExp_strictBin_gap_series
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι)
    (hcomplete : CompleteClockOrder order) :
    finiteIndependentExp rates (strictClockBinChamber δ order) =
      ∑' gaps : Fin order.length → ℕ,
        finiteExpPositiveBinMonomial rates δ
          (((completeClockOrderGapEquiv hcomplete).symm gaps).val) := by
  classical
  rw [finiteIndependentExp_strictBin_series rates hpos δ hδ order]
  change
    (∑' bins : ι → ℕ,
      if strictBinAssignment order bins then
        finiteExpPositiveBinMonomial rates δ bins else 0) = _
  calc
    (∑' bins : ι → ℕ,
      if strictBinAssignment order bins then
        finiteExpPositiveBinMonomial rates δ bins else 0) =
        ∑' bins : {bins : ι → ℕ // strictBinAssignment order bins},
          finiteExpPositiveBinMonomial rates δ bins.val := by
            convert (tsum_subtype
              {bins : ι → ℕ | strictBinAssignment order bins}
              (finiteExpPositiveBinMonomial rates δ)).symm using 1 <;> rfl
    _ = ∑' gaps : Fin order.length → ℕ,
          finiteExpPositiveBinMonomial rates δ
            (((completeClockOrderGapEquiv hcomplete).symm gaps).val) :=
      (Equiv.tsum_eq
        (completeClockOrderGapEquiv hcomplete).symm
        (fun bins : {bins : ι → ℕ // strictBinAssignment order bins} =>
          finiteExpPositiveBinMonomial rates δ bins.val)).symm

end InverseGreedy
