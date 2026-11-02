import InverseGreedy.IndependentExpPair
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# S020: genuine finite independent exponential-clock probability space
Uses Mathlib's finite product of the actual exponential measures.
No discrete priority-order law is assumed.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

variable {ι : Type*} [Fintype ι]

noncomputable def finiteIndependentExp (rates : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun i => expMeasure (rates i))

/-- Positivity of every rate makes the finite product a probability measure,
including an empty index type. -/
theorem finiteIndependentExp_probability (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) :
    IsProbabilityMeasure (finiteIndependentExp rates) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (rates i)) :=
    fun i => isProbabilityMeasure_expMeasure (hpos i)
  unfold finiteIndependentExp
  infer_instance

/-- Every arrival-time coordinate is measurable in the genuine product space. -/
theorem finiteIndependentExp_coordinate_measurable (i : ι) :
    Measurable (Function.eval i : (ι → ℝ) → ℝ) :=
  measurable_pi_apply i

/-- The marginal arrival time at i is the actual Exp(rate i) law. -/
theorem finiteIndependentExp_coordinate_law (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) (i : ι) :
    Measure.map (Function.eval i) (finiteIndependentExp rates) =
      expMeasure (rates i) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (rates j)) :=
    fun j => isProbabilityMeasure_expMeasure (hpos j)
  exact (measurePreserving_eval (fun j => expMeasure (rates j)) i).map_eq

/-- The event that any specified clock equals any prescribed real time
has probability zero (one-point coordinate cylinder). -/
theorem finiteIndependentExp_fixed_time_null (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) (i : ι) (t : ℝ) :
    finiteIndependentExp rates {ω : ι → ℝ | ω i = t} = 0 := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (rates j)) :=
    fun j => isProbabilityMeasure_expMeasure (hpos j)
  change (Measure.pi (fun j => expMeasure (rates j)))
    ((Function.eval i) ⁻¹' ({t} : Set ℝ)) = 0
  exact Measure.pi_eval_preimage_null
    (fun j => expMeasure (rates j)) (expMeasure_point_null (rates i) t)

end InverseGreedy
