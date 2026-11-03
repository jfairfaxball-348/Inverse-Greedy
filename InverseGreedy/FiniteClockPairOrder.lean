import InverseGreedy.ContinuousRaceLimit
import InverseGreedy.FiniteClockChambers

/-!
# S031: genuine finite-clock pair-order marginals

The actual finite independent exponential product has exactly the
rate-proportional comparison probability for *every distinct pair*
of coordinates. This transports S030's measured two-clock theorem
through S022's genuine finite-product pair law. These are not
postulated weights of a discrete permutation space.

For a longer strictClockChamber, every required pair comparison
also gives a certified upper bound on that chamber's mass.
Neither result claims the still-open full finite chamber formula.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- The true finite product of exponential clocks orders any distinct
pair with the expected unequal-rate probability. The ambient family can
have arbitrarily many other vertices. -/
theorem finiteIndependentExp_pair_lt_rateRatio
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (i j : ι) (hij : i ≠ j) :
    finiteIndependentExp rates {ω : ι → ℝ | ω i < ω j} =
      ENNReal.ofReal (rates i / (rates i + rates j)) := by
  let F : (ι → ℝ) → ℝ × ℝ := fun ω => (ω i, ω j)
  have hF : Measurable F :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hlt : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet
  calc
    finiteIndependentExp rates {ω : ι → ℝ | ω i < ω j} =
        (Measure.map F (finiteIndependentExp rates))
          {p : ℝ × ℝ | p.1 < p.2} := by
      rw [Measure.map_apply hF hlt]
      rfl
    _ = independentExpPair (rates i) (rates j)
          {p : ℝ × ℝ | p.1 < p.2} := by
      rw [finiteIndependentExp_pair_law rates hpos i j hij]
    _ = ENNReal.ofReal (rates i / (rates i + rates j)) :=
      independentExpPair_realWinner_rateRatio (rates i) (rates j)
        (hpos i) (hpos j)

/-- A strict real-clock chamber is a subset of each of its required
coordinate comparison events. No permutation completeness is needed. -/
theorem strictClockChamber_subset_pair
    {ι : Type*} (order : List ι)
    (a b : Fin order.length) (hab : a < b) :
    strictClockChamber order ⊆
      {ω : ι → ℝ | ω (order[a]) < ω (order[b])} := by
  intro ω hω
  exact hω a b hab

/-- Every actual finite exponential strict chamber is bounded by each
rate-proportional comparison it requires. The distinct-index hypothesis
is explicit, so this also works for non-permutation lists when useful. -/
theorem finiteIndependentExp_chamber_le_pair_rateRatio
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (order : List ι) (a b : Fin order.length)
    (hab : a < b) (hneq : order[a] ≠ order[b]) :
    finiteIndependentExp rates (strictClockChamber order) ≤
      ENNReal.ofReal
        (rates (order[a]) / (rates (order[a]) + rates (order[b]))) := by
  calc
    finiteIndependentExp rates (strictClockChamber order) ≤
        finiteIndependentExp rates
          {ω : ι → ℝ | ω (order[a]) < ω (order[b])} :=
      measure_mono (strictClockChamber_subset_pair order a b hab)
    _ = ENNReal.ofReal
          (rates (order[a]) / (rates (order[a]) + rates (order[b]))) :=
      finiteIndependentExp_pair_lt_rateRatio rates hpos
        (order[a]) (order[b]) hneq


/-- An empty proposed strict order places no comparisons on any sample. -/
theorem strictClockChamber_nil (ι : Type*) :
    strictClockChamber ([] : List ι) = Set.univ := by
  ext ω
  constructor
  · intro _
    trivial
  · intro _ a
    exact Fin.elim0 a

/-- A singleton proposed strict order places no comparisons either. -/
theorem strictClockChamber_singleton {ι : Type*} (i : ι) :
    strictClockChamber [i] = Set.univ := by
  ext ω
  constructor
  · intro _
    trivial
  · intro _ a b hab
    omega

/-- Genuine probability-one boundary for the empty chamber, including
empty index types with the unique empty clock assignment. -/
theorem finiteIndependentExp_nil_chamber_mass
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i) :
    finiteIndependentExp rates (strictClockChamber ([] : List ι)) = 1 := by
  letI : IsProbabilityMeasure (finiteIndependentExp rates) :=
    finiteIndependentExp_probability rates hpos
  rw [strictClockChamber_nil]
  simp

/-- Genuine probability-one boundary for a singleton proposed order.
Completeness of the order is not assumed for this vacuous event. -/
theorem finiteIndependentExp_singleton_chamber_mass
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i) (i : ι) :
    finiteIndependentExp rates (strictClockChamber [i]) = 1 := by
  letI : IsProbabilityMeasure (finiteIndependentExp rates) :=
    finiteIndependentExp_probability rates hpos
  rw [strictClockChamber_singleton]
  simp

end InverseGreedy
