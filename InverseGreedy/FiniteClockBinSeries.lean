import InverseGreedy.FiniteClockJointBins
import InverseGreedy.FiniteClockBinChambers
import InverseGreedy.FiniteClockBinExceptions

/-!
# S035: countable positive-bin decomposition of genuine finite clock chambers

This module does not assume a discrete priority law. The source of
probability is the *actual* finite independent exponential product
measure. Each positive one-based ceiling-bin cylinder has the S032
geometric probability. The union is pairwise disjoint because different
bin assignments force different values of at least one actual clock bin.

The zero-bin exceptional event is null by S033, so this gives the
strict-bin chamber's genuine, countably additive series. Evaluating
that multiple geometric series and taking the zero-width limit are
separate obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical
namespace InverseGreedy

/-- A genuine simultaneous positive, one-based bin assignment. -/
def positiveClockBinCylinder {ι : Type*} (δ : ℝ) (bins : ι → ℕ) :
    Set (ι → ℝ) :=
  {ω | ∀ i, clockCeilBin δ (ω i) = bins i + 1}

/-- The bin indices increase along the proposed order. This definition
is meaningful even when that list is not a complete permutation. -/
def strictBinAssignment {ι : Type*} (order : List ι) (bins : ι → ℕ) :
    Prop :=
  ∀ a b : Fin order.length, a < b →
    bins (order[a]) < bins (order[b])

/-- Filter the positive-bin cylinders to those supporting the required
strict ordering. -/
noncomputable def validBinCylinder {ι : Type*} (δ : ℝ) (order : List ι)
    (bins : ι → ℕ) : Set (ι → ℝ) :=
  if strictBinAssignment order bins then
    positiveClockBinCylinder δ bins
  else ∅

/-- The positive part of any strict-bin chamber is *exactly* a union
of all its admissible positive-bin cylinders. This is set equality,
not an almost-sure shortcut; the zero bin is excluded explicitly. -/
theorem strictBinChamber_positive_eq_iUnion
    {ι : Type*} [Fintype ι] (δ : ℝ) (order : List ι) :
    strictClockBinChamber δ order ∩
      {ω : ι → ℝ | ∀ i, clockCeilBin δ (ω i) ≠ 0} =
      ⋃ bins : ι → ℕ, validBinCylinder δ order bins := by
  classical
  ext ω
  constructor
  · rintro ⟨hstrict, hpos⟩
    let bins : ι → ℕ := fun i => clockCeilBin δ (ω i) - 1
    have hbin (i : ι) :
        clockCeilBin δ (ω i) = bins i + 1 := by
      dsimp [bins]
      have hi := hpos i
      omega
    have horder : strictBinAssignment order bins := by
      intro a b hab
      have hlt := hstrict a b hab
      have ha := hbin (order[a])
      have hb := hbin (order[b])
      omega
    apply Set.mem_iUnion.mpr
    refine ⟨bins, ?_⟩
    simpa [validBinCylinder, horder, positiveClockBinCylinder] using hbin
  · intro hω
    obtain ⟨bins, hmem⟩ := Set.mem_iUnion.mp hω
    have horder : strictBinAssignment order bins := by
      by_contra hn
      have hfalse : ω ∈ (∅ : Set (ι → ℝ)) := by
        simpa [validBinCylinder, hn] using hmem
      exact (by simpa using hfalse)
    have hbin : ∀ i, clockCeilBin δ (ω i) = bins i + 1 := by
      simpa [validBinCylinder, horder, positiveClockBinCylinder] using hmem
    constructor
    · intro a b hab
      change clockCeilBin δ (ω (order[a])) <
        clockCeilBin δ (ω (order[b]))
      rw [hbin (order[a]), hbin (order[b])]
      exact Nat.add_lt_add_right (horder a b hab) 1
    · intro i
      rw [hbin i]
      omega

/-- Every actual positive-bin cylinder is a measurable event. -/
theorem positiveClockBinCylinder_measurable
    {ι : Type*} [Fintype ι] (δ : ℝ) (bins : ι → ℕ) :
    MeasurableSet (positiveClockBinCylinder δ bins) := by
  have hset :
      positiveClockBinCylinder δ bins =
        ⋂ i, {ω : ι → ℝ | clockCeilBin δ (ω i) = bins i + 1} := by
    ext ω
    simp [positiveClockBinCylinder]
  rw [hset]
  apply MeasurableSet.iInter
  intro i
  change MeasurableSet
    ((fun ω : ι → ℝ => clockCeilBin δ (ω i)) ⁻¹' {bins i + 1})
  exact (finiteIndependentExp_clockCeilBin_measurable δ i)
    (measurableSet_singleton (bins i + 1))

/-- Distinct bin assignments are mutually exclusive on actual clocks. -/
theorem positiveClockBinCylinder_disjoint
    {ι : Type*} (δ : ℝ) (bins other : ι → ℕ) (hne : bins ≠ other) :
    Disjoint (positiveClockBinCylinder δ bins)
      (positiveClockBinCylinder δ other) := by
  apply Set.disjoint_left.mpr
  intro ω hfirst hsecond
  have heq : bins = other := by
    funext i
    have hi := hfirst i
    have hj := hsecond i
    omega
  exact hne heq

/-- Admissible cylinders are pairwise disjoint, including for empty
and singleton index types. -/
theorem validBinCylinder_pairwise_disjoint
    {ι : Type*} [Fintype ι] (δ : ℝ) (order : List ι) :
    Pairwise (fun a b : ι → ℕ =>
      Disjoint (validBinCylinder δ order a) (validBinCylinder δ order b)) := by
  classical
  intro bins other hne
  apply Set.disjoint_left.mpr
  intro ω hfirst hsecond
  have horder : strictBinAssignment order bins := by
    by_contra hn
    have : ω ∈ (∅ : Set (ι → ℝ)) := by
      simpa [validBinCylinder, hn] using hfirst
    exact (by simpa using this)
  have hother : strictBinAssignment order other := by
    by_contra hn
    have : ω ∈ (∅ : Set (ι → ℝ)) := by
      simpa [validBinCylinder, hn] using hsecond
    exact Set.not_mem_empty ω this
  have h1 : ω ∈ positiveClockBinCylinder δ bins := by
    simpa [validBinCylinder, horder] using hfirst
  have h2 : ω ∈ positiveClockBinCylinder δ other := by
    simpa [validBinCylinder, hother] using hsecond
  exact (Set.disjoint_left.mp
    (positiveClockBinCylinder_disjoint δ bins other hne)) h1 h2

/-- Each filtered cylinder is measurable under the true continuous
clock probability model. -/
theorem validBinCylinder_measurable
    {ι : Type*} [Fintype ι] (δ : ℝ) (order : List ι) (bins : ι → ℕ) :
    MeasurableSet (validBinCylinder δ order bins) := by
  classical
  by_cases horder : strictBinAssignment order bins
  · simpa [validBinCylinder, horder] using
      positiveClockBinCylinder_measurable δ bins
  · simp [validBinCylinder, horder]

/-- Exact *countable* positive-bin chamber formula for the genuine
finite product of independent exponential clocks. The right side is
not postulated as a stochastic model; it is derived from disjoint
measurable events and S032's true joint-cylinder probabilities.

The finite-dimensional geometric gap series on the right still needs
evaluation to a finite product in a later theorem. -/
theorem finiteIndependentExp_strictBin_positive_series
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι) :
    finiteIndependentExp rates
      (strictClockBinChamber δ order ∩
        {ω : ι → ℝ | ∀ i, clockCeilBin δ (ω i) ≠ 0}) =
      ∑' bins : ι → ℕ,
        if strictBinAssignment order bins then
          ∏ i : ι, ENNReal.ofReal
            ((1 - Real.exp (-(rates i * δ))) *
              (Real.exp (-(rates i * δ))) ^ (bins i))
        else 0 := by
  classical
  rw [strictBinChamber_positive_eq_iUnion]
  rw [measure_iUnion (validBinCylinder_pairwise_disjoint δ order)
    (validBinCylinder_measurable δ order)]
  apply tsum_congr
  intro bins
  by_cases horder : strictBinAssignment order bins
  · simpa [validBinCylinder, horder, positiveClockBinCylinder] using
      (finiteIndependentExp_all_clockCeilBin_joint rates hpos δ hδ bins)
  · simp [validBinCylinder, horder]

/-- The exceptional zero-bin event has genuine probability zero.
Consequently the *full* strict-bin chamber has exactly the positive-bin
series above, for arbitrary finite index sets, including the empty type. -/
theorem finiteIndependentExp_strictBin_series
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι) :
    finiteIndependentExp rates (strictClockBinChamber δ order) =
      ∑' bins : ι → ℕ,
        if strictBinAssignment order bins then
          ∏ i : ι, ENNReal.ofReal
            ((1 - Real.exp (-(rates i * δ))) *
              (Real.exp (-(rates i * δ))) ^ (bins i))
        else 0 := by
  let C := strictClockBinChamber δ order
  let P : Set (ι → ℝ) :=
    {ω | ∀ i, clockCeilBin δ (ω i) ≠ 0}
  let Z : Set (ι → ℝ) :=
    {ω | ∃ i, clockCeilBin δ (ω i) = 0}
  have hcover : C ⊆ (C ∩ P) ∪ Z := by
    intro ω hC
    by_cases hp : ∀ i, clockCeilBin δ (ω i) ≠ 0
    · exact Or.inl ⟨hC, hp⟩
    · right
      push Not at hp
      exact hp
  have hzero : finiteIndependentExp rates Z = 0 :=
    finiteIndependentExp_any_zeroBin_null rates hpos δ hδ
  have hmeasure :
      finiteIndependentExp rates C =
        finiteIndependentExp rates (C ∩ P) := by
    apply le_antisymm
    · calc
        finiteIndependentExp rates C ≤
            finiteIndependentExp rates ((C ∩ P) ∪ Z) :=
          measure_mono hcover
        _ ≤ finiteIndependentExp rates (C ∩ P) +
              finiteIndependentExp rates Z := measure_union_le _ _
        _ = finiteIndependentExp rates (C ∩ P) := by simp [hzero]
    · exact measure_mono Set.inter_subset_left
  change finiteIndependentExp rates C = _
  rw [hmeasure]
  exact finiteIndependentExp_strictBin_positive_series rates hpos δ hδ order

end InverseGreedy
