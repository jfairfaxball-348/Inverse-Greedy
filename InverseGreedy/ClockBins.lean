import InverseGreedy.ExpBinCells
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# S026: a measurable bin random variable for genuine exponential clocks

The integer-valued ceiling bin convention is used intentionally:
  Kδ(t) = ceil(t / δ).
For each k ≥ 0 its strictly positive cell Kδ = k+1 is exactly
  kδ < t ≤ (k+1)δ
without a boundary correction. The extra zero cell Kδ=0 is
t ≤ 0 and is null under a genuine exponential law. Thus Kδ-1 is
a geometric variable almost surely, but this module does not
postulate any discrete distribution.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- One-based right-closed real clock bin. For δ>0, the event
`clockCeilBin δ t = k+1` is exactly the S025 real bin cell. -/
noncomputable def clockCeilBin (δ t : ℝ) : ℕ :=
  Nat.ceil (t / δ)

/-- The actual real-clock bin map is Borel measurable. -/
theorem clockCeilBin_measurable (δ : ℝ) :
    Measurable (clockCeilBin δ) := by
  change Measurable (fun t : ℝ => Nat.ceil (t / δ))
  exact (measurable_id.div_const δ).nat_ceil

/-- Exact half-open cell identification, including k=0 and endpoints. -/
theorem clockCeilBin_preimage_succ (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    {t : ℝ | clockCeilBin δ t = k + 1} =
      Set.Ioc ((k : ℝ) * δ) (((k : ℝ) + 1) * δ) := by
  ext t
  change Nat.ceil (t / δ) = k + 1 ↔
    (k : ℝ) * δ < t ∧ t ≤ ((k : ℝ) + 1) * δ
  rw [Nat.ceil_eq_iff (show k + 1 ≠ 0 by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨(lt_div_iff₀ hδ).mp hlo, (div_le_iff₀ hδ).mp hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨(lt_div_iff₀ hδ).mpr hlo, (div_le_iff₀ hδ).mpr hhi⟩

/-- The special zero bin is precisely the nonpositive half-line. -/
theorem clockCeilBin_preimage_zero (δ : ℝ) (hδ : 0 < δ) :
    {t : ℝ | clockCeilBin δ t = 0} = Set.Iic (0 : ℝ) := by
  ext t
  change Nat.ceil (t / δ) = 0 ↔ t ≤ 0
  rw [Nat.ceil_eq_zero]
  constructor
  · intro ht
    have := (div_le_iff₀ hδ).mp ht
    simpa using this
  · intro ht
    apply (div_le_iff₀ hδ).mpr
    simpa using ht

/-- The zero bin of a genuine positive-rate exponential clock is null. -/
theorem expMeasure_clockCeilBin_zero (rate δ : ℝ)
    (hr : 0 < rate) (hδ : 0 < δ) :
    expMeasure rate {t : ℝ | clockCeilBin δ t = 0} = 0 := by
  rw [clockCeilBin_preimage_zero δ hδ]
  simpa using expMeasure_Iic_nonnegative rate 0 hr (le_refl 0)

/-- Actual exponential bin PMF, indexed one-based to match S025's
right-closed half-open intervals. This is a genuine measurable
random-variable event, not merely a real interval mass. -/
theorem expMeasure_clockCeilBin_succ (rate δ : ℝ)
    (hr : 0 < rate) (hδ : 0 < δ) (k : ℕ) :
    expMeasure rate {t : ℝ | clockCeilBin δ t = k + 1} =
      ENNReal.ofReal
        ((1 - Real.exp (-(rate * δ))) *
          (Real.exp (-(rate * δ))) ^ k) := by
  rw [clockCeilBin_preimage_succ δ hδ k]
  exact expMeasure_geometric_cell rate δ hr hδ k

/-- The ceiling bin of every coordinate of the true finite
independent exponential product is measurable. -/
theorem finiteIndependentExp_clockCeilBin_measurable
    {ι : Type*} [Fintype ι] (δ : ℝ) (i : ι) :
    Measurable (fun ω : ι → ℝ => clockCeilBin δ (ω i)) :=
  (clockCeilBin_measurable δ).comp (measurable_pi_apply i)

/-- S025's genuine finite-coordinate cell law upgraded to an actual
measurable bin-map point mass. -/
theorem finiteIndependentExp_clockCeilBin_succ
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) (i : ι)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    finiteIndependentExp rates
        {ω : ι → ℝ | clockCeilBin δ (ω i) = k + 1} =
      ENNReal.ofReal
        ((1 - Real.exp (-(rates i * δ))) *
          (Real.exp (-(rates i * δ))) ^ k) := by
  rw [show
      {ω : ι → ℝ | clockCeilBin δ (ω i) = k + 1} =
      {ω : ι → ℝ |
        (k : ℝ) * δ < ω i ∧ ω i ≤ ((k : ℝ) + 1) * δ} from by
    ext ω
    exact Set.ext_iff.mp (clockCeilBin_preimage_succ δ hδ k) (ω i)]
  exact finiteIndependentExp_coordinate_geometric_cell
    rates hpos i δ hδ k


/-- Genuine finite-clock bins remain mutually independent because they
are measurable transformations of the actual independent arrival times.
This covers arbitrary finite index sets (including empty/singleton). -/
theorem finiteIndependentExp_clockCeilBins_independent
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) (δ : ℝ) :
    iIndepFun (fun i (ω : ι → ℝ) => clockCeilBin δ (ω i))
      (finiteIndependentExp rates) := by
  have hind := finiteIndependentExp_coordinates_independent rates hpos
  change iIndepFun
    (fun i => (clockCeilBin δ) ∘ (fun ω : ι → ℝ => ω i))
    (finiteIndependentExp rates)
  exact hind.comp (fun _ => clockCeilBin δ)
    (fun _ => clockCeilBin_measurable δ)


/-- The joint law of any two genuine independent exponential ceiling
bins is the product of their geometric masses. Unlike the rational
oracle, this theorem uses the actual Mathlib real-clock product measure. -/
theorem independentExpPair_clockCeilBin_joint
    (r s δ : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hδ : 0 < δ) (k l : ℕ) :
    independentExpPair r s
      {p : ℝ × ℝ |
        clockCeilBin δ p.1 = k + 1 ∧ clockCeilBin δ p.2 = l + 1} =
      ENNReal.ofReal
        ((1 - Real.exp (-(r * δ))) *
          (Real.exp (-(r * δ))) ^ k) *
      ENNReal.ofReal
        ((1 - Real.exp (-(s * δ))) *
          (Real.exp (-(s * δ))) ^ l) := by
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (expMeasure s) :=
    isProbabilityMeasure_expMeasure hs
  change (expMeasure r).prod (expMeasure s)
    ({t : ℝ | clockCeilBin δ t = k + 1} ×ˢ
      {t : ℝ | clockCeilBin δ t = l + 1}) = _
  rw [Measure.prod_prod]
  rw [expMeasure_clockCeilBin_succ r δ hr hδ k,
    expMeasure_clockCeilBin_succ s δ hs hδ l]

/-- The same actual joint bin law for any two distinct coordinates
inside a genuine finite independent exponential product. -/
theorem finiteIndependentExp_clockCeilBin_pair_joint
    {ι : Type*} [Fintype ι] (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) (i j : ι) (hij : i ≠ j)
    (δ : ℝ) (hδ : 0 < δ) (k l : ℕ) :
    finiteIndependentExp rates
      {ω : ι → ℝ |
        clockCeilBin δ (ω i) = k + 1 ∧
          clockCeilBin δ (ω j) = l + 1} =
      ENNReal.ofReal
        ((1 - Real.exp (-(rates i * δ))) *
          (Real.exp (-(rates i * δ))) ^ k) *
      ENNReal.ofReal
        ((1 - Real.exp (-(rates j * δ))) *
          (Real.exp (-(rates j * δ))) ^ l) := by
  let f : (ι → ℝ) → ℝ × ℝ := fun ω => (ω i, ω j)
  have hf : Measurable f :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hbox :
      MeasurableSet
        {p : ℝ × ℝ |
          clockCeilBin δ p.1 = k + 1 ∧ clockCeilBin δ p.2 = l + 1} := by
    have hk :
        MeasurableSet {t : ℝ | clockCeilBin δ t = k + 1} := by
      rw [clockCeilBin_preimage_succ δ hδ k]
      exact measurableSet_Ioc
    have hl :
        MeasurableSet {t : ℝ | clockCeilBin δ t = l + 1} := by
      rw [clockCeilBin_preimage_succ δ hδ l]
      exact measurableSet_Ioc
    change MeasurableSet
      ({t : ℝ | clockCeilBin δ t = k + 1} ×ˢ
        {t : ℝ | clockCeilBin δ t = l + 1})
    exact hk.prod hl
  calc
    finiteIndependentExp rates
        {ω : ι → ℝ |
          clockCeilBin δ (ω i) = k + 1 ∧
            clockCeilBin δ (ω j) = l + 1} =
      (Measure.map f (finiteIndependentExp rates))
        {p : ℝ × ℝ |
          clockCeilBin δ p.1 = k + 1 ∧
            clockCeilBin δ p.2 = l + 1} := by
      rw [Measure.map_apply hf hbox]
      rfl
    _ = independentExpPair (rates i) (rates j)
        {p : ℝ × ℝ |
          clockCeilBin δ p.1 = k + 1 ∧
            clockCeilBin δ p.2 = l + 1} := by
      rw [finiteIndependentExp_pair_law rates hpos i j hij]
    _ = _ := independentExpPair_clockCeilBin_joint
      (rates i) (rates j) δ (hpos i) (hpos j) hδ k l

end InverseGreedy
