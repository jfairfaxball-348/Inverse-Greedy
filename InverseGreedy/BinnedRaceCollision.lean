import InverseGreedy.BinnedRaceSeries

/-!
# S027: countable collision mass of genuine exponential ceiling bins

A binned collision is a genuine event of the original two-clock product
measure. This module reduces its mass to the countable sum of the
actual independent geometric joint-cell probabilities. The separate
algebraic evaluation of that sum and its width-dependent bound remain open.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- Two actual, measurable ceiling bins coincide. This is *not* the
null real-clock exact-tie event. -/
def sameCeilBinEvent (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | clockCeilBin δ p.1 = clockCeilBin δ p.2}

/-- Positive positive-bin collision cell. -/
def samePositiveBinEvent (δ : ℝ) (k : ℕ) : Set (ℝ × ℝ) :=
  {p | clockCeilBin δ p.1 = k + 1 ∧ clockCeilBin δ p.2 = k + 1}

theorem samePositiveBinEvent_measurable (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    MeasurableSet (samePositiveBinEvent δ k) := by
  have hcell : MeasurableSet {t : ℝ | clockCeilBin δ t = k + 1} := by
    rw [clockCeilBin_preimage_succ δ hδ k]
    exact measurableSet_Ioc
  change MeasurableSet
    ({t : ℝ | clockCeilBin δ t = k + 1} ×ˢ
      {t : ℝ | clockCeilBin δ t = k + 1})
  exact hcell.prod hcell

/-- Each collision cylinder gets the *true joint* geometric point mass. -/
theorem independentExpPair_samePositiveBin_mass (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) (k : ℕ) :
    independentExpPair r s (samePositiveBinEvent δ k) =
      ENNReal.ofReal
        ((1 - Real.exp (-(r * δ))) *
          (Real.exp (-(r * δ))) ^ k) *
      ENNReal.ofReal
        ((1 - Real.exp (-(s * δ))) *
          (Real.exp (-(s * δ))) ^ k) :=
  independentExpPair_clockCeilBin_joint r s δ hr hs hδ k k

/-- Positive collision cells are pairwise disjoint, because the first
clock cannot occupy two different integer-valued bins. -/
theorem samePositiveBinEvent_pairwise_disjoint (δ : ℝ) :
    Pairwise (Disjoint on samePositiveBinEvent δ) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hii : clockCeilBin δ p.1 = i + 1 := hi.1
  have hjj : clockCeilBin δ p.1 = j + 1 := hj.1
  have heq : i = j := by omega
  exact hij heq

/-- Exact union decomposition, including the special (0,0) cell. -/
theorem sameCeilBinEvent_eq (δ : ℝ) :
    sameCeilBinEvent δ =
      {p : ℝ × ℝ | clockCeilBin δ p.1 = 0 ∧ clockCeilBin δ p.2 = 0} ∪
      ⋃ k : ℕ, samePositiveBinEvent δ k := by
  ext p
  change (clockCeilBin δ p.1 = clockCeilBin δ p.2) ↔
    p ∈ ({p : ℝ × ℝ |
      clockCeilBin δ p.1 = 0 ∧ clockCeilBin δ p.2 = 0} ∪
      ⋃ k : ℕ, samePositiveBinEvent δ k)
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h
    cases hfirst : clockCeilBin δ p.1 with
    | zero =>
      exact Or.inl ⟨hfirst, by omega⟩
    | succ k =>
      right
      refine ⟨k, ?_⟩
      change clockCeilBin δ p.1 = k + 1 ∧
        clockCeilBin δ p.2 = k + 1
      omega
  · intro h
    rcases h with ⟨hz, hs⟩ | ⟨k, hk⟩
    · omega
    · change clockCeilBin δ p.1 = k + 1 ∧
          clockCeilBin δ p.2 = k + 1 at hk
      omega

/-- Both clocks lying in their zero bin is a null cylinder. -/
theorem independentExpPair_bothZeroBin_null (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s
      {p : ℝ × ℝ | clockCeilBin δ p.1 = 0 ∧ clockCeilBin δ p.2 = 0}
      = 0 := by
  apply le_antisymm
  · calc
      independentExpPair r s
          {p : ℝ × ℝ |
            clockCeilBin δ p.1 = 0 ∧ clockCeilBin δ p.2 = 0} ≤
        independentExpPair r s
          {p : ℝ × ℝ | clockCeilBin δ p.1 = 0} :=
            measure_mono (by intro p hp; exact hp.1)
      _ = 0 := independentExpPair_fst_zeroBin_null r s δ hr hs hδ
  · exact zero_le _

/-- Measure-level countable additivity for genuine two-clock collisions;
no closed-form geometric-sum formula is assumed. -/
theorem independentExpPair_sameCeilBin_tsum (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (sameCeilBinEvent δ) =
      ∑' k : ℕ,
        ENNReal.ofReal
          ((1 - Real.exp (-(r * δ))) *
            (Real.exp (-(r * δ))) ^ k) *
        ENNReal.ofReal
          ((1 - Real.exp (-(s * δ))) *
            (Real.exp (-(s * δ))) ^ k) := by
  let A : Set (ℝ × ℝ) :=
    {p | clockCeilBin δ p.1 = 0 ∧ clockCeilBin δ p.2 = 0}
  let B : Set (ℝ × ℝ) := ⋃ k : ℕ, samePositiveBinEvent δ k
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro p hpA hpB
    obtain ⟨k, hpK⟩ := Set.mem_iUnion.mp hpB
    have hz : clockCeilBin δ p.1 = 0 := hpA.1
    have hk : clockCeilBin δ p.1 = k + 1 := hpK.1
    omega
  have hB : MeasurableSet B :=
    MeasurableSet.iUnion (fun k => samePositiveBinEvent_measurable δ hδ k)
  calc
    independentExpPair r s (sameCeilBinEvent δ) =
        independentExpPair r s (A ∪ B) := by
      rw [sameCeilBinEvent_eq δ]
    _ = independentExpPair r s B := by
      rw [measure_union hdisj hB,
        independentExpPair_bothZeroBin_null r s δ hr hs hδ, zero_add]
    _ = ∑' k : ℕ, independentExpPair r s (samePositiveBinEvent δ k) :=
      measure_iUnion (samePositiveBinEvent_pairwise_disjoint δ)
        (fun k => samePositiveBinEvent_measurable δ hδ k)
    _ = _ := by
      congr 1
      funext k
      exact independentExpPair_samePositiveBin_mass r s δ hr hs hδ k

end InverseGreedy
