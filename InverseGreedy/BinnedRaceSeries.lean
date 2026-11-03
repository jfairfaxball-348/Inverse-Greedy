import InverseGreedy.BinnedRace

/-!
# S027: countable decomposition of the genuine strict-bin race

The first-positive-bin cylinders of BinnedRace are disjoint and
measurable. Countable additivity therefore converts the measure of
their union to a genuine infinite sum of exponential cylinder masses.
The extra zero-bin event is null under the real exponential product.
No geometric-sum evaluation or continuous-rate ratio is postulated.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- The event that the two actual measurable ceiling bins are strictly ordered. -/
def strictCeilBinRaceEvent (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | clockCeilBin δ p.1 < clockCeilBin δ p.2}

/-- A ceiling bin being greater than k+1 is exactly the real
right-endpoint survival event (also for negative times). -/
theorem clockCeilBin_gt_succ_iff (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (k : ℕ) :
    k + 1 < clockCeilBin δ t ↔ ((k : ℝ) + 1) * δ < t := by
  change k + 1 < Nat.ceil (t / δ) ↔ ((k : ℝ) + 1) * δ < t
  rw [← not_le, Nat.ceil_le, not_le, lt_div_iff₀ hδ]
  simp only [Nat.cast_add, Nat.cast_one]

/-- The genuine strict-bin race splits exactly into an exceptional
zero-first-bin event and a countable union of first-bin cylinders. -/
theorem strictCeilBinRaceEvent_eq (δ : ℝ) (hδ : 0 < δ) :
    strictCeilBinRaceEvent δ =
      {p : ℝ × ℝ |
        clockCeilBin δ p.1 = 0 ∧ 0 < clockCeilBin δ p.2} ∪
      ⋃ k : ℕ, firstBinSurvivalEvent δ k := by
  ext p
  change (clockCeilBin δ p.1 < clockCeilBin δ p.2) ↔
    p ∈ ({p : ℝ × ℝ |
      clockCeilBin δ p.1 = 0 ∧ 0 < clockCeilBin δ p.2} ∪
      ⋃ k : ℕ, firstBinSurvivalEvent δ k)
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
        ((k : ℝ) + 1) * δ < p.2
      refine ⟨by omega, ?_⟩
      exact (clockCeilBin_gt_succ_iff δ hδ p.2 k).mp (by omega)
  · intro h
    rcases h with ⟨hz, hs⟩ | ⟨k, hk⟩
    · omega
    · change clockCeilBin δ p.1 = k + 1 ∧
          ((k : ℝ) + 1) * δ < p.2 at hk
      have hgt := (clockCeilBin_gt_succ_iff δ hδ p.2 k).mpr hk.2
      omega

/-- Genuine rate-r exponential first-clock zero bin has zero product
probability (only the second rate needs to be positive for marginalisation). -/
theorem independentExpPair_fst_zeroBin_null (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s
      {p : ℝ × ℝ | clockCeilBin δ p.1 = 0} = 0 := by
  have hzero : MeasurableSet {t : ℝ | clockCeilBin δ t = 0} := by
    rw [clockCeilBin_preimage_zero δ hδ]
    exact measurableSet_Iic
  calc
    independentExpPair r s
        {p : ℝ × ℝ | clockCeilBin δ p.1 = 0} =
      (Measure.map Prod.fst (independentExpPair r s))
        {t : ℝ | clockCeilBin δ t = 0} := by
          rw [Measure.map_apply measurable_fst hzero]
          rfl
    _ = expMeasure r {t : ℝ | clockCeilBin δ t = 0} := by
      rw [independentExpPair_fst_law r s hs]
    _ = 0 := expMeasure_clockCeilBin_zero r δ hr hδ

/-- The exceptional zero-bin part of the strict-bin winner event is null. -/
theorem independentExpPair_zeroFirstBinRace_null (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s
      {p : ℝ × ℝ |
        clockCeilBin δ p.1 = 0 ∧ 0 < clockCeilBin δ p.2} = 0 := by
  apply le_antisymm
  · calc
      independentExpPair r s
          {p : ℝ × ℝ |
            clockCeilBin δ p.1 = 0 ∧ 0 < clockCeilBin δ p.2} ≤
        independentExpPair r s
          {p : ℝ × ℝ | clockCeilBin δ p.1 = 0} :=
            measure_mono (by intro p hp; exact hp.1)
      _ = 0 := independentExpPair_fst_zeroBin_null r s δ hr hs hδ
  · exact zero_le _

/-- The first-positive-bin cylinders are pairwise disjoint. -/
theorem firstBinSurvivalEvent_pairwise_disjoint (δ : ℝ) :
    Pairwise (Disjoint on firstBinSurvivalEvent δ) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hii : clockCeilBin δ p.1 = i + 1 := hi.1
  have hjj : clockCeilBin δ p.1 = j + 1 := hj.1
  have heq : i = j := by omega
  exact hij heq

/-- Countable additivity for the **actual** exponential product law;
this is not a finite oracle or an assumed discrete bin measure. -/
theorem independentExpPair_firstBinSurvival_tsum
    (r s δ : ℝ) (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (⋃ k : ℕ, firstBinSurvivalEvent δ k) =
      ∑' k : ℕ,
        ENNReal.ofReal
          ((1 - Real.exp (-(r * δ))) *
            (Real.exp (-(r * δ))) ^ k) *
        ENNReal.ofReal
          (Real.exp (-(s * (((k : ℝ) + 1) * δ)))) := by
  calc
    independentExpPair r s (⋃ k : ℕ, firstBinSurvivalEvent δ k) =
        ∑' k : ℕ, independentExpPair r s (firstBinSurvivalEvent δ k) :=
      measure_iUnion (firstBinSurvivalEvent_pairwise_disjoint δ)
        (fun k => firstBinSurvivalEvent_measurable δ hδ k)
    _ = _ := by
      congr 1
      funext k
      exact independentExpPair_firstBinSurvival_mass r s δ hr hs hδ k

/-- Under the genuine exponential clock law, the complete strict-bin
winner event has exactly the countable geometric first-bin sum.
The zero-bin exception contributes nothing. -/
theorem independentExpPair_strictCeilBinRace_tsum
    (r s δ : ℝ) (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (strictCeilBinRaceEvent δ) =
      ∑' k : ℕ,
        ENNReal.ofReal
          ((1 - Real.exp (-(r * δ))) *
            (Real.exp (-(r * δ))) ^ k) *
        ENNReal.ofReal
          (Real.exp (-(s * (((k : ℝ) + 1) * δ)))) := by
  let A : Set (ℝ × ℝ) :=
    {p | clockCeilBin δ p.1 = 0 ∧ 0 < clockCeilBin δ p.2}
  let B : Set (ℝ × ℝ) := ⋃ k : ℕ, firstBinSurvivalEvent δ k
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro p hpA hpB
    obtain ⟨k, hpK⟩ := Set.mem_iUnion.mp hpB
    have hz : clockCeilBin δ p.1 = 0 := hpA.1
    have hk : clockCeilBin δ p.1 = k + 1 := hpK.1
    omega
  have hB : MeasurableSet B :=
    MeasurableSet.iUnion (fun k => firstBinSurvivalEvent_measurable δ hδ k)
  have hA0 : independentExpPair r s A = 0 :=
    independentExpPair_zeroFirstBinRace_null r s δ hr hs hδ
  calc
    independentExpPair r s (strictCeilBinRaceEvent δ) =
        independentExpPair r s (A ∪ B) := by
      rw [strictCeilBinRaceEvent_eq δ hδ]
    _ = independentExpPair r s B := by
      rw [measure_union hdisj hB, hA0, zero_add]
    _ = _ := independentExpPair_firstBinSurvival_tsum r s δ hr hs hδ

/-- The genuinely binned strict-winner probability never exceeds the
continuous strict-winner probability. -/
theorem independentExpPair_strictBin_le_realWinner
    (r s δ : ℝ) (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (strictCeilBinRaceEvent δ) ≤
      independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} := by
  have hsub : (⋃ k : ℕ, firstBinSurvivalEvent δ k) ⊆
      {p : ℝ × ℝ | p.1 < p.2} := by
    intro p hp
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    exact firstBinSurvivalEvent_subset_realWinner δ hδ k hk
  have hmass : independentExpPair r s (strictCeilBinRaceEvent δ) =
      independentExpPair r s (⋃ k : ℕ, firstBinSurvivalEvent δ k) := by
    let A : Set (ℝ × ℝ) :=
      {p | clockCeilBin δ p.1 = 0 ∧ 0 < clockCeilBin δ p.2}
    let B : Set (ℝ × ℝ) := ⋃ k : ℕ, firstBinSurvivalEvent δ k
    have hdisj : Disjoint A B := by
      apply Set.disjoint_left.mpr
      intro p hpA hpB
      obtain ⟨k, hpK⟩ := Set.mem_iUnion.mp hpB
      have hz : clockCeilBin δ p.1 = 0 := hpA.1
      have hk : clockCeilBin δ p.1 = k + 1 := hpK.1
      omega
    have hB : MeasurableSet B :=
      MeasurableSet.iUnion (fun k => firstBinSurvivalEvent_measurable δ hδ k)
    calc
      independentExpPair r s (strictCeilBinRaceEvent δ) =
          independentExpPair r s (A ∪ B) := by
        rw [strictCeilBinRaceEvent_eq δ hδ]
      _ = independentExpPair r s B := by
        rw [measure_union hdisj hB,
          independentExpPair_zeroFirstBinRace_null r s δ hr hs hδ, zero_add]
  rw [hmass]
  exact measure_mono hsub

end InverseGreedy
