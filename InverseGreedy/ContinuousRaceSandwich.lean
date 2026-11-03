import InverseGreedy.BinnedRaceGeometric

/-!
# S029: real-clock winner / ceiling-bin measure sandwich

All sets here live in the genuine real-valued two-clock sample space.
The pointwise monotonicity of the ceiling-bin map gives exact inclusions
for positive bin widths, *including* t≤0 and right-closed endpoints.
The actual independent exponential product is then sandwiched between
the already verified true binned winner and collision measures.
No discrete priority measure is assumed.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- Real-time order is preserved by the one-based ceiling-bin map,
including its exceptional zero bin. -/
theorem clockCeilBin_mono (δ : ℝ) (hδ : 0 < δ) :
    Monotone (clockCeilBin δ) := by
  intro x y hxy
  unfold clockCeilBin
  exact Nat.ceil_le_ceil ((div_le_div_iff_of_pos_right hδ).mpr hxy)

/-- A strictly earlier bin is necessarily a strictly earlier real clock.
Unlike a positive-cell cylinder result, this has *no* null exception. -/
theorem strictCeilBinRaceEvent_subset_realWinner
    (δ : ℝ) (hδ : 0 < δ) :
    strictCeilBinRaceEvent δ ⊆ {p : ℝ × ℝ | p.1 < p.2} := by
  intro p hp
  change clockCeilBin δ p.1 < clockCeilBin δ p.2 at hp
  change p.1 < p.2
  by_contra h
  have hreverse : p.2 ≤ p.1 := le_of_not_gt h
  have hmono := clockCeilBin_mono δ hδ hreverse
  omega

/-- Every strict real winner is either a strict-bin winner or a same-bin
collision. No discarded exceptional cell is needed, even at t=0. -/
theorem realWinner_subset_strictBin_union_sameBin
    (δ : ℝ) (hδ : 0 < δ) :
    {p : ℝ × ℝ | p.1 < p.2} ⊆
      strictCeilBinRaceEvent δ ∪ sameCeilBinEvent δ := by
  intro p hp
  have hmono : clockCeilBin δ p.1 ≤ clockCeilBin δ p.2 :=
    clockCeilBin_mono δ hδ (le_of_lt (show p.1 < p.2 from hp))
  change clockCeilBin δ p.1 < clockCeilBin δ p.2 ∨
    clockCeilBin δ p.1 = clockCeilBin δ p.2
  exact lt_or_eq_of_le hmono

/-- Genuine real-clock event sandwich, for all strictly positive rates
and widths. The right-hand collision mass is an actual product-measure
probability, whose real closed form is proved in S028. -/
theorem independentExpPair_realWinner_bin_sandwich (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (strictCeilBinRaceEvent δ) ≤
        independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} ∧
    independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} ≤
        independentExpPair r s (strictCeilBinRaceEvent δ) +
          independentExpPair r s (sameCeilBinEvent δ) := by
  constructor
  · exact measure_mono (strictCeilBinRaceEvent_subset_realWinner δ hδ)
  · calc
      independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} ≤
          independentExpPair r s
            (strictCeilBinRaceEvent δ ∪ sameCeilBinEvent δ) :=
              measure_mono (realWinner_subset_strictBin_union_sameBin δ hδ)
      _ ≤ independentExpPair r s (strictCeilBinRaceEvent δ) +
            independentExpPair r s (sameCeilBinEvent δ) := measure_union_le _ _

/-- S029's product-measure sandwich expressed explicitly using S028's
verified *real fraction* formulas, not an assumed geometric sampling law. -/
theorem independentExpPair_realWinner_fraction_sandwich (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    ENNReal.ofReal
        (((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
          (1 - Real.exp (-((r + s) * δ)))) ≤
        independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} ∧
    independentExpPair r s {p : ℝ × ℝ | p.1 < p.2} ≤
      ENNReal.ofReal
        (((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
          (1 - Real.exp (-((r + s) * δ)))) +
      ENNReal.ofReal
        (((1 - Real.exp (-(r * δ))) * (1 - Real.exp (-(s * δ)))) /
          (1 - Real.exp (-((r + s) * δ)))) := by
  have h := independentExpPair_realWinner_bin_sandwich r s δ hr hs hδ
  rwa [independentExpPair_strictCeilBinRace_realFraction r s δ hr hs hδ,
       independentExpPair_sameCeilBin_realFraction r s δ hr hs hδ] at h

end InverseGreedy
