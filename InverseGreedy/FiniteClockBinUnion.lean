import InverseGreedy.FiniteClockPairBinCollision

/-!
# S034: finite unions of genuine exponential clock-bin collisions

The S033 pairwise estimate is summed over the finitely many *positions*
of a proposed list.  A hypothesis of pairwise distinct indexed positions
prevents use of the independent-pair lemma for repeated coordinates.
No completeness of the list is needed (thus complete permutations qualify),
and the empty and singleton cases are included.

Every measure here is the actual finite exponential product measure.
The bound below is an explicit ENNReal sum, with no assumed sorting law.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

private def positionalClockBinCollision {ι : Type*} (δ : ℝ)
    (order : List ι) (a b : Fin order.length) : Set (ι → ℝ) :=
  if a < b then
    {ω | clockCeilBin δ (ω (order[a])) =
      clockCeilBin δ (ω (order[b]))}
  else ∅

/-- A genuine finite exponential family's probability of *any* repeated
ceiling-bin value along a non-repeating list is bounded by the sum of the
true pairwise collision estimates. This also handles empty and singleton
lists, for which the right hand side is zero. -/
theorem finiteIndependentExp_clockBinCollisionOnList_le_pair_sum
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι)
    (hdistinct : ∀ a b : Fin order.length, a < b →
      order[a] ≠ order[b]) :
    finiteIndependentExp rates (clockBinCollisionOnList δ order) ≤
      ∑ a : Fin order.length, ∑ b : Fin order.length,
        if a < b then
          ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
        else 0 := by
  let μ := finiteIndependentExp rates
  let E : Fin order.length → Fin order.length → Set (ι → ℝ) :=
    positionalClockBinCollision δ order
  have hunion :
      clockBinCollisionOnList δ order = ⋃ a, ⋃ b, E a b := by
    ext ω
    constructor
    · rintro ⟨a, b, hab, heq⟩
      change ω ∈ ⋃ a, ⋃ b, E a b
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
        ⟨b, by simpa [E, positionalClockBinCollision, hab] using heq⟩⟩
    · intro hω
      change ω ∈ ⋃ a, ⋃ b, E a b at hω
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hω
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp ha
      by_cases hab : a < b
      · exact ⟨a, b, hab, by
          simpa [E, positionalClockBinCollision, hab] using hb⟩
      · have : False := by
          simpa [E, positionalClockBinCollision, hab] using hb
        exact this.elim
  have hpoint (a b : Fin order.length) :
      μ (E a b) ≤
        if a < b then
          ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
        else 0 := by
    by_cases hab : a < b
    · simpa [μ, E, positionalClockBinCollision, hab] using
        (finiteIndependentExp_pair_sameCeilBin_le_width_min_rate
          rates hpos (order[a]) (order[b]) (hdistinct a b hab) δ hδ)
    · simp [E, positionalClockBinCollision, hab]
  rw [hunion]
  calc
    μ (⋃ a, ⋃ b, E a b) ≤
        ∑' a, μ (⋃ b, E a b) := measure_iUnion_le _
    _ ≤ ∑' a, ∑' b, μ (E a b) :=
        ENNReal.tsum_le_tsum (fun a => measure_iUnion_le _)
    _ ≤ ∑' a, ∑' b,
          if a < b then
            ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
          else 0 :=
        ENNReal.tsum_le_tsum (fun a =>
          ENNReal.tsum_le_tsum (fun b => hpoint a b))
    _ = ∑ a : Fin order.length, ∑ b : Fin order.length,
          if a < b then
            ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
          else 0 := by simp only [tsum_fintype]

/-- The S033 genuine chamber sandwich now carries an explicit finite
quantitative error term, rather than an unevaluated collision event. -/
theorem finiteIndependentExp_strictChamber_le_bin_add_pair_sum
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι)
    (hdistinct : ∀ a b : Fin order.length, a < b →
      order[a] ≠ order[b]) :
    finiteIndependentExp rates (strictClockChamber order) ≤
      finiteIndependentExp rates (strictClockBinChamber δ order) +
        ∑ a : Fin order.length, ∑ b : Fin order.length,
          if a < b then
            ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
          else 0 := by
  exact (finiteIndependentExp_strictChamber_bin_sandwich rates δ hδ order).2.trans
    (add_le_add_left
      (finiteIndependentExp_clockBinCollisionOnList_le_pair_sum
        rates hpos δ hδ order hdistinct) _)

end InverseGreedy
