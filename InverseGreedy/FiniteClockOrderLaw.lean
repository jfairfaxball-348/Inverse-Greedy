import InverseGreedy.FiniteClockGapClosedForm
import InverseGreedy.FiniteClockBinUnion
import InverseGreedy.ContinuousRaceLimit
import InverseGreedy.OrderMassBridge

/-!
# S041: the genuine real-clock strict-order law for every complete order

For an arbitrary finite index type, strictly positive real rates and a
certified complete order `σ`, the *actual* finite independent exponential
product measure of the strict real-clock chamber
  `{ω | ω σ₀ < ω σ₁ < ⋯ < ω σ_{n-1}}`
equals `ENNReal.ofReal (orderMass rates σ)`, the successive
remaining-rate (Plackett-Luce) product.

Proof route (no discrete law is assumed):
* S041 closed form for the measured strict-bin chamber at width δ > 0;
* each closed-form factor `(1-qⱼ) qⱼ^j / (1-Qⱼ)` tends to `λⱼ/Λⱼ` as
  δ → 0⁺ (S030's exponential CDF slope lemma);
* S033 sandwich and S034 finite collision bound `O(δ)` squeeze the
  constant chamber probability between the two limits.
-/

open MeasureTheory ProbabilityTheory Filter Topology
namespace InverseGreedy

/-- Total rate of the positional suffix of an order starting at `a`. -/
noncomputable def clockSuffixRate {ι : Type*} (rates : ι → ℝ)
    (order : List ι) (a : Fin order.length) : ℝ :=
  (Finset.univ.filter (fun j : Fin order.length => a ≤ j)).sum
    (fun j => rates (order[j]))

theorem clockSuffixRate_pos {ι : Type*} (rates : ι → ℝ)
    (hpos : ∀ i, 0 < rates i) (order : List ι) (a : Fin order.length) :
    0 < clockSuffixRate rates order a :=
  Finset.sum_pos (fun j _ => hpos _) ⟨a, by simp⟩

/-- S039's suffix bin ratio is the exponential of minus the suffix rate. -/
theorem clockBinSuffixRatio_eq_exp {ι : Type*} (rates : ι → ℝ) (δ : ℝ)
    (order : List ι) (a : Fin order.length) :
    clockBinSuffixRatio rates δ order a =
      Real.exp (-(clockSuffixRate rates order a * δ)) := by
  unfold clockBinSuffixRatio clockSuffixRate clockBinRatio
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- The head suffix of a cons list is the whole list. -/
private theorem clockSuffixRate_cons_zero {ι : Type*} (rates : ι → ℝ)
    (v : ι) (tail : List ι) :
    clockSuffixRate rates (v :: tail) ⟨0, by simp⟩ =
      rates v + (tail.map rates).sum := by
  unfold clockSuffixRate
  have hfilter :
      (Finset.univ.filter
        (fun j : Fin (v :: tail).length => (⟨0, by simp⟩ : Fin _) ≤ j)) =
        Finset.univ := by
    ext j
    simp
  rw [hfilter]
  change (∑ j : Fin (tail.length + 1), rates ((v :: tail)[j.val])) = _
  rw [Fin.sum_univ_succ]
  simp

/-- Later suffixes of a cons list are the tail's suffixes. -/
private theorem clockSuffixRate_cons_succ {ι : Type*} (rates : ι → ℝ)
    (v : ι) (tail : List ι) (j : Fin tail.length) :
    clockSuffixRate rates (v :: tail) (Fin.succ j) =
      clockSuffixRate rates tail j := by
  unfold clockSuffixRate
  rw [Finset.sum_filter, Finset.sum_filter]
  change (∑ l : Fin (tail.length + 1),
      if Fin.succ j ≤ l then rates ((v :: tail)[l.val]) else 0) = _
  rw [Fin.sum_univ_succ]
  simp [Fin.succ_le_succ_iff]

/-- The recursive successive-choice mass is the positional product of
rate over remaining suffix rate. -/
theorem orderMass_eq_suffix_prod {α : Type*} [DecidableEq α]
    (rates : α → ℝ) :
    ∀ order : List α, orderMass rates order =
      ∏ j : Fin order.length, rates (order[j]) / clockSuffixRate rates order j
  | [] => by simp [orderMass]
  | v :: tail => by
      rw [orderMass_cons, orderMass_eq_suffix_prod rates tail]
      change _ = ∏ j : Fin (tail.length + 1),
        rates ((v :: tail)[j]) / clockSuffixRate rates (v :: tail) j
      rw [Fin.prod_univ_succ]
      congr 1
      · rw [show (0 : Fin (tail.length + 1)) = ⟨0, by simp⟩ from rfl,
          clockSuffixRate_cons_zero]
        rfl
      · apply Finset.prod_congr rfl
        intro j _
        rw [clockSuffixRate_cons_succ]
        rfl

/-- One closed-form factor converges to its successive-choice ratio. -/
theorem clockBinChamberClosedForm_factor_tendsto {ι : Type*}
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i) (order : List ι)
    (j : Fin order.length) :
    Tendsto
      (fun δ : ℝ =>
        (1 - clockBinRatio rates δ (order[j])) *
          (clockBinRatio rates δ (order[j])) ^ j.val *
          (1 / (1 - clockBinSuffixRatio rates δ order j)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (rates (order[j]) / clockSuffixRate rates order j)) := by
  set r := rates (order[j]) with hr_def
  set R := clockSuffixRate rates order j with hR_def
  have hr : 0 < r := hpos _
  have hR : 0 < R := clockSuffixRate_pos rates hpos order j
  have hslope :
      Tendsto
        (fun δ : ℝ =>
          ((1 - Real.exp (-(r * δ))) / δ) /
            ((1 - Real.exp (-(R * δ))) / δ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (r / R)) :=
    (exponential_cdf_initial_slope r).div
      (exponential_cdf_initial_slope R) (ne_of_gt hR)
  have hc : Continuous (fun δ : ℝ => (Real.exp (-(r * δ))) ^ j.val) := by
    fun_prop
  have hpow :
      Tendsto (fun δ : ℝ => (Real.exp (-(r * δ))) ^ j.val)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have ht0 : Tendsto (fun δ : ℝ => (Real.exp (-(r * δ))) ^ j.val)
        (nhds (0 : ℝ)) (nhds 1) := by
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    exact ht0.mono_left nhdsWithin_le_nhds
  have hprod := hslope.mul hpow
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := hδ
  have hden : 1 - Real.exp (-(R * δ)) ≠ 0 := by
    have he : Real.exp (-(R * δ)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hR hδ'])
    linarith
  have hδne : δ ≠ 0 := ne_of_gt hδ'
  rw [clockBinSuffixRatio_eq_exp]
  unfold clockBinRatio
  rw [← hr_def, ← hR_def]
  field_simp

/-- The real closed product converges to the successive-choice mass. -/
theorem clockBinChamberClosedForm_tendsto_orderMass {ι : Type*}
    [DecidableEq ι] (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (order : List ι) :
    Tendsto (fun δ : ℝ => clockBinChamberClosedForm rates δ order)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (orderMass rates order)) := by
  rw [orderMass_eq_suffix_prod]
  unfold clockBinChamberClosedForm
  exact tendsto_finsetProd _ (fun j _ =>
    clockBinChamberClosedForm_factor_tendsto rates hpos order j)

/-- The S034 explicit collision error tends to zero with the width. -/
theorem clockBinCollision_pair_sum_tendsto_zero {ι : Type*}
    (rates : ι → ℝ) (order : List ι) :
    Tendsto
      (fun δ : ℝ =>
        ∑ a : Fin order.length, ∑ b : Fin order.length,
          if a < b then
            ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
          else 0)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hterm : ∀ a b : Fin order.length,
      Tendsto
        (fun δ : ℝ =>
          if a < b then
            ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
          else 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro a b
    by_cases hab : a < b
    · simp only [hab, ↓reduceIte]
      have hc : Continuous (fun δ : ℝ =>
          δ * min (rates (order[a])) (rates (order[b]))) := by fun_prop
      have ht0 : Tendsto (fun δ : ℝ =>
          δ * min (rates (order[a])) (rates (order[b])))
          (nhds (0 : ℝ)) (nhds 0) := by
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
      simpa using ENNReal.tendsto_ofReal (ht0.mono_left nhdsWithin_le_nhds)
    · simp only [hab, ↓reduceIte]
      exact tendsto_const_nhds
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin order.length))
    (fun a _ => tendsto_finsetSum (Finset.univ : Finset (Fin order.length))
      (fun b _ => hterm a b))
  simpa using hsum

/-- **S041 main theorem: genuine real-clock strict-order law.**
For every finite index type, strictly positive real rates and certified
complete order, the actual finite independent exponential probability
that the real clocks ring in exactly that strict order is the successive
remaining-rate product `orderMass`. Includes the empty and singleton
index types. -/
theorem finiteIndependentExp_strictClockChamber_orderMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (order : List ι) (hcomplete : CompleteClockOrder order) :
    finiteIndependentExp rates (strictClockChamber order) =
      ENNReal.ofReal (orderMass rates order) := by
  let P : ENNReal := finiteIndependentExp rates (strictClockChamber order)
  let F : ℝ → ENNReal := fun δ =>
    ENNReal.ofReal (clockBinChamberClosedForm rates δ order)
  let C : ℝ → ENNReal := fun δ =>
    ∑ a : Fin order.length, ∑ b : Fin order.length,
      if a < b then
        ENNReal.ofReal (δ * min (rates (order[a])) (rates (order[b])))
      else 0
  have hF : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (ENNReal.ofReal (orderMass rates order))) :=
    ENNReal.tendsto_ofReal
      (clockBinChamberClosedForm_tendsto_orderMass rates hpos order)
  have hC : Tendsto C (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    clockBinCollision_pair_sum_tendsto_zero rates order
  have hFC : Tendsto (fun δ => F δ + C δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (ENNReal.ofReal (orderMass rates order))) := by
    simpa using hF.add hC
  have hdistinct : ∀ a b : Fin order.length, a < b →
      order[a] ≠ order[b] := by
    intro a b hab heq
    exact (ne_of_lt hab) (hcomplete.positions_injective heq)
  have hlo : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), F δ ≤ P := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hs := (finiteIndependentExp_strictChamber_bin_sandwich
      rates δ hδ order).1
    rw [finiteIndependentExp_strictBin_closedForm rates hpos δ hδ order
      hcomplete] at hs
    exact hs
  have hhi : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), P ≤ F δ + C δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hs := finiteIndependentExp_strictChamber_le_bin_add_pair_sum
      rates hpos δ hδ order hdistinct
    rw [finiteIndependentExp_strictBin_closedForm rates hpos δ hδ order
      hcomplete] at hs
    exact hs
  have hpin : Tendsto (fun _ : ℝ => P) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (ENNReal.ofReal (orderMass rates order))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hF hFC hlo hhi
  have hconst : Tendsto (fun _ : ℝ => P) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds P) := tendsto_const_nhds
  exact tendsto_nhds_unique hconst hpin

end InverseGreedy
