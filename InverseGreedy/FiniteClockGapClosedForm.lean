import InverseGreedy.FiniteClockGapMonomial

/-!
# S041: exact finite-width closed product of the measured strict-bin chamber

Starting point: S038's *genuine measured* identity
`finiteIndependentExp_strictBin_gap_series`, whose left side is the actual
finite independent exponential product measure of the strict ceiling-bin
chamber of a certified complete order.

This module proves
1. the S038 measured monomial at the S037/S038 gap equivalence is the
   positional ENNReal monomial `∏ⱼ ofReal(1-qⱼ) * ofReal(qⱼ)^(kⱼ)`
   (including `Fin 0`);
2. via S040's triangular identity, it factors as a constant times
   `∏ₐ ofReal(Qₐ)^(dₐ)`;
3. the finite-index product of countable ENNReal series identity
   `∑' d, ∏ₐ fₐ(dₐ) = ∏ₐ ∑' k, fₐ k` (Tonelli in ENNReal, by induction
   along `Fin.consEquiv`, including `Fin 0`);
4. the exact finite-width closed product, as a *real* product embedded
   by `ENNReal.ofReal`, with all denominators `1 - Qₐ` strictly positive.

No discrete Plackett-Luce law is assumed; no limit is taken here.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical
namespace InverseGreedy

/-- Finite-index Tonelli/product identity for countable ENNReal series.
For `n = 0` both sides are one (the unique empty gap vector and the
empty product). No summability hypothesis is needed in ENNReal. -/
theorem ennreal_tsum_fin_pi_prod :
    ∀ (n : ℕ) (f : Fin n → ℕ → ENNReal),
      (∑' d : Fin n → ℕ, ∏ a : Fin n, f a (d a)) =
        ∏ a : Fin n, ∑' k : ℕ, f a k
  | 0, f => by
      simp
  | n + 1, f => by
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq]
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
      rw [ENNReal.tsum_prod']
      simp only [ENNReal.tsum_mul_left]
      rw [ennreal_tsum_fin_pi_prod n (fun a => f a.succ), ENNReal.tsum_mul_right]

/-- The S037 equivalence evaluates to `gapBinValue` in every length,
including the empty length where both sides are the empty vector. -/
theorem finiteGapBinEquiv_val (n : ℕ) (gaps : Fin n → ℕ) :
    ((finiteGapBinEquiv n) gaps).val = gapBinValue gaps := by
  cases n with
  | zero =>
      funext j
      exact Fin.elim0 j
  | succ n => rfl

/-- The vertex-indexed bins attached by S038 to a gap vector. -/
theorem completeClockOrderGapEquiv_symm_val
    {ι : Type*} {order : List ι} (h : CompleteClockOrder order)
    (gaps : Fin order.length → ℕ) (i : ι) :
    ((completeClockOrderGapEquiv h).symm gaps).val i =
      gapBinValue gaps (h.index.symm i) := by
  change ((finiteGapBinEquiv order.length) gaps).val (h.index.symm i) = _
  rw [finiteGapBinEquiv_val]

/-- S038's *measured* positive-bin monomial, at the gap-coordinate
assignment, is the positional ENNReal monomial with exponents
`gapBinValue`. The real factors are nonnegative, so `ofReal` splits
exactly. -/
theorem finiteExpPositiveBinMonomial_gap_positional
    {ι : Type*} [Fintype ι] (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ)
    {order : List ι} (h : CompleteClockOrder order)
    (gaps : Fin order.length → ℕ) :
    finiteExpPositiveBinMonomial rates δ
        (((completeClockOrderGapEquiv h).symm gaps).val) =
      ∏ j : Fin order.length,
        ENNReal.ofReal (1 - clockBinRatio rates δ (order[j])) *
          (ENNReal.ofReal (clockBinRatio rates δ (order[j]))) ^
            (gapBinValue gaps j) := by
  unfold finiteExpPositiveBinMonomial
  simp only [completeClockOrderGapEquiv_symm_val]
  symm
  apply Fintype.prod_equiv h.index
  intro j
  rw [h.agrees j, Equiv.symm_apply_apply]
  have hq0 : 0 ≤ clockBinRatio rates δ (h.index j) :=
    (clockBinRatio_pos rates δ (h.index j)).le
  have hq1 : 0 ≤ 1 - clockBinRatio rates δ (h.index j) := by
    linarith [clockBinRatio_lt_one rates hpos δ hδ (h.index j)]
  unfold clockBinRatio at hq0 hq1 ⊢
  rw [ENNReal.ofReal_mul hq1, ENNReal.ofReal_pow hq0]

/-- The ENNReal product of the positional bin ratios over a suffix is the
image of S039's real suffix ratio. -/
theorem ennreal_suffix_prod_eq_ofReal
    {ι : Type*} (rates : ι → ℝ) (δ : ℝ) (order : List ι)
    (a : Fin order.length) :
    (Finset.univ.filter (fun j : Fin order.length => a ≤ j)).prod
        (fun j => ENNReal.ofReal (clockBinRatio rates δ (order[j]))) =
      ENNReal.ofReal (clockBinSuffixRatio rates δ order a) := by
  unfold clockBinSuffixRatio
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro j _
  exact (clockBinRatio_pos rates δ (order[j])).le

/-- The exact finite-width real closed product attached to an order:
`∏ⱼ (1-qⱼ) qⱼ^j / (1-Qⱼ)`, with `qⱼ = exp(-λ_{σ j} δ)` and
`Qⱼ = ∏_{l ≥ j} q_l`. -/
noncomputable def clockBinChamberClosedForm {ι : Type*}
    (rates : ι → ℝ) (δ : ℝ) (order : List ι) : ℝ :=
  ∏ j : Fin order.length,
    (1 - clockBinRatio rates δ (order[j])) *
      (clockBinRatio rates δ (order[j])) ^ j.val *
      (1 / (1 - clockBinSuffixRatio rates δ order j))

/-- Each closed-form factor is nonnegative for positive rates and width. -/
theorem clockBinChamberClosedForm_factor_nonneg {ι : Type*}
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι) (j : Fin order.length) :
    0 ≤ (1 - clockBinRatio rates δ (order[j])) *
      (clockBinRatio rates δ (order[j])) ^ j.val *
      (1 / (1 - clockBinSuffixRatio rates δ order j)) := by
  have hq := clockBinRatio_lt_one rates hpos δ hδ (order[j])
  have hq0 := clockBinRatio_pos rates δ (order[j])
  have hden := one_sub_clockBinSuffixRatio_pos rates hpos δ hδ order j
  apply mul_nonneg
  · apply mul_nonneg
    · linarith
    · exact pow_nonneg hq0.le _
  · exact (one_div_pos.mpr hden).le

/-- **Main S041 theorem.** The genuine finite independent exponential
probability of the strict ceiling-bin chamber of a certified complete
order is the exact finite-width closed product. The left side is the
*actual measure*; the right side is a real number in `[0, ∞)`. -/
theorem finiteIndependentExp_strictBin_closedForm
    {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι)
    (hcomplete : CompleteClockOrder order) :
    finiteIndependentExp rates (strictClockBinChamber δ order) =
      ENNReal.ofReal (clockBinChamberClosedForm rates δ order) := by
  rw [finiteIndependentExp_strictBin_gap_series rates hpos δ hδ order hcomplete]
  simp only [finiteExpPositiveBinMonomial_gap_positional rates hpos δ hδ hcomplete,
    ennreal_gapBinValue_monomial_factor, ennreal_suffix_prod_eq_ofReal]
  rw [ENNReal.tsum_mul_left,
    ennreal_tsum_fin_pi_prod order.length
      (fun a k => (ENNReal.ofReal (clockBinSuffixRatio rates δ order a)) ^ k)]
  simp only [clockBinSuffixRatio_geometric_series rates hpos δ hδ order]
  rw [← Finset.prod_mul_distrib]
  unfold clockBinChamberClosedForm
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    clockBinChamberClosedForm_factor_nonneg rates hpos δ hδ order j)]
  apply Finset.prod_congr rfl
  intro j _
  have hq := clockBinRatio_lt_one rates hpos δ hδ (order[j])
  have hq0 := clockBinRatio_pos rates δ (order[j])
  have h1 : 0 ≤ 1 - clockBinRatio rates δ (order[j]) := by linarith
  have h2 : 0 ≤ (1 - clockBinRatio rates δ (order[j])) *
      (clockBinRatio rates δ (order[j])) ^ j.val :=
    mul_nonneg h1 (pow_nonneg hq0.le _)
  rw [ENNReal.ofReal_mul h2, ENNReal.ofReal_mul h1, ENNReal.ofReal_pow hq0.le]

end InverseGreedy
