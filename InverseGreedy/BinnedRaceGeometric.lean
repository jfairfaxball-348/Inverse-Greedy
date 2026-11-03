import InverseGreedy.BinnedRaceCollision

/-!
# S028: geometric evaluation for actual exponential ceiling-bin collisions

The algebraic geometric-series helper works in ENNReal. Its application below
starts from the true countable measure identity of S027, not an assumed
geometric probability space. The continuous clock comparison and its limit
are separate obligations.
-/

open MeasureTheory ProbabilityTheory
namespace InverseGreedy

/-- A two-factor geometric series, including the extended-value cases.
No convergence assumption is needed in ENNReal. -/
theorem ennreal_tsum_two_geometric (a b x y : ENNReal) :
    (∑' k : ℕ, (a * x ^ k) * (b * y ^ k)) =
      (a * b) * (1 - x * y)⁻¹ := by
  calc
    (∑' k : ℕ, (a * x ^ k) * (b * y ^ k)) =
        ∑' k : ℕ, (a * b) * (x * y) ^ k := by
      congr 1
      funext k
      rw [mul_pow]
      ac_rfl
    _ = (a * b) * (∑' k : ℕ, (x * y) ^ k) := by
      rw [ENNReal.tsum_mul_left]
    _ = (a * b) * (1 - x * y)⁻¹ := by
      rw [ENNReal.tsum_geometric]

/-- The *actual* same-ceiling-bin event has a finite geometric expression
in ENNReal. This evaluates S027's previously unevaluated event measure
for arbitrary strictly positive real rates and bin widths. -/
theorem independentExpPair_sameCeilBin_geometric (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (sameCeilBinEvent δ) =
      ENNReal.ofReal
        ((1 - Real.exp (-(r * δ))) * (1 - Real.exp (-(s * δ)))) *
      (1 - ENNReal.ofReal
        (Real.exp (-(r * δ)) * Real.exp (-(s * δ))))⁻¹ := by
  let qr : ℝ := Real.exp (-(r * δ))
  let qs : ℝ := Real.exp (-(s * δ))
  have hqr0 : 0 ≤ qr := (Real.exp_pos _).le
  have hqs0 : 0 ≤ qs := (Real.exp_pos _).le
  have hqr1 : qr < 1 := Real.exp_lt_one_iff.mpr (by
    nlinarith [mul_pos hr hδ])
  have hqs1 : qs < 1 := Real.exp_lt_one_iff.mpr (by
    nlinarith [mul_pos hs hδ])
  have h1qr : 0 ≤ 1 - qr := by linarith
  have h1qs : 0 ≤ 1 - qs := by linarith
  change independentExpPair r s (sameCeilBinEvent δ) =
    ENNReal.ofReal ((1 - qr) * (1 - qs)) *
      (1 - ENNReal.ofReal (qr * qs))⁻¹
  calc
    independentExpPair r s (sameCeilBinEvent δ) =
        ∑' k : ℕ,
          (ENNReal.ofReal (1 - qr) * (ENNReal.ofReal qr) ^ k) *
          (ENNReal.ofReal (1 - qs) * (ENNReal.ofReal qs) ^ k) := by
      rw [independentExpPair_sameCeilBin_tsum r s δ hr hs hδ]
      congr 1
      funext k
      dsimp [qr, qs]
      rw [ENNReal.ofReal_mul h1qr, ENNReal.ofReal_pow hqr0 k,
          ENNReal.ofReal_mul h1qs, ENNReal.ofReal_pow hqs0 k]
    _ = (ENNReal.ofReal (1 - qr) * ENNReal.ofReal (1 - qs)) *
          (1 - ENNReal.ofReal qr * ENNReal.ofReal qs)⁻¹ :=
      ennreal_tsum_two_geometric _ _ _ _
    _ = ENNReal.ofReal ((1 - qr) * (1 - qs)) *
          (1 - ENNReal.ofReal (qr * qs))⁻¹ := by
      rw [ENNReal.ofReal_mul h1qr, ENNReal.ofReal_mul hqr0]


/-- The true strictly earlier ceiling-bin winner event also admits a
geometric closed form. This is not the yet-open continuous race ratio. -/
theorem independentExpPair_strictCeilBinRace_geometric (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (strictCeilBinRaceEvent δ) =
      ENNReal.ofReal
        ((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) *
      (1 - ENNReal.ofReal
        (Real.exp (-(r * δ)) * Real.exp (-(s * δ))))⁻¹ := by
  let qr : ℝ := Real.exp (-(r * δ))
  let qs : ℝ := Real.exp (-(s * δ))
  have hqr0 : 0 ≤ qr := (Real.exp_pos _).le
  have hqs0 : 0 ≤ qs := (Real.exp_pos _).le
  have hqr1 : qr < 1 := Real.exp_lt_one_iff.mpr (by
    nlinarith [mul_pos hr hδ])
  have h1qr : 0 ≤ 1 - qr := by linarith
  have hexp (k : ℕ) :
      Real.exp (-(s * (((k : ℝ) + 1) * δ))) = qs ^ (k + 1) := by
    dsimp [qs]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  change independentExpPair r s (strictCeilBinRaceEvent δ) =
    ENNReal.ofReal ((1 - qr) * qs) *
      (1 - ENNReal.ofReal (qr * qs))⁻¹
  calc
    independentExpPair r s (strictCeilBinRaceEvent δ) =
        ∑' k : ℕ,
          (ENNReal.ofReal (1 - qr) * (ENNReal.ofReal qr) ^ k) *
          (ENNReal.ofReal qs * (ENNReal.ofReal qs) ^ k) := by
      rw [independentExpPair_strictCeilBinRace_tsum r s δ hr hs hδ]
      congr 1
      funext k
      rw [hexp k, pow_succ]
      rw [ENNReal.ofReal_mul h1qr, ENNReal.ofReal_pow hqr0 k,
          ENNReal.ofReal_mul (pow_nonneg hqs0 k),
          ENNReal.ofReal_pow hqs0 k]
      ac_rfl
    _ = (ENNReal.ofReal (1 - qr) * ENNReal.ofReal qs) *
          (1 - ENNReal.ofReal qr * ENNReal.ofReal qs)⁻¹ :=
      ennreal_tsum_two_geometric _ _ _ _
    _ = ENNReal.ofReal ((1 - qr) * qs) *
          (1 - ENNReal.ofReal (qr * qs))⁻¹ := by
      rw [ENNReal.ofReal_mul h1qr, ENNReal.ofReal_mul hqr0]


/-- The ENNReal geometric denominator is the image of the ordinary real
denominator whenever the ratio is strictly below one. -/
theorem ennreal_geometric_real_quotient (a q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    ENNReal.ofReal a * (1 - ENNReal.ofReal q)⁻¹ =
      ENNReal.ofReal (a / (1 - q)) := by
  have hden : (1 : ENNReal) - ENNReal.ofReal q =
      ENNReal.ofReal (1 - q) := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_sub (1 : ℝ) hq).symm
  calc
    ENNReal.ofReal a * (1 - ENNReal.ofReal q)⁻¹ =
        ENNReal.ofReal a * (ENNReal.ofReal (1 - q))⁻¹ := by
      rw [hden]
    _ = ENNReal.ofReal (a / (1 - q)) := by
      rw [ENNReal.ofReal_div_of_pos (by linarith), div_eq_mul_inv]

/-- Fully real-valued fraction for the true same-bin collision event. -/
theorem independentExpPair_sameCeilBin_realFraction (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (sameCeilBinEvent δ) =
      ENNReal.ofReal
        (((1 - Real.exp (-(r * δ))) * (1 - Real.exp (-(s * δ)))) /
          (1 - Real.exp (-((r + s) * δ)))) := by
  have hqr1 : Real.exp (-(r * δ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hr hδ])
  have hqs1 : Real.exp (-(s * δ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hs hδ])
  have hq0 : 0 ≤ Real.exp (-(r * δ)) * Real.exp (-(s * δ)) := by positivity
  have hq1 : Real.exp (-(r * δ)) * Real.exp (-(s * δ)) < 1 := by
    calc
      Real.exp (-(r * δ)) * Real.exp (-(s * δ)) <
          1 * Real.exp (-(s * δ)) :=
        mul_lt_mul_of_pos_right hqr1 (Real.exp_pos _)
      _ = Real.exp (-(s * δ)) := one_mul _
      _ < 1 := hqs1
  have hprod : Real.exp (-(r * δ)) * Real.exp (-(s * δ)) =
      Real.exp (-((r + s) * δ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    independentExpPair r s (sameCeilBinEvent δ) =
        ENNReal.ofReal
          ((1 - Real.exp (-(r * δ))) * (1 - Real.exp (-(s * δ)))) *
        (1 - ENNReal.ofReal
          (Real.exp (-(r * δ)) * Real.exp (-(s * δ))))⁻¹ :=
      independentExpPair_sameCeilBin_geometric r s δ hr hs hδ
    _ = ENNReal.ofReal
          (((1 - Real.exp (-(r * δ))) * (1 - Real.exp (-(s * δ)))) /
            (1 - Real.exp (-(r * δ)) * Real.exp (-(s * δ)))) :=
      ennreal_geometric_real_quotient _ _ hq0 hq1
    _ = ENNReal.ofReal
          (((1 - Real.exp (-(r * δ))) * (1 - Real.exp (-(s * δ)))) /
            (1 - Real.exp (-((r + s) * δ)))) := by
      rw [hprod]

/-- Fully real-valued fraction for the true earlier-bin winner event. -/
theorem independentExpPair_strictCeilBinRace_realFraction (r s δ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ) :
    independentExpPair r s (strictCeilBinRaceEvent δ) =
      ENNReal.ofReal
        (((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
          (1 - Real.exp (-((r + s) * δ)))) := by
  have hqr1 : Real.exp (-(r * δ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hr hδ])
  have hqs1 : Real.exp (-(s * δ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hs hδ])
  have hq0 : 0 ≤ Real.exp (-(r * δ)) * Real.exp (-(s * δ)) := by positivity
  have hq1 : Real.exp (-(r * δ)) * Real.exp (-(s * δ)) < 1 := by
    calc
      Real.exp (-(r * δ)) * Real.exp (-(s * δ)) <
          1 * Real.exp (-(s * δ)) :=
        mul_lt_mul_of_pos_right hqr1 (Real.exp_pos _)
      _ = Real.exp (-(s * δ)) := one_mul _
      _ < 1 := hqs1
  have hprod : Real.exp (-(r * δ)) * Real.exp (-(s * δ)) =
      Real.exp (-((r + s) * δ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    independentExpPair r s (strictCeilBinRaceEvent δ) =
        ENNReal.ofReal
          ((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) *
        (1 - ENNReal.ofReal
          (Real.exp (-(r * δ)) * Real.exp (-(s * δ))))⁻¹ :=
      independentExpPair_strictCeilBinRace_geometric r s δ hr hs hδ
    _ = ENNReal.ofReal
          (((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
            (1 - Real.exp (-(r * δ)) * Real.exp (-(s * δ)))) :=
      ennreal_geometric_real_quotient _ _ hq0 hq1
    _ = ENNReal.ofReal
          (((1 - Real.exp (-(r * δ))) * Real.exp (-(s * δ))) /
            (1 - Real.exp (-((r + s) * δ)))) := by
      rw [hprod]

end InverseGreedy
