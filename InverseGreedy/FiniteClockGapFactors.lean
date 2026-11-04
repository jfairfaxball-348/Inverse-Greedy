import InverseGreedy.FiniteClockMeasuredGapSeries

/-!
# S039: strictly contractive geometric ratios for actual clock bins

For rates > 0 and widths > 0, each real clock-bin ratio
  q(i) = exp (-rate(i) * δ)
lies strictly between zero and one. The product of the q's over
any nonempty positional suffix is also strictly between zero and one.

These are the denominator and convergence preconditions for evaluating
S038's true-measure gap series. The multivariate ENNReal monomial
factorisation, multiple tsum evaluation and continuous-clock limit
are NOT asserted here.
-/

namespace InverseGreedy

/-- The real geometric ratio of a genuine exponential clock's
ceiling-bin probabilities. -/
noncomputable def clockBinRatio {ι : Type*}
    (rates : ι → ℝ) (δ : ℝ) (i : ι) : ℝ :=
  Real.exp (-(rates i * δ))

theorem clockBinRatio_pos {ι : Type*}
    (rates : ι → ℝ) (δ : ℝ) (i : ι) :
    0 < clockBinRatio rates δ i := by
  exact Real.exp_pos _

theorem clockBinRatio_lt_one {ι : Type*}
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (i : ι) :
    clockBinRatio rates δ i < 1 := by
  change Real.exp (-(rates i * δ)) < 1
  apply Real.exp_lt_one_iff.mpr
  nlinarith [mul_pos (hpos i) hδ]

/-- A product of real numbers in (0,1) stays positive and at most one.
The empty product is exactly one. -/
private theorem finite_prod_unit_interval {α : Type*} (f : α → ℝ) :
    ∀ s : Finset α,
      (∀ x ∈ s, 0 < f x ∧ f x < 1) →
      0 < s.prod f ∧ s.prod f ≤ 1 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert a s ha ih =>
      intro hf
      have hfa : 0 < f a ∧ f a < 1 := hf a (by simp)
      have hfs : ∀ x ∈ s, 0 < f x ∧ f x < 1 := by
        intro x hx
        exact hf x (by simp [hx])
      obtain ⟨hsp, hsle⟩ := ih hfs
      rw [Finset.prod_insert ha]
      constructor
      · exact mul_pos hfa.1 hsp
      · calc
          f a * s.prod f ≤ 1 * s.prod f :=
            mul_le_mul_of_nonneg_right hfa.2.le hsp.le
          _ = s.prod f := one_mul _
          _ ≤ 1 := hsle

/-- A nonempty product of factors in (0,1) is strictly below one. -/
private theorem finite_prod_strict_unit_interval {α : Type*}
    (f : α → ℝ) (s : Finset α) (hne : s.Nonempty)
    (hf : ∀ x ∈ s, 0 < f x ∧ f x < 1) :
    0 < s.prod f ∧ s.prod f < 1 := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hrest : ∀ x ∈ s.erase a, 0 < f x ∧ f x < 1 := by
    intro x hx
    exact hf x (Finset.mem_erase.mp hx).2
  obtain ⟨hrestpos, hrestle⟩ :=
    finite_prod_unit_interval f (s.erase a) hrest
  have hfa : 0 < f a ∧ f a < 1 := hf a ha
  have hnot : a ∉ s.erase a := by simp
  have hprod : s.prod f = f a * (s.erase a).prod f := by
    calc
      s.prod f = (insert a (s.erase a)).prod f := by
        rw [Finset.insert_erase ha]
      _ = f a * (s.erase a).prod f := Finset.prod_insert hnot
  rw [hprod]
  constructor
  · exact mul_pos hfa.1 hrestpos
  · calc
      f a * (s.erase a).prod f ≤ f a * 1 :=
        mul_le_mul_of_nonneg_left hrestle hfa.1.le
      _ = f a := mul_one _
      _ < 1 := hfa.2

/-- Product of real bin ratios over the suffix beginning at a.
Here a : Fin order.length, so the suffix is ALWAYS nonempty.
The special empty-order case has no such index, rather than a
spurious claim that the empty product is less than one. -/
noncomputable def clockBinSuffixRatio {ι : Type*}
    (rates : ι → ℝ) (δ : ℝ) (order : List ι)
    (a : Fin order.length) : ℝ :=
  (Finset.univ.filter (fun j : Fin order.length => a ≤ j)).prod
    (fun j => clockBinRatio rates δ (order[j]))

/-- Every defined suffix ratio is positive and strictly less than one;
the proof uses no assumption that an arbitrary order list is complete. -/
theorem clockBinSuffixRatio_pos_lt_one {ι : Type*}
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι)
    (a : Fin order.length) :
    0 < clockBinSuffixRatio rates δ order a ∧
      clockBinSuffixRatio rates δ order a < 1 := by
  classical
  have hne :
      (Finset.univ.filter (fun j : Fin order.length => a ≤ j)).Nonempty := by
    exact ⟨a, by simp⟩
  have hf :
      ∀ j ∈ Finset.univ.filter (fun j : Fin order.length => a ≤ j),
        0 < clockBinRatio rates δ (order[j]) ∧
          clockBinRatio rates δ (order[j]) < 1 := by
    intro j _
    exact ⟨clockBinRatio_pos rates δ (order[j]),
      clockBinRatio_lt_one rates hpos δ hδ (order[j])⟩
  exact finite_prod_strict_unit_interval
    (fun j : Fin order.length => clockBinRatio rates δ (order[j]))
    (Finset.univ.filter (fun j : Fin order.length => a ≤ j))
    hne hf

/-- Each denominator in the proposed finite-width geometric product
is strictly positive, including singleton orders. -/
theorem one_sub_clockBinSuffixRatio_pos {ι : Type*}
    (rates : ι → ℝ) (hpos : ∀ i, 0 < rates i)
    (δ : ℝ) (hδ : 0 < δ) (order : List ι)
    (a : Fin order.length) :
    0 < 1 - clockBinSuffixRatio rates δ order a := by
  have h := (clockBinSuffixRatio_pos_lt_one rates hpos δ hδ order a).2
  linarith

end InverseGreedy
