import InverseGreedy.FiniteClockBinSeries

/-!
# S036: the gap-to-bin direction of the finite geometric chamber reindexing

For a finite linear order of `n` clocks, the admissible strictly
increasing zero-based bins are obtained from arbitrary nonnegative gaps.
This module proves the forward map is strictly increasing and injective
in its position argument. It does *not* claim a bijection, evaluation
of the countable geometric series, or a real-clock chamber formula.

The true-measure starting point remains
`finiteIndependentExp_strictBin_series` from S035.
-/

namespace InverseGreedy

/-- The zero-based bin at position `j`: its minimum `j`, plus all
nonnegative gap increments from positions `a ≤ j`. -/
def gapBinValue {n : ℕ} (gaps : Fin n → ℕ) (j : Fin n) : ℕ :=
  j.val + (Finset.univ.filter (fun a : Fin n => a ≤ j)).sum gaps

/-- Every gap assignment produces bins strictly increasing in position.
This is the forward half of S036's desired gap-coordinate bijection. -/
theorem gapBinValue_strictMono {n : ℕ} (gaps : Fin n → ℕ) :
    StrictMono (gapBinValue gaps) := by
  intro a b hab
  have hsubset :
      (Finset.univ.filter (fun i : Fin n => i ≤ a)) ⊆
        (Finset.univ.filter (fun i : Fin n => i ≤ b)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi (le_of_lt hab)
  have hsum :
      (Finset.univ.filter (fun i : Fin n => i ≤ a)).sum gaps ≤
        (Finset.univ.filter (fun i : Fin n => i ≤ b)).sum gaps := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro i hi hnot; exact Nat.zero_le (gaps i))
  change a.val +
        (Finset.univ.filter (fun i : Fin n => i ≤ a)).sum gaps <
      b.val +
        (Finset.univ.filter (fun i : Fin n => i ≤ b)).sum gaps
  omega

/-- In particular, no two different positions are assigned the same bin. -/
theorem gapBinValue_injective {n : ℕ} (gaps : Fin n → ℕ) :
    Function.Injective (gapBinValue gaps) :=
  (gapBinValue_strictMono gaps).injective

/-- The least possible zero-based bin at position `j` is `j`. -/
theorem gapBinValue_lower_bound {n : ℕ} (gaps : Fin n → ℕ)
    (j : Fin n) : j.val ≤ gapBinValue gaps j := by
  unfold gapBinValue
  omega

/-- Adjacent bins differ by exactly one plus the new gap.
This recurrence is the local identity needed for the inverse gap map. -/
theorem gapBinValue_succ {n : ℕ} (gaps : Fin (n + 1) → ℕ)
    (j : Fin n) :
    gapBinValue gaps (Fin.succ j) =
      gapBinValue gaps (Fin.castSucc j) + 1 + gaps (Fin.succ j) := by
  have hfilter :
      (Finset.univ.filter (fun i : Fin (n + 1) => i ≤ Fin.succ j)) =
        insert (Fin.succ j)
          (Finset.univ.filter (fun i : Fin (n + 1) => i ≤ Fin.castSucc j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases heq : i = Fin.succ j
      · exact Or.inl heq
      · right
        apply Fin.le_def.mpr
        have hv : i.val ≤ j.val + 1 := Fin.le_def.mp hi
        have hneq : i.val ≠ j.val + 1 := by
          intro hval
          exact heq (Fin.ext hval)
        change i.val ≤ j.val
        omega
    · rintro (heq | hi)
      · rw [heq]
      · apply Fin.le_def.mpr
        have hv : i.val ≤ j.val := Fin.le_def.mp hi
        change i.val ≤ j.val + 1
        omega
  have hnot :
      Fin.succ j ∉
        (Finset.univ.filter (fun i : Fin (n + 1) => i ≤ Fin.castSucc j)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    have hv : j.val + 1 ≤ j.val := Fin.le_def.mp h
    omega
  dsimp only [gapBinValue]
  rw [hfilter, Finset.sum_insert hnot]
  change (j.val + 1) +
        (gaps (Fin.succ j) +
          (Finset.univ.filter
            (fun i : Fin (n + 1) => i ≤ Fin.castSucc j)).sum gaps) =
      j.val +
        (Finset.univ.filter
          (fun i : Fin (n + 1) => i ≤ Fin.castSucc j)).sum gaps +
        1 + gaps (Fin.succ j)
  omega

end InverseGreedy
