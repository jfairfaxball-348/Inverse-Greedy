import InverseGreedy.FiniteClockGapEncoding

/-!
# S037: the reverse map from strictly increasing bins to finite gaps

For nonempty finite orders, `gapDifferenceSucc` takes a bin at position
zero and consecutive predecessor differences at later positions.
The proof uses the actual S036 prefix-sum encoding and its successor
identity. No exponential-clock probability or geometric-series
evaluation is claimed in this module.
-/

namespace InverseGreedy

/-- Consecutive gap coordinates for bins indexed by `Fin (n+1)`.
The subtraction is natural subtraction; it is an exact inverse on
strictly increasing bin assignments. -/
def gapDifferenceSucc {n : ℕ} (bins : Fin (n + 1) → ℕ) :
    Fin (n + 1) → ℕ :=
  Fin.cases (bins 0)
    (fun j : Fin n =>
      bins (Fin.succ j) - bins (Fin.castSucc j) - 1)

/-- At the first position the prefix sum contains only the first gap. -/
theorem gapBinValue_zero {n : ℕ} (gaps : Fin (n + 1) → ℕ) :
    gapBinValue gaps 0 = gaps 0 := by
  have hs :
      (Finset.univ.filter (fun i : Fin (n + 1) => i ≤ 0)) =
        {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hi
      apply Fin.ext
      have hv := Fin.le_def.mp hi
      simpa using hv
    · intro hi
      subst i
      exact le_refl 0
  simp [gapBinValue, hs]

/-- Taking successive differences of the prefix-sum encoding recovers
the original nonnegative gaps at every position. -/
theorem gapDifferenceSucc_gapBinValue {n : ℕ}
    (gaps : Fin (n + 1) → ℕ) :
    gapDifferenceSucc (gapBinValue gaps) = gaps := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [gapDifferenceSucc] using gapBinValue_zero gaps
  · change gapBinValue gaps (Fin.succ j) -
        gapBinValue gaps (Fin.castSucc j) - 1 =
      gaps (Fin.succ j)
    rw [gapBinValue_succ]
    omega

/-- Conversely, the prefix-sum encoding of the consecutive differences
recovers all strictly increasing bins, not just the first one. -/
theorem gapBinValue_gapDifferenceSucc {n : ℕ}
    (bins : Fin (n + 1) → ℕ) (hinc : StrictMono bins) :
    gapBinValue (gapDifferenceSucc bins) = bins := by
  funext i
  have aux : ∀ k : ℕ, ∀ j : Fin (n + 1), j.val = k →
      gapBinValue (gapDifferenceSucc bins) j = bins j := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hzero : j = 0 := by
          apply Fin.ext
          simpa using hj
        subst j
        simpa [gapDifferenceSucc] using
          (gapBinValue_zero (gapDifferenceSucc bins))
    | succ k ih =>
        intro j hj
        have hk : k < n := by
          have := j.isLt
          omega
        let prev : Fin n := ⟨k, hk⟩
        have heq : j = Fin.succ prev := by
          apply Fin.ext
          simp [prev]
          omega
        subst j
        have hprev :
            gapBinValue (gapDifferenceSucc bins) (Fin.castSucc prev) =
              bins (Fin.castSucc prev) :=
          ih (Fin.castSucc prev) rfl
        have hlt : bins (Fin.castSucc prev) < bins (Fin.succ prev) :=
          hinc (by
            apply Fin.lt_def.mpr
            simp [Fin.castSucc, Fin.succ])
        rw [gapBinValue_succ, hprev]
        change bins (Fin.castSucc prev) + 1 +
            (bins (Fin.succ prev) - bins (Fin.castSucc prev) - 1) =
          bins (Fin.succ prev)
        omega
  exact aux i.val i rfl

/-- The gap encoding is injective as a map of complete finite vectors,
rather than merely injective in its position argument. -/
theorem gapBinValue_vector_injective {n : ℕ} :
    Function.Injective
      (gapBinValue (n := n + 1) : (Fin (n + 1) → ℕ) →
        (Fin (n + 1) → ℕ)) := by
  intro x y h
  calc
    x = gapDifferenceSucc (gapBinValue x) :=
      (gapDifferenceSucc_gapBinValue x).symm
    _ = gapDifferenceSucc (gapBinValue y) := by rw [h]
    _ = y := gapDifferenceSucc_gapBinValue y

end InverseGreedy
