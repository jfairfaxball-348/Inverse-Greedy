import InverseGreedy.RaceTerms

/-!
# S041: kernel-checkable rational EGU witnesses

`raceValueQ` evaluates the certified path expansion of S041 in exact
rational arithmetic. `realClockEGU_of_ratWitness` is the soundness theorem:
if a strictly positive rational rate vector makes every maximal independent
set's exact rational path value equal to `1 / #MIS`, then the graph is EGU
under **genuine** independent exponential clocks (with those rates cast to ℝ).
The hypotheses are decidable, so a concrete witness is checked by kernel
reduction (`decide +kernel`), never by native code evaluation.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Exact rational value of one path. -/
def raceTermValueQ (q : α → ℚ) (t : List (α × List α)) : ℚ :=
  (t.map (fun p => q p.1 / (p.2.map q).sum)).prod

/-- Exact rational value of a list of paths. -/
def raceValueQ (q : α → ℚ) (ts : List (List (α × List α))) : ℚ :=
  (ts.map (raceTermValueQ q)).sum

omit [DecidableEq α] in
theorem raceTermValue_cast (q : α → ℚ) (t : List (α × List α)) :
    raceTermValue (fun v => (q v : ℝ)) t = ((raceTermValueQ q t : ℚ) : ℝ) := by
  induction t with
  | nil => simp [raceTermValue, raceTermValueQ]
  | cons p t ih =>
      simp only [raceTermValue, raceTermValueQ, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]
      push_cast
      congr 2
      induction p.2 with
      | nil => simp
      | cons x xs ihx => simp [ihx]

omit [DecidableEq α] in
theorem raceValue_cast (q : α → ℚ) (ts : List (List (α × List α))) :
    raceValue (fun v => (q v : ℝ)) ts = ((raceValueQ q ts : ℚ) : ℝ) := by
  induction ts with
  | nil => simp [raceValue, raceValueQ]
  | cons t ts ih =>
      simp only [raceValue, raceValueQ, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, raceTermValue_cast]
      push_cast
      rfl

/-- **Soundness of rational witnesses** for graphs on `Fin n`. -/
theorem realClockEGU_of_ratWitness {n : ℕ} (nb : Fin n → Finset (Fin n))
    (q : Fin n → ℚ) (hq : ∀ v, 0 < q v)
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (h : ∀ I ∈ maximalIndependentSets nb,
      raceValueQ q (raceTerms (List.finRange n) nb n Finset.univ I) =
        1 / ((maximalIndependentSets nb).card : ℚ)) :
    RealClockEGU nb := by
  rw [realClockEGU_iff_firstChoiceEGU nb hs]
  refine ⟨fun v => (q v : ℝ), fun v => by simpa using hq v, fun I hI => ?_⟩
  rw [Fintype.card_fin, finiteRaceLaw_eq_raceValue (List.finRange n) (List.nodup_finRange n)
    (fun x => List.mem_finRange x), raceValue_cast, h I hI]
  push_cast
  rfl

end InverseGreedy
