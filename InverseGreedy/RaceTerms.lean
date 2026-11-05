import InverseGreedy.RealClockGreedyMIS

/-!
# S041: certified symbolic expansion of the first-choice recursion

`raceTerms L nb fuel active target` is a *computable* list of choice
paths; each path is a list of pairs `(v, S)` meaning "v is chosen first
among the active vertices listed in S". The theorem
`finiteRaceLaw_eq_raceValue` proves, for every rate vector, that the real
first-choice recursion equals the sum over paths of the products of
`rates v / Σ_{w ∈ S} rates w`.

For a concrete graph the path list can then be checked by `decide` in the
kernel (no native code evaluation), turning an output probability into an explicit
rational function of the rates.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

/-- Computable list of first-choice paths. `L` enumerates the vertices. -/
def raceTerms (L : List α) (nb : α → Finset α) :
    ℕ → Finset α → Finset α → List (List (α × List α))
  | 0, active, target => if active = ∅ ∧ target = ∅ then [[]] else []
  | fuel + 1, active, target =>
      if active = ∅ then (if target = ∅ then [[]] else [])
      else (L.filter (fun v => v ∈ active ∧ v ∈ target)).flatMap (fun v =>
        (raceTerms L nb fuel (afterChoice nb active v) (target.erase v)).map
          (fun t => (v, L.filter (fun w => w ∈ active)) :: t))

/-- Real value of one path. -/
noncomputable def raceTermValue (rates : α → ℝ) (t : List (α × List α)) : ℝ :=
  (t.map (fun p => rates p.1 / (p.2.map rates).sum)).prod

/-- Real value of a list of paths. -/
noncomputable def raceValue (rates : α → ℝ) (ts : List (List (α × List α))) : ℝ :=
  (ts.map (raceTermValue rates)).sum

/-- A finset sum is the sum over the filtered enumeration list. -/
theorem finset_sum_eq_filter_list_sum {β : Type*} [AddCommMonoid β]
    (L : List α) (hL : L.Nodup) (hall : ∀ x, x ∈ L)
    (s : Finset α) (g : α → β) :
    ∑ v ∈ s, g v = ((L.filter (fun v => v ∈ s)).map g).sum := by
  have hset : (L.filter (fun v => v ∈ s)).toFinset = s := by
    ext x
    simp [hall x]
  rw [← List.sum_toFinset g (hL.filter _), hset]

omit [DecidableEq α] in
theorem raceValue_flatMap_cons (rates : α → ℝ) (xs : List α)
    (f : α → List (List (α × List α))) (S : List α) :
    raceValue rates (xs.flatMap (fun v => (f v).map (fun t => (v, S) :: t))) =
      (xs.map (fun v => rates v / (S.map rates).sum * raceValue rates (f v))).sum := by
  induction xs with
  | nil => simp [raceValue]
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [← ih]
      unfold raceValue
      rw [List.map_append, List.sum_append]
      congr 1
      simp only [List.map_map]
      rw [← List.sum_map_mul_left]
      congr 1

/-- **Certified expansion.** The real first-choice recursion equals the
value of the computable path list, for every rate vector, fuel, active
set and target. -/
theorem finiteRaceLaw_eq_raceValue (L : List α) (hL : L.Nodup)
    (hall : ∀ x, x ∈ L) (rates : α → ℝ) (nb : α → Finset α) :
    ∀ (fuel : ℕ) (active target : Finset α),
      finiteRaceLaw rates nb fuel active target =
        raceValue rates (raceTerms L nb fuel active target)
  | 0, active, target => by
      by_cases h : active = ∅ ∧ target = ∅
      · simp [finiteRaceLaw, raceTerms, h, raceValue, raceTermValue]
      · simp [finiteRaceLaw, raceTerms, h, raceValue]
  | fuel + 1, active, target => by
      by_cases h : active = ∅
      · by_cases ht : target = ∅
        · simp [finiteRaceLaw, raceTerms, h, ht, raceValue, raceTermValue]
        · simp [finiteRaceLaw, raceTerms, h, ht, raceValue]
      · rw [finiteRaceLaw_step rates nb fuel active target h]
        simp only [raceTerms, h, ↓reduceIte]
        rw [raceValue_flatMap_cons]
        have hden : activeRate rates active =
            ((L.filter (fun w => w ∈ active)).map rates).sum :=
          finset_sum_eq_filter_list_sum L hL hall active rates
        have hsum :
            (∑ v ∈ active, if v ∈ target then
              firstChoice rates active v *
                finiteRaceLaw rates nb fuel (afterChoice nb active v)
                  (target.erase v) else 0) =
            ∑ v ∈ active ∩ target, firstChoice rates active v *
                finiteRaceLaw rates nb fuel (afterChoice nb active v)
                  (target.erase v) := by
          rw [Finset.sum_ite_mem]
        rw [hsum, finset_sum_eq_filter_list_sum L hL hall]
        simp only [Finset.mem_inter]
        congr 1
        apply List.map_congr_left
        intro v _
        rw [finiteRaceLaw_eq_raceValue L hL hall rates nb fuel, firstChoice, hden]

end InverseGreedy
