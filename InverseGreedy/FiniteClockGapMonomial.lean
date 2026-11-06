import InverseGreedy.FiniteClockGapFactors

/-!
# S040: finite gap-monomial factorisation in ENNReal

This is the algebraic step needed to evaluate S038's measured countable
chamber series. It holds for *arbitrary* ENNReal factors, hence also for
the genuine exponential-clock bin factors once they are transported to
the certified order positions. No countable-series or real-clock
pushforward claim is made in this file.
-/

namespace InverseGreedy

/-- Exponentiation turns a finite sum of natural exponents into a product. -/
private theorem ennreal_pow_finset_sum {α : Type*} (x : ENNReal)
    (s : Finset α) (d : α → ℕ) :
    x ^ (s.sum d) = s.prod (fun a => x ^ d a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, pow_add, ih]

/-- A filtered finite product is the full finite product with unit
factors at precisely those indices that fail the predicate. -/
private theorem finite_prod_filter_ite {α M : Type*} [DecidableEq α]
    [CommMonoid M] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (f : α → M) :
    (s.filter p).prod f =
      s.prod (fun a => if p a then f a else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hp : p a
      · simp [Finset.filter_insert, hp, ha, ih]
      · simp [Finset.filter_insert, hp, ha, ih]

/-- Exchange the triangular product in positions j with the triangular
product in gap coordinates a. No nonzero or finiteness assumptions are
needed, even with the values 0 and infinity in ENNReal. -/
theorem ennreal_prefix_suffix_pow_product {n : ℕ}
    (q : Fin n → ENNReal) (gaps : Fin n → ℕ) :
    (∏ j : Fin n,
      (q j) ^ ((Finset.univ.filter (fun a : Fin n => a ≤ j)).sum gaps)) =
    ∏ a : Fin n,
      ((Finset.univ.filter (fun j : Fin n => a ≤ j)).prod q) ^ gaps a := by
  classical
  calc
    (∏ j : Fin n,
      (q j) ^ ((Finset.univ.filter (fun a : Fin n => a ≤ j)).sum gaps)) =
      ∏ j : Fin n, ∏ a : Fin n,
        if a ≤ j then (q j) ^ gaps a else 1 := by
          apply Finset.prod_congr rfl
          intro j _
          rw [ennreal_pow_finset_sum]
          exact finite_prod_filter_ite Finset.univ
            (fun a : Fin n => a ≤ j) (fun a => (q j) ^ gaps a)
    _ = ∏ a : Fin n, ∏ j : Fin n,
          if a ≤ j then (q j) ^ gaps a else 1 := by
            rw [Finset.prod_comm]
    _ = ∏ a : Fin n,
          ((Finset.univ.filter (fun j : Fin n => a ≤ j)).prod q) ^ gaps a := by
          apply Finset.prod_congr rfl
          intro a _
          calc
            (∏ j : Fin n, if a ≤ j then (q j) ^ gaps a else 1) =
              (Finset.univ.filter (fun j : Fin n => a ≤ j)).prod
                (fun j => (q j) ^ gaps a) := by
                exact (finite_prod_filter_ite Finset.univ
                  (fun j : Fin n => a ≤ j) (fun j => (q j) ^ gaps a)).symm
            _ = ((Finset.univ.filter (fun j : Fin n => a ≤ j)).prod q) ^
                  gaps a := by rw [Finset.prod_pow]

/-- Exact pointwise gap monomial factorisation, including Fin 0 and Fin 1.
The c factors stand for the actual exponential-bin one-step masses,
and q for their exponential survival ratios. -/
theorem ennreal_gapBinValue_monomial_factor {n : ℕ}
    (c q : Fin n → ENNReal) (gaps : Fin n → ℕ) :
    (∏ j : Fin n, c j * (q j) ^ (gapBinValue gaps j)) =
    (∏ j : Fin n, c j * (q j) ^ j.val) *
      (∏ a : Fin n,
        ((Finset.univ.filter (fun j : Fin n => a ≤ j)).prod q) ^ gaps a) := by
  classical
  calc
    (∏ j : Fin n, c j * (q j) ^ (gapBinValue gaps j)) =
      ∏ j : Fin n,
        (c j * (q j) ^ j.val) *
          (q j) ^ ((Finset.univ.filter
            (fun a : Fin n => a ≤ j)).sum gaps) := by
          apply Finset.prod_congr rfl
          intro j _
          simp only [gapBinValue, pow_add, mul_assoc]
    _ = (∏ j : Fin n, c j * (q j) ^ j.val) *
        (∏ j : Fin n,
          (q j) ^ ((Finset.univ.filter
            (fun a : Fin n => a ≤ j)).sum gaps)) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ j : Fin n, c j * (q j) ^ j.val) *
        (∏ a : Fin n,
          ((Finset.univ.filter (fun j : Fin n => a ≤ j)).prod q) ^ gaps a) := by
          rw [ennreal_prefix_suffix_pow_product]

end InverseGreedy
