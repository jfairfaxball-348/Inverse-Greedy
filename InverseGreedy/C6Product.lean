import InverseGreedy.CubicAMGM

/-!
# C6: sharp algebraic obstruction for the three opposite-pair probabilities

The positive-rate rational formula for each pair probability is proved
informally using the exponential race, and its two-first-choice
algebraic identity is formalised in ExponentialRace.lean.

This file proves the sharp product inequality and contradiction with
the value 1/5. It does not yet define the stochastic greedy process in Lean.
-/

namespace InverseGreedy

theorem c6_six_denominators_ge
    (a0 a1 a2 d0 d1 d2 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2) :
    729 * (a0*a1*a2*d0*d1*d2) ≤
      (a1+a2+d0)*(a0+a2+d1)*(a0+a1+d2)*
        (d1+d2+a0)*(d0+d2+a1)*(d0+d1+a2) := by
  let u0 := a1+a2+d0
  let u1 := a0+a2+d1
  let u2 := a0+a1+d2
  let v0 := d1+d2+a0
  let v1 := d0+d2+a1
  let v2 := d0+d1+a2
  let l0 := 27*a1*a2*d0
  let l1 := 27*a0*a2*d1
  let l2 := 27*a0*a1*d2
  let l3 := 27*d1*d2*a0
  let l4 := 27*d0*d2*a1
  let l5 := 27*d0*d1*a2
  have h0 : l0 ≤ u0^3 := triple_sum_cube_ge_27_mul _ _ _ (le_of_lt ha1) (le_of_lt ha2) (le_of_lt hd0)
  have h1 : l1 ≤ u1^3 := triple_sum_cube_ge_27_mul _ _ _ (le_of_lt ha0) (le_of_lt ha2) (le_of_lt hd1)
  have h2 : l2 ≤ u2^3 := triple_sum_cube_ge_27_mul _ _ _ (le_of_lt ha0) (le_of_lt ha1) (le_of_lt hd2)
  have h3 : l3 ≤ v0^3 := triple_sum_cube_ge_27_mul _ _ _ (le_of_lt hd1) (le_of_lt hd2) (le_of_lt ha0)
  have h4 : l4 ≤ v1^3 := triple_sum_cube_ge_27_mul _ _ _ (le_of_lt hd0) (le_of_lt hd2) (le_of_lt ha1)
  have h5 : l5 ≤ v2^3 := triple_sum_cube_ge_27_mul _ _ _ (le_of_lt hd0) (le_of_lt hd1) (le_of_lt ha2)
  have h01 : l0*l1 ≤ u0^3*u1^3 :=
    mul_le_mul h0 h1 (by positivity) (by positivity)
  have h012 : l0*l1*l2 ≤ u0^3*u1^3*u2^3 :=
    mul_le_mul h01 h2 (by positivity) (by positivity)
  have h0123 : l0*l1*l2*l3 ≤ u0^3*u1^3*u2^3*v0^3 :=
    mul_le_mul h012 h3 (by positivity) (by positivity)
  have h01234 : l0*l1*l2*l3*l4 ≤ u0^3*u1^3*u2^3*v0^3*v1^3 :=
    mul_le_mul h0123 h4 (by positivity) (by positivity)
  have h012345 : l0*l1*l2*l3*l4*l5 ≤ u0^3*u1^3*u2^3*v0^3*v1^3*v2^3 :=
    mul_le_mul h01234 h5 (by positivity) (by positivity)
  let q := 729*(a0*a1*a2*d0*d1*d2)
  let p := u0*u1*u2*v0*v1*v2
  have hcubed : q^3 ≤ p^3 := by
    calc
      q^3 = l0*l1*l2*l3*l4*l5 := by
        dsimp [q, l0, l1, l2, l3, l4, l5]
        ring
      _ ≤ u0^3*u1^3*u2^3*v0^3*v1^3*v2^3 := h012345
      _ = p^3 := by
        change u0^3*u1^3*u2^3*v0^3*v1^3*v2^3 = (u0*u1*u2*v0*v1*v2)^3
        simp only [mul_pow]
  have hqp : q ≤ p := by
    by_contra h
    have hlt : p < q := lt_of_not_ge h
    have hpos : 0 < (q-p)*(q^2+q*p+p^2) := by
      apply mul_pos (by linarith)
      have hqp0 : 0 ≤ q := by dsimp [q]; positivity
      have hpp0 : 0 ≤ p := by dsimp [p,u0,u1,u2,v0,v1,v2]; positivity
      positivity
    nlinarith [hcubed, hpos]
  exact hqp

theorem c6_opposite_pair_product_le
    (a0 a1 a2 d0 d1 d2 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2) :
    (a0*d0/((a1+a2+d0)*(d1+d2+a0))) *
      (a1*d1/((a0+a2+d1)*(d0+d2+a1))) *
      (a2*d2/((a0+a1+d2)*(d0+d1+a2))) ≤ (1:ℝ)/729 := by
  let den := (a1+a2+d0)*(a0+a2+d1)*(a0+a1+d2)*
        (d1+d2+a0)*(d0+d2+a1)*(d0+d1+a2)
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hbound : 729*(a0*a1*a2*d0*d1*d2) ≤ den :=
    c6_six_denominators_ge a0 a1 a2 d0 d1 d2 ha0 ha1 ha2 hd0 hd1 hd2
  have hfract :
      (a0*d0/((a1+a2+d0)*(d1+d2+a0))) *
        (a1*d1/((a0+a2+d1)*(d0+d2+a1))) *
        (a2*d2/((a0+a1+d2)*(d0+d1+a2))) =
        (a0*a1*a2*d0*d1*d2)/den := by
    dsimp [den]
    field_simp
    <;> ring
  rw [hfract]
  apply (div_le_iff₀ hden).2
  nlinarith [hbound]

theorem c6_opposite_pairs_not_all_one_fifth
    (a0 a1 a2 d0 d1 d2 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2) :
    ¬ ((a0*d0/((a1+a2+d0)*(d1+d2+a0)) = (1:ℝ)/5) ∧
       (a1*d1/((a0+a2+d1)*(d0+d2+a1)) = (1:ℝ)/5) ∧
       (a2*d2/((a0+a1+d2)*(d0+d1+a2)) = (1:ℝ)/5)) := by
  rintro ⟨h0,h1,h2⟩
  have hp := c6_opposite_pair_product_le a0 a1 a2 d0 d1 d2 ha0 ha1 ha2 hd0 hd1 hd2
  rw [h0,h1,h2] at hp
  norm_num at hp

end InverseGreedy
