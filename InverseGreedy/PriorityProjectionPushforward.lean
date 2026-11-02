import InverseGreedy.FullProjectedOrderExact

/-!
# S018: weighted expectation under deletion of irrelevant priorities

This is an exact pushforward over Mathlib's actual complete priority
permutations. The proof groups finite weighted sums by their projected
order and invokes the all-target S017 deletion-consistency theorem.
It is not a probabilistic assertion about continuous exponential clocks.
-/
namespace InverseGreedy
variable {α : Type*} [DecidableEq α]

private theorem list_sum_map_add {β : Type*} (ys : List β)
    (f g : β → ℝ) :
    (ys.map (fun y => f y + g y)).sum =
      (ys.map f).sum + (ys.map g).sum := by
  induction ys with
  | nil => simp
  | cons y tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

private theorem list_sum_swap {β γ : Type*} (xs : List β)
    (ys : List γ) (f : β → γ → ℝ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      calc
        ((x :: tail).map (fun a => (ys.map (f a)).sum)).sum =
            (ys.map (f x)).sum +
              (ys.map (fun y => (tail.map (fun a => f a y)).sum)).sum := by
                simp only [List.map_cons, List.sum_cons]
                rw [ih]
        _ = (ys.map (fun y => f x y +
              (tail.map (fun a => f a y)).sum)).sum :=
              (list_sum_map_add ys (f x)
                (fun y => (tail.map (fun a => f a y)).sum)).symm
        _ = (ys.map (fun y =>
              ((x :: tail).map (fun a => f a y)).sum)).sum := by
                simp only [List.map_cons, List.sum_cons]

private theorem list_sum_indicator_absent {β : Type*}
    [DecidableEq β] (ys : List β) (z : β) (c : ℝ)
    (hz : z ∉ ys) :
    (ys.map (fun y => if z = y then c else 0)).sum = 0 := by
  induction ys with
  | nil => simp
  | cons y tail ih =>
      have hne : z ≠ y := by
        intro h
        exact hz (by simp [h])
      have ht : z ∉ tail := by
        intro h
        exact hz (by simp [h])
      simp only [List.map_cons, List.sum_cons]
      simp [hne, ih ht]

private theorem list_sum_indicator_present {β : Type*}
    [DecidableEq β] (ys : List β) (z : β) (c : ℝ)
    (hnd : ys.Nodup) (hz : z ∈ ys) :
    (ys.map (fun y => if z = y then c else 0)).sum = c := by
  induction ys with
  | nil => simp at hz
  | cons y tail ih =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnd
      by_cases heq : z = y
      · subst y
        simp only [List.map_cons, List.sum_cons]
        simp [list_sum_indicator_absent tail z c hnot]
      · have hmem : z ∈ tail := by
          simpa [heq] using hz
        simp only [List.map_cons, List.sum_cons]
        simp [heq, ih htail hmem]

private theorem list_sum_select_scaled {β γ : Type*}
    [DecidableEq γ] (xs : List β) (p : β → γ)
    (y : γ) (c : ℝ) (mass : β → ℝ) :
    (xs.map (fun x => if p x = y then c * mass x else 0)).sum =
      c * (xs.map (fun x => if p x = y then mass x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      by_cases hp : p x = y <;> simp [hp] <;> ring

/-- Weighted finite regrouping for a projection whose image lies in a
duplicate-free list. No probability or positivity assumptions. -/
theorem weighted_list_projection_sum {β γ : Type*}
    [DecidableEq γ] (xs : List β) (ys : List γ)
    (p : β → γ) (mass : β → ℝ) (f : γ → ℝ)
    (hnd : ys.Nodup) (hs : ∀ x ∈ xs, p x ∈ ys) :
    (xs.map (fun x => f (p x) * mass x)).sum =
      (ys.map (fun y => f y *
        (xs.map (fun x => if p x = y then mass x else 0)).sum)).sum := by
  classical
  let k : β → γ → ℝ :=
    fun x y => if p x = y then f y * mass x else 0
  have hsingle (x : β) (hx : x ∈ xs) :
      (ys.map (k x)).sum = f (p x) * mass x := by
    calc
      (ys.map (k x)).sum =
          (ys.map (fun y => if p x = y then
            f (p x) * mass x else 0)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro y hy
            by_cases hp : p x = y
            · subst y
              simp [k]
            · simp [k, hp]
      _ = f (p x) * mass x :=
          list_sum_indicator_present ys (p x)
            (f (p x) * mass x) hnd (hs x hx)
  calc
    (xs.map (fun x => f (p x) * mass x)).sum =
        (xs.map (fun x => (ys.map (k x)).sum)).sum := by
          congr 1
          apply List.map_congr_left
          intro x hx
          exact (hsingle x hx).symm
    _ = (ys.map (fun y => (xs.map (fun x => k x y)).sum)).sum :=
      list_sum_swap xs ys k
    _ = (ys.map (fun y =>
          f y * (xs.map (fun x => if p x = y then mass x else 0)).sum)).sum := by
          congr 1
          apply List.map_congr_left
          intro y hy
          exact list_sum_select_scaled xs p y (f y) mass

/-- For every real statistic of the retained order, its weighted
expectation under full priority permutations equals its expectation
under the intrinsic priority law of the retained set. This is the
event-level S017 consequence needed for the S018 greedy law. -/
theorem weighted_priority_projection_expectation
    (rates : α → ℝ) (hrates : ∀ v, 0 < rates v)
    (active retained : Finset α) (hsub : retained ⊆ active)
    (f : List α → ℝ) :
    ((active.toList.permutations).map (fun order =>
      f (order.filter (fun w => w ∈ retained)) * orderMass rates order)).sum =
    ((retained.toList.permutations).map (fun order =>
      f order * orderMass rates order)).sum := by
  classical
  let xs := active.toList.permutations
  let ys := retained.toList.permutations
  have hgroup := weighted_list_projection_sum xs ys
    (fun order : List α => order.filter (fun w => w ∈ retained))
    (orderMass rates) f
    (List.nodup_permutations retained.toList (Finset.nodup_toList retained))
    (fun order ho => filtered_full_order_is_retained_permutation
      active retained hsub order ho)
  calc
    _ = (ys.map (fun order => f order *
          projectedOrderMass rates active retained order)).sum := by
            rw [hgroup]
            rfl
    _ = (ys.map (fun order => f order * orderMass rates order)).sum := by
          congr 1
          apply List.map_congr_left
          intro order ho
          rw [projectedOrderMass_eq_orderMass rates hrates
            active retained order hsub ho]
    _ = _ := rfl

end InverseGreedy
