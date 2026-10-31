import InverseGreedy.PriorityOutputLaw

/-!
# S013: exact first-head conditioning for weighted finite priority orders

The full Mathlib List.permutations enumeration is partitioned by its
unique first vertex. The following weighted identity works for an
arbitrary test function of the first vertex and remaining order.
It is a law-level conditional head factorisation, not yet arbitrary
subset deletion consistency or the greedy pushforward theorem.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

private theorem head_sum_flatMap (xs : List α)
    {β : Type*} (f : α → List β) (g : β → ℝ) :
    ((xs.flatMap f).map g).sum =
      (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih => simp [ih]

private theorem head_sum_scale (xs : List (List α))
    (c : ℝ) (f : List α → ℝ) :
    (xs.map (fun x => c * f x)).sum =
      c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- For any full priority permutation beginning at v, its mass
factors exactly as the first-choice mass times the remaining
permutation mass. No positivity assumption is needed for the identity. -/
theorem orderMass_cons_full_tail (rates : α → ℝ)
    (active : Finset α) (v : α) (hv : v ∈ active)
    (tail : List α)
    (ht : tail ∈ (active.erase v).toList.permutations) :
    orderMass rates (v :: tail) =
      firstChoice rates active v * orderMass rates tail := by
  obtain ⟨htnodup, htset⟩ :=
    (mem_full_priority_permutations_iff (active.erase v) tail).mp ht
  have hvnot : v ∉ tail.toFinset := by
    rw [htset]
    simp
  have hn : (v :: tail).Nodup :=
    List.nodup_cons.mpr ⟨by simpa using hvnot, htnodup⟩
  have hset : (v :: tail).toFinset = active := by
    calc
      (v :: tail).toFinset = insert v tail.toFinset := by simp
      _ = insert v (active.erase v) := by rw [htset]
      _ = active := Finset.insert_erase hv
  calc
    orderMass rates (v :: tail) =
        orderLeafMass rates (v :: tail) :=
          (orderLeafMass_eq_orderMass rates (v :: tail) hn).symm
    _ = firstChoice rates active v * orderLeafMass rates tail := by
          change firstChoice rates (v :: tail).toFinset v *
            orderLeafMass rates tail = _
          rw [hset]
    _ = firstChoice rates active v * orderMass rates tail := by
          rw [orderLeafMass_eq_orderMass rates tail htnodup]

/-- Every nonempty full priority order has a unique head, so a
weighted test on its head and tail decomposes into first-choice
masses times the corresponding weighted tail sums. This is for
the *actual* List.permutations list with no overcounting. -/
theorem full_priority_weighted_head_sum
    (rates : α → ℝ) (active : Finset α)
    (he : active ≠ ∅) (test : α → List α → ℝ) :
    ((active.toList.permutations).map (fun order =>
      match order with
      | [] => (0 : ℝ)
      | v :: tail => orderMass rates (v :: tail) * test v tail)).sum =
    (active.toList.map (fun v =>
      firstChoice rates active v *
        (((active.erase v).toList.permutations).map
          (fun tail => orderMass rates tail * test v tail)).sum)).sum := by
  have hperm := full_priority_permutations_head_decomposition active
  calc
    ((active.toList.permutations).map (fun order =>
        match order with
        | [] => (0 : ℝ)
        | v :: tail => orderMass rates (v :: tail) * test v tail)).sum =
      ((headSplitOrders active).map (fun order =>
        match order with
        | [] => (0 : ℝ)
        | v :: tail => orderMass rates (v :: tail) * test v tail)).sum :=
          (hperm.map _).sum_eq
    _ = (active.toList.map (fun v =>
        (((active.erase v).toList.permutations.map (List.cons v)).map
          (fun order => match order with
            | [] => (0 : ℝ)
            | w :: tail => orderMass rates (w :: tail) * test w tail)).sum)).sum := by
          simp only [headSplitOrders, if_neg he]
          exact head_sum_flatMap active.toList
            (fun v => (active.erase v).toList.permutations.map (List.cons v))
            (fun order => match order with
              | [] => (0 : ℝ)
              | w :: tail => orderMass rates (w :: tail) * test w tail)
    _ = (active.toList.map (fun v =>
        firstChoice rates active v *
          (((active.erase v).toList.permutations).map
            (fun tail => orderMass rates tail * test v tail)).sum)).sum := by
          congr 1
          apply List.map_congr_left
          intro v hv
          have hmap :
              (((active.erase v).toList.permutations.map (List.cons v)).map
                  (fun order => match order with
                    | [] => (0 : ℝ)
                    | w :: tail => orderMass rates (w :: tail) * test w tail)) =
                ((active.erase v).toList.permutations.map
                  (fun tail => firstChoice rates active v *
                    (orderMass rates tail * test v tail))) := by
            simp only [List.map_map]
            apply List.map_congr_left
            intro tail ht
            simp only [Function.comp_apply]
            rw [orderMass_cons_full_tail rates active v
              (Finset.mem_toList.mp hv) tail ht]
            ring
          rw [hmap]
          exact head_sum_scale (active.erase v).toList.permutations
            (firstChoice rates active v)
            (fun tail => orderMass rates tail * test v tail)

end InverseGreedy
