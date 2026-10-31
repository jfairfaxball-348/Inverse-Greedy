import InverseGreedy.FullPermutationDecomposition

/-!
# S011: normalisation of the actual weighted priority-permutation list

The proof sums the leaf mass over Mathlib's actual `List.permutations`,
not just an abstract head-choice tree. The preceding module supplies
unique-head decomposition including multiplicities.
This says nothing yet about the greedy-output pushforward or
the continuous exponential-clock law.
-/

namespace InverseGreedy

variable {α : Type*} [DecidableEq α]

private theorem sum_map_flatMap (xs : List α)
    {β : Type*} (f : α → List β) (g : β → ℝ) :
    ((xs.flatMap f).map g).sum =
      (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih => simp [ih]

private theorem sum_map_scale (xs : List α) (c : ℝ) (f : α → ℝ) :
    (xs.map (fun x => c * f x)).sum =
      c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- A full priority leaf has head-choice denominator equal to the
sum of the rates of the full active set, not just a suffix of the scan. -/
private theorem leaf_head_mass (rates : α → ℝ)
    (active : Finset α) (v : α) (hv : v ∈ active)
    (tail : List α)
    (htail : tail ∈ (active.erase v).toList.permutations) :
    orderLeafMass rates (v :: tail) =
      firstChoice rates active v * orderLeafMass rates tail := by
  have hset := (mem_full_priority_permutations_iff (active.erase v) tail).mp htail |>.2
  have hactive : (v :: tail).toFinset = active := by
    calc
      (v :: tail).toFinset = insert v tail.toFinset := by simp
      _ = insert v (active.erase v) := by rw [hset]
      _ = active := Finset.insert_erase hv
  change firstChoice rates (v :: tail).toFinset v *
    orderLeafMass rates tail = _
  rw [hactive]

/-- Structural weighted head decomposition of the full list, not a
finite enumeration or a `decide` proof. -/
private theorem leaf_sum_head (rates : α → ℝ)
    (active : Finset α) (he : active ≠ ∅) :
    ((active.toList.permutations).map (orderLeafMass rates)).sum =
      ((active.toList).map (fun v =>
        firstChoice rates active v *
        (((active.erase v).toList.permutations).map
          (orderLeafMass rates)).sum)).sum := by
  have hperm := full_priority_permutations_head_decomposition active
  calc
    ((active.toList.permutations).map (orderLeafMass rates)).sum =
        ((headSplitOrders active).map (orderLeafMass rates)).sum :=
          (hperm.map (orderLeafMass rates)).sum_eq
    _ = ((active.toList).map (fun v =>
          (((active.erase v).toList.permutations.map (List.cons v)).map
            (orderLeafMass rates)).sum)).sum := by
          simp only [headSplitOrders, if_neg he]
          exact sum_map_flatMap active.toList
            (fun v => (active.erase v).toList.permutations.map (List.cons v))
            (orderLeafMass rates)
    _ = ((active.toList).map (fun v =>
          firstChoice rates active v *
          (((active.erase v).toList.permutations).map
            (orderLeafMass rates)).sum)).sum := by
          apply List.map_congr_left
          intro v hv
          have hva : v ∈ active := Finset.mem_toList.mp hv
          have hmap :
              (((active.erase v).toList.permutations.map (List.cons v)).map
                  (orderLeafMass rates)) =
              ((active.erase v).toList.permutations.map
                  (fun tail => firstChoice rates active v *
                    orderLeafMass rates tail)) := by
            simp only [List.map_map]
            apply List.map_congr_left
            intro tail ht
            exact leaf_head_mass rates active v hva tail ht
          rw [hmap]
          exact sum_map_scale (active.erase v).toList.permutations
            (firstChoice rates active v) (orderLeafMass rates)

/-- For every finite vertex set and strictly positive real rate
assignment, the masses of *all actual full priority permutations*
sum to one, with no factorial enumeration in the proof. -/
theorem full_priority_orderMass_sum_one (rates : α → ℝ)
    (hrates : ∀ v, 0 < rates v) :
    ∀ active : Finset α,
      ((active.toList.permutations).map (orderMass rates)).sum = 1 := by
  have hleaf : ∀ fuel (active : Finset α), active.card ≤ fuel →
       ((active.toList.permutations).map (orderLeafMass rates)).sum = 1 := by
    intro fuel
    induction fuel with
    | zero =>
        intro active hcard
        have he : active = ∅ :=
          Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
        subst active
        simp [orderLeafMass]
    | succ fuel ih =>
        intro active hcard
        by_cases he : active = ∅
        · subst active
          simp [orderLeafMass]
        · rw [leaf_sum_head rates active he]
          have hmass : ∀ v ∈ active,
              (((active.erase v).toList.permutations).map
                (orderLeafMass rates)).sum = 1 := by
            intro v hv
            have hs := Finset.card_erase_add_one hv
            apply ih (active.erase v)
            omega
          simp_rw [show ∀ v ∈ active.toList,
              (((active.erase v).toList.permutations).map
                (orderLeafMass rates)).sum = 1 from
              fun v hv => hmass v (Finset.mem_toList.mp hv)]
          simp only [mul_one]
          have hpos : active.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
          convert firstChoice_sum_one rates active hpos
              (by intro v hv; exact hrates v) using 1
          simp [Finset.sum]
  intro active
  have hmass := hleaf active.card active (le_refl _)
  have hpoint : ∀ order ∈ active.toList.permutations,
      orderLeafMass rates order = orderMass rates order := by
    intro order ho
    exact full_priority_leaf_mass_eq_orderMass rates active order ho
  calc
    ((active.toList.permutations).map (orderMass rates)).sum =
        ((active.toList.permutations).map (orderLeafMass rates)).sum := by
          congr 1
          apply List.map_congr_left
          intro order ho
          exact (hpoint order ho).symm
    _ = 1 := hmass

end InverseGreedy
