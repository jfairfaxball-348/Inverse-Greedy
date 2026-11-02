import InverseGreedy.PriorityProjectionPushforward

/-!
# S018: exact output-event pushforward and deterministic residual support

These are consequences of S017's full weighted order projection.
No random continuous clock model is assumed.
-/
namespace InverseGreedy
variable {α : Type*} [DecidableEq α]

/-- The genuinely weighted probability of any greedy-output event
is unchanged by projecting complete priorities onto a retained set. -/
theorem weighted_priority_filtered_greedy_event
    (rates : α → ℝ) (hrates : ∀ v, 0 < rates v)
    (neighbours : α → Finset α)
    (active retained target : Finset α) (hsub : retained ⊆ active) :
    ((active.toList.permutations).map (fun order =>
      if greedyOutput neighbours (order.filter (fun w => w ∈ retained)) = target
      then orderMass rates order else (0 : ℝ))).sum =
    priorityOutputMass rates neighbours retained target := by
  classical
  let f : List α → ℝ :=
    fun order => if greedyOutput neighbours order = target then 1 else 0
  have h := weighted_priority_projection_expectation
    rates hrates active retained hsub f
  calc
    _ = ((active.toList.permutations).map (fun order =>
          f (order.filter (fun w => w ∈ retained)) *
            orderMass rates order)).sum := by
          congr 1
          apply List.map_congr_left
          intro order ho
          simp [f, ite_mul]
    _ = ((retained.toList.permutations).map (fun order =>
          f order * orderMass rates order)).sum := h
    _ = priorityOutputMass rates neighbours retained target := by
          unfold priorityOutputMass
          congr 1
          apply List.map_congr_left
          intro order ho
          simp [f, ite_mul]

/-- The accepted greedy set cannot contain vertices not present in
the priority list. The statement allows arbitrary neighbour maps. -/
theorem greedyScan_subset_vertices (neighbours : α → Finset α) :
    ∀ (order : List α) (accepted : Finset α),
      order.foldl (greedyAccept neighbours) accepted ⊆
        accepted ∪ order.toFinset := by
  intro order
  induction order with
  | nil =>
      intro accepted
      simp
  | cons w tail ih =>
      intro accepted z hz
      have hz' := ih (greedyAccept neighbours accepted w) hz
      have hstep : greedyAccept neighbours accepted w ⊆ insert w accepted := by
        intro x hx
        unfold greedyAccept at hx
        split_ifs at hx
        · exact Finset.mem_insert_of_mem hx
        · exact hx
      rcases Finset.mem_union.mp hz' with ha | ht
      · rcases Finset.mem_insert.mp (hstep ha) with heq | hacc
        · apply Finset.mem_union.mpr
          exact Or.inr (by simp [heq])
        · apply Finset.mem_union.mpr
          exact Or.inl hacc
      · apply Finset.mem_union.mpr
        exact Or.inr (by simp [ht])

theorem greedyOutput_subset_vertices (neighbours : α → Finset α)
    (order : List α) :
    greedyOutput neighbours order ⊆ order.toFinset := by
  intro x hx
  have h := greedyScan_subset_vertices neighbours order ∅ x hx
  simpa [greedyOutput] using h

/-- Filtering a list with predicates that agree on its elements gives
exactly the same list, including order and multiplicity. -/
theorem list_filter_eq_of_iff (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (order : List α)
    (h : ∀ w ∈ order, p w ↔ q w) :
    order.filter p = order.filter q := by
  induction order with
  | nil => rfl
  | cons w tail ih =>
      have hw := h w (by simp)
      have ht : ∀ x ∈ tail, p x ↔ q x := by
        intro x hx
        exact h x (by simp [hx])
      by_cases hp : p w
      · have hq : q w := hw.mp hp
        simp [hp, hq, ih ht]
      · have hq : ¬q w := fun hqw => hp (hw.mpr hqw)
        simp [hp, hq, ih ht]

/-- On a complete ordering of active.erase v, deleting neighbours
of v is exactly restricting to afterChoice active v. -/
theorem residual_filter_eq_afterChoice
    (neighbours : α → Finset α) (active : Finset α)
    (v : α) (order : List α)
    (hsub : order.toFinset ⊆ active.erase v) :
    order.filter (fun w => w ∉ neighbours v) =
      order.filter (fun w => w ∈ afterChoice neighbours active v) := by
  classical
  apply list_filter_eq_of_iff
  intro w hw
  have hva : w ∈ active.erase v := hsub (by simpa using hw)
  obtain ⟨hneq, hactive⟩ := Finset.mem_erase.mp hva
  simp only [afterChoice, Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · intro hn
    exact ⟨hactive, fun hor => hor.elim (fun heq => hneq heq) hn⟩
  · intro hh
    exact fun hn => hh.2 (Or.inr hn)

end InverseGreedy
