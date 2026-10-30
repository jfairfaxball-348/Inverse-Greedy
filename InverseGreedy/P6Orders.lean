import InverseGreedy.FiniteRace

/-!
# P6 finite-order event certificates

These propositions enumerate all 6! priority permutations, using
Lean's kernel reduction (`decide`), not native_decide.
They certify *combinatorial greedy-output events*, not yet the
weighted probabilities of those events.
-/
namespace InverseGreedy

/-- Neighbour sets of path 0--1--2--3--4--5. -/
def p6Neighbours (v : Fin 6) : Finset (Fin 6) :=
  match v.val with
  | 0 => {1}
  | 1 => {0, 2}
  | 2 => {1, 3}
  | 3 => {2, 4}
  | 4 => {3, 5}
  | 5 => {4}
  | _ => ∅

def p6LeftFirst (o : List (Fin 6)) : Prop :=
  o.idxOf 1 < o.idxOf 0 ∧ o.idxOf 1 < o.idxOf 2

def p6RightFirst (o : List (Fin 6)) : Prop :=
  o.idxOf 4 < o.idxOf 3 ∧ o.idxOf 4 < o.idxOf 5

/-- For every one of the 720 permutations, output {1,4} exactly
when the two disjoint triples have their central vertex first. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem p6_middle_pair_event_for_all_orders :
    ∀ o ∈ (List.finRange 6).permutations,
      (greedyOutput p6Neighbours o = ({1, 4} : Finset (Fin 6)) ↔
         p6LeftFirst o ∧ p6RightFirst o) := by
  decide

/-- Both outputs {0,2,5} and {0,3,5} preclude each of the
two central-first triple events. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem p6_outer_outputs_force_complement_events :
    ∀ o ∈ (List.finRange 6).permutations,
      ((greedyOutput p6Neighbours o = ({0, 2, 5} : Finset (Fin 6)) ∨
        greedyOutput p6Neighbours o = ({0, 3, 5} : Finset (Fin 6))) →
        ¬ p6LeftFirst o ∧ ¬ p6RightFirst o := by
  decide

end InverseGreedy
