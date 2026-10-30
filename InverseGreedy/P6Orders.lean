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

/-- Predicate asserting that the output {1,4} exactly matches
the two independent triple-first events for one priority order. -/
def p6MiddleAgreement (o : List (Fin 6)) : Bool :=
  decide (greedyOutput p6Neighbours o = ({1, 4} : Finset (Fin 6)) ↔
    p6LeftFirst o ∧ p6RightFirst o)

/-- Predicate asserting that both outer-output events exclude
each of the two triple-first events. -/
def p6OuterAgreement (o : List (Fin 6)) : Bool :=
  decide (((greedyOutput p6Neighbours o = ({0, 2, 5} : Finset (Fin 6))) ∨
    (greedyOutput p6Neighbours o = ({0, 3, 5} : Finset (Fin 6)))) →
    (¬ p6LeftFirst o ∧ ¬ p6RightFirst o)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Kernel evaluation of all 720 ordered greedy-output event matches. -/
theorem p6_middle_pair_event_for_all_orders :
    ((List.finRange 6).permutations.all p6MiddleAgreement) = true := by
  decide

/-- Kernel evaluation of all 720 outer-output event inclusions. -/
theorem p6_outer_outputs_force_complement_events :
    ((List.finRange 6).permutations.all p6OuterAgreement) = true := by
  decide

end InverseGreedy
