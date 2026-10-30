import InverseGreedy.FiniteRace

/-!
# P6 combinatorial priority-order certificates

The two closed Boolean theorems enumerate every one of the 720
priority permutations using kernel evaluation. They are not proofs
of probabilistic independence or exponential-clock equivalence.
-/
namespace InverseGreedy

def p6Neighbours (v : Fin 6) : Finset (Fin 6) :=
  match v.val with
  | 0 => {1}
  | 1 => {0, 2}
  | 2 => {1, 3}
  | 3 => {2, 4}
  | 4 => {3, 5}
  | 5 => {4}
  | _ => ∅

/-- Whether 1 is first in its disjoint left triple. -/
def p6LeftFirst (o : List (Fin 6)) : Bool :=
  decide (o.idxOf 1 < o.idxOf 0) && decide (o.idxOf 1 < o.idxOf 2)

/-- Whether 4 is first in its disjoint right triple. -/
def p6RightFirst (o : List (Fin 6)) : Bool :=
  decide (o.idxOf 4 < o.idxOf 3) && decide (o.idxOf 4 < o.idxOf 5)

def p6MiddleAgreement (o : List (Fin 6)) : Bool :=
  decide (greedyOutput p6Neighbours o = ({1, 4} : Finset (Fin 6))) ==
    (p6LeftFirst o && p6RightFirst o)

def p6OuterAgreement (o : List (Fin 6)) : Bool :=
  (!(decide (greedyOutput p6Neighbours o = ({0, 2, 5} : Finset (Fin 6))) ||
    decide (greedyOutput p6Neighbours o = ({0, 3, 5} : Finset (Fin 6))))) ||
    (!p6LeftFirst o && !p6RightFirst o)

/-!
The global 720-permutation reduction is deliberately deferred:
ordinary `decide` gets stuck on `List.permutationsAux` under the
pinned toolchain. Do not treat this as a machine-checked equivalence.
The exhaustive independent Python check remains in tests/test_s003.py.
-/

/-- A simple exact worked example for the two central-first events. -/
theorem p6_middle_pair_example :
    greedyOutput p6Neighbours [1, 4, 0, 2, 3, 5] =
      ({1, 4} : Finset (Fin 6)) := by
  decide

/-- The two central-first flags in the same worked example. -/
theorem p6_middle_flags_example :
    p6LeftFirst [1, 4, 0, 2, 3, 5] = true ∧
    p6RightFirst [1, 4, 0, 2, 3, 5] = true := by
  decide

end InverseGreedy
