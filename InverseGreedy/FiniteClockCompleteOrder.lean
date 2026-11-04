import InverseGreedy.FiniteClockGapInverse

/-!
# S038: certified complete clock orders and admissible gap coordinates

The input is not an arbitrary list: `CompleteClockOrder` carries
a concrete equivalence between list positions and **all** vertices,
with a proof that the equivalence agrees with the list entries.
It therefore rules out missing and repeated coordinates without
silently treating an arbitrary list as a permutation.

This module transports S035's strict-bin admissibility condition to
S037's proved finite gap/bin equivalence. It does *not* evaluate
the infinite geometric sum or assert a continuous-clock order law.
-/

namespace InverseGreedy

/-- A list of clock coordinates certified to contain each coordinate
exactly once. The positional equivalence is an explicit witness. -/
structure CompleteClockOrder {ι : Type*} (order : List ι) where
  index : Fin order.length ≃ ι
  agrees : ∀ j : Fin order.length, order[j] = index j

/-- Complete clock orders never repeat coordinates in distinct positions. -/
theorem CompleteClockOrder.positions_injective
    {ι : Type*} {order : List ι} (h : CompleteClockOrder order) :
    Function.Injective (fun j : Fin order.length => order[j]) := by
  intro a b hab
  apply h.index.injective
  calc
    h.index a = order[a] := (h.agrees a).symm
    _ = order[b] := hab
    _ = h.index b := h.agrees b

/-- Complete clock orders include every coordinate, with no omissions. -/
theorem CompleteClockOrder.positions_surjective
    {ι : Type*} {order : List ι} (h : CompleteClockOrder order) :
    Function.Surjective (fun j : Fin order.length => order[j]) := by
  intro i
  obtain ⟨j, hj⟩ := h.index.surjective i
  exact ⟨j, by simpa only [h.agrees j] using hj⟩

/-- Pull a bin assignment back along the certified positional equivalence. -/
def completeClockOrderBinEquiv
    {ι : Type*} {order : List ι} (h : CompleteClockOrder order) :
    (ι → ℕ) ≃ (Fin order.length → ℕ) where
  toFun bins j := bins (h.index j)
  invFun k i := k (h.index.symm i)
  left_inv := by
    intro bins
    funext i
    simp
  right_inv := by
    intro k
    funext j
    simp

/-- A complete clock order's admissibility predicate is exactly strict
monotonicity in its positional coordinates. -/
theorem strictBinAssignment_iff_strictMono
    {ι : Type*} {order : List ι}
    (h : CompleteClockOrder order) (bins : ι → ℕ) :
    strictBinAssignment order bins ↔
      StrictMono (completeClockOrderBinEquiv h bins) := by
  constructor
  · intro hb a b hab
    have hl := hb a b hab
    simpa only [completeClockOrderBinEquiv, h.agrees a, h.agrees b] using hl
  · intro hb a b hab
    have hl := hb hab
    simpa only [completeClockOrderBinEquiv, h.agrees a, h.agrees b] using hl

/-- The admissible vertex-indexed assignments are equivalent to
strictly increasing bins indexed by their certified positions. -/
def completeClockOrderValidBinEquiv
    {ι : Type*} {order : List ι} (h : CompleteClockOrder order) :
    {bins : ι → ℕ // strictBinAssignment order bins} ≃
      {k : Fin order.length → ℕ // StrictMono k} where
  toFun bins :=
    ⟨completeClockOrderBinEquiv h bins.1,
      (strictBinAssignment_iff_strictMono h bins.1).mp bins.2⟩
  invFun k :=
    ⟨(completeClockOrderBinEquiv h).symm k.1,
      (strictBinAssignment_iff_strictMono h _).mpr (by
        simpa using k.2)⟩
  left_inv := by
    intro bins
    apply Subtype.ext
    exact (completeClockOrderBinEquiv h).symm_apply_apply bins.1
  right_inv := by
    intro k
    apply Subtype.ext
    exact (completeClockOrderBinEquiv h).apply_symm_apply k.1

/-- Compose the certified full-coordinate order with S037's genuine
finite gap/bin equivalence. The result works for empty, singleton,
and larger finite index types. -/
def completeClockOrderGapEquiv
    {ι : Type*} {order : List ι} (h : CompleteClockOrder order) :
    {bins : ι → ℕ // strictBinAssignment order bins} ≃
      (Fin order.length → ℕ) :=
  (completeClockOrderValidBinEquiv h).trans
    (finiteGapBinEquiv order.length).symm

end InverseGreedy
