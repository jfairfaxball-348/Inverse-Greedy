# S032 — finite-family genuine geometric-bin joint law

**Date:** 2026-11-03. PR #31. Imported Lean module:
`InverseGreedy/FiniteClockJointBins.lean`.

## New measured statement

For any finite index type `ι`, positive real rates `r_i`,
bin width `δ>0` and assignment `k : ι → ℕ`, define independent
real exponential clocks distributed under the *actual*
`finiteIndependentExp rates = Measure.pi (fun i => expMeasure r_i)`.
For the right-closed one-based ceiling bins
`Kδ(t) = Nat.ceil (t/δ)`, Lean states:

```text
P(∀ i, Kδ(T_i) = k_i+1)
 = ∏_i [(1 - exp(-r_i δ)) · exp(-r_i δ)^(k_i)].
```

Proof: the event is exactly the finite set rectangle
`Set.univ.pi (fun i => {t | Kδ(t)=k_i+1})`.
The actual Mathlib product-measure theorem `Measure.pi_pi`
evaluates its mass as the product of the one-dimensional cell
probabilities. S026's `expMeasure_clockCeilBin_succ` supplies
the genuine one-clock probability. Positivity establishes all
probability measure / sigma-finiteness instances. For empty `ι`,
the empty product and unique clock assignment both have mass one.

This is **not** a model built by declaring a priority permutation
law; the measure is the independent product of continuous Exp clocks.

## Actual pair chambers and repeated coordinates

For arbitrary indices `i,j`, the chamber `[i,j]` is exactly
`{ω | ω i < ω j}`. Thus S031/S030's true measured pair formula
gives `P(chamber [i,j]) = r_i/(r_i+r_j)` for `i ≠ j` and positive
rates. This does **not** require the ambient index type to have
cardinality two.

If a strict chamber list contains an identical vertex in two
different positions, it requires `T_i < T_i`; hence the event is
empty and has zero mass for *any* rate vector.

Independent exact regression `tests/test_s032.py` checks rational
finite geometric products / survival telescoping, deterministic
two-item chambers, repeated-index impossibility and strict-bin
order implications. Tests are not a replacement for the Lean theorem.

## Still open

The new theorem supplies masses of **individual joint bin
assignments**, not the sum over all assignments
`k_1 < k_2 < ... < k_m` defining a strictly ordered bin sequence.
That *finite-dimensional multiple geometric series* still needs a
formal summation theorem, followed by collision-union control,
width-to-zero limit and a full `n≥3` real-clock chamber formula.

A canonical total tie-broken measurable sorting function, identification
of all its fibres with strict real chambers outside the null tie set,
and its output-law pushforward via S018's
`priorityOutputMass_eq_finiteRaceLaw` are also unproved in Lean.

No new EGU graph classification, independent novelty claim, or
Palomar/arXiv action. Partial connected n≤6 atlas unchanged:
**90 EGU / 8 non-EGU / 45 unresolved**.
