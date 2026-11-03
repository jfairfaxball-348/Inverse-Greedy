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

## Complete strict-bin series: informal derivation for S033

The finite-family joint-cylinder theorem allows a fully explicit
*mathematical* summation, which is **not yet a Lean theorem**.
Fix a permutation `order=[i₁,…,iₘ]` of `m` indices and write
`q_j = exp(-r_(i_j) δ)`, so `0<q_j<1`.
On the positive (one-based) bins, put `k_j = Kδ(T_(i_j))-1`.
The strict-bin chamber corresponds to
`0 ≤ k₁ < k₂ < ⋯ < kₘ` with joint summand
`∏_j (1-q_j)q_j^(k_j)`.

The gap variables

```text
d₁ = k₁ ≥ 0;
d_j = k_j - k_(j-1) - 1 ≥ 0,  j≥2
```

are a bijection to `ℕ^m`, with
`k_j = (j-1) + ∑_(a≤j) d_a`.
Hence, defining `Q_a=∏_(j≥a) q_j`,

```text
Pr(strictly increasing nonzero bins)
  = ∏_(j=1)^m (1-q_j)q_j^(j-1)
      / ∏_(a=1)^m (1-Q_a).
```

The empty product is 1. This follows from `m` absolutely
convergent geometric series; every `Q_a` lies strictly in `(0,1)`.
It also includes the known two-clock formula (S028). For finite
truncations `0≤d_a<N`, replace `1/(1-Q_a)` by
`(1-Q_a^N)/(1-Q_a)`. `tests/test_s032.py` checks this
factorisation with exact rational arithmetic for up to four clocks.
No numerics or informal series are being passed off as Lean results.

As `δ↓0`, `1-q_j ∼ r_(i_j)δ`,
`1-Q_a ∼ δ∑_(j≥a)r_(i_j)` and
`q_j^(j-1)→1`, yielding `orderMass rates order`.
The true *real-clock* chamber differs from the bin chamber only
on a collision of at least one pair of bins (plus null zero-bin
events). A finite union bound and S029's true collision estimate
then give a quantitative route to the same limit. Formalising
this gap-series identity, union bound and limit is the S033 task.

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
