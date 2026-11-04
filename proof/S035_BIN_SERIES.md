# S035 — genuine countable strict-bin chamber series

**Date:** 2026-11-04. [PR #35](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/35).

## Goal and exact progress

The independent Exp-clock product measure is the **actual**
`finiteIndependentExp rates` on all real clock coordinates. In S032, Lean
proved a product formula for the probability of any fixed simultaneous
positive one-based ceiling-bin assignment. S033/S034 supplied a true
real-clock/strict-bin chamber sandwich and finite collision bound.

S035's imported `FiniteClockBinSeries.lean` is intended to close the
**countable additivity step**. Its key events for `bins : ι → ℕ` are

```text
C(bins) = {ω : ι → ℝ | ∀ i, Kδ(ω_i) = bins(i)+1}
Admissible(order,bins) := ∀ a<b, bins(order[a])<bins(order[b])
```

For any finite index type `ι` and *any* proposed list (it need not be a
permutation), the following is a literal pointwise set equality:

```text
strictBinChamber(δ,order) ∩ {ω | ∀ i, Kδ(ω_i) ≠ 0}
  = ⋃_(bins : ι → ℕ, admissible(order,bins)) C(bins).
```

The proof constructs `bins(i)=Kδ(ω_i)-1` on the positive event.
It also proves individual cylinders measurable and distinct cylinders
disjoint (distinct bin-index functions force incompatible actual clock
values). Thus countable additivity and S032's genuine joint-cylinder
formula imply

```text
P(strictBinChamber(δ,order) ∩ all-positive-bins)
 = Σ_(bins : ι → ℕ, admissible(order,bins))
     ∏_(i : ι) [(1-exp(-r_i δ)) exp(-r_i δ)^bins(i)].
```

By S033, the union of all zero-bin coordinate events has probability
zero under positive-rate independent exponential clocks, including
the empty-index case. Finite measure monotonicity and subadditivity
therefore identify the left side with the **full** strict-bin chamber
probability. This is a genuine countable geometric-bin formula, not a
new probability model defined to have the required discrete order law.

## What this does *not* prove

The right side has not yet been **evaluated in imported Lean** as the
closed finite product; its exact gap-coordinate derivation is informal
in `proof/S032_JOINT_BINS.md`. For a complete distinct enumeration
`order=[i₁,...,i_m]`, let `q_j=exp(-r_(i_j) δ)`.
The target remaining algebra is

```text
Σ_(0≤k₁<...<k_m) ∏_j (1-q_j)q_j^k_j
= [∏_j (1-q_j)q_j^(j-1)] /
  [∏_(a=1)^m (1-∏_(j≥a)q_j)].
```

It requires the bijective change to nonnegative gaps
`k_j=j-1+Σ_(a≤j)d_a` and finite-product multiple-geometric series.
Independent tests `tests/test_s035.py` check exact rational
finite-section factorisation, truncation monotonicity, normalization,
and empty/singleton/duplicate-list boundaries. Tests are **not** a
formal probability or continuous limit proof.

Even the full strict-bin finite-product formula does not immediately
imply the true real-clock chamber law. One still needs the
`δ→0+` limit in Lean, together with S034's true collision
`O(δ)` bound, to obtain for complete nonrepeating orders

```text
P(strictClockChamber(order)) = ENNReal.ofReal(orderMass rates order).
```

Finally one needs a total deterministic, tie-broken measurable
sorting map, strict-chamber fibre identification off null ties,
and the continuous-clock greedy-output pushforward using S018.
Do not announce those theorems as Lean-proven.

## Exactness, verification, and graph atlas

The mathematical derivation is valid for strictly positive rates,
positive width and finite vertex index sets. Boundary events for
the nonpositive/zero ceiling bin are handled through genuine nullity
rather than false event equality.

Release verification: **exact-final-head dual-green in both push and PR Actions; squash-merged**. Exact final PR head `2edf01c7da105403ac75c8959fce292a34da34ce` passed **complete imported Lean** and **full Python/exact/certified connected n≤6 census** in both [push Actions 41823819781](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41823819781) and [PR Actions 41823826234](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41823826234); [PR #35](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/35) was squash-merged to `main` as `4aa7459c5bd1a66a612134d106c467ff3d2d7000`. No published or priority novelty claim.
Connected n≤6 census remains **90 EGU / 8 non-EGU / 45 unresolved**;
snapshot flags unchanged.
