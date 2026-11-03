# S031 — genuine finite-clock pair marginals and chamber bounds

**Date:** 2026-11-03. PR: #30. Module:
`InverseGreedy/FiniteClockPairOrder.lean` (imported by
`InverseGreedy.lean`).

## What S031 proves with genuine continuous clocks

Let `ι` be **any finite index type**, including the empty and singleton
types, and let `rates : ι → ℝ` with `∀ i, 0 < rates i`. Set

`μ = finiteIndependentExp rates = Measure.pi (fun i => expMeasure (rates i))`.

For any *distinct* `i,j : ι`, the already Lean-proved S022 pair-marginal
identity gives

```text
map (fun ω => (ω i, ω j)) μ
  = independentExpPair (rates i) (rates j).
```

The comparison event `{ω | ω i < ω j}` is the preimage of the
measurable `{p | p.1 < p.2}`. S030 evaluates the mass of that event
under the **actual exponential product**. Therefore

```text
μ {ω | ω i < ω j}
  = ENNReal.ofReal (rates i / (rates i + rates j)).
```

This is a real-clock theorem even when arbitrarily many additional
vertices are present; it is not a discrete PL law assertion.

For any finite list `order`, and any positions `a<b`, its strict
chamber `strictClockChamber order` is contained in
`{ω | ω (order[a]) < ω (order[b])}`. If the two named indices
are distinct, monotonicity of the *actual product measure* gives

```text
μ (strictClockChamber order)
  ≤ ENNReal.ofReal
      (rates (order[a]) /
       (rates (order[a]) + rates (order[b]))).
```

S031 also proves that the empty and singleton comparison lists give
`strictClockChamber [] = univ` and `strictClockChamber [i] = univ`,
and both events have mass one for the genuine finite product.

The code is compiled under full imported Lean CI only when its
specific exact SHA has a successful Lean job. See PR #30 for final
release-gate provenance.

## What these results **do not** establish

For `m ≥ 3`, pairwise ordering probabilities do **not** determine
all full-order chamber probabilities. For example, both (a) the
uniform law on six permutations of three symbols and (b) a 50/50
mixture of `(1,2,3)` and `(3,2,1)` give probability 1/2 for
each ordered-pair comparison, but have different masses on most
permutations. The S031 pairwise theorem cannot be promoted into the
full chamber formula without a separate argument.

The expected actual finite `m`-clock chamber formula is

```text
μ {T_i1 < ... < T_im}
  = ∏_(k=1)^m rates(i_k) / Σ_(j=k)^m rates(i_j)
```

when `[i1,...,im]` enumerates the entire index type. It holds
mathematically by independence and memorylessness, or by the rigorous
geometric-bin squeeze in `proof/S023_GEOMETRIC_BIN_CHAMBERS.md`.
For a density proof, change variables to gaps
`x_1=t_1`, `x_k=t_k-t_(k-1)`; the triangular change has Jacobian 1,
and the joint exponential density factors as

```text
(∏_k rates(i_k)) ·
  exp(- Σ_(k=1)^m x_k · (Σ_(j=k)^m rates(i_j))).
```

Integrating each `x_k≥0` yields the claimed product. This density
argument is **informal**, not an imported Lean measure proof.

One viable Lean strategy is to reuse S026's actual independent bin
variables, formalise the finite strict-bin geometric-gaps formula
from S023, and use S029's pair-collision upper bounds plus finite
subadditivity to squeeze every real chamber as width tends to zero.
This requires a *finite-dimensional* countable geometric sum, a
collision union bound, analytic convergence of finite products,
and set-level equivalence on collision-free samples.

After the chamber formula, define a canonical total sorting map with a
fixed index tie-breaker; prove measurable preimages for each complete
permutation; use S022 to discard the tie-null set. Only then can the
measured sorted-order law be combined with S018's discrete theorem
`priorityOutputMass_eq_finiteRaceLaw` to certify the **actual
continuous-clock greedy-output pushforward**. All of those steps are
currently **Lean-open**.

## Independent exact regression and research boundary

`tests/test_s031.py` checks with `Fraction` the empty/singleton
cases, all ordered-pair marginals obtained by summing complete
size-biased permutation weights (two to six vertices with strongly
unequal rates), and every required pair upper bound for every complete
six-vertex order. This checks the algebra of the *discrete* model;
the imported Lean theorem, not these tests, gives the genuine
continuous pair probability.

Connected n≤6 graph census remains 90 EGU / 8 non-EGU / 45 unresolved.
No new EGU classification or independent theorem novelty is claimed.
