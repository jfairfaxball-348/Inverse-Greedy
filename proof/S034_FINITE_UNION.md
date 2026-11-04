# S034 — finite union inequality for genuine clock-bin collisions

**Date:** 2026-11-04. [PR #34](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/34). Proposed imported module: `InverseGreedy/FiniteClockBinUnion.lean`.

## Actual measure, hypotheses, statement

Let `ι` be finite, `r : ι → ℝ` have positive rates, and `δ>0`. The law is `finiteIndependentExp r`, Mathlib's genuine finite product of exponential measures. Let `order` be a finite list such that `order[a] ≠ order[b]` whenever `a<b`. The event `clockBinCollisionOnList δ order` says that at least one pair of distinct list positions has the **same actual ceiling bin**. The proposed theorem bounds its real-clock product-measure probability by

```text
∑ a : Fin order.length, ∑ b : Fin order.length,
  if a < b then ENNReal.ofReal (δ * min (r (order[a])) (r (order[b])))
  else 0
```

The statement is deliberately an ENNReal finite double sum (permitted by S034), so no unproved `ofReal` additivity or real-sum rewriting is needed. Complete permutations satisfy the distinctness hypothesis, but completeness is *not* necessary.

## Proof

For each pair of positions `a,b`, introduce the event `E(a,b)` equal to the true two-clock same-bin event when `a<b`, and empty otherwise. The union over all pairs is *exactly* the list collision event, including positions at zero or one elements. By `measure_iUnion_le` twice, and because the index types `Fin order.length` are finite, its genuine measure is at most the finite sum of measures of these `E(a,b)`.

For `a<b` the explicit distinctness hypothesis allows applying the S033 true product-measure pair bound
`finiteIndependentExp_pair_sameCeilBin_le_width_min_rate`; for other pairs `E(a,b)=∅` and its mass is zero. Monotonicity of `tsum` and `tsum_fintype` yield the displayed bound. S033's measured chamber sandwich then gives

```text
P(strictRealClockChamber(order))
  ≤ P(strictClockBinChamber(δ,order))
    + Σ_{a<b} ENNReal.ofReal(δ * min(rate_a,rate_b)).
```

Both are *actual measured clock* statements, never the postulated discrete Plackett–Luce sorting law. For a fixed distinct finite order, the finite sum is `O(δ)`. Repeating one index invalidates the independent-pair bound (one clock always shares its bin with itself); this is why distinctness is an explicit condition. Empty and singleton lists have zero pair sum and zero collision event.

## Scope, tests and remaining obligations

`tests/test_s034.py` independently checks finite rational-geometric truncations for all permutations up to four vertices, empty and singleton boundaries, necessity of excluding repeated indices, and linear width scaling. These exact calculations are not Lean evidence for the actual continuous product law. The Lean claim must be compiled in the full imported build and certified at the exact final PR head in both push and PR Actions.

**Not yet formalised:** strict positive-bin complete-chamber probability as a true countable series; the multiple-gap geometric product and its zero-width limit; any general `n≥3` continuous-clock chamber closed formula; measurable tie-broken sorting and continuous greedy-output pushforward. No atlas promotion or novelty registration. Snapshot **90/8/45**.
