# S030 — genuine continuous exponential race via a zero-width bin squeeze

**Date:** 2026-11-03. Branch: `s030-continuous-race-limit`.

## Analytic rate-ratio lemma

For strictly positive real rates `r,s` and width `δ>0`, S028/S029
proved (for the *actual* product measure
`independentExpPair r s = expMeasure r ⊗ expMeasure s`) the identities

```text
W(δ) = P(ceil(T_r/δ)<ceil(T_s/δ))
     = ((1-exp(-rδ))*exp(-sδ))/(1-exp(-(r+s)δ)),

C(δ) = P(ceil(T_r/δ)=ceil(T_s/δ))
     = ((1-exp(-rδ))*(1-exp(-sδ)))/(1-exp(-(r+s)δ)).
```

Because `exp` is real differentiable and `exp(0)=1`, for any real
`a`, `(1-exp(-aδ))/δ → a` as `δ→0+`. Thus, with the nonzero
denominator limit `r+s>0`,

```text
W(δ)
 = [(1-exp(-rδ))/δ] / [(1-exp(-(r+s)δ))/δ] * exp(-sδ)
 → [r/(r+s)]*1 = r/(r+s).
```

S029's true-measure pointwise set inclusions give

```text
W(δ) ≤ P(T_r<T_s) ≤ W(δ) + C(δ)
```

with no exception for the zero bin, negative reals or bin endpoints.
The certified collision estimate `C(δ) ≤ δ*min(r,s)` tends to zero.
Passing to the limit in `ℝ≥0∞` and using uniqueness of limits yields
the *genuine* product-measure theorem:

```text
P(T_r<T_s) = ENNReal.ofReal (r/(r+s)).
```

This argument does **not** replace the actual exponential clocks with an
assumed Plackett–Luce or geometric measure. S030's
`InverseGreedy/ContinuousRaceLimit.lean` implements the differentiated
initial slope, the real fraction's right-hand limit, its `ENNReal.ofReal`
transport and the measured-event squeeze. The exact source commit `0144a168dd0dfd0ff90d4ea5f089f0bbc55ed319`
was verified by the full imported Lean build and complete Python/exact/
connected-n≤6 census in both [push 41647056971](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647056971)
and [PR 41647064745](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647064745).
The code checkpoint is certified; final documentation-head and merge
verification remain a separate release gate.

## Independent regression

`tests/test_s030.py` checks the symbolic right limits with exact SymPy
expressions, the three-way bin partition, and the first-order terms

```text
(W(δ) - r/(r+s))/δ → -r*s/(2*(r+s)),
C(δ)/δ → r*s/(r+s).
```

These tests independently detect sign or rate-order regressions but are
not substitutes for a measure-theoretic formal proof.

## Remaining programme boundary

Even a checked two-clock theorem would *not* give the complete genuine
finite clock-permutation chamber formula, a measurable total sorting map
with canonical tie breaks, or the actual real-clock greedy-output
pushforward. These are the next formal obligations. The connected-n≤6
atlas is unchanged: 90 EGU, 8 non-EGU, 45 unresolved. Novelty not certified.
