# S025 — Genuine exponential mass of real clock bin cells (2026-11-03)

## Precise claim and status

The target formal statement is in
`InverseGreedy/ExpBinCells.lean`, imported by
`InverseGreedy.lean`. **Machine-checked status is determined by
the exact final GitHub Actions commit**; a written proof, a source
file, or a prior passing CI run is insufficient.

For every **real** rate `r>0`, width `δ>0`, and
natural number `k`, write `q=exp(-r δ)`.
Let `T` have Mathlib's *actual* exponential distribution
`expMeasure r`. Then

```
P(k δ < T ≤ (k+1) δ) = (1-q) q^k.
```

This is a probability formula for a concrete measurable half-open
**real interval**, not an assertion that a particular `Nat.floor`
map or an independent family of binned variables has already been
formalised.

## Proof from the genuine measure

S024 gives, for `0≤t`, the exact identity

```
expMeasure r (Ioi t) = ENNReal.ofReal (exp(-r*t)).
```

If `0≤a≤b`, the measurable set-theoretic identity

```
Ioc a b = (Ioi a) \ (Ioi b)
```

and finiteness of the probability measure give the *actual measure*
difference formula. The survival theorem yields

```
P(a < T ≤ b) = exp(-r*a) - exp(-r*b).
```

The proof uses the real nonnegativity of the right survival term
in `ENNReal.ofReal_sub` to justify subtraction. It does not
postulate a geometric distribution, use S018's priority law, or
assume the final race probability.

Substituting `a=kδ`, `b=(k+1)δ`, and using
`exp(x+y)=exp(x)exp(y)`, induction proves
`exp(-r*kδ)=q^k`. The difference is

```
q^k - q^(k+1) = (1-q)q^k.
```

The case `k=0` follows with no exceptional algebra.

**Endpoint convention:** these proof cells are
`(kδ,(k+1)δ]` rather than the more familiar floor cells
`[kδ,(k+1)δ)`. S019's
`expMeasure_point_null` ensures that every individual endpoint
has zero mass, so the two conventions have identical probabilities.
The measurable `Nat.floor` random-variable law and a formal
identification of the two cell events up to a null set remain
separate Lean tasks.

## Finite-product and two-clock boundary

The S020 genuine product law already gives every coordinate its
actual exponential marginal. Transporting the proved interval
theorem through the measurable `Function.eval` projection yields
the same cell law for any specified coordinate. This transport is
part of the S025 targeted imported code once validated.

For actual independent coordinates the bin box masses should
multiply; to establish the *joint distribution of all binned
coordinates* formally, one still needs a measurable map and
independence-under-composition theorem, or direct product cylinder
proofs. In particular this session does **not** infer

```
P(T_r < T_s) = r/(r+s)
```

from the cell identities alone. The pair comparison requires an
exact geometric-series summation, explicit same-bin collision
control, and a `δ→0` limit (or direct exponential-density integral),
as proved informally in S023.

## Independent exact checks

`tests/test_s025.py` checks true-survival-derived bin-cell
identities in exact `Fraction` arithmetic at widths
`δ=-log(1-1/n)` and positive integer rates.
It separately checks finite-cell partition remainders,
finite-coordinate product-box algebra including empty/singleton
families, and an independent finite-sum/remainder calculation
for two-clock strict-bin winners. These are algebraic regression
tests, **not substitutes for real-measure proofs**, and do not
extend formal results to all rates on their own.

## Next obligations

1. Formalise a measurable natural-valued floor/bin map on the
   nonnegative support; prove inverse-images equal floor cells
   up to endpoint-nullity, then derive the actual geometric PMF.
2. Lift the bin map to the finite product and prove independence
   of all binned coordinates and two-clock strict-bin/collision
   events from genuine `Measure.pi`.
3. Prove the collision bound and continuous two-clock ratio
   `r/(r+s)`; afterwards formalise arbitrary complete chambers
   and the measurable greedy sorting pushforward.

The connected six-vertex atlas remains
**90 EGU / 8 non-EGU / 45 unresolved**.
No independent priority or novelty assertion is made.
