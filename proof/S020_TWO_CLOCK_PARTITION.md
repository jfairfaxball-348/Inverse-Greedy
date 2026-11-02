# S020 — Strict two-clock race events from genuine exponential measures

**Scope:** This is a measure-theoretic intermediate result, *not* the general
rate-ratio theorem and not the finite-clock sorting pushforward. The
continuous product law and the zero-tie event are from S019.

Let r,s > 0, μ = expMeasure(r) ⊗ expMeasure(s) on ℝ².
Define A = {(x,y) : x<y}, B = {(x,y) : y<x} and D={(x,y):x=y}.
Both A and B are measurable open sets, and D is a measurable closed set.
They are pairwise disjoint and A∪B∪D=ℝ² by trichotomy.
S019 proves μ(D)=0 by absolute continuity of each exponential marginal
and product-measure null-diagonal arguments. Since μ is a probability
measure, countable additivity gives

    μ(A) + μ(B) = μ(ℝ²) - μ(D) = 1.

When r=s, the measure μ is invariant under coordinate swap σ(x,y)=(y,x)
by Mathlib's genuine product-measure symmetry, and σ⁻¹(A)=B.
Thus μ(A)=μ(B), and, combining the two identities, each equals 1/2
(as a mathematical consequence, not yet a separately formalized
ENNReal numeral identity).

Lean module: `InverseGreedy/ContinuousRacePartition.lean`. Its
actual verification status is governed by the exact SHA and Actions
run in `CLAIMS.md` and `HANDOVER.md`.

## Remaining gap: arbitrary unequal rates

The exact analytic calculation is

    μ(A) = ∫₀∞ [r exp(-r t)] · exp(-s t) dt = r/(r+s).

Formalisation must first establish for t≥0:
expMeasure(s) {y : t<y}=ENNReal.ofReal(exp(-s*t)), starting from
the pinned Mathlib `cdf_expMeasure_eq` and probability complement.
Then apply `Measure.prod_apply`, identify the one-dimensional
lintegral, and evaluate it by an exponential integral theorem or
the FTC with conversion to ENNReal. Handle endpoints t=0 and negative
t using the a.e. nonnegative support of expMeasure(r).
Only after the actual Lean proof may a theorem claim r/(r+s).

The finite case additionally requires genuine finite product
probability space, a.s. distinct coordinates, measurable strict
ordering chambers, and equality of each chamber's measure to
`orderMass`, followed by S018's verified discrete pushforward.

Atlas remains 90 EGU / 8 non-EGU / 45 unresolved.
