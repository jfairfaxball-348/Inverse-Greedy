# S021 — Rate swapping, measurable clock events and independent replica oracle

**Scope.** The continuous-clock unequal-rate formula and complete finite
ordered-chamber mass theorem remain separate goals. The S021 Lean module
`InverseGreedy/ContinuousRaceSwap.lean` starts from the genuine exponential
product measures of S019–S020. Check `CLAIMS.md` for the exact passing SHA
before describing any of its declarations as Lean-verified.

## 1. True product-measure symmetry at arbitrary rates

For rates `r,s>0`, write
`μ(r,s) = expMeasure(r) ⊗ expMeasure(s)`. The coordinate swap
`S(x,y)=(y,x)` is measurable and satisfies the true measure identity

    S_* μ(r,s) = μ(s,r).

This follows directly from Mathlib's `Measure.prod_swap`; it does not
require the two rates to agree. Consequently,

    μ(r,s){(x,y): y < x} = μ(s,r){(x,y): x < y}.

Together with S020's independently proved zero-tie partition,

    μ(r,s){x<y} + μ(s,r){x<y} = 1.

The above is a *constraint* on the unknown continuous-event probabilities,
not a proof of `μ(r,s){x<y} = r/(r+s)`. That numerical identity still
requires a genuine integral or CDF-tail argument in Lean.

## 2. Measurable events in a genuine finite clock product

For any finite index type `I` and positive rates, S020 already defines
`μ_I = Measure.pi (i ↦ expMeasure(r_i))` with genuine exponential
marginals and joint independence. The S021 module proves measurability
of the comparison event `{ω | ω_i < ω_j}`, the tie event
`{ω | ω_i = ω_j}`, the conjunction of pairwise distinctness for all
different indices and the event that a given `i` is strictly first.
These statements establish event well-formedness only. In particular,
they do *not* establish measure-zero ties between two distinct
coordinates, nor probabilities of any ordered chambers.

## 3. Independent exact oracle using exponential replicas

The exact `tests/test_s021.py` oracle is independent of the repository's
weighted priority recurrence. For positive **integer** rates
`a_1,...,a_k`, replace rate `a_i` with `a_i` individually
labelled unit-rate Exp(1) clocks, and let `T_i` be their minimum.

For `t>=0`, independence gives

    P(T_i > t) = P(all a_i unit clocks > t)
               = exp(-t)^(a_i) = exp(-a_i t),

so `T_i ~ Exp(a_i)`. Disjoint replica families yield independent
`T_i` across groups. Each permutation of the `N=sum a_i`
independent continuous unit clocks is equiprobable (`1/N!`),
since the density is symmetric and ties have probability zero.

Reading the ordered replica labels and retaining only the *first*
appearance of each group gives exactly the strict order of the
independent `T_i`. Thus direct permutation counting gives the
finite-clock ordered-chamber law *without calling the discrete
weighted-priority model*. Exchangeability (or conditioning on the
first replica and recursing) yields the mathematical identity

    P(T_{π1} < ... < T_{πk})
       = product_{j=1..k} a_{πj} / (sum_{h=j..k} a_{πh}).

The oracle exhausts all labelled replica orders when `N<=8`
and checks this formula exactly using `fractions.Fraction`.
It checks the empty-index and singleton cases, equal rates,
highly unequal 1:7 and 7:1 pairs, multiple three-/four-clock
cases and relabelling invariance. A negative test ensures zero
rates are rejected.

**Limits:** this independent oracle is an exact finite test for
integer rates, not a Lean proof and not by itself a proof for
arbitrary positive real rates. It is stronger than a floating-point
reproduction of the first-choice recursion in its independent
sample-space construction, but still must not be conflated with
continuous measure-theory formalisation.

## 4. Remaining formal bridge

A complete Lean proof for all positive real rates should establish:
(1) the exponential survival function from `cdf_expMeasure_eq`;
(2) `Measure.prod_apply` for the strict comparison set and evaluation
of its nonnegative exponential integral;
(3) zero probability of finite pairwise ties, perhaps via pair-marginal
projection to S019's null diagonal;
(4) measurable finite sorting and ordered-chamber mass equality with
S017's `orderMass`; and
(5) the genuine sorting pushforward and S018 greedy-output law.

An informal direct computation for (2), valid mathematically, is

    μ(r,s){x<y} = integral_0^∞ r exp(-(r+s)t) dt = r/(r+s),

with no dependence on the discrete greedy model. The existing complete
all-finite-chamber analytic proof is in
`proof/EXPONENTIAL_CLOCK_BRIDGE.md`.

No change to the EGU atlas (90 positive / 8 negative / 45 open),
and no claim of novelty certification.
