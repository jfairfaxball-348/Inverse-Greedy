# S029 — genuine real-clock/bin-event sandwich and collision-width bound

**Date:** 2026-11-03. Working PR: [#28](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/28).

## The real-clock sample space

For every strictly positive real rate pair r,s, the probability measure is
`independentExpPair r s = expMeasure r ⊗ expMeasure s` on ℝ × ℝ, as in
S019. For every δ>0 the measurable one-based ceiling-bin variable is
`Kδ(t) = Nat.ceil(t/δ)`, including zero/negative times and exact bin
endpoints.

Since division by a positive width and `Nat.ceil` are nondecreasing,
`x≤y ⇒ Kδ(x)≤Kδ(y)`. Consequently, without exceptional sets,

- `Kδ(x)<Kδ(y) ⇒ x<y`;
- `x<y ⇒ (Kδ(x)<Kδ(y) ∨ Kδ(x)=Kδ(y))`.

These inclusions apply *pointwise*, including all null zero-bin and
endpoint configurations. Under the actual independent exponential product,
subadditivity of measure therefore proves the sandwich

[
 W_delta le P(T_r<T_s) le W_delta+C_delta,quad
 W_delta=P(K_delta(T_r)<K_delta(T_s)),quad
 C_delta=P(K_delta(T_r)=K_delta(T_s)).
]

`InverseGreedy/ContinuousRaceSandwich.lean` contains the fully imported
set inclusion and genuine measure-theoretic inequalities, and a version
with S028's closed-form real-fraction expressions substituted. S027's
older lower bound required discarding an almost-surely null first-zero-bin
event; S029 proves a stronger unconditional set inclusion.

## Collision-width bound

Put (q=e^{-rdelta}), (t=e^{-sdelta}); both are strictly between
0 and 1. S028 proves for the *actual* independent exponential product that

[
 C_delta=rac{(1-q)(1-t)}{1-qt}.
]

Because (qt≤t), one has (1-t≤1-qt), so

[
 C_delta≤ 1-q≤rdelta
]

using (e^{-x}≥1-x). Interchanging r,s gives (C_delta≤sdelta);
hence

[
 oxed{C_delta≤deltamin(r,s).}
]

`InverseGreedy/BinnedCollisionBound.lean` formalises these elementary
geometric inequalities and applies them to S028's *genuine measured*
real-fraction result for all positive real rates and widths.

The independent `tests/test_s029.py` checks exact right-closed
endpoint/negative-time monotonicity and the geometric three-outcome
partition with `Fraction`. It does not establish a stochastic theorem.

## What the new results do **not** prove

The mathematical limit
(W_delta	o r/(r+s)) as (deltadownarrow0) follows from
((1-e^{-rdelta})/(1-e^{-(r+s)delta})	o r/(r+s))
and (e^{-sdelta}	o1). Together with the sandwich and the collision
bound, this yields the genuine continuous winner ratio. **That analytic
limit and the rate-ratio equality must be installed as Lean theorems
separately**. The general finite permutation-chamber masses, measurable
canonical sorting of true real clocks, and actual greedy-output
pushforward likewise remain open.

Do not infer independent novelty or a general-graph EGU classification
from this measure-theory bridge. The connected n≤6 atlas is still
90 EGU / 8 non-EGU / 45 unresolved.
