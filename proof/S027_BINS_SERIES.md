**Formal check (2026-11-03):** Both genuine countable bin-event series modules are now **Lean-verified** as imported code, together with the complete Python/exact certified census, at exact code SHA `9b4ca4ea833233ffca4a2d892dabedc0f64aa27b`, [push Actions 41612217839](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41612217839). This certifies the equality of the *true event measures* with their *unevaluated* `ENNReal.tsum` series, not either closed-form sum or the continuous unequal-rate limit. Exact final PR-head verification remains necessary.

# S027 — Genuine exponential bin-race series (2026-11-03)

## Meaning and verification boundary

The S026 bin map is **the measurable real-clock function**
`K_δ(t)=Nat.ceil(t/δ)`, for `δ>0`. Its exceptional zero bin is
`t≤0`, a null event for the genuine exponential distribution, and
the positive bin `K_δ=k+1` is exactly `kδ<t≤(k+1)δ`. We use the
actual probability measure `independentExpPair r s`, with
**arbitrary positive real** `r,s,δ`.

At the first S027 verified checkpoint (SHA `3e9b4cf3b5426d5e6d795447e3f5b7bcc84d42a3`),
`InverseGreedy/BinnedRace.lean` is fully imported and both Lean
and Python/census CI pass. Its true first-bin/survival cylinder has
measure computed from the genuine S026 PMF times S024 survival,
and that cylinder is provably contained in the real strict-winner event.

`InverseGreedy/BinnedRaceSeries.lean` and
`InverseGreedy/BinnedRaceCollision.lean` are the next imported proof
milestones. These countable-measure statements **are Lean-verified at code SHA
`9b4ca4ea`**; final documentation-head CI must be checked before merge. The separate closed-form sums and
continuous ratio are not established by those modules alone.

## Mathematical proof (continuous measure, not discrete postulate)

Put `q_r=exp(-rδ)` and `q_s=exp(-sδ)`, so `0<q_r,q_s<1`.
For each `k≥0`, define

`C_k={kδ<T_r≤(k+1)δ<T_s}`.

S026's true bin point-mass and S024's true exponential tail, together
with independence, give

`P(C_k)=(1-q_r)q_r^k q_s^(k+1)`.

Each `C_k` is measurable. If `i≠j`, the events `C_i` and
`C_j` are disjoint (the first clock cannot occupy two different
ceiling bins). The strict-bin event `{K_δ(T_r)<K_δ(T_s)}` equals
`(⋃_k C_k) ∪ {K_δ(T_r)=0<K_δ(T_s)}`; the second event is null.
Hence countable additivity of the **original real product measure**
yields

```
P(K_r<K_s)= Σ_(k≥0) (1-q_r) q_s (q_r q_s)^k
          = (1-q_r) q_s/(1-q_r q_s).
```

Similarly, each same-positive-bin event
`D_k={K_δ(T_r)=K_δ(T_s)=k+1}` has genuine joint mass
`(1-q_r)(1-q_s)(q_rq_s)^k`. The missing (0,0) event is null.
Pairwise disjointness and countable additivity give

```
P(K_r=K_s)=Σ_(k≥0) (1-q_r)(1-q_s)(q_r q_s)^k
          =(1-q_r)(1-q_s)/(1-q_r q_s).
```

The reverse-bin strict winner is the first formula with r and s
swapped, and the three cases sum to 1.

The nonnegative-time property of genuine Exp clocks and endpoint
conventions give strict-bin ordering ⇒ strict real-clock ordering.
Conversely, on the event of **no** bin collision, real-clock strict
order implies bin strict order. Thus

```
0 ≤ P(T_r<T_s)-P(K_r<K_s) ≤ P(K_r=K_s).
```

As `1-q_r q_s ≥ 1-q_r` and `≥1-q_s`,
`P(K_r=K_s)≤min(1-q_r,1-q_s)`. The elementary real inequality
`1-exp(-x)≤x` for `x≥0` yields
`P(K_r=K_s)≤δ min(r,s)`. The loss goes to zero as
`δ↓0`, and the geometric expression tends to `r/(r+s)`,
using `(1-exp(-xδ))/δ→x`. Therefore the true continuous
race ratio follows mathematically.

**Formalisation boundary:** These last geometric-sum evaluations,
collision bounds, limit and numerical real-race identity are
**not yet claimed Lean-verified**. In particular a true bin-cylinder
mass does not automatically compile an infinite-sum evaluation.

## Independent exact regression

`tests/test_s027.py` implements rational
`q_r=((n-1)/n)^a`, `q_s=((n-1)/n)^b` for integer
rates and `n≥2`. It checks the finite first-bin sum plus exact tail,
both strict winner masses plus collision, symmetry under swapping,
the exact inequality
`P(K_r<K_s)≤a/(a+b)≤P(K_r<K_s)+P(K_r=K_s)`,
and the exact rational bound `P(K_r=K_s)≤min(a,b)/n`.
These are independent arithmetic tests, **not** all-real
measure-theory proofs.

## Research status and follow-on

S027 advances the genuine continuous-clock bridge. The following
remain open until their own imported CI proves them:

1. Evaluate both actual ENNReal series as geometric closed forms;
2. obtain the certified collision error and the zero-width limit;
3. verify `independentExpPair r s {p | p.1<p.2}
     = ENNReal.ofReal (r/(r+s))`;
4. general finite strict ordering chamber masses (including empty and
   singleton types) and the actual real-clock output pushforward.

The existing finite discrete-output theorem from S018 is *not*
equivalent to the last two goals. The connected n≤6 partial graph
atlas remains **90 EGU / 8 non-EGU / 45 unresolved**. Independent
novelty is not certified.
