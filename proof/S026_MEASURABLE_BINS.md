# S026 — Measurable bins of genuine exponential clocks (2026-11-03)

## Why one-based bins?

Use `K_δ(t) = Nat.ceil (t/δ)` with a positive real width `δ`. In Lean, `Nat.ceil` is truncated at 0 on negative arguments. Its inverse-image sets satisfy the **exact** identities

```
{t | Kδ(t) = 0} = (-∞, 0]
{t | Kδ(t) = k+1} = (kδ, (k+1)δ]  for k∈ℕ.
```

These are equality of real sets (including all endpoints), **not**
just equality almost everywhere. The positive-bin convention avoids
having to move from S025's right-closed cells to floor's left-closed
cells. On nonboundary positive times, `Kδ(t)-1 = floor(t/δ)`;
the boundary differences form a countable null subset under Exp.
The exact event identities, rather than a claim about an unproved
floor-map equivalence, are what the Lean proofs use.

## Genuine distributions and product independence

S024 proves the actual Exp(rate) CDF and S025 proves the probability
of the real interval `(kδ,(k+1)δ]`:
`(1-e^{-rate δ})e^{-rate k δ}`, for any real rate and width >0.
Together with the preimage identity this now proves a statement about
the **actual** measurable bin random variable `Kδ`. Its zero-cell
probability is 0 because `P(T≤0)=0`.

S020 proves genuine finite arrival-clock independence. Since `Kδ`
is measurable, composing all finite arrival-time coordinates with
`Kδ` preserves `iIndepFun`. A separate direct two-clock product
measure proof gives, for distinct indices i,j, integer k,l≥0,

```
P(Kδ(T_i)=k+1, Kδ(T_j)=l+1)
  = (1-q_i) q_i^k (1-q_j) q_j^l,
q_i = e^{-rate_i δ}.
```

Both the measure-theoretic statements and the arbitrary finite-index
case include empty and singleton families where meaningful.
These two independent-bin extensions are **Lean-verified** at code
SHA `48ea3c284632e2db7a2df438d45a5e263c81aa35`, with both
imported Lean and full Python/certified census passing in push Actions
41607939473 and PR Actions 41607949333. The eventual final PR head
requires a fresh exact-head check.

## Pair race: exact algebra but still Lean-open measure-level sum

Once the true bin PMFs and independence are available, summing the
nonnegative geometric series gives

```
P(K_r<K_s) = (1-q_r)q_s/(1-q_r q_s)
P(K_s<K_r) = (1-q_s)q_r/(1-q_r q_s)
P(K_r=K_s) = (1-q_r)(1-q_s)/(1-q_r q_s).
```

The `Fraction` regression independently checks these identities and
the collision upper bound `≤min(1-q_r,1-q_s)`.
As `δ↓0`, `1-e^{-rδ} ≤ rδ`, so collision probability tends
to zero. On the event of nonnegative real times, a strict bin
inequality implies the corresponding strict clock inequality,
and no-bin-collision preserves the original order. Thus
`0≤P(T_r<T_s)-P(K_r<K_s)≤P(K_r=K_s)`,
and the mathematical limit yields `r/(r+s)`.
This analytic argument was already documented in S023; S026 does
**not** claim that infinite sums, limits or real race ratio have
been fully formalised in Lean.

## Evidence and boundaries

- `InverseGreedy/ClockBins.lean` imported by `InverseGreedy.lean`.
- First imported milestone dual-green at SHA `67c9b4a0a46cfac6e26cd436bdc115a60bce09c4`, PR Actions 41607274017.
- Expanded genuine finite-family independence and pair PMFs dual-green at SHA `48ea3c284632e2db7a2df438d45a5e263c81aa35`, push Actions 41607939473 and PR Actions 41607949333.
- `tests/test_s026.py`: exact rational endpoints, bin masses, binned winner/collision partition, geometric tail remainder. Exact arithmetic is not an all-real stochastic proof.
- Current connected n≤6 partial atlas: **90 EGU / 8 non-EGU / 45 unresolved**. No priority/novelty certification.
