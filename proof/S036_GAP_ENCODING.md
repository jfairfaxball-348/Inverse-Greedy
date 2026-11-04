# S036 — formal forward gap encoding for genuine geometric clock chambers

**Date:** 2026-11-04. **PR:** [#36](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/36).

## Exact context and Lean scope

S035 established in imported Lean that the **actual finite product of
continuous exponential clocks** gives the measured strict-bin event a
countable sum of admissible positive-bin joint geometric cell masses:
`finiteIndependentExp_strictBin_series`. The aim of S036 is to evaluate
that *genuine measured* series, not assume a discrete order model.

The new imported `InverseGreedy/FiniteClockGapEncoding.lean` begins the
change of variables for an ordered list of length `n`. For arbitrary
`gaps : Fin n → ℕ`, define

`k_j = j + Σ_(a≤j) gaps(a)`.

Lean proves `gapBinValue_strictMono`: if `a<b`, then `k_a<k_b`;
it also proves position-injectivity and `j≤k_j`. This covers
`n=0` and `n=1` without side-case assumptions. Crucially **this is
only the forward direction**. The new module does NOT yet construct a
Lean inverse or reindex the S035 sum.

## Complete paper mathematics, still awaiting Lean formalisation

Given any strictly increasing nonnegative sequence
`0≤k_0<⋯<k_(n-1)`, define
`d_0=k_0` and
`d_j=k_j-k_(j-1)-1` for `j>0`.
Since `k_j>k_(j-1)` are natural numbers, every `d_j≥0`.
Telescoping gives `k_j=j+Σ_(a≤j)d_a`.
Conversely, that forward expression has
`k_j-k_(j-1)-1=d_j` and `k_0=d_0`.
These establish a bijection for every finite length, with
the empty sequence mapping to itself.

Let `0<q_j<1` and `Q_a=∏_(j≥a)q_j`. The identity

`∏_j [(1-q_j)q_j^(k_j)]
 = (∏_j [(1-q_j)q_j^j]) · ∏_a Q_a^(d_a)`

follows by exchanging the two finite index sums in
`Σ_j k_j log(q_j)`, or directly by commutative exponent and
finite-product laws (without using logarithms in the Lean target).
All `Q_a` satisfy `0<Q_a<1` because each suffix product is a
finite product of factors in `(0,1)`. Summing independent
nonnegative gaps produces the finite-width formula

`Pr(strict positive-bin order)
 = (∏_j (1-q_j)q_j^j) · ∏_a (1-Q_a)⁻¹`.

This conclusion is **paper mathematics / exact-regression only**,
not imported Lean in S036. It must be connected by a proved
bijection and reindexing directly to S035's actual measure theorem.

## Independent exact tests

`tests/test_s036.py` checks the two-sided encoding on every
nonnegative gap vector of length 0–5 with entries 0–3, every
strict increasing nonnegative bin tuple of length 0–5 inside
`[0,11)`, exact rational monomial factorisation across those
vectors, invalid boundary sequences, and empty cases. These tests
are independent of Lean and do not prove convergence, the true
continuous-clock law or novelty.

## Remaining obligations

1. Lean-prove the inverse and a true bijection onto admissible
   complete-permutation bin assignments.
2. Reindex the actual S035 `tsum`, commute finite-index ENNReal
   products/countable sums, prove suffix-`q` positivity and
   convergence, and obtain the measured geometric finite product.
3. Lean-prove `δ→0+` and use the genuine S034 collision sandwich
   to establish full `n≥3` continuous-clock strict-chamber masses.
4. Build a measurable tie-broken sorting map and prove the genuine
   greedy-output pushforward.

No EGU classification changed. Connected n≤6 atlas stays
**90 EGU / 8 non-EGU / 45 unresolved**. No novelty assertion or
Palomar/arXiv action. See `sessions/S037.md`.
