# S039 — positive suffix ratios and the finite-width product target

Date: 2026-11-04. Working branch: `s039-clock-suffix-geometry`.

## Formal scope

The imported Lean module `InverseGreedy/FiniteClockGapFactors.lean` establishes,
for arbitrary positive real rates `rates i` and any `δ>0`:

* `clockBinRatio_pos` and `clockBinRatio_lt_one`: `0 < q_i := exp(-rates_i δ) < 1`.
* `clockBinSuffixRatio_pos_lt_one`: every *indexed* suffix product
  `Q_a = ∏_(j : Fin n, a≤j) q_(order[j])` lies strictly in `(0,1)`.
* `one_sub_clockBinSuffixRatio_pos`: all `1-Q_a` are strictly positive.

Suffix nonemptiness is justified by the element `a` itself; there is no assertion
that an *empty* product is below one. The lemma is actually valid for arbitrary
lists, not only `CompleteClockOrder`; the *measured* reindexing still requires
S038's complete-order certificate. The zero-length case has no suffix index and
the empty product is 1. A single clock gives one proper suffix.

## Full evaluation target (mathematical calculation, NOT yet a Lean theorem)

Write `n=order.length`, `q_j=exp(-rates(order[j])*δ)`,
`Q_a=∏_{j≥a}q_j`, `d_a∈ℕ`, and `k_j=j+Σ_{a≤j}d_a`.
Then exactly, as finite algebra,

`∏_{j=0}^{n-1}(1-q_j)q_j^{k_j}
 = [∏_j(1-q_j)q_j^j] [∏_a Q_a^{d_a}].`

Indeed `Σ_j k_j log(q_j)` separates into the base exponents
`Σ_j j log(q_j)` and the doubled triangular sum
`Σ_j Σ_{a≤j} d_a log(q_j) = Σ_a d_a Σ_{j≥a} log(q_j)`;
equivalently use laws of natural powers, finite product commutation and
`k_j=j+Σ_{a≤j}d_a`, avoiding logs entirely in Lean.

Since `0<Q_a<1`, a nonnegative multiple Tonelli/geometric series should give

`P_δ(strictBinChamber(order))
 = [∏_j(1-q_j)q_j^j] / [∏_a(1-Q_a)]`

from **S038's measured gap tsum**, not an assumed priority-order law.
For `n=0`, both empty products are 1; for `n=1`, this fraction is 1.
The ENNReal monomial factorisation, finite multiple-tsum evaluation,
genuine measured fraction, `δ→0+` and measurable continuous-clock
pushforward are **not proved in Lean in S039**.

## Checks and claim boundaries

`tests/test_s039.py` uses independent exact `Fraction` arithmetic for
all permutations of up to four distinct ratios. It verifies positive proper
suffixes, exact pointwise monomial factorisation, all coordinatewise
finite-gap truncations, monotone upper bounds against the candidate closed
product, and zero/singleton cases. Tests are not a convergence proof.

Do not modify the connected n≤6 atlas: 90 EGU / 8 non-EGU / 45 unresolved.
No novelty, registry, or full continuous-clock theorem claim.

Next: `sessions/S040.md` to formalise the actual ENNReal monomial and
multiple-geometric evaluation, then advance the measured finite-width law.
