# S040 — finite ENNReal gap-monomial rearrangement (partial)

Date: 2026-11-04. Check [PR #40](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/40) for exact-head CI status before describing this as Lean-verified.

## Mathematical statement and imported Lean boundary

For an arbitrary finite number n of positions, arbitrary factors `c_j,q_j ∈ ENNReal`, and arbitrary nonnegative gaps `d_a`, S036 defines
`k_j = j + Σ_{a≤j} d_a`. The imported module `FiniteClockGapMonomial.lean` contains the pointwise finite-product identity

`∏_j (c_j q_j^(k_j)) = (∏_j c_j q_j^j) · (∏_a (∏_{j≥a} q_j)^d_a)`.

This is an identity **in ENNReal**, not an informal real logarithm argument. In particular it is valid even for zero and infinite factors. It also handles zero and singleton index types. The triangular index swap is done by writing the exponentiated prefix sum as an inner finite product and commuting finite products.

The intended specialisation is `q_j=ofReal(exp(-rates(order[j])*δ))` and `c_j=ofReal(1-q_j^{real})`. S039 guarantees strict contraction of the corresponding real suffix factors. However this module **does not yet transport** S038's vertex-indexed `finiteExpPositiveBinMonomial` along the complete-order witness into this positional factorisation. The fact that the generic identity is proved does **not** establish the genuine measured finite-width product.

## Checks and excluded claims

`tests/test_s040.py` independently checks the same finite algebra with exact `Fraction` arithmetic for all gap vectors of bounded size, all seed-ratio permutations through four positions, and degenerate 0/1 factors. It is not a proof of `ENNReal` infinity behaviour or countable convergence.

**Still open:** (1) formal direct identification of S038's genuine measured monomial with these positional factors; (2) multivariate nonnegative `tsum` commutation and geometric evaluation; (3) measured finite-width closed product; (4) δ↓0+ continuous-clock strict-order law using S034's collision sandwich; (5) measurable total sorting and true greedy-output pushforward. All EGU atlas counts remain **90 / 8 / 45**; no novelty or registry claim.

Next session: `sessions/S041.md`.
