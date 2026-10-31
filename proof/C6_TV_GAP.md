# S012 — C6 has a uniform positive total-variation gap

All rates are strictly positive. This supplements the exact C6
nonuniformity proof in `proof/C6_OBSTRUCTION.md`.

## Theorem (IG-N1b)

Let `P_r` be the greedy terminal maximal-independent-set distribution
on the six-cycle `C6` at any positive rates `r`. Let `U` be uniform
on its five maximal independent sets. Then

    TV(P_r, U) >= 4/45 > 0.

Consequently `C6` is **not approximately EGU (AEGU)**; its attainable
greedy-output laws stay a fixed positive distance from uniformity.
This contrasts with the star-corona obstruction, for which the
distance is always positive but has infimum zero.

## Proof

Write `p0,p1,p2` for the output probabilities of the three
opposite-pair maximal independent sets of `C6`. The exact formula
and six-factor inequality in `proof/C6_OBSTRUCTION.md` prove,
for *every* strictly positive real rate vector,

    p0 * p1 * p2 <= 1/729 = (1/9)^3.

Therefore at least one pair, say `i`, satisfies `pi <= 1/9`:
otherwise the product of three terms strictly greater than `1/9`
would exceed `1/729`.

The uniform target assigns probability `1/5` to this pair.
Taking the singleton terminal-outcome event `{i}`, the variational
characterization of total variation gives

    TV(P_r,U) >= |U({i}) - P_r({i})|
               = 1/5 - pi
               >= 1/5 - 1/9
               = 4/45.

The inequality holds independently of the rates, hence also after
taking their positive-rate infimum. QED.

This bound is not claimed sharp. For all-six-equal rates the exact
total variation is `4/15` (three pair sets of mass `1/9` and two
alternating sets of mass `1/3`).

## Formalisation and tests

- `InverseGreedy/C6TVGap.lean` verifies the algebraic implication
  from the three-product bound to an event-probability deficit of
  at least `4/45`; its compilation status is recorded in the claim ledger.
  The finite greedy event identification and measure-theoretic
  variation inequality are **not** verified by this Lean theorem.
- `tests/test_s012_c6_gap.py` verifies the opposite-pair formulas
  against the independent exact first-choice recursion for all 729
  positive rate vectors in `{1,2,4}^6`, checks the event and
  total-variation gaps exactly, and compares two cases with the
  complete 720-permutation weighted-order oracle.

By the S010 AEGU necessity under disjoint union and join, every
disjoint union or nonempty join with `C6` also fails to be AEGU.
The union retains at least the same TV lower bound by marginalization;
no quantitative lower bound for joins is claimed here.

This is a mathematical consequence of the existing C6 inequality,
not an independent literature-novelty certificate.
