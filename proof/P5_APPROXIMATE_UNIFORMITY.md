# S012 — P5 is non-EGU but approximately EGU

This note strengthens the strict P5 obstruction in
`proof/P5_OBSTRUCTION.md`. Rates throughout the actual greedy
model are **strictly positive**. No zero rate is ever asserted to
be a valid exact uniformising assignment.

## Theorem (IG-N2b): smallest unattained AEGU example

For the path 0–1–2–3–4, choose positive exponential priority rates

    (a,b,c,d,e) = (1,1,t,1,1),     t > 0.

Let `P_t` be the greedy terminal independent-set law and let `U`
be uniform on the four maximal independent sets of P5.

Then

    TV(P_t,U) = t(3t+10) / [4(t+2)(t+4)] > 0,

and in fact for every `t>0`,

    0 < TV(P_t,U) < 5t/16.

Consequently `P5` is approximately EGU (AEGU), since the infimum
of TV over strictly positive rates is zero, but is **not EGU**,
by the strict all-positive P5 minor already established in S002.
Thus P5 has *unattained* approximate uniformity.

Since all graphs with at most four vertices are exactly EGU,
P5 is a smallest-order unattained AEGU graph.

## Exact four-outcome derivation

The P5 maximal sets are 024, 03, 13 and 14. Substitute
`a=b=d=e=1,c=t` into the exact first-choice formulas of
`proof/P5_OBSTRUCTION.md`. This gives

    P_t(03)  = 1/[2(t+2)]
    P_t(13)  = 1/(t+4)
    P_t(14)  = 1/[2(t+2)]
    P_t(024) = 1 - 1/(t+2) - 1/(t+4).

For each `t>0` the first three masses are strictly below
`1/4`, and the last is strictly above `1/4`. Hence total
variation from the four-outcome uniform law is exactly the
surplus of the 024 outcome:

    TV(P_t,U) = P_t(024) - 1/4
              = 3/4 - 1/(t+2) - 1/(t+4)
              = t(3t+10)/[4(t+2)(t+4)].

Positivity holds for positive t. The linear upper bound follows
by multiplying positive denominators: the desired strict inequality

    t(3t+10)/[4(t+2)(t+4)] < 5t/16

is equivalent for t>0 to

    16(3t+10) < 20(t+2)(t+4),

whose right-minus-left side equals `20t²+72t>0`.

Therefore the total-variation distance tends to zero as
`t→0+` **while every rate vector in the approximating family
remains strictly positive**. The formal t=0 endpoint is a limit,
not an admissible EGU rate vector.

## Structural meaning

This is a new *boundary mechanism within this programme*: the
middle path vertex becomes exceptionally slow. It can still be
accepted late if both nonadjacent outer vertices were accepted
earlier, preserving the 024 maximal set. The other three outputs
converge to equal mass and the fourth follows by normalization.

Unlike the star-corona construction, P5 needs only five vertices.
S010 union/join AEGU closure creates additional unattained families
from P5, and S007 false-twin law equivalence creates more expansions.
These descendants are not claimed to be a new primitive family.

The EGU/non-EGU connected atlas counts **do not change**:
P5 remains one of the eight proved non-EGU graphs through six
vertices. What changes is its newly certified AEGU status.
C6, by contrast, stays at positive TV distance at least 4/45.

## Verification boundary

`tests/test_s012_p5_approx.py` checks the four formulas and
the exact TV expression with Python `Fraction`, the independent
weighted 5! full-priority permutation oracle, and the first-choice
recursion on multiple positive rational t-values. It also confirms
zero-rate inputs are explicitly rejected.

`InverseGreedy/P5ApproximateBoundary.lean` establishes the
rational TV identity, strict positivity and linear bound purely
algebraically, when CI succeeds. It does **not** yet establish the
full stochastic output-law identity inside Lean: that remains
S013 work.

Independent novelty / literature priority is not certified.
