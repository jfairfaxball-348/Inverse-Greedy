# S009 — Strict probability minor for the pendant corona of P3

**IG-N5 (complete informal proof).** Let H be the path a--b--c, with
one private pendant leaf A at a, B at b, and C at c. Give all six
vertices **arbitrary strictly positive** independent exponential
arrival rates. The random-priority greedy MIS law is never uniform.

This is connected six-vertex NetworkX atlas index 3. Its **original**
atlas-label edges are 01,12,13,24,35 (a relabelling of the path corona).
It has precisely five maximal independent sets, indexed by the
independent subsets of the three central vertices: empty, a, b, c,
and {a,c}. We use subscripts on p to denote which centres are accepted.

## Factorisation from disjoint exponential pairs

Write the centre rates as a,b,c > 0 and their private leaf rates as
A,B,C > 0. Let

    u=a+A,    v=c+C,    x=a/u,    y=c/v,
    F(t)=(B+t)/(b+B+t).

The races in the two disjoint end pairs (a,A) and (c,C) have winning
centre indicators X,Y with independent Bernoulli probabilities x,y.
Crucially, for independent exponential clocks, the winner of a pair
is independent of its first-arrival time; the latter is Exp(u) or
Exp(v), respectively.

Condition on X,Y. The middle centre b is accepted precisely when
its clock beats its leaf B and every end centre whose pair winner is
a centre. The competing minimum is exponential with total rate
b+B+u X+v Y. Consequently, the conditional probability that **b is
not accepted** is F(u X+v Y).

When b is not accepted, the two end centres are accepted exactly when
their indicators X,Y are 1. Therefore the four corner probabilities
are exactly

    p_empty = (1-x)(1-y) F(0),
    p_a     = x(1-y) F(u),
    p_c     = (1-x)y F(v),
    p_ac    = xy F(u+v).

The remaining outcome {b} takes the complementary probability. In
particular all five outcomes are accounted for (no limiting-rate
interpretation is used).

## Strict obstruction

A direct rational identity gives

    F(u) F(v) - F(0) F(u+v)
      = b*u*v*(2*B+b+u+v)
        / ((b+B)*(b+B+u)*(b+B+v)*(b+B+u+v)) > 0.

Every factor appearing on the right is strictly positive.
Since x,y are strictly between zero and one, multiplication yields

    p_a*p_c - p_empty*p_ac
      = x*(1-x)*y*(1-y) *
        b*u*v*(2*B+b+u+v)
        / ((b+B)*(b+B+u)*(b+B+v)*(b+B+u+v)) > 0.

Exact uniformity would make all five probabilities 1/5 and the
left-hand side zero. Contradiction. Thus corona(P3) is non-EGU for
**every positive real rate vector**. QED.

Equivalently log F is strictly concave on t >= 0: the strict
four-corner inequality is a submodularity certificate, and can be
useful when searching for analogous obstructions in larger coronas.
This remark alone does not classify arbitrary supergraphs.

## Exact checks and scope

`tests/test_s009.py` tests all 729 rate vectors in {1,2,3}^6 via
exact first-choice recursion and compares each resulting rational
probability to the closed form and positive factorisation. A separate
full 720-permutation oracle checks selected asymmetric vectors
independently. It also confirms the exact original atlas index and
its edges. These tests **illustrate** the general theorem; the proof
above establishes all positive real rates, with no bounded-search
assumption.

`InverseGreedy/CoronaP3Minor.lean` formalises the strict rational
algebraic minor under abstract 0<x,y<1 and b,B,u,v>0; the identification
of these algebraic quantities with the stochastic greedy event
probabilities, and the full finite pushforward, are not yet end-to-end
Lean formalised. Do not overstate the Lean scope.

## Infinite-family strengthening

The same clock-pair argument with m>=2 independent end pairs proves
the strict minor for **every** pendant corona of a star K_(1,m).
See proof/STAR_CORONA_OBSTRUCTION.md. The six-vertex P3 corona is the
smallest member, not an isolated accidental counterexample.
