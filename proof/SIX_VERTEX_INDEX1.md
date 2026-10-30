# S006: an exact six-vertex EGU family (connected atlas index 1)

**Status:** complete elementary probability calculation and exact rational
certificate, independently checked by the 720-order enumerator.
This is not Lean formalisation of the independent-Exponential-clock law
or a claim of independent novelty.

The six vertices are 0,...,5 and the edges are
`01,12,14,15,23` (NetworkX connected 6-vertex atlas index 1).
Its three maximal independent sets are

- A = {0,2,4,5}
- B = {0,3,4,5}
- C = {1,3}

Assign the three leaves 0,4,5 the same rate a>0, and assign
rates t,u,w>0 to vertices 1,2,3 respectively. Put
T=t+u+w+3a.

The minimum-clock exponential race, or equivalently the
weighted first-choice recursion, gives the **exact** probabilities

```
P(A) = u/T + (3a/T)*(u/(u+w))
     = u*(u+w+3a)/((u+w)*T)

P(B) = (3a*w)/((t+3a)*(u+w))

P(C) = t/T + (w/T)*(t/(t+3a))
     = t*(t+w+3a)/((t+3a)*T)
```

For A, either vertex 2 is first, or a leaf is first and then vertex
2 wins the race against 3. For C, either vertex 1 is first, or vertex
3 is first (thereby excluding 2) and vertex 1 wins against the leaves.
The middle expression is also the complementary probability, or
follows directly by splitting on the first arrival. In each expression,
conditioning leaves independent exponential clocks on the remaining
vertices; the formulas are also identities in the finite algebraic law.

Take (a,t,u,w)=(3,6,4,5), i.e. the strictly positive integer
rate vector

```
(lambda_0,...,lambda_5) = (3,6,4,5,3,3).
```

Then T=24, u+w=9, t+3a=15, and the three
probabilities are, **exactly**,

```
P(A) = 4*(4+5+9)/(9*24) = 1/3
P(B) = 9*5/(15*9) = 1/3
P(C) = 6*(6+5+9)/(15*24) = 1/3.
```

This settles atlas index 1 as EGU, not merely numerically plausible.
The independent full priority-order calculation, all 720 orders,
agrees with the first-choice recurrence at the same exact fractions
(`tests/test_s006.py`). The atlas checks the graph's edge set
before applying the witness.

## A positive one-parameter family

Scale to a=1. For any rational t with 3/2 < t < 3, set

```
u = (t-6)*(2*t-3) / (3*(t-3)),
w = u*(t+3)/(6-t).
```

Both u and w are positive on this open interval.
Substituting gives P(A)=P(B)=P(C)=1/3: first, P(B)=1/3
is equivalent to `w*(6-t)=u*(t+3)`; substituting this
relation into P(A)=1/3 gives
`(t-6)*(2*t-3)=3*u*(t-3)`. The remaining equality
follows because all three probabilities sum to one.
The t=2 member gives the integer certificate above after
multiplication by 3.

Thus this noncograph has infinitely many strictly positive rational
uniformising rate assignments. This family is an informal algebraic
theorem backed by exact finite checking, *not a Lean-verified theorem*.

The previous S005 atlas count 69 positive / 4 negative / 70 unresolved
becomes **70 positive / 4 negative / 69 unresolved**. Every
unresolved case still has six vertices.
