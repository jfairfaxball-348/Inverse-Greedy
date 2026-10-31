# S009 — Infinite star-corona obstruction family

**IG-N5 (complete informal theorem).** For every integer m >= 2,
the pendant corona of the star K_(1,m) is **not EGU**: no assignment
of strictly positive exponential rates makes its greedy maximal
independent set uniform. The smallest member m=2 is the
six-vertex corona(P3), connected atlas index 3. In contrast the
m=1 case is P4, which is EGU.

## Graph and outcomes

Let the core star have hub b and pairwise nonadjacent spokes
a_1,...,a_m. Give each core vertex one private leaf:
B is joined only to b, and A_i is joined only to a_i.
The maximal independent sets are indexed by

* every subset S of spokes, with core centres a_i for i in S,
  private leaves A_i for i outside S, and the hub leaf B;
* one additional set containing hub b and **all** spoke leaves A_i.

Thus there are 2^m+1 outcomes.

## Exact joint law of all 2^m corner outputs

Write the positive rates of b,B as b,B, and rates of a_i,A_i as
a_i,A_i. Put u_i=a_i+A_i and x_i=a_i/u_i (so 0<x_i<1).

Let X_i be the indicator that a_i beats A_i in its own two-clock race.
The X_i are independent Bernoulli(x_i). In each pair the winner is
independent of the first arrival time, which is Exp(u_i).
Conditionally on X=(X_i), hub b is selected iff it beats B and
every pair winner a_i with X_i=1. This event has probability
b/(b+B+sum_i u_i X_i).

If b is not selected, precisely the core spokes with X_i=1 are
accepted. Hence, with

    F(t) = (B+t)/(b+B+t),

the probability q_S of the corner output indexed by S is **exactly**

    q_S = (product_{i in S} x_i) *
          (product_{i not in S} (1-x_i)) *
          F(sum_{i in S} u_i).

The remaining hub outcome has mass 1-sum_S q_S. These formulas hold
for every strictly positive real rate vector, without assuming
symmetry between spokes.

## Universal strict minor

Fix distinct i,j, and any S not containing them. Let
t=sum_{k in S} u_k >=0. The Bernoulli factors in the following minor
cancel pairwise; the remainder is strictly positive:

    q_(S+i) q_(S+j) - q_S q_(S+i+j)
      = [strictly positive Bernoulli prefactor] *
        (F(t+u_i)F(t+u_j)-F(t)F(t+u_i+u_j)).

Writing D=B+t>0, the bracket equals

    b*u_i*u_j*(2D+b+u_i+u_j)
      / ((b+D)*(b+D+u_i)*(b+D+u_j)*(b+D+u_i+u_j)) > 0.

At least two spokes exist, so such a strict minor always exists.
For an exactly uniform output law, all q_S would equal 1/(2^m+1),
making the minor zero. Contradiction. QED.

This is a full all-size **non-EGU family**, not a statement about
induced stars inside arbitrary graph coronas. The matrix inequality
also characterises a strictly log-submodular tilt of independent
Bernoulli spoke races. Other graph classes require separate proofs.

## Verification

`experiments/star_corona.py` generates the exact finite corner law.
`tests/test_s009.py` checks it against the independent exact
first-choice recursion on stars with 2, 3 and 4 spokes, including
asymmetric positive rate vectors. The six-vertex base case has
729 additional exact tests and an independent 720-order oracle.
The Lean algebraic theorem in `InverseGreedy/CoronaP3Minor.lean`
handles the four-corner strict rational factor; the full arbitrary-m
stochastic event-law identity is **not yet Lean-verified**.
