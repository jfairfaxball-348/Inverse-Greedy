# S011 — Deletion consistency of finite priorities and the greedy-law pushforward

All graphs are finite, simple, undirected, and loopless. All vertex rates
are strictly positive. This is a **complete informal proof for the finite
weighted-permutation model**, not yet a Lean proof of the full
pushforward, a measure-theoretic construction, or an independently novel
result.

## The weighted priority model

On a finite set V, draw an ordered permutation by repeatedly choosing
the next remaining vertex with probability proportional to its rate.
For an order (v1,...,vn) the mass is

    PL_V(v1,...,vn) = product_{j=1}^n r(vj) /
                                  (sum_{k=j}^n r(vk)).

The last factor is 1. On the empty set the sole order is empty and has
mass 1. Positivity ensures all denominators for nonempty suffixes are
strictly positive.

## The deletion consistency theorem

**Theorem (IG-R2).** If A ⊆ V and all rates are positive, take a random
full order with law PL_V and erase all entries outside A. The
resulting order has law PL_A, for *every* choice of A (including empty).
Moreover, conditional on a prescribed first overall vertex v, the
remaining ordering restricted to any A ⊆ V\\{v} has law PL_A.

**Proof.** Write B=V\\A, and for i∈A let q_i(A,B) be the probability
that i is the first member of A encountered by successive proportional
draws from A∪B. Put R_A=Σ_{i∈A}r_i and R_B=Σ_{b∈B}r_b. For nonempty A,
condition on the very first draw:

    q_i(A,B)
      = r_i/(R_A+R_B)
        + Σ_{b∈B} [r_b/(R_A+R_B)] q_i(A,B\\{b}).

Induct on |B|. The base B=∅ is q_i(A,∅)=r_i/R_A.
For every B\\{b}, the induction hypothesis gives
q_i(A,B\\{b})=r_i/R_A. Hence

    q_i(A,B)
      = (r_i + R_B r_i/R_A)/(R_A+R_B)
      = r_i/R_A.

The cancellation is exact. The argument applies after *any* number
of proportional draws: conditional on the current remainder, the
next A-vertex has probability r_i/R_A, independently of which
irrelevant B-vertices are still present. Repeating this argument after
each A-vertex proves that the entire retained subsequence has exactly
the successive-choice law PL_A. If A=∅ the statement is immediate.

Conditional on first overall draw v, the remaining order is by
definition PL_(V\\{v}), because the finite sequential process restarts
on the remaining vertices. Apply the just-proved deletion consistency
to any A ⊆ V\\{v}. QED.

**Scope.** This is a discrete, purely algebraic conditional-law
argument: no exponential clocks, limit, independence of continuous
random variables, or measure-theoretic theorem is invoked.

## Pushforward to the greedy output law

**Theorem (IG-R3, informal).** Let G=(V,E) be a finite simple graph and
let O be a full weighted priority order with law PL_V. Let
`Greedy_G(O)` accept a vertex iff it is nonadjacent to every previously
accepted vertex. Write

    F_G(V,T) = P(Greedy_G(O) = T)

for any proposed target T⊆V (including impossible targets). Then

    F_G(∅,T) = 1[T=∅],

and for V≠∅,

    F_G(V,T) =
      Σ_{v∈V∩T} r_v/R_V · F_G(V\\N[v], T\\{v}).

Here N[v]={v}∪N(v), intersected with the current active vertex set
if needed; the induced graph on V\\N[v] uses the original adjacency.

**Proof.** Condition on the first vertex v, whose selection has exact
probability r_v/R_V. Because the accepted set is initially empty,
v is accepted. Every neighbour of v is thereafter rejected: v is
already accepted, and accepted sets never shrink. Removing these
blocked vertices from the remainder does not change *any* later
accept/reject decision on surviving vertices. This is a deterministic
skip argument; symmetry of graph adjacency is required to identify
the blocked set with N(v) from the graph's own neighbour map.

Thus the final accepted set equals {v} together with the greedy
output on the residual set A=V\\N[v] scanned in its original relative
order. By IG-R2, conditional on first v this relative order has the
correct law PL_A. Consequently the conditional terminal law is the
residual law translated by adding v. A target not containing v has
conditional probability zero. Summing over the disjoint possible
first vertices gives the recurrence. The empty case is immediate.
QED.

This proves equality of the **discrete priority-permutation
pushforward** with the *unbounded* first-choice recursion in the
mathematical model. The Lean `finiteRaceLaw` is fuel bounded; S010's
`finiteRaceLaw_fuel_eq_card` provides fuel stability once the
formal law-level induction is supplied. None of this automatically
identifies PL with independent Exp arrival times inside Lean.

## What the exact tests do (and do not) certify

- `experiments/priority_deletion.py` enumerates and weights all full
  orders with `Fraction`, computes projected and conditional order
  laws, and implements an independent recursive head-split enumeration.
- `tests/test_s011.py` checks uniqueness and total mass through six
  vertices, *every* subset on four and five vertices for several
  unequal positive rational vectors, conditional-after-first deletion
  for every admissible subset, and separate full-order/first-choice
  greedy laws for multiple graph families.
- These are independent finite checks, not a general Lean theorem,
  not an all-positive-real certificate from finite enumeration,
  and not a claim of publication priority.

## Remaining Lean proof obligations

1. **Closed in Lean (S011, IG-L14):** unique-head enumeration of the
   actual `List.permutations` as lists of orders up to permutation.
2. **Closed in Lean (S011, IG-L15):** total `orderMass` is one,
   imported CI at exact SHA a613bb87 (PR run 41196560831).
3. **Open in Lean:** algebraic weighted-list marginal under erasing
   arbitrary vertices.
4. **Open in Lean:** weighted grouping by `greedyOutput`, induction
   over residual active sets, and equality with `finiteRaceLaw`
   at `active.card`.
5. **Open in Lean:** identifying the discrete weighted law with
   independent continuous exponential clocks.

The first two established results must not be described as proving
the remaining three.
