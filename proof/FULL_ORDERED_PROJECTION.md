# S017 — Full weighted priority-order deletion consistency

## The exact discrete theorem

Let V be a finite set with strictly positive real rates r(v),
let A ⊆ V, and let t list each element of A exactly once.
The complete weighted priority-order law is the successive
size-biased permutation law:

    P_V(v :: suffix) = r(v)/R_V * P_(V\{v})(suffix).

For an order o of V, write o|A for the list obtained by retaining
only A. The *actual event mass*, summed over complete Mathlib
permutations of V, is

    M(V,A,t) = Σ_(o∈Perm(V)) P_V(o) 1[o|A=t].

Then for **every** complete order t of A,

    M(V,A,t) = P_A(t).

Invalid t have zero mass by S015's independent support theorem.
When A=∅, the empty projection has mass one by S014 and S011.

## Proof by induction on |V|

Assume A is nonempty and let t = w :: s, where w∈A and s
is a complete order of A\{w}. Condition on the first globally
selected vertex v. S013–S014 formally provide the exact head
equation over the genuine full-permutation mass, without assuming
any subset-deletion law.

- When v=w, the event requires that the remaining full order,
  projected to A\{w}, equal s. Since w is absent from V\{w},
  projecting to A is identical to projecting to A\{w}. By
  induction this branch has conditional mass P_(A\{w})(s).
- When v∈A\{w}, the event is impossible.
- When v∈V\A, the target list t is unchanged, and by induction
  the projected conditional mass is P_A(t).

Thus, with B=V\A,

    M(V,A,w::s)
      = r(w)/R_V * P_(A\{w})(s)
        + R_B/R_V * P_A(w::s).

The intrinsic size-biased law satisfies
P_A(w::s) = (r(w)/R_A) P_(A\{w})(s).
As R_V=R_A+R_B, elementary algebra gives the equality. More
precisely, the Lean proof applies S016's exact proportional
first-retained fixed-point identity term-by-term, before
factoring out P_(A\{w})(s). This avoids dividing by any mass
of an event, including events of probability zero. Positivity
guarantees the normalising rates are nonzero.

The induction base is the empty active set. The A=∅ boundary
uses complete priority-law normalisation, not an axiom. Thus
the identity holds simultaneously for *all* finite active and
retained sets and every strictly positive real rate vector.

## Conditional deletion and limits

Conditioning the full law on its first overall vertex v
leaves the weighted full-permutation law of V\{v}, by S013.
The theorem above immediately applies to every retained
subset of that remaining set. This is finite *discrete*
conditioning. No continuous independent exponential clocks,
measure-theoretic equivalence or publication priority follows
from it.

This lemma closes IG-R2's previously paper-only
weighted-deletion law in Lean **once imported compilation at
the exact PR head is verified**. The next separate formal
obligation is to push forward along greedyOutput and identify
the result with finiteRaceLaw using S012's deterministic
blocked-erasure result and S010 fuel stability.

## Independent regressions

tests/test_s017.py constructs the full projected distribution
by a separate first-global-winner Fraction dynamic program,
then compares each retained permutation mass with an
independent direct product formula. It checks 95 subset
instances on nine nonidentical positive rational rates,
and residual conditional laws after each possible initial
winner on eight vertices. This is finite exact testing;
it is not a proof of the universal real-rate statement.
