# S013 — Weighted head-conditioning of exact finite priority event laws

## Scope and source model

Let V be a finite set of vertices, r(v)>0 for all v, and let
PL_V be the size-biased permutation distribution:

    PL_V(v :: tail) = [r(v)/R_V] PL_(V\{v})(tail).

Here R_V is the sum of rates on V. S011 verified in imported Lean
that all actual Mathlib `List.permutations(V.toList)` are counted
**once each** and their positive order masses sum to one.

## S013 structural theorem (IG-L20)

For *any* function f from a first vertex and remaining order to
a real number, the exact weighted expectation satisfies

    sum_{o in Perm(V)} PL_V(o) f(head(o),tail(o))
      = sum_{v in V} r(v)/R_V *
          sum_{t in Perm(V\{v})} PL_(V\{v})(t) f(v,t).

The equation is for nonempty V; the arbitrary function may be signed,
and the algebraic identity itself does not require r(v)>0.
Consequently, for any event E of the complete priority ordering,

    P_PL_V(E) = sum_{v in V} [r(v)/R_V]
                        P_PL_(V\{v})( (v::tail) in E ).

The proof decomposes actual permutations into distinct heads (S011),
uses the per-leaf identity `orderMass(v::tail) =
firstChoice(V,v)*orderMass(tail)`, then distributes the finite sum.
The event form follows by setting f to an indicator function. This
proves *conditional head factorisation* of the discrete order law.

## S013 greedy event theorem (IG-L21, algebraic reduction)

For symmetric neighbours N, the S012 deterministic theorem gives

    Greedy(v::tail)
      = {v} union Greedy(filter (not-in N(v)) tail).

Writing `P_order(V,T)` for the exact full weighted-permutation mass
of orders whose greedy terminal set is T, we obtain

    P_order(V,T)
       = sum_{v in V} [r(v)/R_V] *
           sum_{tail in Perm(V\{v})} PL_(V\{v})(tail)
              1[ {v} union Greedy(filter_not_N(v)(tail)) = T ].

**Important:** This formula is *not yet* the `finiteRaceLaw`
first-choice recursion in Lean, because the inner weighted law is
over the full remaining tail before deleting blocked vertices. It
still requires the distributional weighted-deletion consistency
result

    (filter_A)_* PL_(V\{v}) = PL_A

for A = V \ N[v], or an equivalent formal conditional-law proof.
S011 proves that law equality on paper and tests it with exact
rational computations; S013 does **not** silently assume it.

## Independent verification

- `tests/test_s013.py` evaluates the weighted-head identity for
  every nonempty subset of a six-vertex rate vector, with a signed,
  tail-order-dependent rational test function, rather than only
  normalization.
- It independently checks first-choice event mass for every retained
  subset and all possible first winners.
- For edgeless, path, cycle, star and asymmetric six-vertex graphs
  (with symmetric undirected adjacency), it compares the conditional
  filtered suffix law after each first winner with the directly
  enumerated positive weighted law on the residual vertices. The
  deterministic greedy event equality is checked simultaneously.
- CI verification of the imported Lean lemmas and these exact tests is
  recorded by exact SHA in CLAIMS.md/HANDOVER.md.

## Next formal step

1. Prove the first retained-vertex distribution by induction on
   discarded vertices, including positive denominators.
2. Iterate it to obtain the full weighted permutation restriction
   identity.
3. Apply the resulting pushed-forward weighted law to IG-L21 and
   finish `priorityOutputMass = finiteRaceLaw` by active-cardinality
   induction using the S010 fuel-invariance lemma.
4. Only then formally identify the order law with independent
   exponential clocks.

No independently verified novelty is claimed.
