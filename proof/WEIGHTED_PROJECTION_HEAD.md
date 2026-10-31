# S014 — Filtered weighted priority-order events

## Conventions and scope

Fix a finite active set \(V\), a retained set \(A\subseteq V\),
and positive real rates \(r_v\). For a complete order \(o\) of \(V\),
write \(P_V(o)\) for the product of successive proportional-choice
weights, and \(o|_A\) for its subsequence of retained vertices.

Define the *actual projected event mass*
\[
 M(V,A,t)=\sum_{o\in \mathrm{Perm}(V)}
             P_V(o)\,\mathbf1_{\{o|_A=t\}}.
\]
This is implemented as `projectedOrderMass` in
`InverseGreedy/ProjectedOrderLaw.lean`, summing over Mathlib's
actual `List.permutations` without duplicate support. It does
not *define* the projected law to be \(P_A\): that is the theorem
to prove.

## Structural first-head identity (IG-L22 candidate)

For \(V\ne\varnothing\), condition on the unique first global
vertex \(v\), which has first-choice weight \(r_v/R_V\).
Because filtering a list commutes with cons in exactly two cases,

- if \(v\in A\), the projected target must begin with \(v\);
  its suffix is the projection of the remaining full order;
- if \(v\notin A\), the projected target is the unchanged
  projection of the remaining full order.

Consequently, with \(t=w::s\):
\[
 M(V,A,t)=
 \sum_{v\in V}\frac{r_v}{R_V}
 \begin{cases}
   M(V\setminus\{v\},A,s), &v\in A,\;v=w,\\
   0, & v\in A,\;v\ne w,\\
   M(V\setminus\{v\},A,t), &v\notin A.
 \end{cases}
\]
For empty \(t\) the retained-head branch has weight zero and
the discarded-head branch is unchanged. This is an exact
event-level equality for the full weighted permutation
measure, not a heuristic argument. In Lean it follows
from S013's general first-head event factorization, followed
by `List.filter_cons` and event equality simplification.
No graph assumptions are needed.

The all-discarded boundary is independently important:
\(M(V,\varnothing,[])=1\), proved from S011 full permutation
normalization; every nonempty projected target has zero mass.

## First retained winner and the missing induction

Fix nonempty \(A\) and write \(B=V\setminus A\). Let
\(q_i(A,B)\) be the exact mass of the event that \(i\in A\)
is the first retained vertex. The head decomposition yields
\[
 q_i(A,B)=\frac{r_i}{R_A+R_B}
   +\sum_{b\in B}\frac{r_b}{R_A+R_B}
          q_i(A,B\setminus\{b\}).
\]
With the base \(q_i(A,\varnothing)=r_i/R_A\),
induction on \(|B|\) gives
\[
 q_i(A,B)=\frac{r_i}{R_A+R_B}
         +\frac{R_B}{R_A+R_B}\frac{r_i}{R_A}
         =\frac{r_i}{R_A}.
\]
The scalar cancellation is formalized separately in
`retained_first_rate_cancellation`. This is a complete
*paper proof* of the first retained winner law and
already follows from S011's full deletion-consistency
paper argument. **The induction connecting the event-level
Lean equation to this scalar recursion is not yet in Lean.**
Nor is the full projected-order identity
\(M(V,A,t)=P_A(t)\) formally compiled.

## Exact independent checks

`tests/test_s014.py` enumerates the original full law,
evaluates the branch-factorized projected law independently,
and checks full projection and first-retained-winner
probabilities on rational unequal-rate examples across all
nonempty retained subsets of six vertices, plus the empty
case. The full deletion-consistency assertions are test
oracles, not hypotheses in the structural Lean proof.

## Next gap

The required bridge is an actual list-event induction over
discarded heads, with the first retained winner identified
and the remaining retained-order distribution reset on the
remaining retained set. Prove the full weighted
`List.filter` pushforward, then use S013's greedy residual
head event and S010's fuel stability to identify
`priorityOutputMass` with `finiteRaceLaw`. The continuous
independent exponential-clock equivalence is a separate
measure-theoretic obligation.
