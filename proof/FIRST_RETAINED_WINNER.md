# S016 — Formal first-retained-winner marginal

## Setting and exact event

Fix a finite active set V, a nonempty retained subset A⊆V, strictly positive
real rates r_v, and i∈A. A complete priority permutation has successive-choice
weight P_V(o), as defined by `orderMass`. Write o|_A for the list obtained by
filtering o to A.

Define the event mass

  F(V,A,i) = Σ_{o ∈ Perm(V)} P_V(o) 1[(o|_A).head? = i].

This *is an event over actual full permutations*, not a definition that
presupposes the desired retained marginal. In Lean the event is
`firstRetainedMass` in `InverseGreedy/FirstRetainedWinner.lean`.

## Theorem (IG-L24)

For every strictly positive rate vector, every A⊆V with A≠∅, and i∈A,

  F(V,A,i) = r_i / R_A,     R_A = Σ_{a∈A} r_a.

There is no graph assumption and no exponential-clock or measure-theoretic
assumption in this theorem.

## Proof

Condition on the first element v of the *full* priority permutation.
S013 gives exact first-head factorization with correct permutation
multiplicities and weight r_v / R_V. If v∈A, it is the first retained
element. The event is certain if v=i and impossible otherwise. The
conditional law of the complete tail has total mass one by the S011
full-order normalization theorem. If v∉A, the first retained winner is
determined by the tail and its event mass is F(V\\{v}, A, i).
Hence for nonempty V,

  F(V,A,i) = r_i/R_V + Σ_{b∈V\\A} (r_b/R_V) F(V\\{b},A,i).

Induct on |V|, keeping A fixed. If a discarded vertex b is removed,
A remains a nonempty subset of V\\{b}, so the induction hypothesis gives
F(V\\{b},A,i)=r_i/R_A. Therefore,

  F(V,A,i) = [r_i + R_(V\\A) · r_i/R_A] / R_V
           = [r_i + (R_V-R_A) · r_i/R_A] / R_V
           = r_i/R_A.

The final equality uses only R_A>0 and R_V>0. Lean proves
the head equation, fixed-point identity and cardinality induction
as separate named results, without sorry/admit/native_decide.

## Verification and limits

Initial S016 all-green code SHA: `fd83d359cdb5ef5db527bfe59ae72799d8c9913e` (Actions run `41345774024`).
Exact rational tests check the head recurrence, closed form, all subsets
of nine vertices and an independent six-vertex permutation oracle.

**Not proved by IG-L24:** equality of the entire filtered *order*
distribution with intrinsic `orderMass` on A; the discrete
`priorityOutputMass = finiteRaceLaw` pushforward; or equivalence
to independent Exp arrival clocks. Those are the next obligations.
The connected ≤6 atlas stays 90 EGU / 8 non-EGU / 45 unresolved.
