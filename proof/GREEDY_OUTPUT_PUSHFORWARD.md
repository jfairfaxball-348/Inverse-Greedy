# S018 — Greedy-output pushforward for finite weighted priority orders

**Status:** Discrete mathematical argument; Lean implementation in
`InverseGreedy/PriorityProjectionPushforward.lean`,
`PriorityProjectionEvent.lean`, and `PriorityOutputPushforward.lean`.
The CI status is governed by the exact branch/PR commit, not by this document.

## Model and statement

Let (V) be a finite vertex set, let (r_v>0) for every (v), and
let (N(v)) be a finite symmetric neighbour map (irreflexivity is
allowed, but not needed for the algebraic statement). A full priority
list is a permutation (pi) of (V), with size-biased mass
[
  p_V(pi)=\prod_{j=1}^{|V|}
    \frac{r_{\pi_j}}{\sum_{k=j}^{|V|} r_{\pi_k}} .
]
Let (S(pi)) be the greedy independent-set scan and let
(F(V,T)=\sum_{\pi\in\operatorname{Perm}(V)}
 p_V(\pi)\,\mathbf 1_{S(\pi)=T}).

The target theorem is, for **every** (T\subseteq V) (indeed every finite
target set of the ambient type),
[
 F(V,T)=R_{|V|}(V,T),
]
where (R_n) is the explicitly bounded `finiteRaceLaw`:
[
 R_{n+1}(V,T)=\sum_{v\in V}
   \frac{r_v}{\sum_{u\in V}r_u}
   \mathbf 1_{v\in T}
   R_n(V\setminus(\{v\}\cup N(v)),T\setminus\{v\}).
]
When (V=\varnothing), the sole output is (\varnothing) with mass one.

## 1. A genuine weighted projection expectation

S017 proved the complete all-target deletion-consistency law, not just
a first-element marginal. For any (A\subseteq V), its projected mass
at a target list (\sigma) is
[
 \sum_{\pi:\pi|_A=\sigma} p_V(\pi)
  =
  \begin{cases}
  p_A(\sigma)&\text{if }\sigma\text{ is a full permutation of }A,\\
  0&\text{otherwise}.
  \end{cases}
]

Regroup a *finite* sum by the retained list, using the fact that the
list of distinct permutations of (A) has no duplicates and every full
order projects into it. Thus for every statistic
(f:\operatorname{List}(V)\to\mathbb R),
[
 \sum_{\pi\in\operatorname{Perm}(V)}
    p_V(\pi)f(\pi|_A)
 =
 \sum_{\sigma\in\operatorname{Perm}(A)}
    p_A(\sigma)f(\sigma).
]
The Lean module `PriorityProjectionPushforward` proves its finite
double-sum regrouping directly rather than treating the projection
as an independent new random priority sample.

Taking (f(\sigma)=\mathbf 1_{S(\sigma)=T}) yields the exact
filtered greedy-output event law on (A).

## 2. Condition on the actual first vertex

The S011/S013 head decomposition of `List.permutations` is
multiplicity-correct and gives the head weight
(r_v/\sum_{u\in V}r_u). For each first vertex (v), the
deterministic S012 lemma for symmetric adjacency gives
[
 S(v::\tau)
   =\{v\}\cup S(\tau|_{V\setminus(\{v\}\cup N(v))}).
]
The retained sublist is exactly the filter of the tail that deletes
neighbours of (v): the full tail is a permutation of (V\setminus\{v\}).
A greedy scan is always contained in its scanned list, so the residual
output does not contain (v). Consequently the set equality
[
 \{v\}\cup S(\tau|_A)=T
]
is equivalent to both (v\in T) and
(S(\tau|_A)=T\setminus\{v\}).

Applying the **weighted** projection expectation to the tail
discharges the conditional event exactly:
[
 F(V,T)
 =\sum_{v\in V}
    \frac{r_v}{\sum_{u\in V}r_u}
    \mathbf 1_{v\in T}
    F(V\setminus(\{v\}\cup N(v)),T\setminus\{v\}).
]
This is equality for impossible targets too; no conditioning on a
nonzero target event is required.

## 3. Identify the two bounded recursions

Each residual active set (A_v=V\setminus(\{v\}\cup N(v)))
satisfies (A_v\subseteq V\setminus\{v\}), hence
(|A_v|<|V|) when (v\in V). Induct on a fuel bound at least
(|V|), using the displayed exact head equation, the identical
`finiteRaceLaw_step` equation, and S010's
`afterChoice_card_lt`. At zero vertices, both masses are the same
Kronecker delta at the empty output. Choosing fuel (|V|) closes
the claimed theorem; S010 also proves stability for all larger fuel.

## Exact arithmetic and boundaries

`tests/test_s018.py` compares exhaustive weighted full permutations
with an independent memoised first-choice dynamic programme on
empty, edgeless, path, cycle, star, clique and heterogeneous
six- and seven-vertex graph cases. Its all-target checks include
impossible targets and empty graphs. It separately checks a genuinely
order-sensitive nonconstant projected statistic, using rational
arithmetic in both enumerations.

Finite tests do not establish the universal theorem, and the
algebraic Plackett–Luce ordering law is **not** by definition the
pushforward of a product measure on independent continuous Exp clocks.
That latter connection remains a **separate** S019 target. Neither
an EGU graph classification update nor an independent novelty claim
follows from S018.
