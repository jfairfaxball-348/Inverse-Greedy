# Mathematical foundations — S001

All vertex rates lambda_v are strictly positive.

## IG-R1 (exact weighted first-choice recursion)

Let N[v] denote the closed neighbourhood and Lambda(S) the sum of rates in S. For every maximal independent set I of nonempty G:

P_G(I) = sum_{v in I} [lambda_v / Lambda(V)] P_{G-N[v]}(I-{v}).

Proof: the minimum of independent exponential clocks occurs at v with probability lambda_v/Lambda(V). The first arrival v is accepted and forbids N(v). By memorylessness, residual unarrived clocks outside N[v] are independent exponentials with unchanged rates. Condition and sum over possible first v. P_empty(empty)=1.

Independently, a permutation (v1,...,vn) has probability product_i lambda_{vi}/sum_{j>=i}lambda_{vj} (size-biased permutation). Greedy scan gives the same law.

## IG-P1 (complete multipartite construction)

For K_{n1,...,nk}, all parts nonempty, the MIS outcomes are exactly its k parts. The first arrival in part j forces that entire part and no others, with probability total_rate(part j)/total_rate(V). Set every vertex in part j to rate 1/nj; every part total is 1, so each MIS has probability 1/k. In particular K_{1,m} is tuned by centre rate m and leaf rates 1.

## IG-P2 (disjoint unions)

For G = disjoint union of G_j, local greedy outputs depend only on independent clocks within their own components. Thus P_G(union I_j) = product_j P_{G_j}(I_j). Every global MIS decomposes uniquely. If component laws are uniform, the product is uniform. Conversely, global uniformity implies each component marginal is uniform. Hence EGU(G) iff all EGU(G_j).

Only a C6 *connected component* is automatically excluded by IG-N1; an induced C6 in a connected supergraph is not covered.

## IG-P3 (positive algebraic witness on P4)

For path 1-2-3-4 take rates (x,y,y,x), x,y>0. Three MIS: {1,3}, {2,4}, {1,4}. The first two have probability y/[2(x+y)] + xy/[2(x+y)^2]; the last has x^2/(x+y)^2. Set x/y=(1+sqrt(3))/2, equivalent to 3x^2=(x+y)^2. Then the last has probability 1/3 and so do the equal first two.

## Algebraic decision formulation

Every output probability is a rational function in the positive rates with positive denominators. Exact uniformity becomes a finite semialgebraic feasibility system after clearing positive denominators and optionally normalising the sum of rates per component to 1. Floating-point fits are not exact certificates.
