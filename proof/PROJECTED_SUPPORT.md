# S015 — Support and singleton laws for weighted priority projections

## Theorem

Let (V) be a finite active set and (A\subseteq V).
For every complete permutation \(o\) of \(V\), its subsequence
\(o|_A\) is a complete permutation of \(A\).

**Proof.** Filtering cannot duplicate any vertex, so \(o|_A\) is
duplicate-free. Because \(o\) lists each element of \(V\) exactly
once and \(A\subseteq V\), every element of \(A\) occurs once in
\(o|_A\), and no vertex outside \(A\) occurs. Thus its underlying
vertex set equals \(A\), which is precisely the complete-permutation
support condition. This is independent of vertex rates.

## Weighted consequences

With strictly positive vertex rates, put
\[
M(V,A,t)=\sum_{o\in \operatorname{Perm}(V)}
  P_V(o)\mathbf 1_{\{o|_A=t\}}.
\]

1. **Unsupported orders are impossible.** If
   \(t\notin\operatorname{Perm}(A)\), every summand is zero;
   hence \(M(V,A,t)=0\). This is true for arbitrary rates,
   even if some weights were nonpositive.
2. **Singleton retained set is exact.** When \(A=\{a\}\)
   and \(a\in V\), every complete full order projects to \([a]\).
   S011's actual-full-permutation normalization therefore gives
   \(M(V,\{a\},[a])=1\) for every strictly positive real rate vector.

The Lean implementation is
`InverseGreedy/ProjectionSupport.lean`:
`filtered_full_order_is_retained_permutation`,
`projectedOrderMass_zero_of_not_perm`,
`projectedOrderMass_singleton`.

## Exact independent regression

`tests/test_s015.py` enumerates all 7! complete orders of a
seven-vertex set with unequal positive rational rates. For all 128
retained subsets it independently compares exact projected
`Fraction` probabilities with the intrinsic Plackett–Luce
complete-order distribution on that retained subset, and checks
zero unsupported targets, mass-one normalization and singleton
determinism. The comparison is a *test*, not an all-real Lean
proof of deletion consistency.

## Remaining formal boundary

For any retained set with at least two vertices, the support theorem
does **not** determine the relative masses of its possible complete
orders. In particular it does not prove the first-retained-winner law,
full weighted deletion consistency,
`priorityOutputMass = finiteRaceLaw`, or independent exponential
clock semantics. Those are explicit S016 priorities.
