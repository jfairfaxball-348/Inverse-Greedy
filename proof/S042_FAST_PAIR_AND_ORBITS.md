# S042 — fast-pair theorem for every pendant star corona; exact n=6 orbit audit

Date: 2026-11-06. Working base: `main` `f82a6ee8a0072440cd6e200ceac8fd6d90472a39`.

## Result A: IG-N6 for all star sizes — complete mathematical proof

Let `m >= 2` and let `G_m = K_{1,m} ∘ K_1`. There is a
central hub `h`, its leaf `h'`, and `m` pairs `(s_i,s'_i)`.
The hub is adjacent to every `s_i` and to `h'`; each `s_i` is adjacent
to its leaf `s'_i`. No other edges are present.

A maximal independent set must contain exactly one endpoint of each
pendant edge, since it cannot contain both endpoints, and omission of
both would leave the pendant leaf addable. The selected nonleaf
vertices must form an independent set in the underlying star.

Therefore there are exactly `N = 2^m + 1` maximal independent sets:
one `A = {h,s'_1,...,s'_m}` and, for each `S ⊆ {1,...,m}`, the set
`B_S = {h'} ∪ {s_i: i∈S} ∪ {s'_i: i∉S}`.

For any `t>0`, give the vertices **strictly positive** exponential
rates

- `r(h) = t`;
- `r(h') = 2^m*t`;
- `r(s_i) = r(s'_i) = 1` for all `i`.

Set `Λ = Nt+2m`. The probability that `h` is the first vertex of
the full exponential race is `t/Λ`. If it is first, greedy accepts
`h`, rejects every spoke, and accepts every spoke leaf, producing
**exactly** `A`.

The probability that `h'` is first is `2^m*t/Λ`. If it is first,
greedy accepts `h'` and rejects `h`. What remains consists of
`m` disjoint edges `(s_i,s'_i)`, each with equal rates 1 and 1.
The independent exponential memoryless property (equivalently the
first-choice recursive law and its disjoint-union theorem) makes the
choices on these `m` edges independent and equiprobable. Thus for
every `S`,

`P(output=B_S | h' first)=2^{-m}`.

Combining the two first-choice cases gives the *same lower bound* for
every maximal independent set `I`:

```text
P_t(I) >= t / ((2^m + 1)t + 2m) =: a_t.
```

A useful stronger description is an exact mixture:

```text
P_t = p_t U + (1-p_t) R_t,
p_t = Nt/(Nt+2m),
```

where `U` is uniform on all `N` maximal independent sets and
`R_t` is the conditional output law when a spoke or a spoke leaf
is the first vertex. The first event has probability `Nt/Λ`,
and its conditional output is uniform, because `h` wins with
conditional probability `1/N` and `h'` wins with `(N-1)/N`,
followed by `2^m=N-1` independent equiprobable decisions.

By convexity of total variation, or by
`TV(P_t,U) = 1 - Σ_I min(P_t(I), 1/N)`, we obtain

```text
0 <= TV(P_t,U) <= 1-p_t = 2m / ((2^m + 1)t + 2m).
```

The right-hand side tends to zero as `t → +∞`; for any
`ε>0`, it suffices to take `t > 2m/((2^m+1)ε)`.
This proves `RealClockAEGU G_m` **mathematically for every m>=2**.
The previously Lean-certified theorem `starCorona_not_realClockEGU`
(S041; `GeneralFamilies.lean`) proves `¬ RealClockEGU G_m`
for every m>=2. Therefore all these graph families are AEGU but not EGU.
This argument recovers the previous `m=2` family
`(1,t,1,1,4t,1)` up to simultaneous rescaling of the spoke rates
and uses no numerical minimisation.

**Formal boundary:** This all-m AEGU theorem is a *complete mathematical
proof*, not yet an imported Lean theorem. The existing `m=2`
unattained-AEGU result and the all-m non-EGU result ARE in imported Lean.
The new general proof should be translated using the first-choice law,
the union law on the remaining equal-rate matching, the MIS cardinality
`2^m+1`, and the standard finite-TV bound. Do not describe it as
Lean-verified until the full Lean module compiles in CI.

## Result B: exhaustive exact six-vertex graph orbit computation

`experiments/s042_six_vertex_orbits.py` enumerates **every**
15-bit symmetric irreflexive labelled graph on six vertices, without
NetworkX and without sampling. Adjacent vertex swaps generate the
symmetric group. A breadth-first orbit search records, for every
labelled graph, a representative and an explicit six-element
vertex permutation carrying the graph to that representative.
Every permutation witness is independently checked edge by edge.

Exact output:

```text
n=6: labelled=32768, unlabeled=156, connected=112, disconnected=44
```

The classification of **all** 156 six-vertex unlabelled graphs by
isomorphism is a rigorously checked finite computation in Python,
not an imported Lean proof. The connected n=6 atlas (112 classes,
60 previously EGU-certified, 7 previously non-EGU-certified and
45 unresolved) is unchanged. In particular, this orbit calculation
does **not** resolve those 45 cases and does not by itself certify that
a separate NetworkX record and its mathematical EGU label belong
to any given orbit. The next Lean task is to import the witness table
with a self-certifying Boolean edge-vector checker, and connect each
representative to its graph-theoretic certificate or explicit
unresolved designation. Do not equate an exact Python orbit audit
with a Lean theorem.

The generator supports an optional `--emit-json PATH` flag to export
the full 32768-entry table for subsequent Lean generation.

## Independent regression

`tests/test_s042.py`: fresh standard-library `fractions.Fraction`
first-choice recursion; exact checks for `m=2,...,6` and several
positive `t`, including all MIS probabilities, strict nonzero TV,
the pointwise lower bound and the explicit TV bound; construction of
examples with TV below chosen epsilon. It also checks all 32768
permutation-orbit certificates. These finite checks support, but
cannot replace, the all-m mathematical proof.

## Status / next

- IG-N6 all m: **proved mathematically**; only m=2 is Lean formalised.
- Six-vertex graph enumeration: **exhaustive exact independent Python**;
  Lean exhaustiveness remains open.
- Connected atlas: **90 EGU / 8 non-EGU / 45 unresolved** for n<=6.
- No claim of novelty, journal acceptance, or Palomar registration.
- Next prompt: `sessions/S043.md`.
