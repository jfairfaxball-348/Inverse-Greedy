# S033 — actual-clock bin-chamber comparison and finite-family pair collision

**Date:** 2026-11-03. [PR #32](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/32).

## Exact claims and scope

This is a **partial** S033 execution. The imported Lean modules are
`InverseGreedy/FiniteClockBinChambers.lean` and
`InverseGreedy/FiniteClockPairBinCollision.lean`.

For a finite list `order = [i₁,…,iₘ]`, true continuous clock
assignment `ω : ι → ℝ`, and width `δ>0`, let

- `C(order)`: every required real-clock inequality is strict,
- `Bδ(order)`: every required **actual ceiling-bin** inequality is strict,
- `Dδ(order)`: at least two ordered list positions share the same bin.

The ceiling map is monotone. It follows **pointwise**, including
nonpositive times and half-open cell endpoints, that

```text
Bδ(order) ⊆ C(order) ⊆ Bδ(order) ∪ Dδ(order).
```

The first inclusion follows because reverse clock inequality would
imply reverse weak bin inequality. For the second, if real clocks are
strict but a bin comparison is not strict, monotonicity makes the
corresponding two bins equal.

These inclusions are imported Lean theorems. Their consequence for the
**genuine** finite-product Exp measure is also imported:

```text
P(Bδ(order)) ≤ P(C(order))
             ≤ P(Bδ(order)) + P(Dδ(order)).
```

Crucially, `P` is `finiteIndependentExp rates`, NOT an assumed
Plackett–Luce permutation measure.

## Genuine pair collision bound in arbitrary finite families

S022 established the true two-coordinate map law for any distinct
`i,j`, and S029 established the true two-clock same-ceiling-bin bound.
This session transports that bound through the genuine marginal map:

```text
P(Kδ(Tᵢ) = Kδ(Tⱼ)) ≤ ENNReal.ofReal(δ * min(rᵢ, rⱼ))
```

for all positive rates, `δ>0`, and `i ≠ j`, even in the presence
of arbitrarily many other clocks. The collision equality set is Borel
because the real-to-natural ceiling map is measurable.

If the list has no repeated indices, the ordinary finite union bound
then gives, **mathematically**,

```text
P(Dδ(order)) ≤ δ * ∑_{a<b} min(r_{order[a]}, r_{order[b]}).
```

The final **finite union bound itself is not yet imported in Lean**,
and neither the strict-bin multi-geometric series evaluation nor its
zero-width limit is formalised. Thus there is still no imported Lean
proof of the general `P(C(order)) = orderMass rates order` theorem.

## Independent regression

`tests/test_s033.py` exhaustively checks the pointwise inclusions on
small real-clock lists with ties, nonpositive times and bin endpoints;
checks the exact two-geometric collision sum; and checks the finite
pairwise union upper bound for bounded geometric configurations with
`Fraction`. These support, but do not replace, the Lean theorems.

## Outstanding obligations

1. Import a finite union bound over distinct positions of a complete
   no-duplicate vertex order, obtaining a quantitative `O(δ)` bound.
2. Prove the true joint strict-bin measure as a countable sum of S032's
   rectangle masses; formally sum via multi-gap geometric products.
3. Prove the positive-width product limit and squeeze the actual
   `strictClockChamber` mass to `ENNReal.ofReal (orderMass rates order)`
   for every finite complete permutation, including empty/singleton.
4. Construct a measurable deterministic tie-broken sorting map and
   prove its fibres, pushforward mass, and continuous greedy-output
   distribution match S018.

Do not promote these unproved goals to Lean-verified claims. Atlas
unchanged: **90 EGU / 8 non-EGU / 45 unresolved** for connected
graphs through six vertices. No independent novelty certificate.
