# S005: complete connected five-vertex EGU classification

**Theorem (IG-P5).** Among the 21 connected unlabeled simple graphs of
order five, precisely the path P5 is not EGU. Every other connected
five-vertex graph has a strictly positive vertex-rate vector for which
independent exponential priorities, scanned greedily, produce the
uniform maximal-independent-set law.

This is a constructive mathematical result. Exact data and two
independent finite-race implementations are in
`experiments/five_vertex_witnesses.py` and `tests/test_s005.py`.
It is not an independent priority/novelty certificate or a Lean
formalisation of the stochastic clock law.

## The seven newly certified positive instances

Atlas index here means position *among connected five-vertex graphs*
in `networkx.graph_atlas_g()`. Edge sets and rates use the actual
atlas vertex labels 0,...,4, so the witnesses are reproducible.

| Atlas index | Edges | Rates (vertices 0,...,4) | MIS probabilities |
|---:|---|---|---|
| 1 | 04,13,23,34 | (14,6,6,9,10) | 3 × 1/3 |
| 4 | 01,02,04,12,23 | (4,2,4,3,3) | 3 × 1/3 |
| 5 | 04,12,13,23,34 | (25,9,9,7,20) | 5 × 1/5 |
| 6 | 01,13,14,23,24 | (12,9,14,5,5) | 3 × 1/3 |
| 9 | 01,13,14,23,24,34 | (16,8,6,5,5) | 4 × 1/4 |
| 11 | 01,03,04,12,23,34 | (4,5,5,4,6) | 4 × 1/4 |
| 15 | 01,04,12,13,14,23,34 | (1+√3, 2+2√3/3, 1+√3, 2, 2) | 4 × 1/4 |

Every coordinate is strictly positive. The six integer vectors are
checked with exact `fractions.Fraction` recursion *and* an independent
120-permutation ordering oracle. The algebraic witness is checked
with two exact implementations over Q(√3), represented by pairs of
rational coefficients; there is no rounding or approximate equality.

### Exact verification principle

For any graph G with vertex rates λ>0, let L_G(I) be the probability
that the greedy output is I. First-arrival conditioning gives

    L_G(I) = Σ_{v∈I} [λ_v / (Σ_{w∈V(G)} λ_w)]
                          L_{G - N[v]}(I\{v}),

with L_empty(empty)=1. The displayed witness table consists solely of
exact substitutions into this finite rational recurrence (or the same
identity over the quadratic field Q(√3)). The independent permutation
oracle instead sums the mass

    ∏_{j=0}^{4} λ_{π(j)} / (Σ_{k=j}^{4} λ_{π(k)})

over all orders π with greedyOutput(π)=I. Both computations return the
same uniform law for each witness. The recurrence itself is derived
mathematically from independent exponential-clock minima in
`proof/FOUNDATIONS.md`; its full event-level Lean identification is
not yet complete.

### Transparent algebra for the irrational witness (index 15)

Put x=1+√3, z=2 and y=2+2√3/3. Rates are (x,y,x,z,z).
The only four maximal independent sets are {0,2}, {0,3},
{1}, {2,4}; their exact probabilities are respectively

    2x²/[(x+z)(2x+y+2z)],
    z(2x+z)/[(x+z)(2x+y+2z)],
    y/(2x+y+2z),
    z(2x+z)/[(x+z)(2x+y+2z)].

Check x>0,y>0,z>0, and the elementary identities

    2x² = z(2x+z),
    3y = 2(x+z).

The first implies (x+z)²=3x². Substitution yields
y(x+z)=2x²=z(2x+z). Consequently all four displayed
probabilities are exactly 1/4.

### Completion of the classification

There are 21 connected unlabeled graphs on five vertices.
The previous S004 census already certified 13 positive graphs,
including cographs and the algebraic P4 constructions, and the
P5 strict-minor proof certifies the only negative (index 2).
The seven witnesses above are for precisely the seven distinct
remaining atlas indices. Thus 13+7=20 positive and 1 negative,
with no unresolved five-vertex case.

This does not extend a negative statement from an *induced* P5
to arbitrary six-vertex supergraphs. It does not classify any
of the 70 remaining connected six-vertex cases.
