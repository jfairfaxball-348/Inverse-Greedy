# IG-N4: the cone over P5 is not exactly greedy-uniformisable

**Graph.** Let H be the five-vertex path with vertices 0--1--2--3--4.
Add a sixth vertex z adjacent to every vertex of H. The resulting
connected graph is the join G = P5 ∨ K1, appearing at **index 68**
of the connected unlabeled NetworkX six-vertex atlas.

**Theorem (IG-N4).** For every strictly positive vector of six
independent exponential rates, the greedy maximal independent set
output on G is not uniform over its five maximal independent sets.

**Proof.** Write A for the sum of five rates in H, and c>0 for
the rate of z. Let Q be the greedy output law on H using the original
five rates. Since z is universal, the outcomes of G are exactly
{z} together with the four maximal independent sets of H.

The first arrival belongs to H with probability A/(A+c) and
equals z with probability c/(A+c). If z arrives first it is accepted
and all H vertices are excluded. If the first arrival belongs to H,
then z is rejected and the subsequent greedy processing of H has
the same law Q (the independence/memorylessness argument in IG-R1).
Therefore, for every maximal independent set I of H,

    P_G({z}) = c/(A+c),
    P_G(I)   = A/(A+c) Q(I).

The common factor A/(A+c) is positive. Consequently uniformity of
the four probabilities P_G(I) would imply uniformity of the P5 law
Q, contradicting the strict P5 probability minor IG-N2. Thus
G is not EGU.

Alternatively this is an immediate corollary of the already proved
join necessity IG-P4, applied to K1 and P5.

**Exact validation.** `tests/test_s004.py` tests the join factorisation
on all 3^6=729 rate vectors from {1,2,3}^6 using Fraction arithmetic,
and independently checks two vectors against all 720 weighted
permutations. These tests are corroboration of the proof, not its
all-positive-rate justification.

**Scope.** This is a distinct six-vertex connected counterexample,
not an assertion about arbitrary induced P5 subgraphs. The theorem
is proved on paper and is not claimed to be fully Lean-formalised.
