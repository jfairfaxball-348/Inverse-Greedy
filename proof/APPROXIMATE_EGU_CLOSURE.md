# S010 — Closure and inheritance of unattained approximate greedy uniformity

All graphs here are finite and simple, with *strictly positive* exponential
vertex rates. For a graph G, let M(G) denote its nonempty finite set of
maximal independent sets, N_G=|M(G)|, P_G(r) the greedy-output law at
rates r, and U_G the uniform distribution on M(G). Define

    d_G = inf_{r_v>0} TV(P_G(r), U_G).

Call G **approximately EGU (AEGU)** if d_G=0. The infimum need not be
achieved. Call G **unattained AEGU** if d_G=0 but G is not EGU.
These labels are separate from EGU, which requires exact uniformity at
finite positive rates. They make no novelty claim.

## IG-P9: exact closure of AEGU under disjoint union

**Theorem.** G ⊔ H is AEGU iff G and H both are AEGU.

**Proof.** The clocks and accept/reject decisions on different
components are independent, so their terminal law is P_G ⊗ P_H and
their target uniform law is U_G ⊗ U_H.

If both factors are AEGU, use any positive rate vectors giving
TV(P_G,U_G)<ε/2 and TV(P_H,U_H)<ε/2. The standard coupling bound
TV(P_G⊗P_H,U_G⊗U_H)≤TV(P_G,U_G)+TV(P_H,U_H)<ε.

Conversely, each marginal of the joint terminal law is exactly the
corresponding component law. Total variation cannot increase under
taking a marginal, so for *every* positive joint rate vector
TV(P_G,U_G) and TV(P_H,U_H) are both at most
TV(P_G⊗P_H,U_G⊗U_H). Infimum zero for the union therefore implies
infimum zero in both components. QED.

**Exact TV with a uniform partner.** If H is EGU and has fixed
uniformising rates, then, for every choice of positive rates on G,

    TV(P_G⊗U_H,U_G⊗U_H) = TV(P_G,U_G).

The identity follows by summing absolute differences over H. Thus
if G is unattained AEGU, so is G⊔H: convergence is preserved, and
exact uniformity of the union would force exact uniformity of G.

## IG-P10: exact closure of AEGU under graph join

**Theorem.** For *nonempty-vertex* graphs G and H, G ∨ H is AEGU
iff G and H both are AEGU.

**Proof.** All vertices of G are adjacent to all vertices of H, so
each maximal independent set of the join lies entirely in one factor.
Let N_G and N_H be the counts of maximal independent sets of its
two factors, and put q=N_G/(N_G+N_H)∈(0,1).

Let R_G and R_H denote the respective total rates. Conditioning on
which block has the first arrival gives

    P_(G∨H) = w P_G ⊕ (1-w) P_H,    w=R_G/(R_G+R_H).

In this equation, the factor law is the same greedy law as if the
other factor were absent: the minimum of the exponential clocks in
each block is independent of the winner's identity and of the
subsequent internal exponential priority ordering.

For the sufficient direction, select any positive rates on G and
H with factor laws approaching U_G and U_H. Rescale the entire
G rate vector by a common positive factor, without changing P_G,
so that w=q. The disjoint-support identity then gives **exactly**

    TV(P_(G∨H), U_(G∨H))
      = q TV(P_G,U_G) + (1-q) TV(P_H,U_H).

The right-hand side tends to zero.

For necessity, if the joined laws converge to U_(G∨H), the total
probability w of G outcomes converges to q. For each sufficiently
late law w>0 and 1-w>0, and the conditional laws on the two outcome
blocks are P_G and P_H. Since the uniform limit gives each block a
strictly positive limiting probability, both conditional laws
converge to their corresponding uniforms. Hence both factors are
AEGU. QED.

**Unattained inheritance.** If G is unattained AEGU and H is any
AEGU nonempty graph, then G∨H is unattained AEGU: the theorem gives
approximation, while exact uniformity of a join would condition to
an exact uniform law on G, contradicting G not EGU.

## Explicit infinite descendants of the S009 obstruction

For each m≥2, put C_m=K_(1,m) corona K1, with
k=2^m and N_(C_m)=k+1. S009 proves that C_m is unattained AEGU.
For each t>0 its strictly positive rates satisfy:

    rate(a_i)=rate(A_i)=1,   rate(b)=t,  rate(B)=k*t.

Let D_m(t)=TV(P_(C_m)(t),U_(C_m)).
S009 gives 0<D_m(t)<m/((k+1)^2 t).

1. **Disjoint union with K2.** K2 at equal rates is uniform on its
   two single-vertex maximal independent sets. Consequently

       TV(P_(C_m ⊔ K2), U_(C_m ⊔ K2)) = D_m(t) → 0,

   and exact EGU remains impossible. This gives an explicit
   unattained AEGU example of order 2m+4.

2. **Join with K1.** Add one universal vertex z with rate
   R_(C_m)/(k+1), where R_(C_m)=(k+1)t+2m is the total
   rate of C_m. Then the first arrival is in C_m with probability
   (k+1)/(k+2), matching its share of the k+2 terminal maximal
   sets. The singleton outcome {z} has probability 1/(k+2).
   Therefore the exact TV identity is

       TV(P_(C_m ∨ K1), U_(C_m ∨ K1))
         = (k+1)/(k+2) * D_m(t) → 0.

   But C_m∨K1 cannot be EGU, by the join necessity theorem.
   This gives a connected unattained AEGU example of order 2m+3.

These are distinct graph constructions with explicit strictly
positive t-dependent rates and *unattained* TV infimum zero. The
results do not decide any of the 45 outstanding six-vertex atlas
cases; the smallest new join example has seven vertices.

## Verification and formalisation boundary

tests/test_s010.py independently evaluates the two descendants via
the exact rational first-choice recursion, checks total-variation
identities for several strictly positive values of t, and compares
a seven-vertex join with the full weighted-permutation oracle.

The present Lean work proves fuel invariance and local blocked
vertex deletion in the finite model. **It does not yet formalise**
the full weighted permutation pushforward, these closure theorems,
or the continuous exponential-clock interpretation.
