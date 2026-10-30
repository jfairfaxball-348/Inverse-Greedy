# IG-P4: Join closure and explicit uniformisation of cographs

**Model:** every vertex has an independent exponential arrival time with a
strictly positive rate; output is the terminal greedy maximal independent set.

**Theorem (join equivalence).** Let G and H be nonempty vertex-disjoint
finite simple graphs. The join G ∨ H is exactly uniformisable (EGU)
if and only if both G and H are EGU.

**Proof.** Every maximal independent set of the join lies entirely in
one factor, and is a maximal independent set of that factor. Write m,n
for the respective numbers of maximal independent sets, and let the
rate totals of G and H be A,B. The earliest globally arriving vertex
belongs to G with probability A/(A+B). The internal exponential order
in G is independent of its minimum arrival time and of H's clocks.
Conditionally on this event, the terminal set has exactly the
unconditioned greedy distribution of G. Thus for an MIS I of G,

    P_{G∨H}(I) = A/(A+B) * P_G(I),

and symmetrically for every MIS J of H.

If the join output is uniform, its restrictions to each factor are
uniform, hence each factor is EGU. Conversely, fix any positive
uniformising rates within both factors. Scale G's entire rate vector
to total m, and H's to total n. Each of the m+n global MIS then has
probability 1/(m+n). All rates remain strictly positive. QED.

**Corollary (constructive cograph theorem).** Every finite cograph
(P4-free graph), including disconnected ones, is EGU with **positive
rational rates**. Indeed the standard recursive description of
cographs starts with K1 and applies disjoint union and join.
K1 is trivially EGU; IG-P2 gives closure under union and the theorem
above gives closure under join. The construction uses only rational
arithmetic and yields a certificate algorithm (experiments/cograph.py).

**Small-order consequence.** Every graph on at most four vertices is EGU.
The only connected non-cograph on four vertices is P4, covered by
the positive algebraic witness IG-P3. Disconnected graphs inherit
uniformisability from their components. Therefore P5, which is
not EGU by IG-N2, is a smallest-order non-EGU graph.

Scope: join closure does not imply that arbitrary extensions or
induced supergraphs of P5/C6 remain non-EGU. No originality claim.
