# IG-N2: Strict probabilistic obstruction for the five-vertex path

**Theorem.** For strictly positive rates (a,b,c,d,e) on the
path 0–1–2–3–4, let p_024,p_03,p_13,p_14 denote its four
terminal maximal-independent-set probabilities. Then

    p_024 * p_13 > p_03 * p_14.

Consequently **P5 is not exactly uniformisable**: uniformity would
make both sides equal to 1/16.

**Proof (exact rational factorisation, no numerical assumptions).**
The four maximal independent sets are {0,2,4}, {0,3}, {1,3}, {1,4}.
Let B=a+b, E=d+e and T=B+c+E. First-arrival
conditioning (IG-R1) gives

    p_03 = a*d / (B*(c+E)),
    p_13 = b*d*(B+E) / (T*B*E),
    p_14 = b*e / (E*(B+c)),
    p_024 = c/T + a*(c+e)/(T*(c+E)) + e*(a+c)/(T*(B+c)).

The first and third formulas simplify the two possible first-arrival
branches; all denominators are positive.

In particular,

    p_03 * p_14 / p_13 = a*e*T / ((B+c)*(c+E)*(B+E)).

Direct algebra now yields the compact exact identity

    p_024 - p_03*p_14/p_13
     = c/T * [1 + e/(B+c)
       + a/(c+E) * (1 - e*c/((B+c)*(B+E)))].

Every displayed rate is positive. Moreover e < B+E and c < B+c,
so e*c < (B+c)*(B+E). The bracket is strictly positive,
as are c/T and p_13. Multiplying by p_13 proves the strict
probability minor.

The identity was independently checked with exact Fraction
arithmetic on all 3^5=243 rate tuples in {1,2,3}^5.
The proof is the explicit algebra and inequality above, not those
finite tests. Lean formalisation of the P5 law and inequality remains
open.

**Consequence.** Combining IG-N2 with IG-P2 and the cograph/P4
theorems shows that P5 is a smallest-order graph obstructing EGU.
This does **not** prohibit induced-P5 supergraphs, only P5 itself and
graphs having a P5 connected component (via IG-P2).
