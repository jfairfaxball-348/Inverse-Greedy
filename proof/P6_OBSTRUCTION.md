# IG-N3: An exact two-block race obstruction for P6

**Theorem.** The six-vertex path P6 is not EGU: no strictly positive
independent exponential rates make the terminal greedy maximal independent
set uniform.

**Proof.** Label the vertices 0–1–2–3–4–5 and their rates a,b,c,d,e,f>0.
The five maximal independent sets are

    024, 025, 035, 135, 14.

Set

    u = b/(a+b+c),        v = e/(d+e+f).

Let L be the event that vertex 1 is the first arrival among {0,1,2},
and R the event that vertex 4 is first among {3,4,5}. Because these
triples are disjoint and all clocks independent, L,R are independent,
P(L)=u, P(R)=v.

**Claim 1: the terminal output is {1,4} if and only if L and R occur.**
If L and R occur, vertices 1 and 4 are accepted (each precedes both
its neighbours). Their closed neighbourhoods cover all six vertices,
so the terminal set is exactly {1,4}.

Conversely suppose the output is {1,4}. Vertex 0 cannot precede 1:
0 has no other neighbour and would be accepted. Vertex 2 cannot
precede 1: if it did, rejection of 2 would require its other neighbour
3 to have been accepted before it, which would exclude 4. Therefore
1 precedes both 0 and 2. Symmetrically, 5 cannot precede 4; and if
3 preceded 4, its rejection would require 2 to have been accepted,
excluding 1. Thus 4 precedes 3 and 5. The converse follows.
So

    P(output=14) = u*v.                                 (1)

**Claim 2: the probability of either output 025 or 035 is at most
(1-u)(1-v).** Both of these terminal sets contain vertices 0 and 5.
If L occurred then vertex 1 would be accepted, excluding 0; if R
occurred then vertex 4 would be accepted, excluding 5. Therefore
the event {output in {025,035}} is contained in not-L and not-R.
Independence yields

    P(output in {025,035}) <= (1-u)*(1-v).             (2)

Suppose uniformity. All five maximal independent sets have probability
1/5, hence (1) and (2) give

    u*v = 1/5,           2/5 <= (1-u)*(1-v).

Expanding the latter gives u+v <= 4/5. But u,v>0 and

    (u+v)^2 = (u-v)^2+4*u*v >= 4/5 > 16/25.

Since u+v is nonnegative, u+v <=4/5 would imply
(u+v)^2 <=16/25: contradiction. QED.

**Scope/rigour.** This is a complete probability/event proof for all
strictly positive real rates, independent of numerical optimisation.
Its purely algebraic final contradiction is captured separately
in InverseGreedy/P6Bottleneck.lean; the full event/race equivalences
remain informal, checked independently by exhaustive permutation and
exact rational tests. It does NOT show that an arbitrary graph
containing an induced P6 is non-EGU. A P6 connected component is an
obstruction by IG-P2.
