# S007 — False-twin invariance of exponential greedy uniformity

**IG-P7 (complete informal proof).** Let G be a finite simple graph with
two distinct **false twins** x,y: they are nonadjacent and have exactly
the same open neighbourhood. Let H=G-y, retaining x. Then G is EGU
(with all independent exponential rates strictly positive) if and
only if H is EGU. More strongly, every positive rate vector on G
has exactly the same terminal output law as on H under the canonical
bijection of maximal independent sets, after replacing the rate of x
by lambda_x+lambda_y and leaving other rates unchanged.

## Proof

Every maximal independent set of G contains either **both** x and y
or **neither**: if one twin is in an independent set and the other is
not, the missing twin is still nonadjacent to every selected vertex,
so the set is not maximal. Conversely the map
S subset V(H) -> S (if x not in S), or (S-{x}) union {x,y} (if x in S)
is a bijection of maximal independent sets of H and G. The inverse
deletes y. Independence and maximality follow because x,y have
identical neighbours and no edge between them.

Give G strictly positive exponential arrival rates lambda. The
minimum T=min(T_x,T_y) of the two independent clocks has exponential
rate lambda_x+lambda_y, and is independent of all other vertices'
clocks. Thus the induced first-arrival order of the grouped twin
class {x,y} and the other singleton classes is precisely the
weighted priority-order law of H with aggregate rate at x.

It remains to check that accepting/rejecting the grouped class
commutes with greedy scanning. At time T, the first twin is accepted
if and only if no common neighbour has already been accepted.
If a common neighbour has already been accepted, both twins are
rejected. If the first twin is accepted, no common neighbour can ever
be accepted later, because it conflicts with that twin, so the second
twin is necessarily accepted whenever its clock rings. Since neither
twin is adjacent to the other, the accepted/rejected status of every
other vertex also agrees with the contracted process. Thus the
terminal output is the image of the H output under the above bijection,
pathwise, and the probabilities agree exactly.

Conversely, for any positive rate mu on H, assign lambda_x=lambda_y
=mu_x/2 and lambda_z=mu_z for z other than x,y. These rates are
strictly positive and yield the same law. Hence uniformity is
equivalent in the two graphs. QED.

**Warning:** The proof is special to genuine false twins. An arbitrary
induced copy of P5 in a six-vertex graph is not an obstruction.
This theorem is not yet Lean formalised; it is a self-contained
mathematical reduction plus independently checked exact tests.

## Application to the connected six-vertex atlas

The six-vertex NetworkX connected graph-atlas order is used throughout.
For each newly settled graph, the pair below consists of nonadjacent
equal-neighbourhood vertices. Deleting the second gives the indicated
connected five-vertex parent (up to graph isomorphism). Each positive
parent is already equipped with an explicit S005 rate certificate.
The rate at its retained twin is halved on lifting, so all new rates
are strictly positive. Parent 15 uses exact Q(sqrt(3)) arithmetic;
the others use positive rational rates.

| n=6 index | false-twin pair | n=5 parent | result |
|---:|:---:|---:|:---|
| 2 | (1,2) | 1 | EGU |
| 4 | (1,2) | 2 = P5 | not EGU |
| 7 | (1,2) | 4 | EGU |
| 10 | (2,3) | 1 | EGU |
| 13 | (4,5) | 2 = P5 | not EGU |
| 14 | (1,2) | 5 | EGU |
| 16 | (1,2) | 2 = P5 | not EGU |
| 27 | (1,2) | 5 | EGU |
| 28 | (1,3) | 6 | EGU |
| 32 | (1,5) | 1 | EGU |
| 33 | (2,5) | 5 | EGU |
| 43 | (3,5) | 9 | EGU |
| 45 | (1,2) | 4 | EGU |
| 48 | (1,2) | 5 | EGU |
| 54 | (1,5) | 11 | EGU |
| 59 | (1,5) | 6 | EGU |
| 63 | (1,5) | 9 | EGU |
| 66 | (1,5) | 15 | EGU |
| 72 | (0,4) | 9 | EGU |
| 77 | (3,5) | 11 | EGU |
| 85 | (0,4) | 15 | EGU |
| 101 | (4,5) | 15 | EGU |

For the 19 positive rows, `tests/test_s007.py` constructs the
six rates from the **actual graph isomorphism** and checks all maximal
independent sets and all 720 weighted priority orders with two
independent exact evaluators (rational or quadratic number field).
For the three negative rows, the proof above transports the P5
strict inequality obstruction; tests independently verify the
graph-theoretic contraction. Their negative status does not rely on
a bounded computational search.

**Atlas update:** 143 connected graphs of order <=6 =
89 positive, 7 negative, 47 unresolved. Among six-vertex graphs,
59 positive, 6 negative, 47 unresolved. This is not a complete
six-vertex classification and not an independently certified novelty claim.
