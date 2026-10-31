# S008 — Every complete-graph corona is EGU

**IG-P8 (complete informal theorem).** For every integer m >= 1, form
C_m from a clique on m vertices c_1,...,c_m and m pendant leaves
l_1,...,l_m, where l_i has only the neighbour c_i. For independent
exponential vertex-arrival clocks, assign each leaf rate 1 and each
clique vertex rate beta = (m+1)^(1/m) - 1 > 0. Then the greedy maximal
independent set is exactly uniformly distributed over all m+1 MIS.

## Proof

Every maximal independent set must contain exactly one of l_i and c_i
for each i. It cannot contain both since they are adjacent; it must
contain at least one, since l_i has no other neighbour and could be
added if neither was selected. The clique restriction permits either
no clique vertex or exactly one. Thus the complete list consists of
L = {l_1,...,l_m} and S_i = {c_i} union (L - {l_i}), i=1,...,m.

The greedy output is L **if and only if** every leaf l_i arrives before
its partner c_i. Indeed, when all those inequalities hold, each l_i
is accepted before c_i, after which c_i is rejected. Conversely,
if a clique vertex c_i is the first centre to arrive before its own
leaf and no other centre has been accepted, it is accepted, making L
impossible. More explicitly: on the event of output L there are no
accepted centres; hence each rejected centre must have found its own
leaf already accepted, since its other neighbours are only centres.
Therefore T(l_i) < T(c_i) for every i.

The m pairs of independent exponential clocks are disjoint. For rates
1 and beta, P[T(l_i) < T(c_i)] = 1/(1+beta), independently across i.
Consequently P(output L) = (1+beta)^(-m) = 1/(m+1).

The graph and its rate assignment are invariant under all permutations
of the m leaf-centre pairs. Each S_i must therefore have the same
probability. Since their total mass is 1 - 1/(m+1) = m/(m+1), each
S_i has probability 1/(m+1). All rates are strictly positive. QED.

## Six-vertex atlas certificate

At m=3 the graph is the *net graph*, connected NetworkX n=6 atlas
index 8, with edges 04,15,23,34,35,45 in the atlas vertex labelling.
The leaves are 0,1,2 and the central triangle is 3,4,5. The exact
rate vector is (1,1,1,beta,beta,beta), beta = real_cuberoot(4)-1,
whose defining polynomial is beta^3+3beta^2+3beta-3=0, beta>0.
The four MIS are bitmasks 7,11,22,37, each of probability 1/4.

This was independently verified in exact Q(real_cuberoot(4)) arithmetic
using a first-choice active-set recursion and enumeration of all 720
full weighted priority orders, with no numerical approximation.
See tests/test_s008.py and experiments/clique_corona.py.

This is a complete paper proof and exact computation, not a Lean
formalisation of the continuous independent-clock process and not a
claim of independent publication novelty.
