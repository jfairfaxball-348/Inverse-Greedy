# IG-N1: Sharp nonuniformity certificate for C6

**Theorem.** For independent strictly positive exponential arrival rates on the six-cycle C6, the terminal greedy maximal independent-set distribution is never uniform.

**Stronger inequality.** If p1,p2,p3 are the output probabilities of the three independent *opposite pairs*, then p1*p2*p3 <= 1/729. Equality occurs for equal rates.

**Proof.** Label the cycle vertices 0,1,2,3,4,5 in cyclic order. The five maximal independent sets are alternating triples {0,2,4} and {1,3,5}, and opposite pairs {0,3}, {2,5}, {4,1}.

Denote the even rate in opposite pair i by a_i and its odd rate by d_i, for i=1,2,3. Let A=sum_i a_i and D=sum_i d_i. To produce pair i, the first accepted vertex must be one of its members. After choosing a_i, the active induced graph is a three-vertex path, and d_i must arrive before the two other even vertices. After choosing d_i, the mirror condition holds. Consequently the first-choice recurrence gives

p_i = [a_i/(A+D)] * [d_i/(A-a_i+d_i)]
    + [d_i/(A+D)] * [a_i/(D-d_i+a_i)]
    = a_i*d_i / [(A-a_i+d_i)*(D-d_i+a_i)],

because the two bracket denominators sum to A+D.

For {i,j,k}={1,2,3}, AM-GM gives

A-a_i+d_i = a_j+a_k+d_i >= 3*(a_j*a_k*d_i)^(1/3),
D-d_i+a_i = d_j+d_k+a_i >= 3*(d_j*d_k*a_i)^(1/3).

Multiply these six inequalities. Every a_i and d_i occurs with total exponent (2+1)/3=1, hence

product_i [(A-a_i+d_i)*(D-d_i+a_i)] >= 3^6 * product_i(a_i*d_i).

All rates are positive, so divide to obtain product_i p_i <= 3^(-6)=1/729. Equal rates make all three pair probabilities 1/9, attaining equality.

If the complete terminal law were uniform, C6 has five MIS, forcing each opposite-pair probability p_i=1/5. Their product 1/125 is strictly greater than 1/729. Contradiction. QED.

**Status:** complete informal proof, exact checked examples, **not** Lean formalised; originality not fully audited. Disjoint-component closure excludes any graph with a C6 component, not every induced C6.
