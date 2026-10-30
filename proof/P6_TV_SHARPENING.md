# S004: sharpened total-variation separation for P6

**Theorem (IG-N3, strengthened).** For the path P6 with strictly
positive independent exponential vertex rates, let Q be its terminal
greedy maximal-independent-set law and U the uniform law on its five
maximal independent sets. Then

    ||Q-U||_TV ≥ 2 sqrt(2/5) - 6/5
               = 0.0649110640673518... > 1/16 > 1/25.

This improves the S003 bound 1/25. It is a self-contained analytic
proof, not a numerical search or a full Lean certificate.

## Two disjoint output events

Use the notation and full event proof in P6_OBSTRUCTION.md. Write

    p = uv = Q(E),          E = {output = {1,4}},
    q = (1-u)(1-v),        Q(F) ≤ q,
    F = {output = {0,2,5} or {0,3,5}}.

The events E and F are disjoint, with U(E)=1/5 and U(F)=2/5.
For any probability law Q, the TV distance from U dominates the
*sum of positive deficits on disjoint events*: any deficits on
E and F together are transferred to their complement. Therefore

    δ := ||Q-U||_TV
       ≥ max(0, 1/5-Q(E)) + max(0, 2/5-Q(F))
       ≥ max(0, 1/5-p) + max(0, 2/5-q).            (1)

The stronger *sum*, rather than a maximum of the two deficits,
is the improvement over S003.

## One-dimensional minimisation

By Cauchy-Schwarz applied to vectors
(sqrt(u),sqrt(1-u)) and (sqrt(v),sqrt(1-v)),

    sqrt(p) + sqrt(q) ≤ 1.

Set x=sqrt(p)∈[0,1]; then q≤(1-x)^2. Equation (1) implies

    δ ≥ f(x)
      = max(0, 1/5-x²) + max(0, 2/5-(1-x)²).      (2)

Put a=1-sqrt(2/5) and b=sqrt(1/5), so 0<a<b<1.
For 0≤x≤a, f(x)=1/5-x², decreasing; its minimum is f(a).
For a≤x≤b, both deficits are nonnegative and

    f(x) = -2/5+2x-2x².

This is concave, so the minimum on [a,b] occurs at an endpoint.
For b≤x≤1, f(x)=2/5-(1-x)², increasing; its minimum is f(b).

The endpoint values are

    f(a) = 2 sqrt(2/5)-6/5 ≈ 0.064911064...
    f(b) = 2 sqrt(1/5)-4/5 ≈ 0.094427191...

and f(a)<f(b). Thus f(x)≥f(a) on [0,1], proving the
claimed universal lower bound.

Finally, f(a)>1/16 follows by squaring
sqrt(2/5)>101/160 (since 2/5>10201/25600).

## Sharpness qualification

For the two-event inequality data alone the bound is best
possible: choose u=v=a=1-sqrt(2/5). Then p=a² and
q=(1-a)²=2/5, and the lower bound in (1) equals f(a).
This does NOT assert a P6 rate vector with true Q(F)=q
or full TV distance equal to f(a); additional output constraints
may give a stronger bound.

No end-to-end Lean proof of the TV inequality is claimed here;
the S003 imported Lean theorem certifies the weaker conditional
algebraic 1/25 inequality. An S005 goal is to connect the complete
finite output law to these disjoint-event deficits and optionally
formalise the stronger bound.
