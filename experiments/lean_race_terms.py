import sympy as sp
from fractions import Fraction

def race_terms(L, nb, fuel, active, target):
    if fuel == 0:
        return [[]] if not active and not target else []
    if not active:
        return [[]] if not target else []
    out = []
    for v in L:
        if v in active and v in target:
            after = active - ({v} | nb[v])
            for t in race_terms(L, nb, fuel - 1, after, target - {v}):
                out.append([(v, [w for w in L if w in active])] + t)
    return out

def law(n, nb, target, r):
    L = list(range(n))
    tot = 0
    for t in race_terms(L, nb, n, frozenset(L), frozenset(target)):
        term = 1
        for v, S in t:
            term *= r[v] / sum(r[w] for w in S)
        tot += term
    return tot

def graph(n, edges):
    nb = [set() for _ in range(n)]
    for a, b in edges:
        nb[a].add(b); nb[b].add(a)
    return [frozenset(x) for x in nb]

def all_pos(expr, syms):
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    P = sp.Poly(sp.expand(num), *syms)
    Q = sp.Poly(sp.expand(den), *syms)
    return all(c > 0 for c in P.coeffs()), all(c > 0 for c in Q.coeffs()), P, Q
