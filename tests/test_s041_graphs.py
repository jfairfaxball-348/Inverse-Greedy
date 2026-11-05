"""S041 independent exact regression for the graph-level Lean theorems.

Independent of the Lean proofs and of the Lean generators.  Exact Fraction /
sympy checks of particular finite inputs (not proofs):
* disjoint-union product law and join block law;
* scaling invariance;
* clique corona K_m o K1 uniform at leaf rate 1, clique rate (m+1)^(1/m)-1
  (m = 1..4, exact algebraic arithmetic);
* star corona K_{1,m} o K1 strict 2x2 minor (m = 2, 3, 4, random rates);
* false-twin law: twin extension with split rates equals the parent law;
* P5 TV along (1,1,t,1,1) equals 3/4 - 1/(t+2) - 1/(t+4);
* corona(P3) TV along (1,t,1,1,4t,1) is below 2/(25 t).
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import random
import unittest

import sympy as sp


def make(n, edges):
    nb = [set() for _ in range(n)]
    for a, b in edges:
        nb[a].add(b)
        nb[b].add(a)
    return [frozenset(x) for x in nb]


def law(nb, rates):
    """First-choice law {terminal set: probability} (independent code)."""
    n = len(nb)

    @lru_cache(None)
    def rec(active):
        if not active:
            return {frozenset(): 1}
        tot = sum(rates[v] for v in active)
        out = {}
        for v in active:
            sub = rec(active - {v} - nb[v])
            for k, p in sub.items():
                key = k | {v}
                out[key] = out.get(key, 0) + rates[v] / tot * p
        return out
    return rec(frozenset(range(n)))


def union(nbG, nbH):
    nG = len(nbG)
    return [frozenset(x) for x in nbG] + [frozenset(y + nG for y in x) for x in nbH]


def join(nbG, nbH):
    nG, nH = len(nbG), len(nbH)
    left = [frozenset(x) | frozenset(range(nG, nG + nH)) for x in nbG]
    right = [frozenset(range(nG)) | frozenset(y + nG for y in x) for x in nbH]
    return left + right


P4 = make(4, [(0, 1), (1, 2), (2, 3)])
P3 = make(3, [(0, 1), (1, 2)])
K2 = make(2, [(0, 1)])
C4 = make(4, [(0, 1), (1, 2), (2, 3), (3, 0)])


def rnd_rates(n, seed):
    rng = random.Random(seed)
    return [Fraction(rng.randint(1, 9), rng.randint(1, 5)) for _ in range(n)]


class S041GraphTests(unittest.TestCase):
    def test_union_product(self):
        for G, H in ((P4, P3), (K2, C4), (P3, P3)):
            rG, rH = rnd_rates(len(G), 1), rnd_rates(len(H), 2)
            LG, LH, LU = law(G, rG), law(H, rH), law(union(G, H), rG + rH)
            for I, p in LG.items():
                for J, q in LH.items():
                    K = I | frozenset(j + len(G) for j in J)
                    self.assertEqual(LU[K], p * q)

    def test_join_blocks(self):
        for G, H in ((P4, P3), (K2, C4)):
            rG, rH = rnd_rates(len(G), 3), rnd_rates(len(H), 4)
            LG, LH, LJ = law(G, rG), law(H, rH), law(join(G, H), rG + rH)
            lam = sum(rG) / (sum(rG) + sum(rH))
            for I, p in LG.items():
                self.assertEqual(LJ[I], lam * p)
            for J, q in LH.items():
                self.assertEqual(LJ[frozenset(j + len(G) for j in J)], (1 - lam) * q)

    def test_scaling(self):
        r = rnd_rates(4, 5)
        self.assertEqual(law(P4, r), law(P4, [7 * x for x in r]))

    def test_clique_corona_uniform(self):
        for m in range(1, 5):
            edges = [(i, m + i) for i in range(m)]
            edges += [(m + i, m + j) for i, j in combinations(range(m), 2)]
            nb = make(2 * m, edges)
            beta = sp.root(sp.Integer(m + 1), m) - 1
            rates = [sp.Integer(1)] * m + [beta] * m
            L = law(nb, rates)
            self.assertEqual(len(L), m + 1)
            for p in L.values():
                self.assertEqual(sp.nsimplify(sp.simplify(p - sp.Rational(1, m + 1))), 0)

    def test_star_corona_minor(self):
        for m in (2, 3, 4):
            # hub 0, hub leaf 1, spokes 2..m+1, spoke leaves m+2..2m+1
            edges = [(0, 1)] + [(0, 2 + i) for i in range(m)] + [(2 + i, m + 2 + i) for i in range(m)]
            nb = make(2 * m + 2, edges)
            for seed in range(5):
                L = law(nb, rnd_rates(2 * m + 2, 10 * m + seed))
                rest = frozenset(m + 2 + i for i in range(2, m))
                def T(S):
                    return frozenset({1}) | rest | frozenset(
                        (2 + i) if i in S else (m + 2 + i) for i in (0, 1))
                self.assertGreater(L[T({0})] * L[T({1})], L[T(set())] * L[T({0, 1})])

    def test_false_twin(self):
        # P5 with vertex 2 duplicated (twin 5 of 2)
        p5 = make(5, [(0, 1), (1, 2), (2, 3), (3, 4)])
        tw = make(6, [(0, 1), (1, 2), (2, 3), (3, 4), (1, 5), (3, 5)])
        r6 = rnd_rates(6, 7)
        r5 = r6[:5]
        r5[2] = r6[2] + r6[5]
        L5, L6 = law(p5, r5), law(tw, r6)
        for I, p in L5.items():
            K = I | ({5} if 2 in I else set())
            self.assertEqual(L6[frozenset(K)], p)

    def test_p5_tv_formula(self):
        p5 = make(5, [(0, 1), (1, 2), (2, 3), (3, 4)])
        for t in (Fraction(1, 3), Fraction(1), Fraction(5, 2)):
            L = law(p5, [Fraction(1), Fraction(1), t, Fraction(1), Fraction(1)])
            tv = sum(abs(p - Fraction(1, 4)) for p in L.values()) / 2
            self.assertEqual(tv, Fraction(3, 4) - 1 / (t + 2) - 1 / (t + 4))

    def test_corona_p3_tv_family(self):
        cor = make(6, [(0, 1), (1, 2), (0, 3), (1, 4), (2, 5)])
        for t in (Fraction(1), Fraction(3), Fraction(10)):
            L = law(cor, [Fraction(1), t, Fraction(1), Fraction(1), 4 * t, Fraction(1)])
            tv = sum(abs(p - Fraction(1, 5)) for p in L.values()) / 2
            self.assertGreater(tv, 0)
            self.assertLess(tv, Fraction(2, 25) / t)


if __name__ == '__main__':
    unittest.main()
