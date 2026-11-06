"""S041 independent exact regression for the real-clock greedy law chain.

Independent of the Lean proofs and of experiments/exact.py.  It checks:

1. the finite-width closed product
       prod_j (1-q_j) q_j^j / (1-Q_j),   Q_j = prod_{l>=j} q_l,
   against an *independent* first-bin/memoryless recursion for strictly
   increasing geometric bins, with exact Fractions (all orders, n<=4,
   including n=0 and n=1), and against exhaustive truncated sums with an
   exact tail bound;
2. the symbolic delta -> 0+ limit of the exponential closed product equals
   the successive remaining-rate (Plackett-Luce) product, via sympy, for
   all orders of small positive integer rate vectors (n<=3);
3. the full-permutation greedy pushforward equals an independent
   first-choice recursion, the output law sums to one, and its support
   consists of maximal independent sets, on small graphs.

These are exact finite checks of particular inputs; they are not a proof
of the general theorem (that is the Lean development) and they make no
classification claim.
"""
from fractions import Fraction
from itertools import combinations, permutations
from math import prod
import unittest

import sympy as sp


def closed_form(q):
    n = len(q)
    out = Fraction(1)
    for j in range(n):
        suffix = prod(q[j:], start=Fraction(1))
        out *= (1 - q[j]) * q[j] ** j / (1 - suffix)
    return out


def memoryless_recursion(q):
    """P(K_0 < K_1 < ... ) for independent geometric bins
    P(K=k) = (1-q) q^k, k>=0, derived by conditioning on K_0 = k:
    the rest must all exceed k, and by memorylessness the shifted rest
    is a fresh copy of the same problem."""
    if not q:
        return Fraction(1)
    q0, rest = q[0], q[1:]
    rest_survive = prod(rest, start=Fraction(1))  # P(all rest >= 1)
    # sum_k (1-q0) q0^k * prod_rest q_i^(k+1) = (1-q0) R / (1 - q0 R)
    factor = (1 - q0) * rest_survive / (1 - q0 * rest_survive)
    return factor * memoryless_recursion(rest)


def truncated_strict_sum(q, cutoff):
    n = len(q)
    total = Fraction(0)
    # combinations() enumerates exactly the strictly increasing bin vectors
    for bins in combinations(range(cutoff), n):
        total += prod(((1 - q[i]) * q[i] ** bins[i] for i in range(n)),
                      start=Fraction(1))
    return total


def plackett_luce(rates):
    out = Fraction(1)
    for j in range(len(rates)):
        out *= Fraction(rates[j]) / sum(rates[j:])
    return out


def greedy(adj, order):
    accepted = set()
    for v in order:
        if not (adj[v] & accepted):
            accepted.add(v)
    return frozenset(accepted)


def permutation_law(adj, rates):
    law = {}
    for order in permutations(range(len(adj))):
        mass = plackett_luce([rates[v] for v in order])
        out = greedy(adj, order)
        law[out] = law.get(out, Fraction(0)) + mass
    return law


def first_choice_law(adj, rates, active, target):
    if not active:
        return Fraction(1) if not target else Fraction(0)
    total_rate = sum(rates[v] for v in active)
    acc = Fraction(0)
    for v in active:
        if v in target:
            rest = active - {v} - adj[v]
            acc += Fraction(rates[v], 1) / total_rate * first_choice_law(
                adj, rates, rest, target - {v})
    return acc


def is_maximal_independent(adj, s):
    n = len(adj)
    if any(adj[u] & s for u in s):
        return False
    return all(v in s or (adj[v] & s) for v in range(n))


def graph(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return [frozenset(x) for x in adj]


class S041ClosedFormTests(unittest.TestCase):
    seeds = (Fraction(1, 2), Fraction(2, 3), Fraction(3, 5), Fraction(4, 7))

    def test_closed_form_matches_memoryless_recursion(self):
        for n in range(0, 5):
            for q in permutations(self.seeds, n):
                self.assertEqual(closed_form(list(q)),
                                 memoryless_recursion(list(q)))

    def test_empty_and_singleton(self):
        self.assertEqual(closed_form([]), 1)
        self.assertEqual(closed_form([Fraction(1, 3)]), 1)

    def test_truncated_sums_bracket_closed_form(self):
        for n in range(1, 4):
            for q in permutations(self.seeds, n):
                q = list(q)
                exact = closed_form(q)
                cutoff = 30
                partial = truncated_strict_sum(q, cutoff)
                self.assertLessEqual(partial, exact)
                # missing mass lies in {some bin >= cutoff}
                tail = sum((qi ** cutoff for qi in q), start=Fraction(0))
                self.assertLessEqual(exact - partial, tail)


class S041LimitTests(unittest.TestCase):
    def test_symbolic_zero_width_limit_is_plackett_luce(self):
        d = sp.symbols('delta', positive=True)
        for rates in ((1, 2), (2, 3, 5), (1, 1, 4)):
            for order in set(permutations(rates)):
                expr = sp.Integer(1)
                for j in range(len(order)):
                    qj = sp.exp(-order[j] * d)
                    Qj = sp.exp(-sum(order[j:]) * d)
                    expr *= (1 - qj) * qj ** j / (1 - Qj)
                lim = sp.limit(expr, d, 0, dir='+')
                pl = plackett_luce(list(order))
                self.assertEqual(sp.nsimplify(lim),
                                 sp.Rational(pl.numerator, pl.denominator))


class S041GreedyLawTests(unittest.TestCase):
    graphs = {
        'P3': graph(3, [(0, 1), (1, 2)]),
        'P4': graph(4, [(0, 1), (1, 2), (2, 3)]),
        'C5': graph(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
        'K1,3': graph(4, [(0, 1), (0, 2), (0, 3)]),
        'empty0': graph(0, []),
        'K1': graph(1, []),
    }

    def test_permutation_pushforward_equals_first_choice(self):
        for name, adj in self.graphs.items():
            n = len(adj)
            rates = [Fraction(k + 2, k + 1) for k in range(n)]
            law = permutation_law(adj, rates)
            self.assertEqual(sum(law.values(), start=Fraction(0)), 1, name)
            for target, mass in law.items():
                self.assertTrue(is_maximal_independent(adj, target), name)
                self.assertEqual(
                    mass,
                    first_choice_law(adj, rates, frozenset(range(n)), target),
                    name)

    def test_permutation_masses_sum_to_one(self):
        for n in range(0, 6):
            rates = [Fraction(2 * k + 1, k + 3) for k in range(n)]
            total = sum((plackett_luce([rates[v] for v in order])
                         for order in permutations(range(n))),
                        start=Fraction(0))
            self.assertEqual(total, 1)


if __name__ == '__main__':
    unittest.main()
