"""S009: universal strict corona(P3) probability minor.

All 729 small integer rate vectors are checked exactly against the
closed form and factorisation. A separate all-permutations oracle
cross-checks asymmetric rate assignments. Failed finite search does
NOT enter the non-EGU proof.
"""
import sys
import unittest
from fractions import Fraction
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import graph, law_by_recursion, law_by_permutations, maximal_independent_sets

# Private leaf of central 0,1,2 is respectively 3,4,5.
EDGES = ((0, 1), (1, 2), (0, 3), (1, 4), (2, 5))
ADJ = graph(6, EDGES)
# Expected: ac, c, b, a, empty (sets of selected centres).
AC, C_ONLY, B_ONLY, A_ONLY, EMPTY = 21, 28, 42, 49, 56


def corner_probabilities(rates):
    a, b, c, A, B, C = tuple(map(Fraction, rates))
    if min(a, b, c, A, B, C) <= 0:
        raise ValueError("rates must be strictly positive")
    u, v = a + A, c + C
    x, y = a / u, c / v

    def f(t):
        return (B + t) / (b + B + t)

    corner = {
        EMPTY: (1 - x) * (1 - y) * f(0),
        A_ONLY: x * (1 - y) * f(u),
        C_ONLY: (1 - x) * y * f(v),
        AC: x * y * f(u + v),
    }
    positive_minor = (x * (1 - x) * y * (1 - y) * b * u * v
        * (2 * B + b + u + v)
        / ((b + B) * (b + B + u) * (b + B + v) * (b + B + u + v)))
    assert positive_minor > 0
    assert corner[A_ONLY] * corner[C_ONLY] - corner[EMPTY] * corner[AC] == positive_minor
    return corner, positive_minor


class CoronaP3ObstructionTests(unittest.TestCase):
    def test_original_atlas_index_and_mis(self):
        import networkx as nx
        atlas6 = [g for g in nx.graph_atlas_g()
                  if len(g) == 6 and nx.is_connected(g)]
        self.assertEqual(
            sorted(tuple(sorted(e)) for e in atlas6[3].edges()),
            [(0, 1), (1, 2), (1, 3), (2, 4), (3, 5)])
        self.assertTrue(nx.is_isomorphic(atlas6[3], nx.Graph(EDGES)))
        self.assertEqual(set(maximal_independent_sets(ADJ)),
                         {AC, C_ONLY, B_ONLY, A_ONLY, EMPTY})

    def test_729_exact_rate_vectors(self):
        for rates in product((1, 2, 3), repeat=6):
            law = law_by_recursion(ADJ, rates)
            corner, minor = corner_probabilities(rates)
            self.assertEqual(sum(law.values()), 1)
            self.assertEqual(set(law), {AC, C_ONLY, B_ONLY, A_ONLY, EMPTY})
            for mask, p in corner.items():
                self.assertEqual(law[mask], p)
            self.assertEqual(law[A_ONLY] * law[C_ONLY] -
                             law[EMPTY] * law[AC], minor)

    def test_independent_permutation_oracle(self):
        for rates in ((1,)*6, (3, 7, 2, 5, 4, 9),
                      (1, 10, 1, 1, 40, 1), (11, 2, 13, 3, 7, 5)):
            recursion = law_by_recursion(ADJ, rates)
            orders = law_by_permutations(ADJ, rates)
            self.assertEqual(recursion, orders)
            corner, _ = corner_probabilities(rates)
            for mask, p in corner.items():
                self.assertEqual(orders[mask], p)


if __name__ == "__main__":
    unittest.main()
