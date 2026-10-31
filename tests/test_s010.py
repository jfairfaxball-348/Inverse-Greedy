"""S010: exact closure identities for unattained approximate EGU.

Positive rates only. Check the mathematical formulas with the general
first-choice recurrence and an independent 7! weighted-order oracle.
No finite-rate search is used to infer impossibility.
"""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import graph, law_by_recursion, law_by_permutations
from star_corona import (
    star_corona_edges, near_uniform_positive_rates, star_corona_exact_law,
)


def total_variation_to_uniform(law):
    u = Fraction(1, len(law))
    return sum((abs(p - u) for p in law.values()), Fraction(0)) / 2


def joined_to_singleton(m):
    n = 2*m + 2
    edges = star_corona_edges(m) + tuple((v, n) for v in range(n))
    return graph(n+1, edges)


def union_with_edge(m):
    n = 2*m + 2
    return graph(n+2, star_corona_edges(m) + ((n, n+1),))


class ApproximateEGUClosureTests(unittest.TestCase):
    def test_join_with_universal_vertex(self):
        for m in (2, 3):
            k = 2**m
            n = 2*m + 2
            for t in (1, 3, 11, 100):
                with self.subTest(m=m, t=t):
                    core_rates = near_uniform_positive_rates(m, t)
                    core = star_corona_exact_law(core_rates)
                    w = Fraction(k+1, k+2)
                    universal_rate = sum(core_rates, Fraction(0)) / (k+1)
                    rates = core_rates + (universal_rate,)
                    self.assertTrue(all(rate > 0 for rate in rates))
                    joint = law_by_recursion(joined_to_singleton(m), rates)
                    expected = {s: w*p for s, p in core.items()}
                    expected[1 << n] = 1-w
                    self.assertEqual(joint, expected)
                    self.assertEqual(sum(joint.values()), 1)
                    self.assertEqual(len(joint), k+2)
                    self.assertEqual(total_variation_to_uniform(joint),
                                     w*total_variation_to_uniform(core))
                    self.assertGreater(total_variation_to_uniform(joint), 0)
                    self.assertLess(total_variation_to_uniform(joint),
                                    w * Fraction(m, (k+1)**2 * t))

    def test_union_with_uniform_k2(self):
        for m in (2, 3):
            n = 2*m + 2
            for t in (1, 7, 50):
                with self.subTest(m=m, t=t):
                    core_rates = near_uniform_positive_rates(m, t)
                    core = star_corona_exact_law(core_rates)
                    rates = core_rates + (Fraction(1), Fraction(1))
                    joint = law_by_recursion(union_with_edge(m), rates)
                    expected = {}
                    for s, p in core.items():
                        expected[s | (1 << n)] = p/2
                        expected[s | (1 << (n+1))] = p/2
                    self.assertEqual(joint, expected)
                    self.assertEqual(len(joint), 2*len(core))
                    self.assertEqual(sum(joint.values()), 1)
                    self.assertEqual(total_variation_to_uniform(joint),
                                     total_variation_to_uniform(core))
                    self.assertGreater(total_variation_to_uniform(joint), 0)

    def test_independent_full_seven_vertex_order_oracle(self):
        m = 2
        core_rates = near_uniform_positive_rates(m, 3)
        extra = sum(core_rates, Fraction(0)) / (2**m+1)
        rates = core_rates + (extra,)
        adj = joined_to_singleton(m)
        self.assertEqual(law_by_recursion(adj, rates),
                         law_by_permutations(adj, rates))


if __name__ == "__main__":
    unittest.main()
