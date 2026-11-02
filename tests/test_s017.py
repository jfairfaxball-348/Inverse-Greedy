"""S017: exact independent DP test of the full ordered projection law.

The oracle conditions on every first global vertex, including those
not retained, and builds the entire projected distribution. It does not
reuse the proposed retained Plackett–Luce formula as a recursion.
Tests are finite rational checks, not a substitute for the Lean proof.
"""
import math
import unittest
from fractions import Fraction
from functools import lru_cache
from itertools import combinations


def projected_distribution_dp(rates, active, retained):
    kept = frozenset(retained)

    @lru_cache(None)
    def rec(remaining):
        if not remaining:
            return {(): Fraction(1)}
        total = sum((rates[v] for v in remaining), Fraction())
        law = {}
        for v in remaining:
            branch_mass = rates[v] / total
            for suffix, mass in rec(remaining - {v}).items():
                order = (v,) + suffix if v in kept else suffix
                law[order] = law.get(order, Fraction()) + branch_mass * mass
        return law

    return rec(frozenset(active))


def intrinsic_order_mass(rates, order):
    remaining_mass = sum((rates[v] for v in order), Fraction())
    probability = Fraction(1)
    for v in order:
        probability *= rates[v] / remaining_mass
        remaining_mass -= rates[v]
    return probability


class FullOrderedProjectionTests(unittest.TestCase):
    def test_arbitrary_subsets_nine_unequal_positive_rates(self):
        active = tuple(range(9))
        rates = tuple(Fraction(2*v*v + 3*v + 11, (v + 3)*(v + 5))
                      for v in active)
        checked = 0
        for size in range(6):
            subsets = list(combinations(active, size))
            # Exhaust small supports, then sample a deterministic range of
            # placements as the order count grows factorially.
            if size >= 3:
                subsets = subsets[::max(1, len(subsets)//15)]
            for kept in subsets:
                law = projected_distribution_dp(rates, active, kept)
                with self.subTest(retained=kept):
                    self.assertEqual(sum(law.values(), Fraction()), 1)
                    self.assertEqual(len(law), math.factorial(size))
                    for order, mass in law.items():
                        self.assertEqual(set(order), set(kept))
                        self.assertEqual(mass,
                                         intrinsic_order_mass(rates, order))
                checked += 1
        self.assertGreaterEqual(checked, 90)

    def test_removed_first_vertex_independent_residual(self):
        active = tuple(range(8))
        rates = tuple(Fraction(3*v+5, v+11) for v in active)
        for first in active:
            remaining = tuple(v for v in active if v != first)
            for kept in [(0, 2, 5), (1, 3, 7), (2, 4, 6), ()]:
                retained = tuple(v for v in kept if v in remaining)
                law = projected_distribution_dp(rates, remaining, retained)
                for order, mass in law.items():
                    self.assertEqual(mass,
                                     intrinsic_order_mass(rates, order))


if __name__ == "__main__":
    unittest.main()
