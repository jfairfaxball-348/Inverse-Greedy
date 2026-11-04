"""S037: exact tests for complete-order bin/gap reindexing.

This is finite rational arithmetic, not a Lean verification of the
measured geometric series or of the continuous-clock zero-width limit.
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import prod
import unittest

from test_s036 import gaps_to_bins, bins_to_gaps


def demand_complete_order(order, count):
    if len(order) != count or set(order) != set(range(count)):
        raise ValueError("The order must enumerate every coordinate exactly once.")


def strict_bin_sum(q, order, cutoff):
    demand_complete_order(order, len(q))
    total = Fraction(0)
    for bins in combinations(range(cutoff), len(q)):
        assignment = dict(zip(order, bins))
        total += prod((1 - x) * x ** assignment[i] for i, x in enumerate(q))
    return total


def gap_reindexed_sum(q, order, cutoff):
    demand_complete_order(order, len(q))
    total = Fraction(0)
    for gaps in product(range(cutoff), repeat=len(q)):
        bins = gaps_to_bins(gaps)
        if bins and bins[-1] >= cutoff:
            continue
        assignment = dict(zip(order, bins))
        total += prod((1 - x) * x ** assignment[i] for i, x in enumerate(q))
    return total


def finite_width_closed_product(q, order):
    demand_complete_order(order, len(q))
    ordered_q = [q[i] for i in order]
    numerator = prod((1 - x) * x ** i for i, x in enumerate(ordered_q))
    denominator = prod(1 - prod(ordered_q[i:]) for i in range(len(q)))
    return numerator / denominator


class S037CompleteReindex(unittest.TestCase):
    def test_all_permutations_have_identical_finite_truncations(self):
        q_all = tuple(map(Fraction, ("1/2", "2/3", "3/5", "4/7")))
        for n in range(5):
            for order in permutations(range(n)):
                q = q_all[:n]
                for cutoff in (n + 1, n + 3):
                    self.assertEqual(
                        strict_bin_sum(q, order, cutoff),
                        gap_reindexed_sum(q, order, cutoff),
                    )

    def test_closed_product_bounds_and_increasing_truncations(self):
        q_all = tuple(map(Fraction, ("1/3", "2/5", "3/7", "4/9")))
        for n in range(5):
            for order in permutations(range(n)):
                q = q_all[:n]
                a = strict_bin_sum(q, order, n + 2)
                b = strict_bin_sum(q, order, n + 4)
                full = finite_width_closed_product(q, order)
                self.assertLessEqual(a, b)
                self.assertLessEqual(b, full)
                self.assertGreater(full, 0)

    def test_incomplete_or_repeated_order_rejected(self):
        q = (Fraction(1, 2), Fraction(2, 3), Fraction(3, 5))
        for bad in ((0, 1), (0, 0, 2), (0, 1, 3), (2, 2, 1), ()):
            with self.assertRaises(ValueError):
                strict_bin_sum(q, bad, 5)
            with self.assertRaises(ValueError):
                gap_reindexed_sum(q, bad, 5)

    def test_empty_and_singleton_boundaries(self):
        self.assertEqual(strict_bin_sum((), (), 0), 1)
        self.assertEqual(gap_reindexed_sum((), (), 0), 1)
        self.assertEqual(finite_width_closed_product((), ()), 1)
        q = (Fraction(2, 3),)
        self.assertEqual(strict_bin_sum(q, (0,), 1), Fraction(1, 3))
        self.assertEqual(gap_reindexed_sum(q, (0,), 1), Fraction(1, 3))
        self.assertEqual(finite_width_closed_product(q, (0,)), 1)
        for bins in [(), (0,), (2, 4, 7)]:
            self.assertEqual(gaps_to_bins(bins_to_gaps(bins)), bins)


if __name__ == "__main__":
    unittest.main()
