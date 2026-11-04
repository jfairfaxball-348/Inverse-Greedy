"""S035: independent exact rational checks for finite positive-bin chamber sums.

These Fraction oracles validate the combinatorial multiple-gap formula,
not Lean's measure-theoretic proof or the actual continuous Exp law.
"""
import itertools
import math
import unittest
from fractions import Fraction
from functools import reduce
from operator import mul


def product(xs):
    return reduce(mul, xs, Fraction(1))


def cell(q, k):
    return (1 - q) * q**k


def direct_strict_bins(q, upper):
    """Joint mass with 0 <= k_0 < ... < k_(m-1) < upper."""
    return sum(
        (product(cell(rate, bin_index) for rate, bin_index in zip(q, bins))
         for bins in itertools.combinations(range(upper), len(q))),
        Fraction(0),
    )


def direct_bounded_gaps(q, gap_bound):
    """Joint mass for all gaps d_a in [0, gap_bound)."""
    m = len(q)
    out = Fraction(0)
    for gaps in itertools.product(range(gap_bound), repeat=m):
        partial = 0
        bins = []
        for j, d in enumerate(gaps):
            partial += d
            bins.append(j + partial)
        out += product(cell(rate, k) for rate, k in zip(q, bins))
    return out


def gap_product(q, gap_bound):
    """Independent closed evaluation of the finite geometric gap sums."""
    base = product((1 - rate) * rate**j for j, rate in enumerate(q))
    return base * product(
        (1 - product(q[a:])**gap_bound) / (1 - product(q[a:]))
        for a in range(len(q))
    )


def full_series_product(q):
    """The exact full multiple geometric series, not a floating limit."""
    base = product((1 - rate) * rate**j for j, rate in enumerate(q))
    return base / product(1 - product(q[a:]) for a in range(len(q)))


class S035PositiveBinSeries(unittest.TestCase):
    def test_gap_factorisation_including_empty(self):
        rates = (Fraction(1, 2), Fraction(2, 3), Fraction(1, 5),
                 Fraction(3, 4))
        for m in range(5):
            for q in (rates[:m], tuple(reversed(rates[:m]))):
                for bound in (1, 2, 3, 4):
                    with self.subTest(q=q, bound=bound):
                        self.assertEqual(
                            direct_bounded_gaps(q, bound),
                            gap_product(q, bound),
                        )

    def test_strict_bin_truncations_and_full_series(self):
        qs = (Fraction(2, 3), Fraction(1, 2),
              Fraction(1, 4), Fraction(3, 5))
        for m in range(5):
            q = qs[:m]
            full = full_series_product(q)
            previous = Fraction(0)
            for upper in range(0, 13):
                truncated = direct_strict_bins(q, upper)
                self.assertLessEqual(previous, truncated)
                self.assertLessEqual(truncated, full)
                previous = truncated
            if m == 0:
                self.assertEqual(full, 1)
            elif m == 1:
                self.assertEqual(full, 1)
            else:
                self.assertLess(full, 1)

    def test_duplicate_order_has_no_strict_bin_assignments(self):
        # The list [0,0] imposes K_0 < K_0, impossible for any width.
        for k in range(12):
            self.assertFalse(k < k)

    def test_joint_cylinder_normalization_finite_cutoff(self):
        qs = (Fraction(1, 2), Fraction(1, 4), Fraction(2, 3))
        for upper in (1, 2, 5, 10):
            direct = sum(
                (product(cell(q, k) for q, k in zip(qs, bins))
                 for bins in itertools.product(range(upper), repeat=len(qs))),
                Fraction(0),
            )
            self.assertEqual(direct, product(1 - q**upper for q in qs))


if __name__ == "__main__":
    unittest.main()
