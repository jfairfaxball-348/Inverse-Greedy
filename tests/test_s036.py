"""S036: independent exact regression for the strict-bin gap coordinates.

Python checks the full two-sided bijection and monomial factorisation.
The imported S036 Lean theorem currently proves only the forward
strict-monotonicity/injectivity-in-position portion. These tests are not
a substitute for a formal inverse or the actual stochastic limit.
"""
import itertools
import unittest
from fractions import Fraction
from math import prod


def gaps_to_bins(gaps):
    total = 0
    result = []
    for position, gap in enumerate(gaps):
        if gap < 0:
            raise ValueError("gaps must be nonnegative")
        total += gap
        result.append(position + total)
    return tuple(result)


def bins_to_gaps(bins):
    if any(k < 0 for k in bins) or any(
        a >= b for a, b in zip(bins, bins[1:])
    ):
        raise ValueError("bins must be nonnegative and strictly increasing")
    return tuple([bins[0]] + [
        right - left - 1 for left, right in zip(bins, bins[1:])
    ]) if bins else ()


def mass(q, bins):
    return prod((1 - x) * x ** k for x, k in zip(q, bins))


def gap_monomial(q, gaps):
    base = prod((1 - x) * x ** j for j, x in enumerate(q))
    tails = [prod(q[j:]) for j in range(len(q))]
    return base * prod(t ** g for t, g in zip(tails, gaps))


class S036GapCoordinates(unittest.TestCase):
    def test_forward_and_reverse_exhaustively(self):
        for n in range(6):
            for gaps in itertools.product(range(4), repeat=n):
                bins = gaps_to_bins(gaps)
                self.assertEqual(len(bins), n)
                self.assertTrue(all(a < b for a, b in zip(bins, bins[1:])))
                self.assertTrue(all(j <= k for j, k in enumerate(bins)))
                self.assertEqual(bins_to_gaps(bins), gaps)
            for bins in itertools.combinations(range(11), n):
                self.assertEqual(gaps_to_bins(bins_to_gaps(bins)), bins)

    def test_exact_geometric_monomial_reindexing(self):
        qs = tuple(map(Fraction, ("1/2", "2/3", "3/7", "4/5", "5/11")))
        for n in range(6):
            for gaps in itertools.product(range(4), repeat=n):
                self.assertEqual(
                    mass(qs[:n], gaps_to_bins(gaps)),
                    gap_monomial(qs[:n], gaps),
                )

    def test_bad_strict_sequences_rejected(self):
        for bins in ((0, 0), (2, 1), (1, 3, 3), (-1,), (3, 7, 5)):
            with self.assertRaises(ValueError):
                bins_to_gaps(bins)

    def test_empty_and_boundary_gaps(self):
        self.assertEqual(gaps_to_bins(()), ())
        self.assertEqual(bins_to_gaps(()), ())
        self.assertEqual(gaps_to_bins((0, 0, 0, 0)), (0, 1, 2, 3))
        self.assertEqual(bins_to_gaps((0, 1, 2, 3)), (0, 0, 0, 0))
        self.assertEqual(gaps_to_bins((2, 0, 3)), (2, 3, 7))


if __name__ == "__main__":
    unittest.main()
