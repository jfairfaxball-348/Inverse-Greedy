"""S029 exact bin-order and collision algebra regression.

These are independent Fraction tests of deterministic ceiling-bin geometry
and rational geometric identities. They are not a Lean or measured-clock
proof of the continuous exponential winner rate ratio.
"""
from fractions import Fraction
from itertools import product
import unittest


def ceil_bin(x: Fraction, width: Fraction) -> int:
    assert width > 0
    y = x / width
    return max(0, -((-y.numerator) // y.denominator))


class TestS029(unittest.TestCase):
    def test_exact_bin_monotonicity_and_event_sandwich_at_boundaries(self):
        points = sorted({
            Fraction(n, d)
            for d in (1, 2, 3, 4, 5)
            for n in range(-12, 13)
        })
        for width in (Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(3, 2)):
            for a, b in product(points, repeat=2):
                ka, kb = ceil_bin(a, width), ceil_bin(b, width)
                if a <= b:
                    self.assertLessEqual(ka, kb)
                if ka < kb:
                    self.assertLess(a, b)
                if a < b:
                    self.assertTrue(ka < kb or ka == kb)

    def test_exact_collision_fraction_upper_bound(self):
        fractions = (
            Fraction(1, 20), Fraction(1, 7), Fraction(1, 2),
            Fraction(2, 3), Fraction(9, 10), Fraction(99, 100),
        )
        for q, t in product(fractions, repeat=2):
            c = (1-q)*(1-t)/(1-q*t)
            self.assertGreaterEqual(c, 0)
            self.assertLessEqual(c, 1-q)
            self.assertLessEqual(c, 1-t)
            w = (1-q)*t/(1-q*t)
            rev = (1-t)*q/(1-q*t)
            self.assertEqual(w+rev+c, 1)


if __name__ == "__main__":
    unittest.main()
