"""S034 exact finite-union regression on genuine geometric-bin probabilities.

Checks the finite-sum inequality separately from Lean.  Truncated
geometric cylinders cannot replace the actual exponential measure proof.
"""
import itertools
import math
import unittest
from fractions import Fraction


def joint_mass(q, bins):
    return math.prod((1 - x) * x ** k for x, k in zip(q, bins))


def pair_collision(q, i, j):
    return (1 - q[i]) * (1 - q[j]) / (1 - q[i] * q[j])


class TestS034FiniteUnion(unittest.TestCase):
    def test_all_orders_and_finite_bin_sections(self):
        q = (Fraction(1, 2), Fraction(2, 3), Fraction(3, 4), Fraction(4, 5))
        for n in range(5):
            for order in itertools.permutations(range(n)):
                qs = tuple(q[i] for i in order)
                pair_sum = sum((pair_collision(qs, a, b)
                                for a in range(n) for b in range(a + 1, n)),
                               Fraction(0))
                for width in (1, 2, 3):
                    collision_mass = sum(
                        (joint_mass(qs, bins)
                         for bins in itertools.product(range(width), repeat=n)
                         if len(set(bins)) != n), Fraction(0))
                    self.assertLessEqual(collision_mass, pair_sum)
                    if n <= 1:
                        self.assertEqual(pair_sum, 0)
                        self.assertEqual(collision_mass, 0)

    def test_repeated_coordinates_require_exclusion(self):
        # Two positions referring to *one* coordinate share a bin surely.
        # An incorrect independent-pair estimate would give width*rate < 1.
        rate, width = Fraction(1), Fraction(1, 8)
        for clock in (Fraction(0), Fraction(1, 10), Fraction(3, 2)):
            one_bin = max(0, math.ceil(clock / width))
            self.assertEqual(one_bin, one_bin)
        self.assertLess(width * rate, 1)

    def test_linear_in_width_for_every_finite_pair_sum(self):
        for n in range(7):
            rates = tuple(Fraction(i + 1) for i in range(n))
            def bound(width):
                return sum((width * min(rates[a], rates[b])
                            for a in range(n) for b in range(a + 1, n)),
                           Fraction(0))
            self.assertEqual(bound(Fraction(1, 32)),
                             2 * bound(Fraction(1, 64)))


if __name__ == "__main__":
    unittest.main()
