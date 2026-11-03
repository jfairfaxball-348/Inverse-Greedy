"""S033 exact/deterministic tests of genuine clock-bin chamber sandwich.

These tests audit algebra and pointwise event implications. They are NOT
a formal proof of the continuous exponential law or the full n>=3
sorting-chamber distribution.
"""
import itertools
import math
import unittest
from fractions import Fraction


def nat_ceil(q):
    return max(0, math.ceil(q))


def chamber(times):
    return all(times[i] < times[j]
               for i in range(len(times)) for j in range(i + 1, len(times)))


def bin_chamber(times, delta):
    bins = tuple(nat_ceil(t / delta) for t in times)
    return chamber(bins)


def collision(times, delta):
    bins = tuple(nat_ceil(t / delta) for t in times)
    return len(bins) != len(set(bins))


def bin_mass(q, bins):
    return math.prod((1 - qi) * qi ** bi for qi, bi in zip(q, bins))


class TestS033BinChamberSandwich(unittest.TestCase):
    def test_deterministic_inclusions_across_boundaries_and_zero(self):
        values = tuple(map(Fraction, (-2, -1, 0, 1, 2, 3, 4)))
        for n in range(5):
            for times in itertools.product(values, repeat=n):
                for delta in (Fraction(1, 2), Fraction(2, 3), Fraction(1)):
                    self.assertFalse(bin_chamber(times, delta) and not chamber(times))
                    self.assertFalse(chamber(times) and
                                     not bin_chamber(times, delta) and
                                     not collision(times, delta))

    def test_exact_pair_collision_geometric_formula(self):
        qs = (Fraction(1, 2), Fraction(2, 3), Fraction(3, 5))
        for q, t in itertools.combinations(qs, 2):
            closed = (1 - q) * (1 - t) / (1 - q * t)
            for width in (1, 2, 3, 6, 9):
                partial = sum(((1 - q) * q ** k * (1 - t) * t ** k
                               for k in range(width)), Fraction(0))
                self.assertEqual(partial, closed * (1 - (q * t) ** width))
                self.assertLess(partial, closed)

    def test_exact_finite_union_collision_bound(self):
        qs = (Fraction(1, 2), Fraction(2, 3), Fraction(3, 4),
              Fraction(4, 5))
        for n in range(5):
            q = qs[:n]
            for width in (2, 3, 4):
                joint_collision = sum(
                    (bin_mass(q, bins)
                     for bins in itertools.product(range(width), repeat=n)
                     if len(set(bins)) != n), Fraction(0))
                pair_sum = sum(
                    ((1 - q[i]) * (1 - q[j]) / (1 - q[i] * q[j])
                     for i in range(n) for j in range(i + 1, n)),
                    Fraction(0))
                self.assertLessEqual(joint_collision, pair_sum)


if __name__ == "__main__":
    unittest.main()
