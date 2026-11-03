"""S032 independent exact checks of finite geometric-bin cylinders and chambers.

These are rational-algebra and deterministic-event regressions, not a
substitute for the actual continuous Exp-clock Lean theorem.
"""
import itertools
import math
import unittest
from fractions import Fraction


def mass(q, bins):
    """One-based geometric ceiling bins, shifted to zero-based indices."""
    return math.prod((1 - q[i]) * q[i] ** k for i, k in enumerate(bins))


def chamber(order, clocks):
    return all(clocks[order[a]] < clocks[order[b]]
               for a in range(len(order)) for b in range(a + 1, len(order)))


class TestS032JointBinAndChamber(unittest.TestCase):
    def test_all_coordinate_geometric_rectangle(self):
        qs = tuple(map(Fraction, (1, 2, 3, 5)))
        qs = tuple(Fraction(v, v + 2) for v in qs)
        for n in range(5):
            q = qs[:n]
            width = 4
            probability = sum(
                (mass(q, bins)
                 for bins in itertools.product(range(width), repeat=n)),
                Fraction(0),
            )
            # Independently telescope each geometric survival tail.
            expected = math.prod(1 - t ** width for t in q)
            self.assertEqual(probability, expected)

    def test_empty_and_singleton_joint(self):
        self.assertEqual(mass((), ()), Fraction(1))
        for q in (Fraction(1, 2), Fraction(2, 9), Fraction(7, 8)):
            self.assertEqual(sum((mass((q,), (k,)) for k in range(12)),
                                 Fraction(0)), 1 - q ** 12)

    def test_pair_chamber_matches_strict_comparison(self):
        times = tuple(map(Fraction, (-2, 0, 1, 2, 5)))
        for x, y in itertools.product(times, repeat=2):
            clocks = (x, y)
            self.assertEqual(chamber((0, 1), clocks), x < y)
            self.assertEqual(chamber((1, 0), clocks), y < x)
            self.assertFalse(chamber((0, 1), clocks)
                             and chamber((1, 0), clocks))

    def test_repeated_entries_never_form_strict_chamber(self):
        for order in itertools.product(range(3), repeat=4):
            if len(set(order)) == len(order):
                continue
            for clocks in itertools.product((Fraction(0), Fraction(1),
                                             Fraction(2)), repeat=3):
                self.assertFalse(chamber(order, clocks))

    def test_strict_multi_bin_gap_series_finite_sections(self):
        """Check the exact gap-coordinate factorisation with Fraction."""
        qs = (Fraction(1, 2), Fraction(2, 3), Fraction(4, 5),
              Fraction(3, 7))
        width = 4
        for n in range(5):
            q = qs[:n]
            direct = Fraction(0)
            for gaps in itertools.product(range(width), repeat=n):
                ordered_bins = tuple(sum(gaps[:i + 1]) + i
                                     for i in range(n))
                direct += mass(q, ordered_bins)
            base = math.prod((1 - q[i]) * q[i] ** i for i in range(n))
            suffix_q = tuple(math.prod(q[i:]) for i in range(n))
            separated = base * math.prod(
                sum((Q ** d for d in range(width)), Fraction(0))
                for Q in suffix_q
            )
            closed_infinite = base * math.prod(
                Fraction(1) / (1 - Q) for Q in suffix_q
            )
            self.assertEqual(direct, separated)
            self.assertLessEqual(direct, closed_infinite)

    def test_strict_ceiling_bins_force_clock_order(self):
        times = tuple(Fraction(i, 6) for i in range(-2, 15))
        delta = Fraction(1, 3)
        for x, y in itertools.product(times, repeat=2):
            if math.ceil(x / delta) < math.ceil(y / delta):
                self.assertLess(x, y)


if __name__ == "__main__":
    unittest.main()
