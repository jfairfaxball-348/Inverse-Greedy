"""S026 independent exact checks for one-based ceiling bins (no float arithmetic)."""
from fractions import Fraction
from math import ceil
import unittest


def one_based_ceil_bin(t: Fraction, width: Fraction) -> int:
    assert width > 0
    # Nat.ceil on a real number is truncated at zero.
    return max(0, ceil(t / width))


def pair_bin_outcomes(qr: Fraction, qs: Fraction):
    assert 0 < qr < 1 and 0 < qs < 1
    denominator = 1 - qr * qs
    return ((1 - qr) * qs / denominator,
            (1 - qs) * qr / denominator,
            (1 - qr) * (1 - qs) / denominator)


class TestS026(unittest.TestCase):
    def test_one_based_cells_all_endpoints(self):
        for width in [Fraction(1, 7), Fraction(2, 3), Fraction(3, 2)]:
            for n in range(-15, 31):
                for sub in [Fraction(0), Fraction(1, 3), Fraction(1, 2),
                            Fraction(2, 3)]:
                    t = (n + sub) * width
                    b = one_based_ceil_bin(t, width)
                    self.assertEqual(b == 0, t <= 0)
                    for k in range(16):
                        self.assertEqual(b == k + 1,
                                         k * width < t <= (k + 1) * width)

    def test_geometric_box_identity(self):
        for qr, qs in [(Fraction(2, 3), Fraction(3, 5)),
                       (Fraction(7, 11), Fraction(1, 4)),
                       (Fraction(1, 99), Fraction(98, 99))]:
            for k in range(9):
                for j in range(9):
                    one = (1 - qr) * qr ** k
                    two = (1 - qs) * qs ** j
                    self.assertEqual(one * two,
                                     (1 - qr) * (1 - qs) * qr ** k * qs ** j)

    def test_pair_winner_collision_partition(self):
        for qr, qs in [(Fraction(1, 2), Fraction(3, 4)),
                       (Fraction(9, 10), Fraction(13, 17)),
                       (Fraction(1, 100), Fraction(99, 100))]:
            left, right, tied = pair_bin_outcomes(qr, qs)
            self.assertEqual(left + right + tied, 1)
            self.assertTrue(0 < tied <= min(1 - qr, 1 - qs))
            self.assertEqual(left - right,
                             (qs - qr) / (1 - qr * qs))

    def test_geometric_truncation_exact(self):
        for q in [Fraction(1, 2), Fraction(2, 3), Fraction(19, 20)]:
            for cutoff in [0, 1, 5, 20, 100]:
                part = sum(((1 - q) * q ** k for k in range(cutoff)),
                           Fraction())
                self.assertEqual(part + q ** cutoff, 1)


if __name__ == "__main__":
    unittest.main()
