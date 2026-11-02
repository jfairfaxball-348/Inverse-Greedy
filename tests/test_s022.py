"""S022 exact rational independent oracle: binning two genuine Exp clocks.

For positive integer r,s and n>=2 set delta=-log(1-1/n).
Then q_r=exp(-r*delta)=(1-1/n)^r is rational. The probability
that floor(T_r/delta)<floor(T_s/delta), its reverse and a same-bin
collision can all be evaluated as exact rational geometric sums.
"""
import unittest
from fractions import Fraction


def binned_race(r, s, n):
    if any(type(x) is not int for x in (r, s, n)) or min(r, s) <= 0 or n < 2:
        raise ValueError("positive integer rates and n >= 2 required")
    base = Fraction(n - 1, n)
    qr, qs = base**r, base**s
    den = 1 - qr * qs
    return ((1 - qr) * qs / den,
            (1 - qs) * qr / den,
            (1 - qr) * (1 - qs) / den)


class S022BinnedRealClockOracle(unittest.TestCase):
    def test_partition_symmetry(self):
        for r, s in ((1, 1), (1, 7), (7, 1), (2, 5), (3, 4), (8, 9)):
            for n in (2, 3, 4, 8, 16, 64):
                with self.subTest(r=r, s=s, n=n):
                    a, b, t = binned_race(r, s, n)
                    self.assertEqual(a + b + t, 1)
                    self.assertTrue(0 < a < 1 and 0 < b < 1 and 0 < t < 1)
                    self.assertEqual(binned_race(s, r, n), (b, a, t))

    def test_same_bin_collision_rational_bound(self):
        for r, s in ((1, 1), (1, 7), (7, 1), (2, 5), (8, 9)):
            previous = None
            for n in (2, 3, 4, 8, 16, 32, 64, 128, 256, 512):
                t = binned_race(r, s, n)[2]
                self.assertLessEqual(t, Fraction(min(r, s), n))
                if previous is not None:
                    self.assertLess(t, previous)
                previous = t

    def test_winner_ratio_convergence_regression(self):
        # The universal limit is proved on paper, not by finite tests.
        for r, s in ((1, 1), (1, 7), (7, 1), (2, 5), (8, 9)):
            errors = [abs(binned_race(r, s, n)[0] - Fraction(r, r + s))
                      for n in (16, 64, 256, 1024)]
            self.assertTrue(all(a > b for a, b in zip(errors, errors[1:])))
            self.assertLess(errors[-1], Fraction(2 * max(r, s), 1024))

    def test_zero_rates_and_invalid_grid_rejected(self):
        for args in ((0, 1, 2), (1, 0, 2), (1, 1, 1), (1, 1, 0)):
            with self.assertRaises(ValueError):
                binned_race(*args)


if __name__ == "__main__":
    unittest.main()
