"""S028: independent exact geometric mass and rate-limit regression.

These checks are finite rational identities or symbolic analytic checks.
They never substitute for the imported Lean proof of the *true* clock law.
"""
from fractions import Fraction
import unittest

import sympy as sp


def geometric_masses(a, b, n):
    assert a > 0 and b > 0 and n >= 2
    q = Fraction(n - 1, n)
    qr, qs = q ** a, q ** b
    denom = 1 - qr * qs
    return qr, qs, (
        (1 - qr) * qs / denom,
        (1 - qs) * qr / denom,
        (1 - qr) * (1 - qs) / denom,
    )


class TestS028(unittest.TestCase):
    def test_three_geometric_series_with_exact_tails(self):
        for a, b, n in [(1, 1, 2), (2, 9, 7), (7, 3, 19), (12, 5, 31)]:
            qr, qs, (winner, loser, tied) = geometric_masses(a, b, n)
            qproduct = qr * qs
            for length in (0, 1, 3, 7, 17):
                cells = (
                    lambda k: (1 - qr) * qr ** k * qs ** (k + 1),
                    lambda k: (1 - qs) * qs ** k * qr ** (k + 1),
                    lambda k: (1 - qr) * (1 - qs) * (qr * qs) ** k,
                )
                for cell, total in zip(cells, (winner, loser, tied)):
                    partial = sum((cell(k) for k in range(length)), Fraction())
                    self.assertEqual(partial + total * qproduct ** length, total)
            self.assertEqual(winner + loser + tied, 1)
            self.assertLessEqual(tied, min(1 - qr, 1 - qs))

    def test_true_rate_ratio_sandwich_and_explicit_collision_bound(self):
        for a in range(1, 9):
            for b in range(1, 9):
                for n in (2, 5, 11, 32, 128):
                    _, _, (w, _, tied) = geometric_masses(a, b, n)
                    rate_ratio = Fraction(a, a + b)
                    self.assertLessEqual(w, rate_ratio)
                    self.assertLessEqual(rate_ratio, w + tied)
                    self.assertLessEqual(tied, min(Fraction(a, n), Fraction(b, n)))

    def test_sharp_small_width_first_order_analytic_coefficients(self):
        rate_r, rate_s, delta = sp.symbols("rate_r rate_s delta", positive=True)
        qr = sp.exp(-rate_r * delta)
        qs = sp.exp(-rate_s * delta)
        winner = (1 - qr) * qs / (1 - qr * qs)
        collision = (1 - qr) * (1 - qs) / (1 - qr * qs)
        rate_ratio = rate_r / (rate_r + rate_s)
        # These one-sided symbolic limits are exact (not floating heuristics).
        winner_bias = sp.limit((rate_ratio - winner) / delta, delta, 0, dir="+")
        collision_rate = sp.limit(collision / delta, delta, 0, dir="+")
        self.assertEqual(
            sp.simplify(winner_bias - rate_r * rate_s / (2 * (rate_r + rate_s))), 0
        )
        self.assertEqual(
            sp.simplify(collision_rate - rate_r * rate_s / (rate_r + rate_s)), 0
        )


if __name__ == "__main__":
    unittest.main()
