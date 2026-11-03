"""S030: independent symbolic checks of continuous exponential-bin limits.

These regressions are *not* a stochastic or Lean proof; the actual
product-measure identity must be certified by ContinuousRaceLimit.lean.
"""
import unittest

import sympy as sp


class TestS030ContinuousRaceLimit(unittest.TestCase):
    def setUp(self):
        self.r, self.s, self.delta = sp.symbols(
            "r s delta", positive=True, real=True
        )
        r, s, d = self.r, self.s, self.delta
        self.winner = (
            (1 - sp.exp(-r * d)) * sp.exp(-s * d)
            / (1 - sp.exp(-(r + s) * d))
        )
        self.collision = (
            (1 - sp.exp(-r * d)) * (1 - sp.exp(-s * d))
            / (1 - sp.exp(-(r + s) * d))
        )

    def test_symbolic_positive_rate_ratio(self):
        self.assertEqual(
            sp.simplify(sp.limit(self.winner, self.delta, 0, dir="+")),
            self.r / (self.r + self.s),
        )

    def test_first_order_deviations(self):
        r, s, d = self.r, self.s, self.delta
        self.assertEqual(
            sp.simplify(sp.limit((self.winner - r / (r + s)) / d,
                                 d, 0, dir="+")),
            -r * s / (2 * (r + s)),
        )
        self.assertEqual(
            sp.simplify(sp.limit(self.collision / d, d, 0, dir="+")),
            r * s / (r + s),
        )

    def test_swapped_clock_partition(self):
        r, s, d = self.r, self.s, self.delta
        opposite = (
            (1 - sp.exp(-s * d)) * sp.exp(-r * d)
            / (1 - sp.exp(-(r + s) * d))
        )
        self.assertEqual(
            sp.simplify(self.winner + opposite + self.collision), 1
        )


if __name__ == "__main__":
    unittest.main()
