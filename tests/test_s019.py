"""S019: deterministic analytic checks for independent exponential clocks.

These quadrature checks are NOT measure-theoretic proofs. They check the
continuous density formula against independent exact Fraction order masses.
"""
from fractions import Fraction
from math import exp, isclose
import unittest


def simpson_first_arrival(a: Fraction, b: Fraction, steps: int = 4096) -> float:
    """Integrate f_A(t) P(B>t) from 0 to infinity, with bounded tail."""
    aa, bb = float(a), float(b)
    assert aa > 0 and bb > 0 and steps % 2 == 0
    total = aa + bb
    end = 48.0 / total
    h = end / steps

    def density(t: float) -> float:
        return (aa * exp(-aa * t)) * exp(-bb * t)

    acc = density(0.0) + density(end)
    for k in range(1, steps):
        acc += (4 if k % 2 else 2) * density(k * h)
    return acc * h / 3


def simpson_three_arrival(rates: tuple[Fraction, Fraction, Fraction]) -> float:
    """Integrate the first clock against the independent later-clock event.

    Given T1=t, independence gives probability T2<T3 with T2>t as
    (r2/(r2+r3))*exp(-(r2+r3)*t), obtained from continuous densities.
    """
    a, b, c = rates
    return float(b / (b + c)) * simpson_first_arrival(a, b + c)


class IndependentExponentialAnalyticChecks(unittest.TestCase):
    def test_two_clock_chambers_integrate_to_exact_ratio(self):
        for a, b in ((1, 1), (3, 5), (1, 17), (37, 2), (2, 73), (101, 103)):
            with self.subTest(rates=(a, b)):
                left = simpson_first_arrival(Fraction(a), Fraction(b))
                right = simpson_first_arrival(Fraction(b), Fraction(a))
                self.assertTrue(isclose(left, float(Fraction(a, a + b)), abs_tol=2e-9))
                self.assertTrue(isclose(left + right, 1.0, abs_tol=3e-9))

    def test_three_clock_chambers_integrate_to_exact_order_mass(self):
        from itertools import permutations
        rates = (Fraction(2), Fraction(7), Fraction(13))
        mass = Fraction(0)
        for order in permutations(rates):
            with self.subTest(order=order):
                expected = order[0] / sum(order) * order[1] / (order[1] + order[2])
                measured = simpson_three_arrival(order)
                self.assertTrue(isclose(measured, float(expected), abs_tol=3e-9))
                mass += expected
        self.assertEqual(mass, Fraction(1))


if __name__ == "__main__":
    unittest.main()
