"""S024: exact rational CDF/tail/bin regression at exponential bin boundaries.

For integer rate r>0 and delta=-log(1-1/n), genuine Exp survival at
k*delta is q**k, where q=((n-1)/n)**r. These Fraction tests check
algebraic consistency, NOT Lean or the probabilistic measure derivation.
"""
from fractions import Fraction
from itertools import product
import unittest


def q_value(rate: int, n: int) -> Fraction:
    assert rate > 0 and n >= 2
    return Fraction(n - 1, n) ** rate


def survival_bin_boundary(rate: int, n: int, k: int) -> Fraction:
    assert k >= 0
    return q_value(rate, n) ** k


def cdf_bin_boundary(rate: int, n: int, k: int) -> Fraction:
    return 1 - survival_bin_boundary(rate, n, k)


def bin_mass_from_tails(rate: int, n: int, k: int) -> Fraction:
    return survival_bin_boundary(rate, n, k) - survival_bin_boundary(rate, n, k + 1)


def geometric_mass(rate: int, n: int, k: int) -> Fraction:
    q = q_value(rate, n)
    return (1 - q) * q ** k


class TestS024ExpSurvivalExact(unittest.TestCase):
    def test_cdf_survival_complements_and_zero_boundary(self):
        for r, n, k in product(range(1, 10), [2, 3, 5, 11, 101], range(8)):
            cdf, tail = cdf_bin_boundary(r, n, k), survival_bin_boundary(r, n, k)
            self.assertEqual(cdf + tail, 1)
            self.assertLessEqual(0, cdf)
            self.assertLessEqual(0, tail)
            self.assertLessEqual(tail, 1)
            if k == 0:
                self.assertEqual(cdf, 0)
                self.assertEqual(tail, 1)

    def test_bin_pmf_as_difference_of_actual_survival_formula(self):
        for r, n, k in product(range(1, 9), [2, 3, 4, 9, 97], range(12)):
            self.assertEqual(bin_mass_from_tails(r, n, k), geometric_mass(r, n, k))
            self.assertGreater(bin_mass_from_tails(r, n, k), 0)

    def test_finite_partition_and_exact_tail(self):
        for r, n, kmax in product(range(1, 8), [2, 3, 7, 37], range(10)):
            mass = sum((bin_mass_from_tails(r, n, k) for k in range(kmax)), Fraction())
            self.assertEqual(mass + survival_bin_boundary(r, n, kmax), 1)
            self.assertEqual(mass, cdf_bin_boundary(r, n, kmax))

    def test_independent_finite_clock_cylinders(self):
        # Tests the product/survival parameter algebra, not independence itself.
        for rates in [(), (1,), (1, 3), (2, 5, 1), (1, 2, 3, 4)]:
            for n in [2, 3, 11]:
                for k in range(4):
                    joint_tail = Fraction(1)
                    joint_zero_support = Fraction(1)
                    for rate in rates:
                        joint_tail *= survival_bin_boundary(rate, n, k)
                        joint_zero_support *= 1 - cdf_bin_boundary(rate, n, 0)
                    self.assertEqual(joint_tail, Fraction(n - 1, n) ** (k * sum(rates)))
                    self.assertEqual(joint_zero_support, 1)
                    if not rates:
                        self.assertEqual(joint_tail, 1)


if __name__ == "__main__":
    unittest.main()
