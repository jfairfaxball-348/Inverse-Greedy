"""S025 exact Fraction checks for genuine Exp survival-derived real bin cells.

At delta=-log(1-1/n) with n>=2 and positive integer rate r,
the *actual* exponential tail at k delta is q**k, q=((n-1)/n)**r.
These are exact arithmetic consistency/regression checks, not
proofs of the Mathlib measure-theory lemma or bin-map measurability.
"""
from fractions import Fraction
from itertools import product
import unittest


def survivor(rate: int, n: int, k: int) -> Fraction:
    if not (isinstance(rate, int) and rate > 0 and
            isinstance(n, int) and n >= 2 and
            isinstance(k, int) and k >= 0):
        raise ValueError("integer rate>0, n>=2, k>=0 required")
    return Fraction(n - 1, n) ** (rate * k)


def cell(rate: int, n: int, k: int) -> Fraction:
    return survivor(rate, n, k) - survivor(rate, n, k + 1)


class S025RealClockCells(unittest.TestCase):
    def test_actual_tail_difference_equals_geometric_atom(self):
        for r, n, k in product(range(1, 11), (2, 3, 7, 101), range(16)):
            q = Fraction(n - 1, n) ** r
            self.assertEqual(cell(r, n, k), (1 - q) * q ** k)
            self.assertGreater(cell(r, n, k), 0)
            if k == 0:
                self.assertEqual(cell(r, n, 0), 1 - q)

    def test_partition_by_half_open_cells_with_exact_remainder(self):
        for r, n, K in product((1, 2, 5, 11), (2, 3, 5, 97), range(1, 18)):
            total = sum((cell(r, n, k) for k in range(K)), Fraction())
            self.assertEqual(total + survivor(r, n, K), 1)
            self.assertLess(total, 1)

    def test_finite_coordinate_box_products(self):
        # Formula is a product of *survival-difference* masses, not
        # an implementation of the weighted-priority law.
        for rates in ((), (1,), (1, 7), (3, 1, 4), (2, 5, 1, 3)):
            for n in (2, 7, 101):
                for k in range(5):
                    joint_from_tails = Fraction(1)
                    joint_from_atoms = Fraction(1)
                    for rate in rates:
                        q = Fraction(n - 1, n) ** rate
                        joint_from_tails *= survivor(rate, n, k) - survivor(rate, n, k + 1)
                        joint_from_atoms *= (1 - q) * q ** k
                    self.assertEqual(joint_from_tails, joint_from_atoms)
                    if not rates:
                        self.assertEqual(joint_from_tails, 1)

    def test_two_clock_strict_bin_winner_finite_sum(self):
        from test_s022 import binned_race
        for r, s in ((1, 1), (1, 7), (7, 1), (3, 5), (11, 2)):
            for n in (2, 3, 9, 31):
                qr, qs = Fraction(n - 1, n) ** r, Fraction(n - 1, n) ** s
                for K in (1, 2, 5, 12):
                    # One clock in cell k, the other strictly in later bins.
                    partial = sum((cell(r, n, k) * survivor(s, n, k+1)
                                   for k in range(K)), Fraction())
                    remainder = (1 - qr) * qs * (qr * qs)**K / (1 - qr * qs)
                    exact_first = binned_race(r, s, n)[0]
                    self.assertEqual(partial + remainder, exact_first)
                    self.assertGreaterEqual(remainder, 0)

    def test_invalid_parameters_rejected(self):
        for args in ((0, 2, 0), (2, 1, 0), (1, 2, -1), (-3, 5, 0)):
            with self.assertRaises(ValueError):
                cell(*args)


if __name__ == "__main__":
    unittest.main()
