"""S039: exact rational preflight for full finite-gap product evaluation.

These independently check the algebraic candidate and finite truncations.
They do not prove the multivariate tsum in Lean or the continuous pushforward.
"""
from fractions import Fraction
from itertools import permutations, product
from math import prod
import unittest


def suffix_ratios(q):
    return tuple(prod(q[j:] or (Fraction(1),)) for j in range(len(q)))


def gap_bins(gaps):
    total = 0
    answer = []
    for j, d in enumerate(gaps):
        total += d
        answer.append(j + total)
    return tuple(answer)


def bin_monomial(q, gaps):
    k = gap_bins(gaps)
    return prod((1 - q[j]) * q[j] ** k[j] for j in range(len(q)))


def factored_monomial(q, gaps):
    numerator = prod((1 - x) * x ** j for j, x in enumerate(q))
    suffix = suffix_ratios(q)
    return numerator * prod(suffix[j] ** gaps[j] for j in range(len(q)))


def closed_product(q):
    numerator = prod((1 - x) * x ** j for j, x in enumerate(q))
    return numerator / prod(1 - x for x in suffix_ratios(q))


def truncated_product(q, max_gap):
    numerator = prod((1 - x) * x ** j for j, x in enumerate(q))
    return numerator * prod(
        (1 - x ** (max_gap + 1)) / (1 - x) for x in suffix_ratios(q)
    )


class S039GeometricTests(unittest.TestCase):
    def test_nonempty_suffix_strict_contraction(self):
        seed = (Fraction(1, 2), Fraction(2, 5),
                Fraction(3, 7), Fraction(4, 9))
        for n in range(5):
            for q in permutations(seed[:n]):
                for ratio in suffix_ratios(q):
                    self.assertGreater(ratio, 0)
                    self.assertLess(ratio, 1)
                if n == 0:
                    self.assertEqual(closed_product(q), 1)
                    self.assertEqual(truncated_product(q, 2), 1)

    def test_pointwise_gap_monomial_factorization(self):
        seed = (Fraction(1, 2), Fraction(2, 5),
                Fraction(3, 7), Fraction(4, 9))
        for n in range(5):
            for q in permutations(seed[:n]):
                for gaps in product(range(3), repeat=n):
                    self.assertEqual(
                        bin_monomial(q, gaps), factored_monomial(q, gaps)
                    )

    def test_exact_multivariate_geometric_truncations(self):
        seed = (Fraction(1, 2), Fraction(2, 5),
                Fraction(3, 7), Fraction(4, 9))
        for n in range(5):
            for q in permutations(seed[:n]):
                for max_gap in (0, 1, 2, 3):
                    direct = sum(
                        (bin_monomial(q, gaps)
                         for gaps in product(range(max_gap + 1), repeat=n)),
                        Fraction(0),
                    )
                    self.assertEqual(direct, truncated_product(q, max_gap))
                    self.assertLessEqual(direct, closed_product(q))
                    if n:
                        self.assertLess(direct, closed_product(q))
                    else:
                        self.assertEqual(direct, 1)


if __name__ == "__main__":
    unittest.main()
