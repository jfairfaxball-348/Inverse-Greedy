"""S021: independent exact continuous-clock law oracle via unit-rate replicas.

For each positive integer rate a, the minimum of a independent Exp(1)
clocks is exactly Exp(a). All labelled unit-clock arrival permutations
have equal chance, so grouped-order counting provides an independent
oracle without importing the project's weighted-priority implementation.
"""
import itertools
import math
import unittest
from collections import Counter
from fractions import Fraction


def grouped_clock_chambers(rate_counts):
    if any(not isinstance(a, int) or a <= 0 for a in rate_counts):
        raise ValueError("replicated exponential rates must be positive integers")
    labels = tuple(i for i, n in enumerate(rate_counts) for _ in range(n))
    n = len(labels)
    if n > 8:
        raise ValueError("exact oracle intentionally bounded to eight replicas")
    counts = Counter()
    for perm in itertools.permutations(range(n)):
        seen = set()
        output = []
        for k in perm:
            label = labels[k]
            if label not in seen:
                seen.add(label)
                output.append(label)
        counts[tuple(output)] += 1
    return {key: Fraction(count, math.factorial(n)) for key, count in counts.items()}


def direct_density_chamber_formula(counts, order):
    """The continuous exponential-spacings integral, evaluated over Q."""
    remaining = sum(counts)
    probability = Fraction(1)
    for i in order:
        probability *= Fraction(counts[i], remaining)
        remaining -= counts[i]
    return probability


class S021ContinuousRaceOracle(unittest.TestCase):
    def test_two_clocks_rates_unequal(self):
        for a, b in [(1, 1), (1, 7), (7, 1), (2, 5), (5, 2), (3, 3)]:
            with self.subTest(a=a, b=b):
                law = grouped_clock_chambers((a, b))
                self.assertEqual(law[(0, 1)], Fraction(a, a + b))
                self.assertEqual(law[(1, 0)], Fraction(b, a + b))
                self.assertEqual(sum(law.values()), 1)

    def test_multiple_clock_orders(self):
        cases = [(), (1,), (1, 1, 1), (1, 2, 4), (2, 1, 5),
                 (1, 3, 2), (2, 2, 2), (1, 1, 2, 3)]
        for counts in cases:
            with self.subTest(counts=counts):
                law = grouped_clock_chambers(counts)
                self.assertEqual(len(law), math.factorial(len(counts)))
                self.assertEqual(sum(law.values()), 1)
                for order in itertools.permutations(range(len(counts))):
                    self.assertEqual(law[order], direct_density_chamber_formula(counts, order))

    def test_label_permutation_invariance(self):
        for counts in [(1, 5), (1, 2, 3), (1, 1, 2, 3)]:
            original = grouped_clock_chambers(counts)
            reversed_law = grouped_clock_chambers(tuple(reversed(counts)))
            k = len(counts)
            for order, probability in original.items():
                self.assertEqual(probability,
                                 reversed_law[tuple(k - 1 - i for i in order)])

    def test_zero_is_not_an_admissible_rate(self):
        with self.assertRaises(ValueError):
            grouped_clock_chambers((0, 1))


if __name__ == "__main__":
    unittest.main()
