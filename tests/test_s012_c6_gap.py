"""S012: exact rational C6 uniformity separation by a positive TV gap."""
import sys
import unittest
from fractions import Fraction
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import cycle, c6_pair_probabilities, law_by_recursion, law_by_permutations


class C6TVGapTests(unittest.TestCase):
    def test_all_729_positive_rate_vectors(self):
        g = cycle(6)
        pair_masks = (9, 36, 18)  # opposite pairs (0,3), (2,5), (4,1)
        gap = Fraction(4, 45)
        for rates in product((1, 2, 4), repeat=6):
            with self.subTest(rates=rates):
                law = law_by_recursion(g, rates)
                self.assertEqual(len(law), 5)
                pair_probs = c6_pair_probabilities(rates)
                self.assertEqual(pair_probs, tuple(law[m] for m in pair_masks))
                self.assertLessEqual(
                    pair_probs[0] * pair_probs[1] * pair_probs[2],
                    Fraction(1, 729),
                )
                self.assertLessEqual(min(pair_probs), Fraction(1, 9))
                tv = sum((abs(p - Fraction(1, 5)) for p in law.values()),
                         Fraction(0)) / 2
                self.assertGreaterEqual(tv, gap)

    def test_independent_full_order_oracle(self):
        g = cycle(6)
        for rates in ((1, 1, 1, 1, 1, 1), (2, 3, 5, 7, 11, 13)):
            with self.subTest(rates=rates):
                self.assertEqual(law_by_permutations(g, rates),
                                 law_by_recursion(g, rates))

    def test_equal_rate_tv_value(self):
        law = law_by_recursion(cycle(6), (1,)*6)
        self.assertEqual(
            sum((abs(p - Fraction(1, 5)) for p in law.values()),
                Fraction(0)) / 2,
            Fraction(4, 15),
        )


if __name__ == "__main__":
    unittest.main()
