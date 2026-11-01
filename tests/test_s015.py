"""S015: seven-vertex exact projection/support stress test.

Independent complete-order oracle compared with a directly accumulated
filter pushforward. These are exact Fraction checks, NOT an all-real
formal deletion-consistency theorem. The Lean support/singleton theorems
are compiled separately by the imported Lean CI job.
"""
import sys
import unittest
from fractions import Fraction
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from priority_deletion import complete_order_law


class S015ProjectionSupportTests(unittest.TestCase):
    def test_all_subsets_on_seven_unequal_rates(self):
        vertices = tuple(range(7))
        rates = tuple(Fraction(2 * v + 3, v + 4) for v in vertices)
        full_law = complete_order_law(rates, vertices)
        self.assertEqual(len(full_law), 5040)
        self.assertEqual(sum(full_law.values(), Fraction()), 1)

        for k in range(8):
            for retained in combinations(vertices, k):
                allowed = frozenset(retained)
                projected = {}
                for complete, mass in full_law.items():
                    target = tuple(v for v in complete if v in allowed)
                    projected[target] = projected.get(target, Fraction()) + mass

                with self.subTest(retained=retained):
                    expected = complete_order_law(rates, retained)
                    self.assertEqual(projected, expected)
                    self.assertEqual(sum(projected.values(), Fraction()), 1)
                    for target in projected:
                        self.assertEqual(set(target), allowed)
                        self.assertEqual(len(target), k)
                        self.assertEqual(len(target), len(set(target)))

                    if k == 1:
                        self.assertEqual(projected, {(retained[0],): Fraction(1)})
                    if k:
                        self.assertEqual(
                            projected.get(tuple(retained) + (retained[0],), 0),
                            Fraction(0),
                        )
                        self.assertEqual(projected.get(tuple(retained[:-1]), 0),
                                         Fraction(0))
                    else:
                        self.assertEqual(projected, {(): Fraction(1)})


if __name__ == "__main__":
    unittest.main()
