"""S012: exact P5 unattained approximate uniformity at positive rates.

All probabilities use Fraction; independent full 5! weighted-order
oracle validates the rational first-choice recurrence and closed form.
"""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import path, law_by_recursion, law_by_permutations

P5 = path(5)
P024, P03, P13, P14 = 21, 9, 10, 18


def p5_closed_form(t):
    t = Fraction(t)
    if t <= 0:
        raise ValueError("only strictly positive rates are admissible")
    p03 = Fraction(1, 2) / (t + 2)
    p13 = 1 / (t + 4)
    p14 = p03
    p024 = 1 - p03 - p13 - p14
    return {P024: p024, P03: p03, P13: p13, P14: p14}


def p5_total_variation(t):
    t = Fraction(t)
    if t <= 0:
        raise ValueError("strict positivity required")
    return t * (3*t + 10) / (4 * (t + 2) * (t + 4))


class P5ApproximateUniformityTests(unittest.TestCase):
    def test_closed_form_both_independent_oracles(self):
        for t in (Fraction(1, 100), Fraction(1, 20),
                  Fraction(1, 2), 1, 2, 10, 100):
            rates = (1, 1, t, 1, 1)
            with self.subTest(t=t):
                expected = p5_closed_form(t)
                self.assertEqual(law_by_recursion(P5, rates), expected)
                self.assertEqual(law_by_permutations(P5, rates), expected)
                self.assertEqual(sum(expected.values()), 1)
                self.assertTrue(all(p > 0 for p in expected.values()))
                self.assertEqual(set(expected), {P024, P03, P13, P14})

    def test_exact_tv_and_explicit_positive_bound(self):
        for t in (Fraction(1, 1000), Fraction(1, 100),
                  Fraction(1, 10), 1, 7, 100):
            with self.subTest(t=t):
                law = p5_closed_form(t)
                tv = sum((abs(p - Fraction(1, 4)) for p in law.values()),
                         Fraction(0)) / 2
                self.assertEqual(tv, p5_total_variation(t))
                self.assertGreater(tv, 0)
                self.assertLess(tv, Fraction(5, 16)*t)
                self.assertGreater(law[P024], Fraction(1, 4))
                for mask in (P03, P13, P14):
                    self.assertLess(law[mask], Fraction(1, 4))

    def test_limit_has_four_uniform_masses_but_zero_rate_is_forbidden(self):
        self.assertEqual(p5_total_variation(Fraction(1, 10000)) <
                         Fraction(1, 30000), True)
        for mask in (P024, P03, P13, P14):
            self.assertEqual(
                p5_closed_form(Fraction(1, 1000000))[mask] -
                Fraction(1, 4) < Fraction(1, 1000000), True)
        with self.assertRaises(ValueError):
            law_by_recursion(P5, (1, 1, 0, 1, 1))
        with self.assertRaises(ValueError):
            p5_closed_form(0)


if __name__ == "__main__":
    unittest.main()
