"""S040 independent exact finite-monomial regression.

Checks the triangular product identity used by the new Lean theorem.
This is not a verification of ENNReal infinity behaviour, of S038's
measured coordinate transport, or of any countable series.
"""
from fractions import Fraction
from itertools import permutations, product
from math import prod
import unittest


def direct_monomial(c, q, gaps):
    acc = 0
    factors = []
    for j, d in enumerate(gaps):
        acc += d
        factors.append(c[j] * q[j] ** (j + acc))
    return prod(factors, start=Fraction(1))


def factored_monomial(c, q, gaps):
    base = prod(
        (c[j] * q[j] ** j for j in range(len(q))),
        start=Fraction(1),
    )
    suffix = prod(
        (prod(q[a:], start=Fraction(1)) ** gaps[a]
         for a in range(len(q))),
        start=Fraction(1),
    )
    return base * suffix


class S040MonomialTests(unittest.TestCase):
    def test_arbitrary_factors_and_permutations(self):
        seed_q = (Fraction(1, 2), Fraction(2, 3),
                  Fraction(3, 5), Fraction(4, 7))
        seed_c = (Fraction(3, 4), Fraction(5, 6),
                  Fraction(2, 7), Fraction(7, 8))
        for n in range(5):
            for q in permutations(seed_q[:n]):
                for gaps in product(range(3), repeat=n):
                    self.assertEqual(
                        direct_monomial(seed_c[:n], q, gaps),
                        factored_monomial(seed_c[:n], q, gaps),
                    )

    def test_zero_and_unit_factors(self):
        # The identity is algebraic: it needs no positivity or q<1.
        for n in range(4):
            for q in product((Fraction(0), Fraction(1),
                              Fraction(2)), repeat=n):
                c = tuple(Fraction(0) if i % 2 else Fraction(3, 2)
                          for i in range(n))
                for gaps in product(range(3), repeat=n):
                    self.assertEqual(
                        direct_monomial(c, q, gaps),
                        factored_monomial(c, q, gaps),
                    )

    def test_empty_and_singleton(self):
        self.assertEqual(direct_monomial((), (), ()), Fraction(1))
        for c in (Fraction(0), Fraction(1, 3), Fraction(2)):
            for q in (Fraction(0), Fraction(2, 7), Fraction(1)):
                for gap in range(6):
                    self.assertEqual(
                        direct_monomial((c,), (q,), (gap,)),
                        factored_monomial((c,), (q,), (gap,)),
                    )


if __name__ == "__main__":
    unittest.main()
