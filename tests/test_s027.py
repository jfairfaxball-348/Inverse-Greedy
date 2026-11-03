"""S027 exact, independent Fraction oracle for genuine first-bin race cylinders.

For integer rates a,b and rational q=(n-1)/n, the analytic substitution
delta=-log(q) makes individual exponential bin survival factors rational:
q_r=q**a, q_s=q**b. This tests identities and rigorous inequalities;
it is NOT a continuous measure-theory proof or Lean certification.
"""
from fractions import Fraction
import unittest


def bin_parameters(a: int, b: int, n: int):
    assert a > 0 and b > 0 and n >= 2
    q = Fraction(n - 1, n)
    return q ** a, q ** b


def first_bin_cylinder(qr: Fraction, qs: Fraction, k: int):
    assert 0 < qr < 1 and 0 < qs < 1 and k >= 0
    # First time belongs to (k*delta,(k+1)*delta], second exceeds it.
    return (1 - qr) * qr ** k * qs ** (k + 1)


def binned_partition(qr: Fraction, qs: Fraction):
    common = 1 - qr * qs
    return ((1 - qr) * qs / common,
            (1 - qs) * qr / common,
            (1 - qr) * (1 - qs) / common)


class TestS027(unittest.TestCase):
    def test_true_cylinder_geometric_sum_exact_remainder(self):
        for a, b, n in [(1, 1, 2), (1, 3, 7), (6, 2, 11), (7, 5, 17)]:
            qr, qs = bin_parameters(a, b, n)
            strict_first, _, _ = binned_partition(qr, qs)
            for N in [0, 1, 2, 5, 13, 29]:
                partial = sum(
                    (first_bin_cylinder(qr, qs, k) for k in range(N)),
                    Fraction(0),
                )
                tail = strict_first * (qr * qs) ** N
                self.assertEqual(partial + tail, strict_first)
                self.assertGreaterEqual(tail, 0)

    def test_race_partition_and_first_bin_is_lower_bound(self):
        for a in range(1, 8):
            for b in range(1, 8):
                for n in [2, 3, 5, 11, 31]:
                    qr, qs = bin_parameters(a, b, n)
                    first, second, collision = binned_partition(qr, qs)
                    actual_first = Fraction(a, a + b)
                    self.assertEqual(first + second + collision, 1)
                    # These enclosures use the *continuous* exponential
                    # race ratio only as an independent rational oracle.
                    self.assertLessEqual(first, actual_first)
                    self.assertLessEqual(actual_first, first + collision)
                    self.assertLessEqual(collision, min(a, b) * Fraction(1, n))

    def test_first_bin_order_and_rate_swap(self):
        for a, b, n in [(1, 9, 11), (7, 2, 7), (3, 3, 5)]:
            qr, qs = bin_parameters(a, b, n)
            left, right, tied = binned_partition(qr, qs)
            swapped = binned_partition(qs, qr)
            self.assertEqual((left, right, tied),
                             (swapped[1], swapped[0], swapped[2]))
            # Probability of a first-bin victory for k=0 is a genuine
            # product of P(T_r<=delta) and P(T_s>delta).
            self.assertEqual(first_bin_cylinder(qr, qs, 0), (1-qr) * qs)


if __name__ == "__main__":
    unittest.main()
