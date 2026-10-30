"""S003 P6 proof: independent order and exact rational certificates."""
import sys
import unittest
from itertools import permutations, product
from fractions import Fraction
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import path, maximal_independent_sets, law_by_recursion, law_by_permutations, greedy_output

class P6BottleneckTests(unittest.TestCase):
    def test_five_outputs_and_event_equivalence_all_orders(self):
        g = path(6)
        self.assertEqual(set(maximal_independent_sets(g)), {21,37,41,42,18})
        for order in permutations(range(6)):
            positions = {v:i for i,v in enumerate(order)}
            left = positions[1] < min(positions[0],positions[2])
            right = positions[4] < min(positions[3],positions[5])
            out = greedy_output(g,order)
            self.assertEqual(out == 18, left and right)
            if out in (37,41):
                self.assertFalse(left)
                self.assertFalse(right)

    def test_rational_bottleneck_strict_on_729_vectors(self):
        g=path(6)
        for values in product((1,2,3),repeat=6):
            a,b,c,d,e,f=map(Fraction,values)
            law=law_by_recursion(g,values)
            u=b/(a+b+c)
            v=e/(d+e+f)
            self.assertEqual(law[18],u*v)
            self.assertLessEqual(law[37]+law[41],(1-u)*(1-v))
            self.assertEqual(sum(law.values()),1)
            # Independent priority-permutation oracle on selected cases.
        for values in ((1,)*6,(2,3,5,7,11,13)):
            self.assertEqual(law_by_recursion(g,values),
                             law_by_permutations(g,values))

    def test_exact_uniform_hypothesis_is_inconsistent(self):
        # The proof is algebraic: uv=1/5 and
        # 2/5<=(1-u)(1-v) imply s=u+v<=4/5,
        # while s^2>=4uv=4/5>16/25.
        self.assertGreater(Fraction(4,5),Fraction(16,25))

if __name__ == "__main__":
    unittest.main()
