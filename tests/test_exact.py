import sys
import unittest
from fractions import Fraction
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import (graph, path, cycle, star, complete_multipartite,
                   maximal_independent_sets, law_by_recursion, law_by_permutations,
                   c6_pair_probabilities, is_uniform)

class ExactLawTests(unittest.TestCase):
    def test_recurrence_vs_independent_permutation_oracle(self):
        for g in (path(3), path(4), cycle(4), cycle(5), cycle(6)):
            r = [Fraction(2*i+1, 3*i+2) for i in range(len(g))]
            self.assertEqual(law_by_recursion(g,r), law_by_permutations(g,r))
            self.assertEqual(set(law_by_recursion(g,r)), set(maximal_independent_sets(g)))
            self.assertEqual(sum(law_by_recursion(g,r).values()), 1)

    def test_stars(self):
        for m in range(1,8):
            law = law_by_recursion(star(m), [m]+[1]*m)
            self.assertEqual(len(law), 2)
            self.assertEqual(set(law.values()), {Fraction(1,2)})

    def test_multipartite(self):
        parts = (2,3,1)
        rates = [Fraction(1,k) for k in parts for _ in range(k)]
        law = law_by_recursion(complete_multipartite(parts), rates)
        self.assertEqual(len(law),3)
        self.assertEqual(set(law.values()), {Fraction(1,3)})

    def test_components(self):
        g = graph(5, [(0,1),(1,2),(3,4)])
        a = law_by_recursion(path(3), [1,2,3])
        b = law_by_recursion(graph(2, [(0,1)]), [4,5])
        law = law_by_recursion(g, [1,2,3,4,5])
        self.assertEqual(law, {u|(v<<3): p*q for u,p in a.items() for v,q in b.items()})

    def test_c6_exact_obstruction_formula(self):
        g = cycle(6)
        self.assertEqual(len(maximal_independent_sets(g)),5)
        masks = [(1<<i)|(1<<((i+3)%6)) for i in (0,2,4)]
        for rates in ([1]*6, [2,3,5,7,11,13]):
            law = law_by_recursion(g,rates)
            pp = c6_pair_probabilities(rates)
            self.assertEqual(pp, tuple(law[s] for s in masks))
            self.assertLessEqual(pp[0]*pp[1]*pp[2],Fraction(1,729))
        self.assertEqual(c6_pair_probabilities([1]*6), (Fraction(1,9),)*3)
        self.assertGreater(Fraction(1,5)**3, Fraction(1,729))

    def test_empty_and_invalid(self):
        self.assertEqual(law_by_recursion(graph(0, []), ()), {0:Fraction(1)})
        with self.assertRaises(ValueError): law_by_recursion(path(2), [0,1])
        with self.assertRaises(ValueError): law_by_recursion(path(2), [1])

if __name__ == "__main__": unittest.main()
