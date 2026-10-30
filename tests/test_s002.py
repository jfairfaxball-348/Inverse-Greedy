"""S002 exact constructive and obstruction checks; no numerical optimizer."""
import sys
import unittest
from fractions import Fraction
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import graph, path, cycle, maximal_independent_sets, law_by_recursion, law_by_permutations, is_uniform
from cograph import uniformise_cograph


class NewTheoremTests(unittest.TestCase):
    def test_join_construction(self):
        # K1 join P3: rates (universal=2, path=[1,2,1]); both factors have
        # MIS counts 1 and 2, respectively.
        g = graph(4, [(0,1),(0,2),(0,3),(1,2),(2,3)])
        rates, count = uniformise_cograph(g)
        self.assertEqual(count, 3)
        self.assertEqual(is_uniform(law_by_recursion(g, rates)), True)
        self.assertEqual(set(law_by_recursion(g, rates).values()), {Fraction(1,3)})

    def test_disconnected_cograph(self):
        g = graph(5, [(0,1),(0,2),(3,4)])
        rates, count = uniformise_cograph(g)
        self.assertEqual(count, 4)
        self.assertEqual(set(law_by_recursion(g,rates).values()), {Fraction(1,4)})

    def test_p5_strict_probability_minor(self):
        g = path(5)
        self.assertEqual(len(maximal_independent_sets(g)), 4)
        for nums in product(range(1,4), repeat=5):
            a,b,c,d,e = map(Fraction, nums)
            B, E = a+b, d+e
            T = B+c+E
            p = law_by_recursion(g,(a,b,c,d,e))
            self.assertEqual(set(p), {9,10,18,21})
            self.assertEqual(p[9], a*d/(B*(c+E)))
            self.assertEqual(p[10], b*d*(B+E)/(T*B*E))
            self.assertEqual(p[18], b*e/(E*(B+c)))
            self.assertEqual(p[21], c/T+a*(c+e)/(T*(c+E))+e*(a+c)/(T*(B+c)))
            positive = p[10]*c/T*(
                1 + e/(B+c) + a/(c+E) * (1-e*c/((B+c)*(B+E)))
            )
            self.assertEqual(p[21]*p[10]-p[9]*p[18], positive)
            self.assertGreater(positive, 0)

    def test_c6_and_p5_are_different_obstructions(self):
        self.assertEqual(len(maximal_independent_sets(cycle(6))),5)
        self.assertEqual(len(maximal_independent_sets(path(5))),4)

    def test_cograph_atlas_small(self):
        # Optional atlas verification; the standard-library tests above
        # remain active even in environments without networkx.
        try:
            import networkx as nx
        except ImportError:
            self.skipTest("optional networkx not installed")
        hits = []
        for n in range(1,7):
            positive = 0
            for g in nx.graph_atlas_g():
                if len(g) != n or not nx.is_connected(g):
                    continue
                adj = graph(n, g.edges())
                try:
                    rates, count = uniformise_cograph(adj)
                except ValueError:
                    continue
                law = law_by_recursion(adj, rates)
                self.assertEqual(len(law), count)
                self.assertEqual(len(law),len(maximal_independent_sets(adj)))
                self.assertTrue(is_uniform(law))
                self.assertEqual(sum(law.values()), 1)
                positive += 1
            hits.append(positive)
        self.assertEqual(hits,[1,1,2,5,12,33])


if __name__ == "__main__":
    unittest.main()
