"""S008: exact algebraic clique-corona certificate, two independent oracles."""
import unittest
from functools import lru_cache
from itertools import permutations
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
import sympy as sp
import networkx as nx
from clique_corona import clique_corona_edges


def exact_algebraic_oracles(m, edges=None):
    """No floating point: arithmetic in Q((m+1)^(1/m))."""
    n = 2*m
    q = sp.real_root(m+1, m)
    field = sp.QQ.algebraic_field(q)
    one, zero = field.one, field.zero
    rates = (one,)*m+(field.from_sympy(q-1),)*m
    assert q > 1
    adj = [(1<<v) for v in range(n)]
    for u,v in (clique_corona_edges(m) if edges is None else edges):
        adj[u] |= (1<<v)
        adj[v] |= (1<<u)

    @lru_cache(None)
    def recursion(active):
        if not active:
            return {0: one}
        total = sum((rates[v] for v in range(n) if active & (1<<v)), zero)
        ans = {}
        for v in range(n):
            if active & (1<<v):
                for sub,p in recursion(active & ~adj[v]).items():
                    terminal=sub | (1<<v)
                    ans[terminal] = ans.get(terminal, zero) + rates[v]*p/total
        return ans

    # Independent oracle: all (2m)! full priority permutations with
    # sequential greedy scanning, not recurrence by active subsets.
    permutation_law = {}
    for order in permutations(range(n)):
        accepted, total, weight = 0, sum(rates, zero), one
        for v in order:
            weight *= rates[v]/total
            total -= rates[v]
            if not (adj[v] & accepted):
                accepted |= (1<<v)
        permutation_law[accepted] = permutation_law.get(accepted, zero)+weight
    return recursion((1<<n)-1), permutation_law, field, rates


class S008CliqueCoronaTests(unittest.TestCase):
    def test_n6_index8_structure_and_both_exact_oracles(self):
        six = [g for g in nx.graph_atlas_g() if len(g)==6 and nx.is_connected(g)]
        self.assertEqual(len(six),112)
        self.assertEqual({frozenset(e) for e in six[8].edges()},
                         {frozenset(e) for e in [(0,4),(1,5),(2,3),(3,4),(3,5),(4,5)]})
        canonical = nx.Graph()
        canonical.add_nodes_from(range(6)); canonical.add_edges_from(clique_corona_edges(3))
        self.assertTrue(nx.is_isomorphic(six[8], canonical))
        recurrence, orders, field, rates = exact_algebraic_oracles(3, list(six[8].edges()))
        self.assertEqual(recurrence, orders)
        self.assertEqual(len(recurrence),4)
        self.assertEqual(set(recurrence.values()),{field.from_sympy(sp.Rational(1,4))})
        self.assertEqual(set(recurrence),{7,11,22,37})
        self.assertEqual(rates[3],field.from_sympy(sp.real_root(4,3)-1))

    def test_m2_recovers_p4_exactly(self):
        recurrence, orders, field, rates = exact_algebraic_oracles(2)
        self.assertEqual(recurrence, orders)
        self.assertEqual(len(recurrence),3)
        self.assertEqual(set(recurrence.values()),{field.from_sympy(sp.Rational(1,3))})

    def test_general_analytical_pair_probability(self):
        for m in range(2,10):
            q = sp.real_root(m+1,m)
            self.assertEqual(sp.simplify(q**m),m+1)

if __name__=='__main__':
    unittest.main()
