"""Reproducible PARTIAL certificate atlas of connected graphs of order <= 6.

Requires optional networkx. Graph indices are within each connected order in
networkx.graph_atlas_g() order. An unresolved graph is NOT a negative result.
"""
import argparse
import json
from itertools import product

from cograph import uniformise_cograph
from exact import graph, law_by_recursion, maximal_independent_sets, is_uniform


def enumerate_atlas(max_n=6, max_rate=4):
    import networkx as nx
    for n in range(1, max_n + 1):
        graphs = [g for g in nx.graph_atlas_g()
                  if len(g) == n and nx.is_connected(g)]
        for index, g in enumerate(graphs):
            edges = sorted([sorted(e) for e in g.edges()])
            adj = graph(n, edges)
            targets = maximal_independent_sets(adj)
            entry = dict(n=n, index=index, edges=edges, maximal_sets=len(targets),
                         status='unresolved', certificate=None)
            try:
                rates, count = uniformise_cograph(adj)
                assert len(targets) == count
                assert set(law_by_recursion(adj, rates)) == set(targets)
                assert is_uniform(law_by_recursion(adj, rates))
                entry.update(status='proved-positive', certificate='cograph join/union',
                             rates=[str(x) for x in rates])
            except ValueError:
                pass
            if entry['status'] == 'unresolved':
                for rates in product(range(1, max_rate + 1), repeat=n - 1):
                    witness = rates + (1,)
                    if is_uniform(law_by_recursion(adj, witness)):
                        entry.update(status='proved-positive', certificate='exact rational rates',
                                     rates=list(witness))
                        break
            if entry['status'] == 'unresolved' and n == 4 and nx.is_isomorphic(g, nx.path_graph(4)):
                entry.update(status='proved-positive', certificate='P4 algebraic witness; proof/FOUNDATIONS.md')
            if entry['status'] == 'unresolved' and n == 5 and nx.is_isomorphic(g, nx.path_graph(5)):
                entry.update(status='proved-negative', certificate='P5 strict determinant; proof/P5_OBSTRUCTION.md')
            if entry['status'] == 'unresolved' and n == 6 and nx.is_isomorphic(g, nx.cycle_graph(6)):
                entry.update(status='proved-negative', certificate='C6 AM-GM; proof/C6_OBSTRUCTION.md')
            yield entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=6)
    parser.add_argument('--max-rate', type=int, default=4)
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args()
    if not 1 <= args.max_n <= 6 or not 1 <= args.max_rate <= 8:
        parser.error('max-n must be 1..6 and max-rate must be 1..8')
    rows = list(enumerate_atlas(args.max_n, args.max_rate))
    if args.json:
        print(json.dumps(rows, indent=2))
    else:
        for n in range(1, args.max_n + 1):
            sample = [r for r in rows if r['n'] == n]
            counts = {k: sum(r['status'] == k for r in sample)
                      for k in ('proved-positive', 'proved-negative', 'unresolved')}
            print(f'n={n} total={len(sample)}', counts)
            print('  negative atlas indices:', [r['index'] for r in sample if r['status'] == 'proved-negative'])
        print('Unresolved means unclassified, NOT impossible.')


if __name__ == '__main__':
    main()
