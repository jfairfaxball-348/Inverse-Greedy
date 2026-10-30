"""Reproducible PARTIAL certificate atlas of connected graphs of order <= 6.

Requires optional networkx. Graph indices are within each connected order in
networkx.graph_atlas_g() order. An unresolved graph is NOT a negative result.
"""
import argparse
import json
from itertools import product

from cograph import uniformise_cograph
from exact import graph, law_by_recursion, maximal_independent_sets, is_uniform
from five_vertex_witnesses import FIVE_VERTEX_RATIONAL, ALGEBRAIC_INDEX, ALGEBRAIC_EDGES
from six_vertex_witnesses import SIX_VERTEX_RATIONAL
from false_twin import contraction_parent


def enumerate_atlas(max_n=6, max_rate=4, include_false_twins=True):
    import networkx as nx
    # S004: the six-vertex cone over P5 is a rigorous negative by
    # join necessity and the already proved strict P5 obstruction.
    five_atlas = [g for g in nx.graph_atlas_g() if len(g) == 5 and nx.is_connected(g)]
    cone_p5 = nx.path_graph(5)
    cone_p5.add_node(5)
    cone_p5.add_edges_from((5, i) for i in range(5))
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
            # S005: seven independently certified positive n=5 instances.
            # This branch checks the structure, not a failed bounded rate search.
            if entry['status'] == 'unresolved' and n == 5 and index in FIVE_VERTEX_RATIONAL:
                expected_edges, rates = FIVE_VERTEX_RATIONAL[index]
                assert {frozenset(e) for e in g.edges()} == {frozenset(e) for e in expected_edges}
                assert is_uniform(law_by_recursion(adj, rates))
                entry.update(status='proved-positive',
                             certificate='S005 exact positive rational witness; proof/FIVE_VERTEX_ATLAS.md',
                             rates=list(rates))
            if entry['status'] == 'unresolved' and n == 5 and index == ALGEBRAIC_INDEX:
                assert {frozenset(e) for e in g.edges()} == {frozenset(e) for e in ALGEBRAIC_EDGES}
                entry.update(status='proved-positive',
                             certificate='S005 exact Q(sqrt(3)) witness; proof/FIVE_VERTEX_ATLAS.md',
                             rates=['1+sqrt(3)', '2+2sqrt(3)/3', '1+sqrt(3)', '2', '2'])
            # S006: new independently verified, exactly uniform n=6 witness.
            if entry['status'] == 'unresolved' and n == 6 and index in SIX_VERTEX_RATIONAL:
                expected_edges, rates = SIX_VERTEX_RATIONAL[index]
                assert {frozenset(e) for e in g.edges()} == {frozenset(e) for e in expected_edges}
                assert all(x > 0 for x in rates)
                assert is_uniform(law_by_recursion(adj, rates))
                entry.update(status='proved-positive',
                             certificate='S006 exact positive rational witness; proof/SIX_VERTEX_INDEX1.md',
                             rates=list(rates))
            if entry['status'] == 'unresolved' and n == 4 and nx.is_isomorphic(g, nx.path_graph(4)):
                entry.update(status='proved-positive', certificate='P4 algebraic witness; proof/FOUNDATIONS.md')
            if entry['status'] == 'unresolved' and n == 5 and nx.is_isomorphic(g, nx.path_graph(5)):
                entry.update(status='proved-negative', certificate='P5 strict determinant; proof/P5_OBSTRUCTION.md')
            if entry['status'] == 'unresolved' and n == 6 and nx.is_isomorphic(g, nx.path_graph(6)):
                entry.update(status='proved-negative', certificate='P6 double-triple race bottleneck; proof/P6_OBSTRUCTION.md')
            if entry['status'] == 'unresolved' and n == 6 and nx.is_isomorphic(g, nx.cycle_graph(6)):
                entry.update(status='proved-negative', certificate='C6 AM-GM; proof/C6_OBSTRUCTION.md')
            if entry['status'] == 'unresolved' and n == 6 and nx.is_isomorphic(g, cone_p5):
                entry.update(status='proved-negative',
                             certificate='K1 join P5; join necessity + P5 strict minor; proof/CONE_P5_OBSTRUCTION.md')
            # S007: a false-twin pair contracts to a connected five-vertex
            # graph. Terminal laws agree after adding twin rates. The complete
            # S005 n=5 theorem is therefore a genuine proof for both signs.
            if include_false_twins and entry["status"] == "unresolved" and n == 6:
                contraction = contraction_parent(g, five_atlas)
                if contraction is not None:
                    pair, parent_index, reduced = contraction
                    entry["twin_pair"] = list(pair)
                    entry["contracted_n5_index"] = parent_index
                    if parent_index == 2:
                        assert nx.is_isomorphic(reduced, nx.path_graph(5))
                        entry.update(
                            status="proved-negative",
                            certificate="S007 false-twin contraction to P5; proof/FALSE_TWIN_INVARIANCE.md")
                    else:
                        entry.update(
                            status="proved-positive",
                            certificate=("S007 false-twin lift of complete S005 n=5 witness;"
                                         " proof/FALSE_TWIN_INVARIANCE.md"))
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
