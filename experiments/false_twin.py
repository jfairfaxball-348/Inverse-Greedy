"""S007: false-twin contraction and exact transfer of EGU witnesses.

Distinct nonadjacent vertices with the same open neighbourhood are false
twins. The projected greedy terminal law is identical after contraction
and addition of their strictly positive arrival rates.
"""
from itertools import combinations
from fractions import Fraction


def first_false_twin(g):
    """Return the lexicographically first false-twin pair or None."""
    for u, v in combinations(sorted(g.nodes), 2):
        if not g.has_edge(u, v) and set(g.neighbors(u)) == set(g.neighbors(v)):
            return u, v
    return None


def contraction_parent(g, atlas5):
    """Return (pair, five-vertex atlas index, reduced graph) or None."""
    import networkx as nx
    pair = first_false_twin(g)
    if pair is None:
        return None
    u, v = pair
    reduced = g.copy()
    reduced.remove_node(v)
    matches = [i for i, h in enumerate(atlas5) if nx.is_isomorphic(reduced, h)]
    if len(matches) != 1:
        raise AssertionError("ambiguous atlas contraction")
    return pair, matches[0], reduced


def lift_rates(reduced, parent, u, v, atlas5, parent_rates):
    """Split the parent rate at u between the twins, using exact arithmetic.

    The map reduced -> atlas5[parent] is determined by graph isomorphism.
    Rates are ordered by the original six vertex labels, 0..5.
    """
    import networkx as nx
    matcher = nx.algorithms.isomorphism.GraphMatcher(reduced, atlas5[parent])
    mapping = next(matcher.isomorphisms_iter())
    normalized = tuple(Fraction(r) if isinstance(r, int) else r for r in parent_rates)
    return tuple(normalized[mapping[u]] / 2 if w == u or w == v
                 else normalized[mapping[w]] for w in range(6))
