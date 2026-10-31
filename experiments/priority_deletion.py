"""S011 exact weighted-priority deletion and head-decomposition oracle.

This module independently sums *all* weighted priority permutations,
using fractions throughout. It deliberately does not call the recursive
greedy law: the caller can compare it against that separate algorithm.
"""
from fractions import Fraction
from itertools import permutations


def weighted_order_mass(order, rates):
    """Plackett-Luce mass of a complete order of the given vertex IDs."""
    order = tuple(order)
    rates = tuple(Fraction(q) for q in rates)
    if not all(q > 0 for q in rates):
        raise ValueError("all rates must be positive")
    if len(set(order)) != len(order) or any(v < 0 or v >= len(rates) for v in order):
        raise ValueError("invalid priority list")
    total = sum((rates[v] for v in order), Fraction(0))
    mass = Fraction(1)
    for v in order:
        mass *= rates[v] / total
        total -= rates[v]
    return mass


def complete_order_law(rates, vertices=None):
    """Exact full-permutation law on an arbitrary retained vertex subset."""
    rates = tuple(Fraction(q) for q in rates)
    if vertices is None:
        vertices = tuple(range(len(rates)))
    vertices = tuple(vertices)
    if len(set(vertices)) != len(vertices):
        raise ValueError("vertices must be distinct")
    return {order: weighted_order_mass(order, rates) for order in permutations(vertices)}


def projected_order_law(rates, retained):
    """Marginal law after erasing all discarded vertices from full orders."""
    retained = frozenset(retained)
    law = {}
    for order, mass in complete_order_law(rates).items():
        projected = tuple(v for v in order if v in retained)
        law[projected] = law.get(projected, Fraction(0)) + mass
    return law


def conditional_projected_after_first(rates, first, retained):
    """Relative order of retained vertices given the global first vertex."""
    rates = tuple(Fraction(q) for q in rates)
    retained = frozenset(retained)
    if first in retained:
        raise ValueError("first vertex cannot also be retained")
    p_first = rates[first] / sum(rates)
    law = {}
    for order, mass in complete_order_law(rates).items():
        if order and order[0] == first:
            projected = tuple(v for v in order[1:] if v in retained)
            law[projected] = law.get(projected, Fraction(0)) + mass / p_first
    return law


def head_split_orders(vertices):
    """Combinatorial head partition, independent from itertools.permutations."""
    vertices = tuple(vertices)
    if not vertices:
        return [()]
    return [(v,) + tail
            for v in vertices
            for tail in head_split_orders(tuple(w for w in vertices if w != v))]


if __name__ == "__main__":
    print("S011 exact priority deletion and decomposition")
    rates = (1, 2, 3, 4, 5, 6)
    full = complete_order_law(rates)
    assert sum(full.values()) == 1
    for keep in ((0, 1), (1, 3, 5), (0, 2, 4, 5), ()):
        assert projected_order_law(rates, keep) == complete_order_law(rates, keep)
    print("full mass:", sum(full.values()), "orders:", len(full))
