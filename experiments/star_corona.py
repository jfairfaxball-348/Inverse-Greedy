"""Exact rational corner probabilities for the pendant corona of K_(1,m).

This is an *independent formula* checked against the general greedy
first-choice recursion, not a numerical optimiser or nonexistence oracle.
Core hub = vertex 0; spokes = 1..m; hub leaf = m+1;
spoke i's private leaf = m+1+i. Total vertices = 2*m+2.
"""
from fractions import Fraction
from itertools import product


def star_corona_edges(m):
    if m < 1:
        raise ValueError("m must be positive")
    return tuple([(0, i) for i in range(1, m + 1)] +
                 [(0, m + 1)] +
                 [(i, m + 1 + i) for i in range(1, m + 1)])


def star_corona_exact_law(rates):
    if len(rates) < 4 or len(rates) % 2:
        raise ValueError("need 2*m+2 rates, m >= 1")
    rates = tuple(map(Fraction, rates))
    if any(r <= 0 for r in rates):
        raise ValueError("strictly positive rates required")
    m = (len(rates) - 2) // 2
    b, B = rates[0], rates[m + 1]
    u = [rates[i] + rates[m + 1 + i] for i in range(1, m + 1)]
    x = [rates[i] / u[i - 1] for i in range(1, m + 1)]
    out = {}
    for indicators in product((0, 1), repeat=m):
        t = sum((u[i] for i, flag in enumerate(indicators) if flag), Fraction(0))
        weight = (B + t) / (b + B + t)
        mask = 1 << (m + 1)
        for i, flag in enumerate(indicators):
            mask |= 1 << (1 + i if flag else m + 2 + i)
            weight *= x[i] if flag else (1 - x[i])
        out[mask] = weight
    hub_mask = 1
    for i in range(1, m + 1):
        hub_mask |= 1 << (m + 1 + i)
    out[hub_mask] = 1 - sum(out.values(), Fraction(0))
    assert out[hub_mask] > 0 and all(p > 0 for p in out.values())
    return out


def near_uniform_positive_rates(m, t):
    """Positive rates approaching uniform law as t -> infinity (m>=2).

    This is NOT an exactly uniform witness for finite t.
    """
    if m < 2:
        raise ValueError("star obstruction requires at least two spokes")
    t = Fraction(t)
    if t <= 0:
        raise ValueError("t must be strictly positive")
    return (t,) + (Fraction(1),) * m + ((2**m) * t,) + (Fraction(1),) * m
