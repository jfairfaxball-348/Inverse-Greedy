"""Construct exact positive uniformising rates for any finite cograph.

Works with closed-neighbourhood bitmask adjacency from experiments/exact.py.
On non-cographs raises ValueError; this is not evidence of non-uniformisability.
"""
from fractions import Fraction
from functools import lru_cache


def components(adj, mask, complement=False):
    remaining = mask
    result = []
    while remaining:
        todo = remaining & -remaining
        seen = 0
        while todo:
            bit = todo & -todo
            todo -= bit
            if bit & seen:
                continue
            seen |= bit
            v = bit.bit_length() - 1
            neighbors = (mask & ~adj[v]) if complement else (mask & adj[v])
            todo |= neighbors & ~seen
        result.append(seen)
        remaining &= ~seen
    return tuple(result)


def uniformise_cograph(adj):
    """Return (positive Fraction-rate vector, number of maximal independent sets)."""
    n = len(adj)

    @lru_cache(None)
    def rec(mask):
        if mask.bit_count() <= 1:
            return ({i: Fraction(1) for i in range(n) if mask >> i & 1}, 1)
        parts = components(adj, mask)
        if len(parts) > 1:
            result = {}
            count = 1
            for p in parts:
                rates, k = rec(p)
                result.update(rates)
                count *= k
            return result, count
        parts = components(adj, mask, complement=True)
        if len(parts) > 1:
            result = {}
            count = 0
            for p in parts:
                rates, k = rec(p)
                scale = Fraction(k, 1) / sum(rates.values())
                result.update({v: x * scale for v, x in rates.items()})
                count += k
            return result, count
        raise ValueError("not a cograph: connected graph and complement both connected")

    rates, number_of_mis = rec((1 << n) - 1)
    return tuple(rates[i] for i in range(n)), number_of_mis
