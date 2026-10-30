"""Exact rational output law of exponential-clock greedy independent sets."""
from fractions import Fraction
from functools import lru_cache
from itertools import permutations

def graph(n, edges):
    if n < 0: raise ValueError("n must be nonnegative")
    adj = [1 << i for i in range(n)]
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n) or u == v: raise ValueError("invalid edge")
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return tuple(adj)

def path(n):
    return graph(n, ((i, i+1) for i in range(n-1)))

def cycle(n):
    if n < 3: raise ValueError("cycle needs at least 3 vertices")
    return graph(n, ((i, (i+1) % n) for i in range(n)))

def star(leaves):
    if leaves < 1: raise ValueError("at least one leaf required")
    return graph(leaves+1, ((0, i) for i in range(1, leaves+1)))

def complete_multipartite(parts):
    if not parts or any(k < 1 for k in parts): raise ValueError("nonempty positive parts needed")
    n = sum(parts)
    buckets = [i for i, k in enumerate(parts) for _ in range(k)]
    return graph(n, ((u, v) for u in range(n) for v in range(u+1, n) if buckets[u] != buckets[v]))

def vertices(mask):
    while mask:
        b = mask & -mask
        yield b.bit_length()-1
        mask ^= b

def maximal_independent_sets(adj):
    n = len(adj)
    return tuple(s for s in range(1 << n)
                 if all(not (adj[v] & (s & ~(1 << v))) for v in vertices(s))
                 and all(adj[v] & s for v in range(n)))

def validate_rates(adj, rates):
    values = tuple(Fraction(x) for x in rates)
    if len(values) != len(adj) or any(v <= 0 for v in values):
        raise ValueError("strictly positive rates required at every vertex")
    return values

def law_by_recursion(adj, rates):
    rates = validate_rates(adj, rates)
    @lru_cache(None)
    def f(active):
        if not active: return {0: Fraction(1)}
        total = sum((rates[v] for v in vertices(active)), Fraction(0))
        ans = {}
        for v in vertices(active):
            for sub, p in f(active & ~adj[v]).items():
                key = sub | (1 << v)
                ans[key] = ans.get(key, Fraction(0)) + rates[v]*p/total
        return ans
    return f((1 << len(adj))-1)

def greedy_output(adj, order):
    if sorted(order) != list(range(len(adj))): raise ValueError("invalid permutation")
    ans = 0
    for v in order:
        if ans & adj[v] == 0: ans |= 1 << v
    return ans

def law_by_permutations(adj, rates):
    rates = validate_rates(adj, rates)
    law = {}
    for order in permutations(range(len(adj))):
        total = sum(rates, Fraction(0))
        weight = Fraction(1)
        for v in order:
            weight *= rates[v]/total
            total -= rates[v]
        key = greedy_output(adj, order)
        law[key] = law.get(key, Fraction(0)) + weight
    return law

def c6_pair_probabilities(rates):
    rates = validate_rates(cycle(6), rates)
    a = [rates[i] for i in (0,2,4)]
    d = [rates[i] for i in (3,5,1)]
    A, D = sum(a), sum(d)
    return tuple(a[i]*d[i]/((A-a[i]+d[i])*(D-d[i]+a[i])) for i in range(3))

def is_uniform(law):
    return bool(law) and len(set(law.values())) == 1

if __name__ == "__main__":
    for name, g, rates in [
        ("P3 equal", path(3), [1,1,1]),
        ("K1,2 tuned", star(2), [2,1,1]),
        ("C6 equal", cycle(6), [1]*6)]:
        law = law_by_recursion(g, rates)
        print(name, "uniform=", is_uniform(law), "law=", law)
        assert sum(law.values()) == 1
    print("C6 sharp pair product", Fraction(1,9)**3)
