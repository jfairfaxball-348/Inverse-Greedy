"""S005: exact positive EGU witnesses for the seven open connected n=5 graphs.

Indices refer to connected NetworkX graph-atlas order. Six integer witnesses
are checked using Fraction; the last uses exact Q(sqrt(3)) arithmetic.
No floating-point approximate witness is treated as a certificate.
"""
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import permutations

from exact import graph, vertices

# Edges are retained to prevent silent misidentification from atlas indexing.
FIVE_VERTEX_RATIONAL = {
    1: (((0,4),(1,3),(2,3),(3,4)), (14,6,6,9,10)),
    4: (((0,1),(0,2),(0,4),(1,2),(2,3)), (4,2,4,3,3)),
    5: (((0,4),(1,2),(1,3),(2,3),(3,4)), (25,9,9,7,20)),
    6: (((0,1),(1,3),(1,4),(2,3),(2,4)), (12,9,14,5,5)),
    9: (((0,1),(1,3),(1,4),(2,3),(2,4),(3,4)), (16,8,6,5,5)),
    11: (((0,1),(0,3),(0,4),(1,2),(2,3),(3,4)), (4,5,5,4,6)),
}
ALGEBRAIC_INDEX = 15
ALGEBRAIC_EDGES = ((0,1),(0,4),(1,2),(1,3),(1,4),(2,3),(3,4))


@dataclass(frozen=True)
class Q3:
    """Exact number a + b sqrt(3), with rational a,b; sqrt(3)^2=3."""
    a: Fraction
    b: Fraction = Fraction(0)

    def __post_init__(self):
        object.__setattr__(self, "a", Fraction(self.a))
        object.__setattr__(self, "b", Fraction(self.b))

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q3) else Q3(Fraction(x))

    def __add__(self, other):
        q = self.cast(other)
        return Q3(self.a + q.a, self.b + q.b)

    __radd__ = __add__

    def __neg__(self):
        return Q3(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) + (-self)

    def __mul__(self, other):
        q = self.cast(other)
        return Q3(self.a*q.a + 3*self.b*q.b, self.a*q.b + self.b*q.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        q = self.cast(other)
        norm = q.a*q.a - 3*q.b*q.b
        if not norm:
            raise ZeroDivisionError("zero norm in Q(sqrt(3))")
        return Q3((self.a*q.a-3*self.b*q.b)/norm,
                  (self.b*q.a-self.a*q.b)/norm)

    def __rtruediv__(self, other):
        return self.cast(other) / self


SQRT3 = Q3(0, 1)
ALGEBRAIC_RATES = (Q3(1)+SQRT3, Q3(2)+Q3(Fraction(0), Fraction(2,3)),
                   Q3(1)+SQRT3, Q3(2), Q3(2))


def quadratic_law_by_recursion(adj, rates):
    """Independent exact-field implementation of the first-choice recurrence."""
    rates = tuple(map(Q3.cast, rates))
    @lru_cache(None)
    def rec(active):
        if not active:
            return {0: Q3(1)}
        total = sum((rates[v] for v in vertices(active)), Q3(0))
        out = {}
        for v in vertices(active):
            for sub, p in rec(active & ~adj[v]).items():
                target = sub | (1 << v)
                out[target] = out.get(target, Q3(0)) + rates[v]*p/total
        return out
    return rec((1 << len(adj))-1)


def quadratic_law_by_permutations(adj, rates):
    """Independent full priority-order oracle in the same exact number field."""
    rates = tuple(map(Q3.cast, rates))
    out = {}
    for order in permutations(range(len(adj))):
        total = sum(rates, Q3(0))
        weight = Q3(1)
        accepted = 0
        for v in order:
            weight = weight * rates[v] / total
            total = total - rates[v]
            if not (adj[v] & accepted):
                accepted |= 1 << v
        out[accepted] = out.get(accepted, Q3(0)) + weight
    return out
