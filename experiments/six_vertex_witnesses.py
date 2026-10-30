"""S006: additional exact positive EGU certificate at connected n=6 atlas index 1.

Indices refer to NetworkX graph_atlas_g() restricted to connected n=6.
Edge and maximal-independent-set checks must accompany the rate witness:
a bounded failed search is not a negative classification.
"""
from fractions import Fraction

SIX_VERTEX_RATIONAL = {
    1: (((0, 1), (1, 2), (1, 4), (1, 5), (2, 3)),
        (3, 6, 4, 5, 3, 3)),
}


def index_one_closed_form(a, t, u, w):
    """Exactly the three output probabilities for rates (a,t,u,w,a,a).

    The maximal independent sets, in the same order, are
    {0,2,4,5}, {0,3,4,5}, and {1,3}.
    """
    a, t, u, w = map(Fraction, (a, t, u, w))
    if min(a, t, u, w) <= 0:
        raise ValueError("all rates must be strictly positive")
    first = u * (u + w + 3*a) / ((u+w) * (t+u+w+3*a))
    second = 3*a*w / ((t+3*a) * (u+w))
    third = t * (t+w+3*a) / ((t+3*a) * (t+u+w+3*a))
    assert first + second + third == 1
    return first, second, third
