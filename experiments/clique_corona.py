"""S008: complete-graph coronas with one private leaf per clique vertex.

The graph K_m circ K1 is EGU with leaf rates 1 and clique rates
(m+1)^(1/m)-1. The proof is in proof/CLIQUE_CORONA.md.
"""
from itertools import combinations


def clique_corona_edges(m):
    if m < 1:
        raise ValueError("clique size must be positive")
    return ([(i, m+i) for i in range(m)] +
            [(m+i, m+j) for i, j in combinations(range(m), 2)])
