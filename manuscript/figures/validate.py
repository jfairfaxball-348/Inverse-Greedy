#!/usr/bin/env python3
"""S049 exact, independent checks for all mathematical diagram claims.
Run from any working directory; requires networkx + sympy.
This is not a proof of the entire five-vertex classification.
"""
from fractions import Fraction as F
from itertools import permutations
from collections import Counter
import sympy as s
import networkx as nx


def mis(graph):
    nodes=list(graph.nodes())
    out=[]
    for mask in range(1<<len(nodes)):
        S={nodes[i] for i in range(len(nodes)) if mask>>i&1}
        if any(u in S and v in S for u,v in graph.edges()):
            continue
        if all(v in S or any(graph.has_edge(v,u) for u in S) for v in nodes):
            out.append(frozenset(S))
    return set(out)


def exact_law(graph, rates):
    nodes=list(graph.nodes())
    counts=Counter()
    from math import factorial
    for order in permutations(nodes):
        rem=F(1)
        active=set(nodes)
        selected=set()
        for v in order:
            rem *= rates[v]/sum((rates[u] for u in active),F(0))
            active.remove(v)
            if not any(graph.has_edge(v,u) for u in selected):
                selected.add(v)
        counts[frozenset(selected)]+=rem
    assert sum(counts.values(),F(0))==1
    assert set(counts)==mis(graph)
    return counts


def main():
    classes=[g for g in nx.graph_atlas_g() if len(g)<=5]
    assert [sum(len(g)==n for g in classes) for n in range(6)]==[1,1,2,4,11,34]
    for n in range(6):
        group=[g for g in classes if len(g)==n]
        assert all(not nx.is_isomorphic(a,b) for i,a in enumerate(group) for b in group[i+1:])
    assert sum(nx.is_isomorphic(g,nx.path_graph(5)) for g in classes)==1

    p3=nx.path_graph(3)
    p3law=exact_law(p3,{0:F(1),1:F(2),2:F(1)})
    assert p3law=={frozenset([1]):F(1,2),frozenset([0,2]):F(1,2)}
    star=nx.star_graph(3)
    star_law=exact_law(star,{0:F(3),1:F(1),2:F(1),3:F(1)})
    assert star_law=={frozenset([0]):F(1,2),frozenset([1,2,3]):F(1,2)}
    p5=nx.path_graph(5)
    p5sets={frozenset(x) for x in [(0,2,4),(0,3),(1,3),(1,4)]}
    assert mis(p5)==p5sets
    equal=exact_law(p5, {i:F(1) for i in range(5)})
    assert equal[frozenset((0,2,4))]==F(7,15)
    assert equal[frozenset((1,3))]==F(1,5)
    assert equal[frozenset((0,3))]==F(1,6)
    assert equal[frozenset((1,4))]==F(1,6)

    a,b,c,d,e=s.symbols('a b c d e',positive=True)
    S=a+b+c+d+e
    p14=a*d/((a+b)*(c+d+e))
    p25=b*e/((a+b+c)*(d+e))
    p24=(b*d/S)*(1/(a+b)+1/(d+e))
    p135=(a*(c+e)/(c+d+e)+c+e*(a+c)/(a+b+c))/S
    delta=s.factor(p135*p24-p14*p25)
    Q=s.cancel(delta*((a+b)*(d+e)*(a+b+c)*(c+d+e)*S**2)/(b*c*d))
    q0=(a**3+2*a*a*(b+d+e)+a*(b*b+3*b*d+3*b*e+d*d+3*d*e+2*e*e)
        +b*b*(d+e)+b*(d*d+3*d*e+2*e*e)+d*d*e+2*d*e*e+e**3)
    q1=(2*a*a+3*a*b+3*a*d+3*a*e+b*b+2*b*d+3*b*e+d*d+3*d*e+2*e*e)
    assert s.expand(Q-(q0+c*q1+c*c*(a+b+d+e)))==0
    poly=s.Poly(Q,a,b,c,d,e)
    assert len(poly.terms())==32 and all(coeff>0 for _mon,coeff in poly.terms())
    assert s.simplify(delta-b*c*d*Q/((a+b)*(d+e)*(a+b+c)*(c+d+e)*S**2))==0
    numP4=s.sqrt(3)-1
    A=s.Integer(1); B=numP4
    pOuter=s.simplify(A**2/(A+B)**2)
    assert pOuter==s.Rational(1,3)
    assert s.simplify((1-pOuter)/2-s.Rational(1,3))==0
    print('PASS: atlas 1/1/2/4/11/34; unique P5; P5 four MIS; P3, K1,3 and P4 exact witnesses')
    print('PASS: P5 four exact equal-rate masses:', {','.join(str(v+1) for v in sorted(k)):str(x) for k,x in equal.items()})
    print('PASS: strict P5 minor factors as b*c*d*Q / positive denominator; Q has',len(poly.terms()),'positive monomials')

if __name__=='__main__':main()