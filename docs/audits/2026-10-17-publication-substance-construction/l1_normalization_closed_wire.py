"""Replay the closed-order L1 plaquette-wire contraction.

Use the same five layout arguments as l1_normalization_plaquette_wire.py.
"""

from functools import cache
from itertools import product
from sys import argv
from l1_normalization_uniform_mixed_edge import moment,unit,mul,qadj
from l1_residual_source_contract import add_indices,empty,pauli
from sympy import eye,I,diag
import l1_normalization_plaquette_wire as w

@cache
def projection(alpha,a,b,i,j):
    ch,v=divmod(alpha,3)
    X,Y=unit(a%4),unit(b%4)
    ans=0
    for s,t in product(range(4),repeat=2):
        c=moment(i,j,4*ch+s,4*ch+t)
        if c:
            q=mul(mul(qadj(X),qadj(unit(s))),mul(Y,unit(t)))
            ans+=c*q[v+1]
    return ans

@cache
def edge_wire(a,b,wire,dm,ds):
    return [(j,i,z) for i,j,z in orig_edge(a,b,wire,dm,ds)]

@cache
def vertex_wire(a,b,ch,wire):
    return [(j,i,z) for i,j,z in orig_vertex(a,b,ch,wire)]

@cache
def curv(a,b):
    if a==b:return ()
    basis=[eye(2)]+[-I*p for p in pauli]
    dag=[eye(2)]+[I*p for p in pauli]
    test=w.gamma[a]*w.gamma[b]*diag(1,1,-1,-1)
    out=[]
    for ch in range(2):
        cut=test[2*ch:2*ch+2,2*ch:2*ch+2]
        for i,j,k,l in product(range(4),repeat=4):
            z=(dag[l]*dag[k]*basis[j]*basis[i]*cut).trace().expand()
            if z:
                x=add_indices(empty,4*ch+i,4*ch+k)
                y=add_indices(empty,4*ch+j,4*ch+l)
                out.append((x,y,w.gaussian(z)))
    return tuple(out)
orig_edge, orig_vertex = w.e_wire, w.vertex_wire

if __name__ == "__main__":
    w.projection = projection
    w.e_wire = edge_wire
    w.vertex_wire = vertex_wire
    w.curv = curv
    w.run(bool(int(argv[1])), tuple(map(int, argv[2:])))
