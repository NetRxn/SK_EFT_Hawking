"""Exact shared-quadratic link sectors via coordinate second moments."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import factorial,prod

from l1_equal_time_shared_quartic import (
    AXES,forward,quat,adj,diag,gamma,bilinear,add,scale,wedge,
    frame_pair,square,contract,edges_for,same_site_quadratic_support,
    reduce_source_dependence,
)

bases=tuple((tuple(int(i==k) for i in range(4)),
             tuple(int(i+4==k) for i in range(4))) for k in range(8))


@cache
def fixed_frame(site,axis,link_site,coordinate):
    left,right=bases[coordinate]
    U=diag(quat(left),quat(right));Ud=diag(quat(adj(left)),quat(adj(right)))
    end=forward(site,axis)
    if end==site:
        d=Ud-U
        return tuple(bilinear(g*d+d*g,site,site) for g in gamma)
    if link_site==site:
        return tuple(add(bilinear(g*Ud,site,end),scale(bilinear(U*g,end,site),-1)) for g in gamma)
    assert link_site==end
    return tuple(add(bilinear(Ud*g,end,site),scale(bilinear(g*U,site,end),-1)) for g in gamma)


@cache
def partial_pair(first,second,state):
    x,k,l,u,v=first
    y,q,r,z,t=second
    assert (x,k,l)==(y,q,r)
    axes=tuple(d for d in AXES if d not in (k,l))
    ext=dict(state)
    factors=[]
    for d,e,f in zip(axes,(u,v),(z,t),strict=True):
        if e==f:
            assert (e,d) not in ext
            factors.append(frame_pair(x,d,e))
        else:
            A=fixed_frame(x,d,e,ext[e,d])
            B=fixed_frame(x,d,f,ext[f,d])
            factors.append(tuple(tuple(wedge(a,b) for b in B) for a in A))
    A,B=factors
    return add(*(add(wedge(A[a][a],B[b][b]),scale(wedge(A[a][b],B[b][a]),-1))
                 for a,b in product(AXES,repeat=2)))
