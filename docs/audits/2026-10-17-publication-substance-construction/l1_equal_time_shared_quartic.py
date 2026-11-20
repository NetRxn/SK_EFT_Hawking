"""Exact one-shared-quartic action sector."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product

from l1_equal_time_private_pairs import (
    AXES,forward,quat,adj,diag,gamma,bilinear,add,scale,wedge,wedge_sign,
    frame_pair,square,reduce_source_dependence,same_site_quadratic_support,R,TOP,
)
from l1_interacting_support import AXES
from l1_normalization_opposed_fourth import nodes


@cache

def edges_for(word):
    edges = defaultdict(Counter)
    for site, k, l, u, v in word:
        mu, nu = (axis for axis in AXES if axis not in (k, l))
        edges[u, mu][site, k, l] += 1
        edges[v, nu][site, k, l] += 1
    return edges

def fixed_pair(site, axis, link_site, left, right):
    end=forward(site,axis)
    U=diag(quat(left),quat(right)); Ud=diag(quat(adj(left)),quat(adj(right)))
    if site==end:
        d=Ud-U
        T=[bilinear(g*d+d*g,site,site) for g in gamma]
    elif link_site==site:
        T=[add(bilinear(g*Ud,site,end),scale(bilinear(U*g,end,site),-1))
           for g in gamma]
    else:
        assert link_site==end
        T=[add(bilinear(Ud*g,end,site),scale(bilinear(g*U,site,end),-1))
           for g in gamma]
    return tuple(tuple(wedge(a,b) for b in T) for a in T)


@cache
def partial_square(term, shared, left, right):
    site,k,l,u,v=term
    m,n=(axis for axis in AXES if axis not in (k,l))
    A,B=(fixed_pair(site,d,z,left,right) if (z,d)==shared else frame_pair(site,d,z)
         for z,d in ((u,m),(v,n)))
    return add(*(add(wedge(A[a][a],B[b][b]),scale(wedge(A[a][b],B[b][a]),-1))
                 for a,b in product(AXES,repeat=2)))


@cache
def joint(a,b,shared):
    out={}
    for l,r,w in nodes():
        A=partial_square(a,shared,tuple(l),tuple(r))
        B=partial_square(b,shared,tuple(l),tuple(r))
        out=add(out,scale(wedge(A,B),w))
    return out


def contract(A,B):
    raw=R.zero
    for mask,z in A.items():
        complement=TOP^mask
        if complement in B:
            raw+=z*B[complement]*wedge_sign(mask,complement)
    assert raw.is_ground and raw.const().y==0
    return int(raw.const().x)


def main():
    out=Counter()
    for word in same_site_quadratic_support():
        _,h=reduce_source_dependence(word)
        if len(h)<2:
            continue
        edges=edges_for(word)
        active=[(link,cs) for link,cs in edges.items() if len(cs)>1]
        if len(active)!=1 or tuple(sorted(active[0][1].values()))!=(2,2):
            continue
        assert set(Counter(word).values())=={2}
        shared,centers=active[0]
        a,b,c=sorted(Counter(word),key=lambda term:term[:3] not in centers)
        raw=contract(joint(a,b,shared),square(c))
        cov=F(8) if len(h)==3 else F(64,9)
        # nodes() computes 96 times the degree-four mean at doubled quaternion coordinates.
        result=21*F(raw,96*2**4*8**4*4**12*2**3)*cov
        out[result]+=1
    print('one-shared quartic exact outcomes',sorted(out.items()))
    print('words',sum(out.values()),'subtotal',sum(k*v for k,v in out.items()))
    assert sum(out.values())==48

if __name__=='__main__':
    main()
