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

from l1_equal_time_int_contract import sparse_int,triple

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
    return sparse_int(add(*(add(wedge(A[a][a],B[b][b]),scale(wedge(A[a][b],B[b][a]),-1))
                 for a,b in product(AXES,repeat=2))))


def run():
    sums=Counter()
    for word in same_site_quadratic_support():
        _,history=reduce_source_dependence(word)
        if len(history)<2:
            continue
        edges=edges_for(word)
        active=tuple(sorted(link for link,sites in edges.items() if len(sites)>1))
        if len(active)!=2 or any(tuple(sorted(edges[link].values()))!=(1,1) for link in active):
            continue
        groups=defaultdict(list)
        for term in word:
            groups[term[:3]].append(term)
        assert len(groups)==3 and all(len(g)==2 for g in groups.values())
        groups=sorted(groups.items(),key=lambda item:sum(item[0] in edges[link] for link in active))
        raw=0
        for indices in product(range(8),repeat=len(active)):
            state=dict(zip(active,indices,strict=True))
            A,B,C=(partial_pair(*g,tuple((link,state[link]) for link in active if p in edges[link]))
                   for p,g in groups)
            raw+=triple(A,B,C)
        cov=F(8) if len(history)==3 else F(64,9)
        # Each shared second moment is I/4. Every remaining private frame pair
        # uses the 8-node covariance; action frames always carry 4^-12.
        denom=4**len(active)*8**(6-len(active))*4**12
        denom*=prod(factorial(n) for n in Counter(word).values())
        value=21*F(raw,denom)*cov
        sums[(len(history),len(active),value)]+=1
    print('shared quadratic outcomes',sorted(sums.items()))
    assert sum(sums.values())==24
    print('subtotal',sum(k[2]*v for k,v in sums.items()))


if __name__=='__main__':
    run()
