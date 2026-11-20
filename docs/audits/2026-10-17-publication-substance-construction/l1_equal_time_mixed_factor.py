"""Factor shared quadratic branch before the quartic integration."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from itertools import product
from math import factorial,prod

from l1_equal_time_shared_quartic import (
    AXES,add,wedge,partial_square,fixed_pair,nodes,contract,
    edges_for,same_site_quadratic_support,reduce_source_dependence,
)
from l1_equal_time_four_quadratic_factor import branch
from l1_equal_time_int_contract import sparse_int,triple


def transform(term,space_time,transverse):
    x,k,l,u,v=term
    perm=[0,1,2,3]
    if space_time:perm[:2]=[1,0]
    if transverse:perm[2:]=[3,2]
    def site(a):
        return (((a&1)<<1)|((a&2)>>1)) if space_time else a
    m,n=(d for d in AXES if d not in (k,l))
    u,v=sorted(((perm[m],site(u)),(perm[n],site(v))))
    return (site(x),*sorted((perm[k],perm[l])),u[1],v[1])




def solve(word,quartic,quadratic,owners):
    groups=defaultdict(list)
    for term in word:groups[term[:3]].append(term)
    same=next(g for g in groups.values() if g[0]==g[1])
    center,=set(owners[quartic])-{same[0][:3]}
    middle=groups[center]
    outer=next(g for g in groups.values() if g not in [same,middle])
    x,k,l,u,v=middle[0]
    _,_,_,z,t=middle[1]
    m,n=(axis for axis in AXES if axis not in (k,l))
    if (u,m)==quartic:
        assert u==z and set(quadratic)=={(v,n),(t,n)}
        Q=branch(x,n,v,t,tuple(outer))
    else:
        assert v==t and (v,n)==quartic and set(quadratic)=={(u,m),(z,m)}
        Q=branch(x,m,u,z,tuple(outer))
    Q={idx:sparse_int(poly) for idx,poly in Q.items()}
    raw=0
    for l,r,w in nodes():
        l,r=tuple(l),tuple(r)
        A=sparse_int(partial_square(same[0],quartic,l,r))
        B=fixed_pair(x,quartic[1],quartic[0],l,r)
        B=[[sparse_int(poly) for poly in row] for row in B]
        raw+=w*sum(triple(A,B[a][a],Q[b,b])-triple(A,B[a][b],Q[b,a])
                   for a,b in product(AXES,repeat=2))
    denom=96*2**4*4**2*8**2*4**12*prod(factorial(n) for n in Counter(word).values())
    return 21*F(64,9)*F(raw,denom)


def run():
    words=set()
    for word in same_site_quadratic_support():
        _,h=reduce_source_dependence(word)
        if len(h)!=2:continue
        edges=edges_for(word)
        tags=sorted(tuple(sorted(sites.values())) for sites in edges.values() if len(sites)>1)
        if tags==[(1,1),(1,1),(2,2)]:words.add(tuple(sorted(word)))
    assert len(words)==16
    result=Counter()
    while words:
        w=min(words)
        orbit={tuple(sorted(transform(t,s,u) for t in w)) for s,u in product((False,True),repeat=2)}
        assert orbit<=words
        words-=orbit
        edges=edges_for(w)
        quartic,=(link for link,sites in edges.items() if len(sites)>1 and sum(sites.values())==4)
        quadratic=tuple(sorted(link for link,sites in edges.items() if len(sites)>1 and sum(sites.values())==2))
        v=solve(w,quartic,quadratic,edges)
        print('representative',len(orbit),v,flush=True)
        result[v]+=len(orbit)
    print('mixed shared result',sorted(result.items()),'subtotal',sum(k*v for k,v in result.items()))

if __name__=='__main__':run()
