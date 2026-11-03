"""Exact two-shared-quartic chain for the equal-time plus numerator."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import combinations_with_replacement,product

from l1_equal_time_shared_quartic import (
    AXES,add,scale,wedge,frame_pair,fixed_pair,nodes,contract,TOP,
    edges_for,same_site_quadratic_support,reduce_source_dependence,
)

pairs=tuple(combinations_with_replacement(AXES,2))
weights={(p,q):int(p[0]==p[1] and q[0]==q[1])-int(p==q)*(1 if p[0]==p[1] else 2)
         for p,q in product(pairs,repeat=2)}
weights={key:v for key,v in weights.items() if v}
assert len(weights)==18


@cache
def outer_moment(middle,outer,link):
    link_site,axis=link
    x,k,l,u,v=outer
    m,n=(d for d in AXES if d not in (k,l))
    private=next((z,d) for z,d in ((u,m),(v,n)) if (z,d)!=link)
    K=frame_pair(x,private[1],private[0])
    result={p:{} for p in pairs}
    for left,right,w in nodes():
        A=fixed_pair(middle[0],axis,link_site,tuple(left),tuple(right))
        B=fixed_pair(x,axis,link_site,tuple(left),tuple(right))
        outer_response={q:add(*(scale(wedge(B[q[0]][q[1]],K[r[0]][r[1]]),v)
                                for (p,r),v in weights.items() if p==q))
                        for q in pairs}
        for p in pairs:
            result[p]=add(result[p],scale(wedge(A[p[0]][p[1]],add(*outer_response.values())),w))
    return result


def main():
    outcomes=Counter()
    for word in same_site_quadratic_support():
        _,history=reduce_source_dependence(word)
        if len(history)!=2:
            continue
        edges=edges_for(word)
        links=[(link,set(owners)) for link,owners in edges.items() if len(owners)>1]
        if len(links)!=2 or any(tuple(sorted(edges[link].values()))!=(2,2) for link,_ in links):
            continue
        terms={term[:3]:term for term in Counter(word)}
        assert set(Counter(word).values())=={2}
        (first,owners1),(second,owners2)=links
        middle=terms[next(iter(owners1 & owners2))]
        outer1=terms[next(iter(owners1-owners2))]
        outer2=terms[next(iter(owners2-owners1))]
        A=outer_moment(middle,outer1,first)
        B=outer_moment(middle,outer2,second)
        raw=sum(w*contract(A[p],B[q]) for (p,q),w in weights.items())
        value=F(21*64,9)*F(raw,96**2*2**8*8**2*4**12*2**3)
        outcomes[value]+=1
    print('double-shared quartic outcomes',sorted(outcomes.items()))
    assert sum(outcomes.values())==16
    print('subtotal',sum(k*v for k,v in outcomes.items()))


if __name__=='__main__':
    main()
