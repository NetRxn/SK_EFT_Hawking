"""Factor both two-link second-moment branches before joining."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import factorial,prod

from l1_equal_time_shared_quartic import AXES,add,wedge,contract,edges_for,same_site_quadratic_support,reduce_source_dependence
from l1_equal_time_shared_quadratic import fixed_frame,partial_pair


@cache
def branch(mid_x,axis,mid_link1,mid_link2,outer):
    out={(a,b):{} for a,b in product(AXES,repeat=2)}
    for i,j in product(range(8),repeat=2):
        state=tuple(sorted((((mid_link1,axis),i),((mid_link2,axis),j))))
        C=partial_pair(*outer,state)
        A=fixed_frame(mid_x,axis,mid_link1,i)
        B=fixed_frame(mid_x,axis,mid_link2,j)
        for a,b in out:
            out[a,b]=add(out[a,b],wedge(wedge(A[a],B[b]),C))
    return out


def run():
    outcomes=Counter()
    for word in same_site_quadratic_support():
        _,h=reduce_source_dependence(word)
        if len(h)!=2:continue
        edges=edges_for(word)
        active={link:owners for link,owners in edges.items() if len(owners)>1}
        if len(active)!=4 or any(tuple(sorted(v.values()))!=(1,1) for v in active.values()):
            continue
        groups=defaultdict(list)
        for term in word:groups[term[:3]].append(term)
        center=next(p for p in groups if all(p in o for o in active.values()))
        first,second=groups[center]
        x,k,l,u,v=first
        _,_,_,z,t=second
        m,n=(axis for axis in AXES if axis not in (k,l))
        Akey,=set(active[u,m])-{center}
        Bkey,=set(active[v,n])-{center}
        assert Akey in active[z,m] and Bkey in active[t,n]
        A=branch(x,m,u,z,tuple(groups[Akey]))
        B=branch(x,n,v,t,tuple(groups[Bkey]))
        raw=sum(contract(A[a,a],B[b,b])-contract(A[a,b],B[b,a])
                for a,b in product(AXES,repeat=2))
        denom=4**4*8**2*4**12*prod(factorial(n) for n in Counter(word).values())
        value=21*F(64,9)*F(raw,denom)
        print('word',word,'value',value,flush=True)
        outcomes[value]+=1
    assert sum(outcomes.values())==8
    print('four quadratic subtotal',sum(k*v for k,v in outcomes.items()),sorted(outcomes.items()),flush=True)


if __name__=='__main__':run()
