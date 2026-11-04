"""An exactly integrated repeated-plane g2^32 word on 2^4."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import permutations,product
from math import factorial,prod
from l1_direct_b_haar import R,add,scale,wedge,haar_moment
from l1_normalization_opposed_fourth import L,tuples,fourth_T

@cache
def curvature(pairs):
    total=F(0)
    for term in product(*(L[p] for p in pairs)):
        counts=Counter(i for i,_ in term)
        left=(0,*(counts[i] for i in range(3)))
        right=(0,*(counts[i] for i in range(3,6)))
        total+=haar_moment(left)*haar_moment(right)*prod(v for _,v in term)
    total*=48
    assert total.denominator==1
    return int(total)

def center():
    A,B=fourth_T(0),fourth_T(1)
    out={}
    for a in tuples:
        multiplicity=factorial(4)//prod(factorial(k) for k in Counter(a).values())
        for b in tuples:
            w=sum(curvature(tuple(sorted(zip(a,y)))) for y in set(permutations(b)))
            if w:
                p={m:c for m,c in wedge(A[a],B[b]).items() if m&255==255}
                out=add(out,scale(p,multiplicity*w))
    return out,48*96**2*8**8

def pair_value():
    pol,den=center()
    def shift(mask):
        return sum(((mask>>(8*x))&255)<<(8*(x^3)) for x in range(4))
    opposite={shift(mask):v for mask,v in pol.items()}
    top=(1<<32)-1
    raw=R.zero
    for m,v in pol.items():
        w=top^m
        if w in opposite:
            raw+=wedge({m:v},{w:opposite[w]}).get(top,R.zero)
    assert raw.is_ground and not raw.const().y
    value=F(int(raw.const().x),den**2*factorial(4)**2)
    return len(pol),value

def geometry():
    # x0,x1 are curvature axes; x2,x3 are frames.
    active=[x for x in range(16) if x.bit_count()%2==0]
    degree=Counter()
    used=set()
    for x in active:
        ports={(x,0),(x^1,1),(x^2,0),(x,1),(x,2),(x,3)}
        assert not used&ports
        used.update(ports)
        degree[x]+=8
        degree[x^4]+=4
        degree[x^8]+=4
    assert degree==Counter({x:8 for x in range(16)})
    return active

if __name__=='__main__':
    print('active sites',geometry(),flush=True)
    n,value=pair_value()
    print('one center support',n,'opposed pair coefficient',value,flush=True)
    print('full 2^4 word coefficient including factorials',value**4)
    assert value
