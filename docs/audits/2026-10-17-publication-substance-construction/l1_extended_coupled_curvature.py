"""Exact anchor-summed repeated-plane subnetwork with two coupled plaquette sheets."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import permutations,product
from math import factorial,prod
from time import perf_counter
from l1_extended_split_layer import full_fourth,tuples,clean
from l1_normalization_opposed_fourth import L
from l1_direct_b_haar import R,add,scale,wedge

@cache
def angular(exponents):
    if any(n%2 for n in exponents):return F(0)
    numerator=prod(prod(range(1,n,2)) for n in exponents)
    denominator=prod(range(3,3+sum(exponents),2))
    return F(numerator,denominator)

@cache
def curvature_channels(pairs):
    out=[F(0)]*3
    for terms in product(*(L[p] for p in pairs)):
        q=Counter(i for i,_ in terms)
        left=tuple(q[i] for i in range(3))
        right=tuple(q[i] for i in range(3,6))
        left_power=sum(left)
        if left_power%2:continue
        out[left_power//2]+=angular(left)*angular(right)*prod(v for _,v in terms)
    scaled=tuple(45*x for x in out)
    assert all(x.denominator==1 for x in scaled)
    return tuple(map(int,scaled))

def center():
    A,B=(full_fourth(d,True) for d in (0,1))
    out=[{} for _ in range(3)]
    for a in tuples:
        mult=factorial(4)//prod(factorial(n) for n in Counter(a).values())
        for b in tuples:
            weights=[0]*3
            for p in set(permutations(b)):
                for i,w in enumerate(curvature_channels(tuple(sorted(zip(a,p))))):
                    weights[i]+=w
            if not any(weights):continue
            term={m:v for m,v in wedge(A[a],B[b]).items() if m&255==255}
            for i,w in enumerate(weights):
                if w:out[i]=add(out[i],scale(term,w*mult))
    return [clean(p) for p in out]

def frame_pair(left,right):
    den=45*(96*8**4)**2*factorial(4)
    top=(1<<32)-1
    opposite={}
    for mask,val in right.items():
        moved=sum(((mask>>(8*x))&255)<<(8*(x^3)) for x in range(4))
        opposite[moved]=val
    raw=R.zero
    matches=0
    for mask,val in left.items():
        m=top^mask
        if m in opposite:
            raw+=wedge({mask:val},{m:opposite[m]}).get(top,R.zero)
            matches+=1
    assert raw.is_ground and raw.const().y==0
    return F(int(raw.const().x),den**2),matches

# For SU(2) p=|vec(q)|²=(3−χ₁)/4. Square uses χ₁²=χ₀+χ₁+χ₂.
CHAR=((F(1),F(0),F(0)),(F(3,4),F(-1,4),F(0)),
      (F(10,16),F(-5,16),F(1,16)))

@cache
def sheet(powers):
    # Opposite orientations of every common edge force all four character
    # representations equal. Four vertices and eight edges give d_j^-4.
    return sum(prod(CHAR[p][j] for p in powers)/((2*j+1)**4) for j in range(3))

def check_geometry():
    # Two full longitudinal sheets, at transverse positions (0,0) and (1,1).
    all_sites=tuple(range(16))
    active=[x for x in all_sites if (x>>2) in (0,3)]
    degree=Counter()
    ports=Counter()
    for x in active:
        degree[x]+=8
        degree[x^4]+=4
        degree[x^8]+=4
        ports.update(((x,0),(x^1,1),(x^2,0),(x,1)))
    assert len(ports)==16 and set(ports.values())=={2}
    assert degree==Counter({x:8 for x in all_sites})

if __name__=='__main__':
    start=perf_counter()
    check_geometry()
    C=center()
    K=[[frame_pair(a,b) for b in C] for a in C]
    print('center channel supports',list(map(len,C)))
    print('frame pair complement matches',[[n for _,n in row] for row in K])
    print('frame pair channel matrix',[[q for q,_ in row] for row in K])
    control=sum(K[a][b][0]*CHAR[a][0]*CHAR[2-a][0]*CHAR[b][0]*CHAR[2-b][0]
                for a,b in product(range(3),repeat=2))
    assert control==F(9995625,131072)
    print('independent Haar control',control)
    assignments=tuple(product(range(3),repeat=4))
    sheets={p:sheet(p)*sheet(tuple(2-k for k in p)) for p in assignments}
    value=F(0)
    used=0
    for p,q in product(assignments,repeat=2):
        f=prod(K[a][b][0] for a,b in zip(p,q,strict=True))
        if f:
            used+=1
            value+=f*sheets[p]*sheets[q]
    pair_scale, vector = F(15993, 2048), (F(1), F(10, 3), F(1))
    assert all(K[a][b][0] == pair_scale * vector[a] * vector[b]
               for a, b in product(range(3), repeat=2))
    reduced_sheet = sum(
        weight * prod(vector[channel] for channel in channels)
        for channels, weight in sheets.items()
    )
    assert value == pair_scale**4 * reduced_sheet**2
    print('rank-one sheet contraction', reduced_sheet)
    print('nonzero sheet boundaries',sum(bool(v) for v in sheets.values()),'of',len(sheets))
    print('nonzero pair joins',used,'of',len(sheets)**2)
    print('coupled curvature subnetwork exact',value,'seconds',perf_counter()-start)
    print('difference from independent-sheet control',value-control**4)
    assert value and value!=control**4
