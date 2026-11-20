from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import factorial,prod

from l1_equal_time_structural import (
    AXES,forward,same_site_quadratic_support,private_groups,reduce_source_dependence,
)
from l1_normalization_disjoint_sector import quat,adj
from l1_direct_b_haar import R,diag,gamma,bilinear,add,scale,wedge,wedge_sign


@cache
def frame_pair(site, axis, link_site):
    end=forward(site,axis)
    entries=[[{} for _ in AXES] for _ in AXES]
    for i, sign in product(AXES,(-1,1)):
        left=[int(j==i) for j in AXES]
        right=[sign*v for v in left]
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
        for a,b in product(AXES,repeat=2):
            entries[a][b]=add(entries[a][b],wedge(T[a],T[b]))
    return entries


@cache
def square(term):
    site,k,l,u,v=term
    m,n=(axis for axis in AXES if axis not in (k,l))
    A,B=frame_pair(site,m,u),frame_pair(site,n,v)
    return add(*(add(wedge(A[a][a],B[b][b]),scale(wedge(A[a][b],B[b][a]),-1))
                 for a,b in product(AXES,repeat=2)))


TOP=(1<<32)-256
counts=Counter()
total=F(0)
for word in same_site_quadratic_support():
    _,h=reduce_source_dependence(word)
    if len(h)<2 or not private_groups(word):
        continue
    multiplicities=Counter(word)
    assert len(multiplicities)==3 and set(multiplicities.values())=={2}
    a,b,c=map(square,multiplicities)
    ab=wedge(a,b)
    raw=R.zero
    for mask,z in ab.items():
        complement=TOP^mask
        if complement in c:
            raw += z*c[complement]*wedge_sign(mask,complement)
    assert raw.is_ground and raw.const().y==0
    removed=set(h)
    cov=prod(F(2) if t[:3] in removed else F(16,9) for t in multiplicities)
    result=21*F(int(raw.const().x),8**6*4**12*2**3)*cov
    total+=result
    counts[result]+=1
print("private quadratic exact results",sorted(counts.items()),"total",total)
assert sum(counts.values())==33
assert counts[122472]==1
