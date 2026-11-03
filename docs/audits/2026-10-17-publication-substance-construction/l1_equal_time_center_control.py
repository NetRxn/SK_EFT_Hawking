"""Independent direct quaternion integration of selected center coefficients."""
from fractions import Fraction as F
from itertools import product

from l1_equal_time_coupled import (
    TYPES, UNIT, VEC, AXES, local_frame, local_center, add, scale, wedge,
    nodes, R, L,
)
from l1_direct_a_haar import qproduct,adj


def direct(x,t,a,b):
    i,j=t
    # Only local vector components contribute because the frames annihilate scalars.
    result={}
    for l,r,w in nodes():
        Q=(l,r)
        A=Q[i//4]
        B=Q[j//4]
        for p,q in product(range(1,4),repeat=2):
            f=local_frame(x,i//4,p)
            g=local_frame(x,j//4,q)
            c=qproduct(A,UNIT[i%4],adj(A),adj(UNIT[p]))
            d=qproduct(B,UNIT[j%4],adj(B),adj(UNIT[q]))
            P=add(*(scale(g[e],sum(v*c[k%3+1] for k,v in L[a,e] if k//3==i//4)) for e in AXES))
            Q_=add(*(scale(f[e],sum(v*d[k%3+1] for k,v in L[b,e] if k//3==j//4)) for e in AXES))
            result=add(result,scale(wedge(P,Q_),w))
    return result


for t in ((0,0),(0,4),(1,1),(5,5)):
    C=local_center(1,t)
    a,b=next(idx for idx,poly in C.items() if any(z!=(0,0) for z in poly.values()))
    P=direct(1,t,a,b)
    lhs={m:(F(int(z.const().x),96*2**4*16),F(int(z.const().y),96*2**4*16))
         for m,z in P.items()}
    rhs={m:(F(z[0],48),F(z[1],48)) for m,z in C[a,b].items() if any(z)}
    assert lhs==rhs,(t,(a,b),lhs,rhs)
    print('direct center control',t,(a,b),len(lhs),flush=True)
