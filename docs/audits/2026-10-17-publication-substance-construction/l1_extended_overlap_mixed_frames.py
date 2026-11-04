"""Exact complete frame attachment at either surviving shared A/B link."""
from collections import Counter,defaultdict
from functools import cache
from itertools import combinations_with_replacement, product
from time import perf_counter
from sympy import I,QQ
from sympy.polys.matrices import DomainMatrix
from l1_equal_time_shared_quadratic_pair import fixed_frame
from l1_equal_time_int_contract import sparse_int
from l1_normalization_opposed_fourth import L
from l1_normalization_uniform_mixed_edge import moment
from l1_direct_b_haar import add,scale,wedge
from l1_reduced_wedge_reference import wedge_sign

Q=range(8)
PAIR=tuple(combinations_with_replacement(Q,2))

@cache
def vertex(endpoint,coord,alpha):
    # Local axes 0,1 correspond to global 1,3. Lower anchor for T1,
    # and own base fixed to identity for T3.
    frame=fixed_frame(endpoint,0,0,coord)
    fixed=tuple(add(l,r) for l,r in zip(fixed_frame(endpoint,1,endpoint,0),
                                      fixed_frame(endpoint,1,endpoint,4),strict=True))
    out={}
    for (g,h),terms in L.items():
        for a,v in terms:
            if a==alpha:out=add(out,scale(wedge(frame[g],fixed[h]),-v))
    return sparse_int(out)

def coefficients():
    poly=defaultdict(Counter)
    for i,j,a,b in product(Q,Q,range(6),range(6)):
        p=tuple(sorted((i,j)))
        for m,(r,s) in vertex(0,i,a).items():
            for n,(u,v) in vertex(1,j,b).items():
                if m&n:continue
                sign=wedge_sign(m,n)
                poly[p][a,b,m|n,0]+=sign*(r*u-s*v)
                poly[p][a,b,m|n,1]+=sign*(r*v+s*u)
    return {p:{key:v for key,v in row.items() if v} for p,row in poly.items()}

def projected():
    frame=coefficients()
    out={}
    for p in PAIR:
        row=Counter()
        for q,values in frame.items():
            weight=moment(*p,*q)
            if weight:
                for k,v in values.items():row[k]+=weight*v
        out[p]={k:v for k,v in row.items() if v}
    return frame,out

def rank(rows):
    keys=sorted({k[:3] for row in rows.values() for k in row})
    # Rank over Q(i), preserving the Gaussian coefficient structure.
    from sympy import QQ_I
    ci={key:i for i,key in enumerate(keys)}
    data={}
    for i,row in enumerate(rows.values()):
        vals={}
        for (*k,phase),v in row.items():
            j=ci[tuple(k)]
            vals[j]=vals.get(j,QQ_I.zero)+QQ_I(v)*(QQ_I.imag_unit if phase else QQ_I.one)
        data[i]={j:v for j,v in vals.items() if v}
    return len(keys),DomainMatrix(data,(len(data),len(keys)),QQ_I).rank()

if __name__=='__main__':
    import sys
    start=perf_counter()
    frame,rows=projected()
    for mode,data in [('unprojected',frame),('projected',rows)]:
        nnz=sum(len({k[:3] for k in row}) for row in data.values())
        print(mode,'rows',len(data),'nnz',nnz,'boundary/rank',rank(data),file=sys.stderr,flush=True)
    for (i,j),row in sorted(rows.items()):
        for a,b,m in sorted({key[:3] for key in row}):
            assert all(((m>>sh)&255).bit_count()==d for sh,d in ((0,3),(8,3),(16,1),(24,1)))
            print(i,j,a,b,m,row.get((a,b,m,0),0),row.get((a,b,m,1),0))
    print('max component',max(abs(v) for row in rows.values() for v in row.values()),
          'seconds',perf_counter()-start,file=sys.stderr)
