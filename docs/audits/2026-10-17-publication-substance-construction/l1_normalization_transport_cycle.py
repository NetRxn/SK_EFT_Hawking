"""Exact all-transverse-curvature normalization via site elimination."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import factorial,prod
from l1_normalization_shared_transport import (
    TERMS,component_multisets,pair,cross_pair,R,wedge,scale,translate,
)
from l1_normalization_six_transport import shared_moment
from l1_reduced_wedge_reference import wedge_sign

ORDERED=tuple(product(range(4),repeat=2))
EDGES=((0,1),(0,2),(1,3),(2,3))
DIM=96*8**4
M={((a,e),(b,f)):int(a==e and b==f)-int(a==f and b==e)
   for (a,e),(b,f) in product(ORDERED,repeat=2)}
M={k:v for k,v in M.items() if v}
assert len(M)==24

def signed_mul(a,b,s):
    return s*(a[0]*b[0]-a[1]*b[1]),s*(a[0]*b[1]+a[1]*b[0])

def poly_int(p):
    assert all(c.is_ground for c in p.values())
    return {m:(int(c.const().x),int(c.const().y)) for m,c in p.items()
            if c.const()!=R.domain.zero}

@cache
def edge_base(kind):
    if kind==1:
        H=shared_moment(0,0)
        return {(p,q):H[tuple(sorted(p)),tuple(sorted(q))]
                for p,q in product(ORDERED,repeat=2)}
    if kind==0:
        K,L=pair(0,0),pair(1,0)
        return {(p,q):scale(wedge(K[p[0]][p[1]],L[q[0]][q[1]]),24)
                for p,q in product(ORDERED,repeat=2)}
    C=cross_pair(0,0)
    flip=kind==3
    return {(p,q):scale(wedge(C[p[0]][q[int(flip)]],C[p[1]][q[1-int(flip)]]),24)
            for p,q in product(ORDERED,repeat=2)}

@cache
def edge(kind,x,y):
    axis=0 if x^y==1 else 1
    def move(z):
        return x ^ ((((z&1)<<1)|((z&2)>>1)) if axis else z)
    return {key:poly_int(translate(p,move)) for key,p in edge_base(kind).items()}

@cache
def half(left,right,mid):
    x=0
    p=edge(left,x,mid);q=edge(right,mid,3)
    mark=255<<(8*mid)
    # Right mask buckets indexed by gamma and intermediate occupancy.
    Q={}
    for key,poly in q.items():
        row=defaultdict(list)
        for word,val in poly.items():row[word&mark].append((word,val))
        Q[key]=row
    out=defaultdict(dict)
    joins=0
    for (u,v),w in M.items():
        for a,b in product(ORDERED,repeat=2):
            target=out[a,b]
            bucket=Q[v,b]
            for word,c in p[a,u].items():
                for mask,d in bucket.get((word&mark)^mark,()):
                    joins+=1
                    k=(word|mask)^mark
                    real,imag=signed_mul(c,d,w*wedge_sign(word,mask))
                    prev=target.get(k,(0,0))
                    target[k]=(prev[0]+real,prev[1]+imag)
    out={k:{m:c for m,c in p.items() if any(c)} for k,p in out.items()}
    return out,joins,sum(map(len,out.values()))

@cache
def cycle(kinds):
    A,ja,na=half(kinds[0],kinds[2],1)
    B,jb,nb=half(kinds[1],kinds[3],2)
    target=255|(255<<24)
    real=imag=joins=0
    for ((a,c),u),((d,b),v) in product(M.items(),repeat=2):
        p,q=A[a,b],B[c,d]
        for m,aa in p.items():
            n=m^target
            if n not in q:continue
            joins+=1
            x,y=signed_mul(aa,q[n],u*v*wedge_sign(m,n))
            real+=x;imag+=y
    denom=9**4*DIM**4
    return F(real*16**4,denom),F(imag*16**4,denom),(ja,jb,na,nb,joins)

def pattern(ii):
    rows=defaultdict(list)
    for i in ii:
        x,k,l,u,v=TERMS[i][2]
        if (k,l)!=(2,3):return None
        rows[x].append((u,v))
    if any(len(rows[x])!=2 for x in range(4)):return None
    kinds=[]
    parity=0
    for x,y in EDGES:
        axis=0 if x^y==1 else 1
        a,b=(v[axis] for v in rows[x]);c,d=(v[axis] for v in rows[y])
        if a==b:
            assert c==d
            kinds.append(int(a==c))
        else:
            assert c!=d
            kinds.append(2)
            parity^=a!=c
    if all(k==2 for k in kinds) and parity:kinds[0]=3
    return tuple(kinds)

def canonical(kinds):
    if max(kinds)==3:return kinds
    m=[]
    for s,t in product(range(4),(False,True)):
        def move(x):
            return s ^ ((((x&1)<<1)|((x&2)>>1)) if t else x)
        p=[None]*4
        for e,k in zip(EDGES,kinds):p[EDGES.index(tuple(sorted(map(move,e))))]=k
        m.append(tuple(p))
    return min(m)

def main():
    census=Counter()
    for comps in component_multisets():
        ii=[i for c in comps for i in c]
        kinds=pattern(ii)
        if kinds is None:continue
        wt=prod(factorial(n) for n in Counter(ii).values())
        census[tuple(sorted(map(len,comps))),canonical(kinds),wt]+=1
    totals=Counter();pop=Counter()
    for (shape,k,wt),n in sorted(census.items()):
        a,b,sz=cycle(k)
        assert b==0
        pop[shape]+=n
        totals[shape]+=a*n/wt
        print('shape',shape,'pattern',k,'factorial',wt,'count',n,'coefficient',a/wt,'joins & supports',sz,flush=True)
    print('coverage',pop,'sums',totals,'entire cycle sector',sum(totals.values()),flush=True)
if __name__=='__main__':main()
