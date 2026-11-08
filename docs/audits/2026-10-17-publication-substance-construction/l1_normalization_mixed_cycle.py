from collections import Counter,defaultdict
from functools import cache
from itertools import product
from fractions import Fraction as F
from math import prod
import numpy as np
from scipy.sparse import coo_matrix
from l1_normalization_uniform_mixed_edge import projection,tt,unit
from l1_normalization_uniform_mixed_trace import multiply,inner_transpose
from l1_normalization_shared_transport import (
    TERMS,component_multisets,L,quat,adj,R,diag,gamma,bilinear,wedge,
)
from l1_direct_b_haar import haar_moment
from l1_normalization_transport_cycle import poly_int,wedge_sign

CYCLE=(0,1,3,2)
PAIR_TYPES=tuple(product((2,3),repeat=2))

def canonical(assignment):
    ans=[]
    for dx,ds,dq in product(range(4),(False,True),(False,True)):
        def move(x):return dx ^ ((((x&1)<<1)|((x&2)>>1)) if ds else x)
        arr=[[None,None] for _ in range(4)]
        for x,k in product(range(4),range(2)):
            a=assignment[x][k]
            arr[move(x)][k^ds]=(5-a) if dq else a
        ans.append(tuple(map(tuple,arr)))
    return min(ans)

def cases():
    n=Counter()
    for cs in component_multisets():
        ii=[i for c in cs for i in c]
        rows={}
        for i in ii:
            x,k,l,u,v=TERMS[i][2]
            if k>=2 or l<2 or (x,k) in rows:break
            rows[x,k]=l
        else:
            assert len(rows)==8
            n[tuple(tuple(rows[x,k] for k in (0,1)) for x in range(4))]+=1
    assert len(n)==16 and set(n.values())=={16}
    ans=Counter(canonical(x) for x in n)
    return ans

def plus(row,k,r,i):
    if not(r or i):return
    a,b=row.get(k,(0,0))
    row[k]=(a+r,b+i)

@cache
def trace_to_local():
    out={}
    for (c,d),ls in L.items():
        for a,v in ls:
            assert (a,c) not in out
            out[a,c]=(d,v)
    return out

@cache
def owned_edge(lx,ly):
    out={}
    for a in range(6):
        ch=a//3
        for x,y in product(range(4*ch,4*ch+4),repeat=2):
            terms=[(i,j,w) for i,j in product(range(8),repeat=2)
                   if (w:=projection(a,x,y,i,j))]
            if not terms:continue
            for b,t,u in product(range(6),range(4),range(4)):
                cb,v=divmod(b,3)
                q=tuple(sorted(((lx,x),(ly,4*cb))))
                z=tuple(sorted(((lx,y),(ly,4*cb+v+1))))
                for i,j,w in terms:
                    for mask,(r,s) in cached_tt(i,j,t,u).items():
                        A=(a,t,q,mask&255);B=(b,u,z,mask>>8)
                        plus(out,(A,B),-w*r,-w*s)
    return {k:v for k,v in out.items() if any(v)}

@cache
def cached_tt(i,j,t,u):
    return poly_int(tt(i,j,t,u))

def parity(word):
    out=[0,0]
    for d,q in word:out[d-2]^=1<<q
    return tuple(out)

@cache
def local_t(i):
    l=unit(i) if i<4 else (0,)*4
    r=unit(i-4) if i>=4 else (0,)*4
    U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
    X=Ud-U
    return [bilinear(g*X+X*g,0,0) for g in gamma]

@cache
def local_product(i,j,d,e):
    return poly_int(wedge(local_t(i)[d],local_t(j)[e]))

@cache
def singleton_moment(word):
    n=Counter(word)
    value=F(1)
    for d in (2,3):
        ex=tuple(n[d,i] for i in range(8))
        value*=haar_moment(ex[:4])*haar_moment(ex[4:])
    value*=192
    assert value.denominator==1
    return int(value)

def vertex(labels,groups,lin,lout):
    u,v=5-lin,5-lout
    lookup=trace_to_local()
    offsets=defaultdict(list)
    for i,j in product(range(8),repeat=2):
        off=parity(((u,i),(v,j)))
        offsets[off].append((i,j))
    out={}
    for A in labels:
        a,t,x,m=A
        q0,q1=parity(x)
        for (r0,r1),ijs in offsets.items():
            for B in groups.get((q0^r0,q1^r1),()):
                if (B[3]&m):continue
                b,w,y,n=B
                d,sign0=lookup[a,w];e,sign1=lookup[b,t]
                rest=255^(m|n)
                sign=sign0*sign1*wedge_sign(m,n)*wedge_sign(m|n,rest)
                sr=si=0
                for i,j in ijs:
                    z=local_product(i,j,d,e).get(rest)
                    if z is None:continue
                    weight=singleton_moment(tuple(sorted(x+y+((u,i),(v,j)))))
                    sr+=z[0]*weight;si+=z[1]*weight
                if sr or si:plus(out,(A,B),sign*sr,sign*si)
    return out

def assemble():
    es={}
    labels=set()
    for x,y in PAIR_TYPES:
        out=dict(owned_edge(x,y))
        for (B,A),(r,i) in owned_edge(y,x).items():plus(out,(A,B),r,i)
        out={k:v for k,v in out.items() if any(v)}
        es[x,y]=out
        labels.update(z for k in out for z in k)
    labels=sorted(labels)
    ids={a:i for i,a in enumerate(labels)}
    groups=defaultdict(list)
    for a in labels:groups[parity(a[2])].append(a)
    def csr(rows):
        rr=[(ids[a],ids[b],r,s) for (a,b),(r,s) in rows.items()]
        i,j,r,s=map(np.array,zip(*rr))
        out=tuple(coo_matrix((x,(i,j)),shape=(len(labels),len(labels)),dtype=np.int64).tocsr() for x in (r,s))
        for x in out:x.eliminate_zeros()
        return out
    print('general boundary dimension',len(labels),flush=True)
    E={k:csr(e) for k,e in es.items()}
    V={}
    for k in PAIR_TYPES:
        if k[::-1] in V:
            V[k]=tuple(v.T.tocsr() for v in V[k[::-1]])
        else:
            V[k]=csr(vertex(labels,groups,*k))
        print('case',k,'E nonzeros',tuple(a.nnz for a in E[k]),'V nonzeros',tuple(a.nnz for a in V[k]),flush=True)
    return E,V

def dot(A,B):
    ar,ai=A;br,bi=B
    return (inner_transpose(ar,br)-inner_transpose(ai,bi),
            inner_transpose(ar,bi)+inner_transpose(ai,br))

def run():
    pops=cases()
    print('orientation-summed plane classes',pops,flush=True)
    E,V=assemble()
    @cache
    def step(a,b,c):
        return multiply(E[a,b],V[b,c])
    @cache
    def two(x,y):
        return multiply(step(*x),step(*y))
    total=[0,0]
    den=(48*16*16*192)**4
    for pl,n in sorted(pops.items()):
        args=[]
        for i,x in enumerate(CYCLE):
            y=CYCLE[(i+1)%4]
            k=0 if x^y==1 else 1
            args.append((pl[x][k],pl[y][k],pl[y][1-k]))
        z=dot(two(*args[:2]),two(*args[2:]))
        for t,v in enumerate(z):total[t]+=n*v
        print('plane class',pl,'assignments',n,'coefficient per 16 orientations',tuple(F(v,den) for v in z),flush=True)
    print('full 256 mixed-plane cycle sector',tuple(F(v,den) for v in total),flush=True)
if __name__=='__main__':run()
