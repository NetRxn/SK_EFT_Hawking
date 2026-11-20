from collections import defaultdict,Counter
from fractions import Fraction as F
from itertools import product
import numpy as np
from scipy.sparse import coo_matrix
from l1_normalization_uniform_mixed_edge import edge,moment
from l1_normalization_shared_transport import L,local_pair,component_multisets,TERMS
from l1_normalization_transport_cycle import poly_int,signed_mul,wedge_sign

def residual_population():
    cases=Counter()
    for cs in component_multisets():
        ii=[i for c in cs for i in c]
        labels=[TERMS[i][2] for i in ii]
        planes={t[1:3] for t in labels}
        if planes not in ({(0,2),(1,2)},{(0,3),(1,3)}):continue
        if len(set(labels))!=8:continue
        count=Counter((x,k) for x,k,l,u,v in labels)
        if len(count)==8 and set(count.values())=={1}:
            cases[labels[0][2]]+=1
    assert cases=={2:16,3:16}
    return cases

def assemble():
    E=edge()
    entries=[]
    labels=set()
    for (a,b,t,u,x,y),p in E.items():
        for m,(r,i) in poly_int(p).items():
            q=(a,t,x,m&255);w=(b,u,y,m>>8)
            entries.append((q,w,r,i));labels.update((q,w))
    labels=sorted(labels);ids={v:i for i,v in enumerate(labels)}
    groups=defaultdict(list)
    for j,label in enumerate(labels):
        q=label[2]
        groups[(1<<q[0])^(1<<q[1])].append((j,label))
    lookup={}
    for (c,d),ls in L.items():
        for a,v in ls:
            assert (a,c) not in lookup
            lookup[a,c]=(d,v)
    K=[[poly_int(a) for a in row] for row in local_pair(0)]
    vertices=[]
    for i,(a,t,x,m) in enumerate(labels):
        for j,(b,u,y,n) in groups[(1<<x[0])^(1<<x[1])]:
            if m&n:continue
            d,v=lookup[a,u];e,w=lookup[b,t]
            z=K[d][e].get(255^(m|n))
            if not z:continue
            h=moment(*x,*y)
            assert h
            s=v*w*h*wedge_sign(m,n)*wedge_sign(m|n,255^(m|n))
            vertices.append((i,j,s*z[0],s*z[1]))
    dim=len(labels)
    def csr(rows,mode):
        rr=[(ids[a],ids[b],x,y) for a,b,x,y in rows] if mode else rows
        x,y,z,w=map(np.array,zip(*rr))
        shape=(dim,dim)
        out=[coo_matrix((r,(x,y)),shape=shape,dtype=np.int64).tocsr() for r in (z,w)]
        for a in out:a.eliminate_zeros()
        return tuple(out)
    E=csr(entries,True);V=csr(vertices,False)
    assert all((a!=a.T).nnz==0 for a in V)
    print('boundary dimension',dim,'edge nonzeros',tuple(a.nnz for a in E),
          'vertex nonzeros',tuple(a.nnz for a in V),flush=True)
    return E,V

def l1row(a):
    return int(np.max(np.asarray(abs(a).sum(axis=1)),initial=0))

def multiply(A,B):
    x,y=A;z,w=B
    L=l1row(x)+l1row(y);R=l1row(z)+l1row(w)
    assert L*R<2**63,(L,R,L*R)
    p=x@z-y@w;q=x@w+y@z
    p.eliminate_zeros();q.eliminate_zeros()
    print('safe multiply bound',L*R,'nonzero entries',(p.nnz,q.nnz),flush=True)
    return p,q

def inner_transpose(a,b):
    # Both sparse matrices are indexed by the same boundary state;
    # products summed as Python arbitrary-precision integers.
    b=b.T.tocsr();a.sort_indices();b.sort_indices()
    out=0
    for i in range(a.shape[0]):
        p,q=a.indptr[i:i+2];r,s=b.indptr[i:i+2]
        while p<q and r<s:
            x,y=a.indices[p],b.indices[r]
            if x==y:
                out+=int(a.data[p])*int(b.data[r]);p+=1;r+=1
            elif x<y:p+=1
            else:r+=1
    return out

def trace4(T):
    x,y=multiply(T,T)
    return inner_transpose(x,x)-inner_transpose(y,y),2*inner_transpose(x,y)

if __name__=='__main__':
    print('uniform plane census',residual_population(),flush=True)
    E,V=assemble()
    T=multiply(tuple((a+a.T).tocsr() for a in E),V)
    z=trace4(T)
    den=(48*16*128*48)**4
    out=tuple(F(2*k,den) for k in z)
    print('raw signed Gaussian trace',z,'full 32-multiset sector',out,flush=True)
