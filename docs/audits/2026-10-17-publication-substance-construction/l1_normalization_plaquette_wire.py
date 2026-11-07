from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import prod
from time import perf_counter
import numpy as np
from scipy.sparse import coo_matrix
from l1_normalization_shared_transport import R,quat,adj,diag,gamma,bilinear,add,scale,wedge,L
from l1_normalization_transport_cycle import poly_int,signed_mul,wedge_sign
from l1_normalization_uniform_mixed_edge import unit,projection
from l1_normalization_uniform_mixed_trace import multiply,inner_transpose
from l1_normalization_mixed_cycle import local_product,plus,trace_to_local
from l1_residual_source_contract import curv
from l1_direct_b_haar import haar_moment
from sympy import diag as symdiag

EDGE_SPECS=((1,1,0,False),(0,0,1,True),(0,1,0,False),(1,0,1,True))
# (wire of mixed-owned link, dagger for mixed, dagger for source,
#  directed edge starts at mixed). Source-owned wire is the other wire.
EDGE_AXES=(0,1,0,1)
G5=symdiag(1,1,-1,-1)

@cache
def qbasis(q,dag):
    p=unit(q%4)
    return quat(adj(p) if dag else p)

@cache
def blocks(q):
    l=unit(q) if q<4 else (0,)*4
    r=unit(q-4) if q>=4 else (0,)*4
    return diag(quat(l),quat(r)),diag(quat(adj(l)),quat(adj(r)))

@cache
def tbase(owner,at,q,gamma_index):
    other=1-owner
    U,Ud=blocks(q)
    g=gamma[gamma_index]
    if owner==at:
        return add(bilinear(g*Ud,owner,other),scale(bilinear(U*g,other,owner),-1))
    return add(bilinear(Ud*g,owner,other),scale(bilinear(g*U,other,owner),-1))

@cache
def two_transport(mixed_coord,source_coord,t,u,at_source):
    us=0 if at_source else 1
    p=wedge(tbase(1,1,mixed_coord,t),tbase(0,us,source_coord,u))
    q=wedge(tbase(0,1,source_coord,t),tbase(1,us,mixed_coord,u))
    return poly_int(add(p,q))

def gaussian(z):
    r,i=z.expand().as_real_imag()
    return int(r),int(i)

@cache
def e_wire(a,b,w,dm,ds):
    mats=[None,None]
    mats[w]=qbasis(a,dm);mats[1-w]=qbasis(b,ds)
    ans=[]
    for i,j,k,l in product(range(2),repeat=4):
        r=gaussian(mats[0][i,k]*mats[1][j,l])
        if any(r):ans.append((2*i+j,2*k+l,r))
    assert len(ans)==4
    return ans


def csr(rows,left,right):
    ids=[{z:i for i,z in enumerate(t)} for t in (left,right)]
    a=[];b=[];r=[];s=[]
    for (p,q,i,j),(x,y) in rows.items():
        if not(x or y):continue
        a.append(4*ids[0][p]+i);b.append(4*ids[1][q]+j);r.append(x);s.append(y)
    shape=(4*len(left),4*len(right))
    out=tuple(coo_matrix((v,(a,b)),shape=shape,dtype=np.int64).tocsr() for v in (r,s))
    for m in out:m.eliminate_zeros()
    return out

@cache
def edge(spec,ch0,ch3,at_source):
    wire,dm,ds,rev=EDGE_SPECS[spec]
    ch=(ch0,ch3)
    qs=range(4*ch[1-wire],4*ch[1-wire]+4)
    qm=range(4*ch[wire],4*ch[wire]+4)
    out={}
    for alpha in range(6):
        cc=alpha//3
        cx=range(4*cc,4*cc+4)
        for x,y,a in product(cx,cx,qm):
            H=[(i,w) for i in range(8) if (w:=projection(alpha,x,y,i,a))]
            if not H:continue
            for b,t,u in product(qs,range(4),range(4)):
                poly={}
                for i,w in H:
                    for m,(r,s) in two_transport(i,b,t,u,at_source).items():plus(poly,m,w*r,w*s)
                for m,z in poly.items():
                    if not any(z):continue
                    S=(u,y,m&255) if at_source else (y,m&255)
                    M=(alpha,t,x,m>>8) if at_source else (alpha,t,u,x,m>>8)
                    left,right=(M,S) if rev else (S,M)
                    for i,j,w in e_wire(a,b,wire,dm,ds):
                        r,s=signed_mul(z,w,1)
                        plus(out,(left,right,i,j),r,s)
    out={k:z for k,z in out.items() if any(z)}
    left=tuple(sorted({k[0] for k in out}));right=tuple(sorted({k[1] for k in out}))
    matrix=csr(out,left,right)
    print('edge',spec,ch0,ch3,'source B',at_source,'labels',len(left),len(right),
          'nnz',tuple(z.nnz for z in matrix),flush=True)
    return left,right,matrix

@cache
def singleton_weights(ex,ey):
    z=haar_moment(ex[:4])*haar_moment(ex[4:])*haar_moment(ey[:4])*haar_moment(ey[4:])
    return z

def terms(ext,axis_g,comm):
    base=[Counter(),Counter()]
    for d,i in ext:base[d-2][i]+=1
    zero=(0,)*8
    raw=[(zero,zero,(1,0))] if comm is None else curv(*comm)
    ds=[d-2 for d,g in axis_g]
    for ex,ey,z in raw:
        E=[list(ex),list(ey)]
        for a in range(2):
            for k,v in base[a].items():E[a][k]+=v
        odd=[[k for k,n in enumerate(e) if n%2] for e in E]
        if ds[0]!=ds[1]:
            if any(len(w)!=1 for w in odd):continue
            choices=[(odd[ds[0]][0],odd[ds[1]][0])]
        else:
            if odd[1-ds[0]]:continue
            m=odd[ds[0]]
            choices=[(i,i) for i in range(8)] if not m else [tuple(m),tuple(m[::-1])] if len(m)==2 else []
        for i,j in choices:
            E[ds[0]][i]+=1;E[ds[1]][j]+=1
            w=singleton_weights(tuple(E[0]),tuple(E[1]))*(16 if comm is None else 48**2)
            E[ds[0]][i]-=1;E[ds[1]][j]-=1
            assert w.denominator==1
            if w:yield i,j,int(w),z

@cache
def local_kernel(ext,axis_g,comm):
    out={}
    for i,j,w,z in terms(ext,axis_g,comm):
        for m,v in local_product(i,j,axis_g[0][1],axis_g[1][1]).items():
            plus(out,m,*signed_mul(z,v,w))
    return {m:v for m,v in out.items() if any(v)}

@cache
def vertex_wire(a,b,ch,wire):
    m=gamma[a]*gamma[b]*G5
    mat=m[2*ch:2*ch+2,2*ch:2*ch+2]
    out=[]
    for i,j,k,l in product(range(2),repeat=4):
        if wire==0:
            z=gaussian(mat[i,k]) if j==l else (0,0)
        else:
            z=gaussian(mat[j,l]) if i==k else (0,0)
        if any(z):out.append((2*i+j,2*k+l,z))
    return out

@cache
def vertex(left,right,idx,lin,lout,ch0,ch3,at_source):
    source=idx%2==0
    out={}
    tr=trace_to_local()
    for A in left:
        m=A[-1]
        for B in right:
            n=B[-1]
            if m&n:continue
            rest=255^(m|n)
            sign=wedge_sign(m,n)*wedge_sign(m|n,rest)
            ext=((lin,A[-2]),(lout,B[-2]))
            if source:
                comm=(B[0],A[0]) if at_source else None
                if comm is not None and comm[0]==comm[1]:continue
                for c,d in product(range(4),repeat=2):
                    if c==d:continue
                    z=local_kernel(ext,((2,c),(3,d)),comm).get(rest)
                    if not z:continue
                    wire=idx//2;ch=(ch0,ch3)[wire]
                    for i,j,v in vertex_wire(c,d,ch,wire):
                        plus(out,(A,B,i,j),*signed_mul(z,v,sign))
            else:
                a,t=A[:2];b,u=B[:2]
                d,x=tr[a,u];e,y=tr[b,t]
                comm=None if at_source else (A[2],B[2])
                if comm is not None and comm[0]==comm[1]:continue
                z=local_kernel(ext,((5-lin,d),(5-lout,e)),comm).get(rest)
                if z:
                    for i in range(4):plus(out,(A,B,i,i),sign*x*y*z[0],sign*x*y*z[1])
    M=csr(out,left,right)
    print('vertex',idx,lin,lout,'source B',at_source,'nnz',tuple(x.nnz for x in M),flush=True)
    return M

def dot(A,B):
    ar,ai=A;br,bi=B
    return (inner_transpose(ar,br)-inner_transpose(ai,bi),
            inner_transpose(ar,bi)+inner_transpose(ai,br))

def run(at_source,mixed_l):
    start=perf_counter()
    out=[0,0]
    for ch0,ch3 in product(range(2),repeat=2):
        E=[edge(i,ch0,ch3,at_source) for i in range(4)]
        M=[]
        for i in range(4):
            v=(i+1)%4
            V=vertex(E[i][1],E[v][0],v,mixed_l[i],mixed_l[v],ch0,ch3,at_source)
            M.append(multiply(E[i][2],V))
        ans=dot(multiply(M[0],M[1]),multiply(M[2],M[3]))
        print('chiral pair',ch0,ch3,'exact trace',ans,'elapsed',perf_counter()-start,flush=True)
        for k,a in enumerate(ans):out[k]+=a
    # Each link pair contributes two T factors /16 and exact Haar /192.
    # Local vertices contribute raw T /16 each; two commutator moments
    # with denom 48², two independent singleton pairs with denom 16.
    den=(192*16)**4*(48**2*16)**2*(16*16)**2
    print('orientation sum',tuple(F(z,den) for z in out),flush=True)
if __name__=='__main__':
    from sys import argv
    run(bool(int(argv[1])),tuple(map(int,argv[2:])))
