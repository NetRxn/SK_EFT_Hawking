"""Exact all-signed benchmark for one two-column exterior chirality block."""
from collections import defaultdict
from sys import argv
from fractions import Fraction
from itertools import product
from time import perf_counter
import numpy as np
from scipy.sparse import csr_matrix, vstack
from l1_extended_overlap_pure_strip import strip,P
from l1_extended_overlap_all_links_alpha0 import paired_haar

N=36**2
def flat(a):
    key=0
    for i in a:key=3*key+i
    return key

def tensors():
    T,_=strip()
    out=defaultdict(list)
    for (ends,a),v in T.items():
        if max(a)>=3:continue
        i,j,k,l=ends
        out[flat(a)].append((36*i+j,36*k+l,v))
    all_states=sorted({x for rows in out.values() for a,b,_ in rows for x in (a,b)})
    ix={x:i for i,x in enumerate(all_states)}
    dims=len(ix),len(ix)
    def make(rows):
        if not rows:return csr_matrix(dims,dtype=np.int64)
        a,b,c=zip(*rows)
        return csr_matrix((c,([ix[i] for i in a],[ix[i] for i in b])),shape=dims,dtype=np.int64)
    S=[make(out[i]) for i in range(81)]
    def link(fix=False):
        H=paired_haar(fix)
        return make([(a,b,v) for a,row in H.items() if a in ix for b,v in row.items() if b in ix])
    return S,link(),link(True),len(ix)

def maxrow(a):
    return int(abs(a).sum(axis=1).max()) if a.nnz else 0

def checked(A,B):
    assert maxrow(A)*maxrow(B)<2**63
    return A@B

def path_matrices():
    S,H,F,n=tensors()
    left=[];right=[]
    L=[checked(H,s.T) for s in S]
    R=[checked(s,H) for s in S]
    for j,k in product(range(81),repeat=2):
        left.append(checked(checked(L[j],F),R[k]))
        right.append(checked(R[j],S[k].T))
    def pack(xs):
        records=[]
        for x in xs:
            a,b=x.nonzero()
            vals=np.asarray(x[a,b]).ravel()
            records.append(csr_matrix((vals,(np.zeros(len(a),dtype=int),a*n+b)),shape=(1,n*n)))
        return vstack(records,format='csr')
    A,B=pack(left),pack(right)
    print('states',n,'path rows',A.shape[0],B.shape[0],'entries',A.nnz,B.nnz,
          'peak rows',max(np.diff(A.indptr)),max(np.diff(B.indptr)),flush=True)
    return A,B

def exterior():
    a=[];weights=[]
    with open(argv[1]) as f:
        for line in f:
            i,j,k,r,s=map(int,line.split())
            if i or j:continue
            alpha=[]
            for _ in range(8):k,t=divmod(k,6);alpha.append(t)
            if max(alpha)>=3:continue
            a.append(alpha[::-1]);weights.append(r)
    return np.array(a,dtype=np.int16),weights

def indices(a,pure,nopure):
    # Nonpure even/odd, pure even/odd.
    x=a[:,nopure];y=a[:,pure]
    return (((x[:,None]*3+x)*3+y[:,None])*3+y).astype(np.int32)

def main():
    start=perf_counter()
    L,R=path_matrices()
    a,w=exterior()
    # M4,M6,M0,M2,O0,O4,O2,O6.
    S3,S0,S2,S1=(indices(a,p,n) for p,n in ((0,2),(6,4),(7,5),(1,3)))
    u=(81*S3+S0).ravel();v=(81*S2+S1).ravel()
    order=np.argsort(u,kind='stable')
    U=u[order];V=v[order]
    total=0;live=0;blocks=0;maxnnz=0
    bound=maxrow(L)*maxrow(R)
    assert bound<2**63
    for i in range(0,6561,128):
        j=min(i+128,6561)
        lo,hi=np.searchsorted(U,[i,j])
        if lo==hi:continue
        blocks+=1
        G=L[i:j]@R.T
        maxnnz=max(maxnnz,G.nnz)
        gauge=np.asarray(G[U[lo:hi]-i,V[lo:hi]]).ravel()
        for pos,n in zip(order[lo:hi],gauge,strict=True):
            if n:
                x,y=divmod(int(pos),len(w))
                total+=int(n)*w[x]*w[y]
                live+=1
    print('exterior rows',len(w),'pair count',len(U),'live',live,'blocks',blocks,
          'max Gram nnz',maxnnz,'gauge dot absolute bound',bound,flush=True)
    print('exact signed block raw',total,'normalized gauge factors',Fraction(total,48**8*4**4),
          'seconds',perf_counter()-start,flush=True)
if __name__=='__main__':main()
