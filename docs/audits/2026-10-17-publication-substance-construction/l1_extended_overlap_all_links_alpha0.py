"""Full Haar join of one exterior alpha sector of the shared 16-site motif."""
from collections import Counter,defaultdict
from fractions import Fraction
from itertools import product
from time import perf_counter
from sys import argv
from l1_extended_overlap_pure_strip import strip,qproduct,pair,P,Q
from l1_normalization_uniform_mixed_edge import moment

def rows(data):
    out=defaultdict(dict)
    for (a,b),v in data.items():
        if v:out[a][b]=v
    return out

def mm(A,B):
    out={}
    n=0
    for a,block in A.items():
        c=Counter()
        for b,v in block.items():
            for d,z in B.get(b,()).items() if b in B else ():
                c[d]+=v*z;n+=1
        if any(c.values()):out[a]={d:v for d,v in c.items() if v}
    print('sparse product',n,'rows',len(out),'entries',sum(map(len,out.values())),flush=True)
    return out

def transpose(A):
    return rows({(b,a):z for a,row in A.items() for b,z in row.items()})

def paired_haar(fix_even=False):
    # All alpha slots here are left chirality, hence restrict both pair
    # legs to left coordinate support. Missing right terms are never read.
    ids=[pair(i,j) for i in Q for j in range(i,4)]
    q={k:p for k,p in enumerate(P) if k in ids}
    H={(i,j):moment(*a,*b) for i,a in q.items() for j,b in q.items()}
    return rows({(36*a+b,36*c+d):(48*int(P[a]==P[c]==(0,0)) if fix_even else H[a,c])*H[b,d]
                 for a,b,c,d in product(ids,repeat=4)})

def special(a,b,c,d):
    # Nonpure even face uses raw A=a, B=b; odd uses B=d, A=c.
    # Pure alpha pair i=j=0. Exact numerator in units of 1/4.
    out=Counter()
    for x,y,t,X,Y,Z,T in product(Q,repeat=7):
        # Pure anchor (site 6) y,t; nonpure anchor (site 4) x,z=x.
        v=qproduct(y+1,2,t+1)[1]
        if not v:continue
        p=qproduct(-a-1,-Y-1,b+1,X+1)[1]
        q=qproduct(-d-1,-T-1,c+1,Z+1)[1]
        if p and q:
            s=qproduct(-x-1,-x-1)[0]
            h=36*pair(x,X)+pair(x,Z)
            k=36*pair(y,Y)+pair(t,T)
            out[h,k]-=s*v*p*q
    return {k:v for k,v in out.items() if v}

def exterior():
    result={}
    with open(argv[1]) as f:
        for line in f:
            i,j,k,r,s=map(int,line.split())
            if k==0 and i<4 and j<4:
                assert not s
                result[i,j]=r
    return result

if __name__=='__main__':
    start=perf_counter()
    T,_=strip()
    S=rows({(36*e0+o0,36*e1+o1):v for ((e0,o0,e1,o1),a),v in T.items() if a==(0,0,0,0)})
    H=paired_haar();F=paired_haar(True)
    M=H
    for A in (transpose(S),F,S,H,S,H):M=mm(M,A)
    X=exterior()
    total=0;live=0;gauges=Counter()
    for a,b,c,d in product(Q,repeat=4):
        u=X.get(tuple(sorted((a,c))),0)
        v=X.get(tuple(sorted((b,d))),0)
        if not u or not v:continue
        n=sum(M.get(i,{}).get(j,0)*w for (i,j),w in special(a,b,c,d).items())
        if n:total+=n*u*v;live+=1;gauges[n]+=1
    print('all-link alpha-zero sector live mixed assignments',live,'of 256','gauge histogram',dict(sorted(gauges.items())),flush=True)
    print('raw full-motif term',total,'after temporal and pure transverse factors',Fraction(total,48**8*4**4),
          'seconds',perf_counter()-start,flush=True)
