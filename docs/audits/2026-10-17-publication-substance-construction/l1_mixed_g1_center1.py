"""Exact center-1 tensor for the mixed composite/dressed coefficient."""
from collections import Counter, defaultdict
from functools import cache
from itertools import product
import sys
from contextlib import redirect_stdout

with redirect_stdout(sys.stderr):
    from l1_equal_time_shared_quadratic_pair import fixed_frame
    from l1_equal_time_int_contract import sparse_int
    from l1_normalization_opposed_fourth import L
    from l1_normalization_uniform_mixed_edge import moment, mul, qadj, unit
    from l1_direct_b_haar import wedge
    from l1_reduced_wedge_reference import wedge_sign

AX = range(4)
Q = range(8)
# Two extended-link joint moments, two transverse second moments, and four frames.
DEN = 192**2 * 4**2 * 4**4

@cache
def projection(alpha,x,y,v,e,shared):
    ch,k=divmod(alpha,3)
    if x//4!=ch or y//4!=ch:return 0
    X,Y=unit(x%4),unit(y%4)
    total=0
    for i,j in product(AX,repeat=2):
        if shared:
            w=4*moment(v,e,4*ch+i,4*ch+j)
        else:
            w=12*int(i==j and v==e)
        if w:
            p=mul(mul(qadj(X),qadj(unit(i))),mul(Y,unit(j)))
            total+=w*p[k+1]
    return total

@cache
def edge(axis,shared):
    site=1
    anchor=site if shared else site^(1<<axis)
    out=defaultdict(Counter)
    for x,alpha,e,y,v in product(Q,range(6),Q,Q,Q):
        weight=projection(alpha,x,y,v,e,shared)
        if not weight:continue
        for g,frame in enumerate(fixed_frame(site,axis,anchor,v)):
            for mask,(r,i) in sparse_int(frame).items():
                if r:out[x,alpha,g][e,y,mask,0]+=weight*r
                if i:out[x,alpha,g][e,y,mask,1]+=weight*i
    return {key:{k:v for k,v in c.items() if v} for key,c in out.items()}

@cache
def local_pair():
    out=defaultdict(Counter)
    for q in Q:
        frames=fixed_frame(1,3,1,q)
        for g,h in product(AX,repeat=2):
            for mask,(r,i) in sparse_int(wedge(frames[g],frames[h])).items():
                if r:out[g,h][mask,0]+=r
                if i:out[g,h][mask,1]+=i
    return {k:{m:z for m,z in c.items() if z} for k,c in out.items()}

def add(poly,key,z,phase):
    if phase&2:z=-z
    poly[key,phase&1]+=z

def tensor(mode):
    source=edge(0,bool(mode&1))
    det=edge(1,bool(mode&2))
    local=local_pair()
    out=Counter()
    for x,g0,g1,h0,h1 in product(Q,AX,AX,AX,AX):
        for a,u in L.get((g1,h0),()):
            A=source.get((x,a,g0))
            if not A:continue
            for b,v in L.get((g0,h1),()):
                B=det.get((x,b,g1))
                if not B:continue
                for (e,y,m,im),r in A.items():
                    for (f,z,n,jn),s in B.items():
                        if m&n:continue
                        for (p,kn),t in local[h0,h1].items():
                            if p&(m|n):continue
                            # Product epsilon(0,2,1,3)*epsilon(1,2,0,3)=-1.
                            sign=-u*v*wedge_sign(m,n)*wedge_sign(m|n,p)
                            add(out,(e,f,y,z,m|n|p),sign*r*s*t,im+jn+kn)
    clean={k:v for k,v in out.items() if v}
    keys={k for k,p in clean}
    assert all((m&255).bit_count()==1 and ((m>>8)&255).bit_count()==6
               and ((m>>16)&255)==0 and (m>>24).bit_count()==1 for *_,m in keys)
    print('mode',mode,'entries',len(keys),'max',max(map(abs,clean.values()),default=0),file=sys.stderr,flush=True)
    return {k:(clean.get((k,0),0),clean.get((k,1),0)) for k in keys}

if __name__=='__main__':
    for mode in range(4):
        rows = tensor(mode)
        assert len(rows) == (2048, 5120, 5120, 11648)[mode]
        for k,(r,i) in sorted(rows.items()):
            print(mode,*k,r,i)
