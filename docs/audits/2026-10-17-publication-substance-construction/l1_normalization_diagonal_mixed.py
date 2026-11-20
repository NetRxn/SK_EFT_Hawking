from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import factorial,prod
from l1_normalization_shared_transport import L,TERMS,component_multisets
from l1_normalization_six_transport import weights
from l1_normalization_uniform_mixed_edge import moment
from l1_normalization_repeated_mixed_cycle import p_coeff
from l1_normalization_mixed_cycle import local_product,plus
from l1_normalization_transport_cycle import ORDERED,M,edge_base,DIM,poly_int,signed_mul,wedge_sign

def case_for(ii):
    rows=defaultdict(list)
    for i in ii:rows[TERMS[i][2][0]].append(TERMS[i][2])
    if any(len(rows[x])!=2 for x in range(4)):return
    A=[x for x,ts in rows.items() if all(t[1:3]==(0,1) for t in ts)]
    if len(A)!=1:return
    a,=A
    b=a^3;x=a^1;y=a^2
    if sorted(t[1:3] for t in rows[x])!=[(0,2),(0,3)]:return
    if sorted(t[1:3] for t in rows[y])!=[(1,2),(1,3)]:return
    if any(t[1:3]!=(2,3) for t in rows[b]):return
    kinds=[]
    for p,d in ((x,1),(y,0)):
        ts=sorted(rows[p])
        u,v=[t[3] for t in ts] # mixed extended axis always first T slot
        s,t=[z[3+d] for z in rows[b]]
        if u==v:
            assert s==t
            kinds.append(int(u==s))
        else:
            assert s!=t
            kinds.append(2+int(u!=s))
    return tuple(kinds),prod(factorial(n) for n in Counter(ii).values())

@cache
def curvature(a,b,x,y,u,v):
    return sum(p*q*moment(*i,*j) for i,p in p_coeff(a,x,y) for j,q in p_coeff(b,u,v))

@cache
def mixed_local():
    out=defaultdict(dict)
    for (c,d),A in L.items():
        for (e,f),B in L.items():
            for a,s in A:
                for b,t in B:
                    ac=range(4*(a//3),4*(a//3)+4)
                    bc=range(4*(b//3),4*(b//3)+4)
                    for x,y,u,v in product(ac,ac,bc,bc):
                        z=s*t*curvature(a,b,x,y,u,v)
                        if not z:continue
                        # X_l in curvature l shares with local T_l in the
                        # other action. Degree-two Haar pairs align the basis.
                        for m,(r,i) in local_product(u,x,d,f).items():
                            plus(out[y,v,(c,e)],m,z*r,z*i)
    return {k:{m:v for m,v in p.items() if any(v)} for k,p in out.items() if any(map(any,p.values()))}

@cache
def branch(kind):
    E={k:poly_int(p) for k,p in edge_base(kind).items()}
    groups={}
    for k,p in E.items():
        q=defaultdict(list)
        for mask,w in p.items():q[mask&255].append((mask>>8,w))
        groups[k]=q
    out=defaultdict(dict)
    joins=0
    for (y,z,p),poly in mixed_local().items():
        for q in ORDERED:
            G=groups[p,q]
            for m,r in poly.items():
                for n,s in G.get(255^m,()):
                    joins+=1
                    a,b=signed_mul(r,s,wedge_sign(m,255^m))
                    plus(out[q],(y,z,n),a,b)
    ans={q:{m:v for m,v in p.items() if any(v)} for q,p in out.items()}
    print('branch kind',kind,'local rows',len(mixed_local()),'joins',joins,
          'nonzero branch terms',sum(map(len,ans.values())),flush=True)
    return ans

@cache
def local_pair_with_external(y,z,p):
    ans={}
    for i,j in product(range(8),repeat=2):
        h=moment(y,z,i,j)
        if h:
            for m,(r,s) in local_product(i,j,*p).items():plus(ans,m,h*r,h*s)
    return {m:v for m,v in ans.items() if any(v)}

@cache
def source(y,z,w,v):
    r=s=0
    for (p,q),c in weights.items():
        A=local_pair_with_external(y,w,p)
        B=local_pair_with_external(z,v,q)
        for m,a in A.items():
            b=B.get(255^m)
            if b is not None:
                u,vv=signed_mul(a,b,c*wedge_sign(m,255^m))
                r+=u;s+=vv
    return r,s

@cache
def trace(k,l):
    A,B=branch(k),branch(l)
    groups={}
    for q,p in B.items():
        out=defaultdict(list)
        for (y,z,m),v in p.items():out[m].append((y,z,v))
        groups[q]=out
    r=s=joins=0
    for (p,q),c in M.items():
        for (y,z,m),a in A.get(p,{}).items():
            for w,v,b in groups.get(q,{}).get(255^m,()):
                z0=source(y,z,w,v)
                if not any(z0):continue
                joins+=1
                u,t=signed_mul(signed_mul(a,b,1),z0,c*wedge_sign(m,255^m))
                r+=u;s+=t
    assert s==0
    # Two mixed centers: quartic U moment /48, independent two
    # singleton second moments /16, two raw T factors /16.
    # Each branch's transport edge /DIM. Local A0 two quartic weighted
    # moments /(48*16)^2. Curvature scalar 2*(16/9).
    den=(48*16*16*DIM)**2*(48*16)**2*9
    return F(32*r,den),joins

if __name__=='__main__':
    cases=Counter()
    for comps in component_multisets():
        ii=[i for g in comps for i in g]
        if (v:=case_for(ii)) is not None:cases[v]+=1
    assert sum(cases.values())==160
    total=F(0)
    for ((k,l),f),n in sorted(cases.items()):
        r,j=trace(k,l)
        assert trace(l,k)[0]==r
        value=r/f
        total+=n*value
        print('edge kinds',k,l,'multiplicity',n,'factorial',f,'top joins',j,'representative',value,flush=True)
    print('full 160-case diagonal mixed sector',total,flush=True)
