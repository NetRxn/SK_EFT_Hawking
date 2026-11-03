"""Conditional-Haar exact contraction for the coupled equal-time family."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import factorial,prod

from l1_equal_time_shared_quartic import (
    AXES,forward,quat,adj,diag,gamma,bilinear,add,scale,wedge,wedge_sign,
    nodes,same_site_quadratic_support,reduce_source_dependence,R,TOP,
)
from l1_equal_time_mixed_factor import transform
from l1_equal_time_int_contract import sparse_int
from l1_equal_time_joint_source_weights import kernel
from l1_normalization_opposed_fourth import L
from l1_direct_a_haar import mul,qproduct

ZERO=(0,)*4
UNIT=tuple(tuple(int(i==j) for i in range(4)) for j in range(4))
ALL_INDICES=tuple(product(AXES,repeat=2))
VEC=tuple(product(range(2),range(1,4)))
TYPES=((0,0),(0,4),(4,0),(4,4),(1,1),(5,5))
MEMBERS={k:(k,) if k[0]%4==0 else tuple((j,j) for j in range(k[0],k[0]+3))
         for k in TYPES}


@cache
def local_frame(x,ch,i):
    q=UNIT[i]
    U=diag(quat(q if ch==0 else ZERO),quat(q if ch==1 else ZERO))
    Ud=diag(quat(adj(q) if ch==0 else ZERO),quat(adj(q) if ch==1 else ZERO))
    delta=Ud-U
    return tuple(bilinear(g*delta+delta*g,x,x) for g in gamma)


@cache
def longitudinal(x,d,z,l,r):
    y=forward(x,d)
    U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
    if z==x:
        return tuple(add(bilinear(g*Ud,x,y),scale(bilinear(U*g,y,x),-1)) for g in gamma)
    assert z==y
    return tuple(add(bilinear(Ud*g,y,x),scale(bilinear(g*U,x,y),-1)) for g in gamma)


@cache
def projected_curvature(a,b,rotation_coordinate,ch,local_coord):
    q=mul(UNIT[rotation_coordinate],adj(UNIT[local_coord]))
    return sum(w*q[j%3+1] for j,w in L[a,b] if j//3==ch)


@cache
def local_center(x,source_type):
    i,j=source_type
    chi,chj=i//4,j//4
    rotations=(0,) if i%4==0 else (1,2,3)
    mult=3 if i%4==0 else 1
    out={pair:{} for pair in ALL_INDICES}
    for r,p,q in product(rotations,range(1,4),range(1,4)):
        A=local_frame(x,chi,p);B=local_frame(x,chj,q)
        for a,b in ALL_INDICES:
            # First action curvature uses source 2 and local 2, with its
            # transverse T on link 3. The second interchanges 2 and 3.
            C=add(*(scale(B[d],projected_curvature(a,d,r,chi,p)) for d in AXES))
            D=add(*(scale(A[e],projected_curvature(b,e,r,chj,q)) for e in AXES))
            out[a,b]=add(out[a,b],scale(wedge(C,D),mult))
    return {idx:sparse_int(poly) for idx,poly in out.items()}


@cache
def coordinate_rule(degree):
    if degree==2:
        return tuple((q,ZERO,1) for q in UNIT)+tuple((ZERO,q,1) for q in UNIT)
    assert degree==4
    return tuple((tuple(l),tuple(r),w) for l,r,w in nodes())


def pair_product(A,B):
    return {idx:sparse_int(wedge(A[idx[0]],B[idx[1]])) for idx in ALL_INDICES}


def add_projected(out, local, x, center_frames, remote_frames, weight):
    site_mask=255<<(8*x)
    remote_mask=255<<(8*3)
    for k,P in center_frames.items():
        L=local[k]
        for a,(ar,ai) in P.items():
            for j,Q in remote_frames.items():
                dest=out[j]
                for b,(br,bi) in Q.items():
                    if a&b:
                        continue
                    u=a|b
                    m=site_mask^(u&site_mask)
                    z=L.get(m)
                    if z is None:
                        continue
                    s=weight*wedge_sign(a,b)*wedge_sign(m,u)
                    cr,ci=z
                    er,ei=ar*br-ai*bi,ar*bi+ai*br
                    old_r,old_i=dest.get(u&remote_mask,(0,0))
                    dest[u&remote_mask]=(old_r+s*(cr*er-ci*ei),old_i+s*(cr*ei+ci*er))


@cache
def branch(x,axis,xlinks,ylinks):
    multiplicities=Counter(xlinks+ylinks)
    keys=sorted(multiplicities)
    assert sorted(multiplicities.values()) in ([2,2],[4])
    outcomes={t:{k:{} for k in ALL_INDICES} for t in TYPES}
    denominator=prod(4 if multiplicities[k]==2 else 96*2**4 for k in keys)
    for values in product(*(coordinate_rule(multiplicities[k]) for k in keys)):
        settings=dict(zip(keys,values,strict=True))
        weight=prod(w for l,r,w in values)
        A,B=(longitudinal(x,axis,z,*settings[z][:2]) for z in xlinks)
        C,D=(longitudinal(3,axis,z,*settings[z][:2]) for z in ylinks)
        left,right=pair_product(A,B),pair_product(C,D)
        for t in TYPES:
            add_projected(outcomes[t],local_center(x,t),x,left,right,weight)
    return outcomes,denominator


@cache
def source_mix(t,u):
    return sum(kernel(tuple(sorted((i,a))),tuple(sorted((j,b))))
               for (i,j),(a,b) in product(MEMBERS[t],MEMBERS[u]))


def join(A,B):
    val=0
    imag=0
    for a,(ar,ai) in A.items():
        b=B.get((255<<(8*3))^a)
        if b is None: continue
        br,bi=b
        s=wedge_sign(a,(255<<(8*3))^a)
        val+=s*(ar*br-ai*bi)
        imag+=s*(ar*bi+ai*br)
    assert imag==0
    return val


def solve(word):
    slots=defaultdict(list)
    for term in word:slots[term[0]].append(term)
    assert set(slots)=={1,2,3} and all(len(v)==2 for v in slots.values())
    assert [t[1:3] for t in slots[1]]==[(0,2),(0,3)]
    assert [t[1:3] for t in slots[2]]==[(1,2),(1,3)]
    assert all(t[1:3]==(2,3) for t in slots[3])
    A,da=branch(1,1,tuple(t[3] for t in slots[1]),tuple(t[4] for t in slots[3]))
    B,db=branch(2,0,tuple(t[3] for t in slots[2]),tuple(t[3] for t in slots[3]))
    result=F(0)
    for t,u in product(TYPES,repeat=2):
        h=source_mix(t,u)
        if not h:continue
        raw=sum(join(A[t][a,a],B[u][b,b])-join(A[t][a,b],B[u][b,a]) for a,b in ALL_INDICES)
        result+=raw*h
    # 48 per local center = 3 (rotation) × 4² (two local vector covariances).
    # All twelve action frames use 4T; source_mix is in physical source units.
    denom=da*db*48**2*4**12*prod(factorial(v) for v in Counter(word).values())
    return result*F(16,9*denom)


def main():
    words={tuple(sorted(w)) for w in same_site_quadratic_support() if not reduce_source_dependence(w)[1]}
    assert len(words)==40
    results=Counter()
    while words:
        w=min(words)
        orbit={tuple(sorted(transform(t,a,b) for t in w)) for a,b in product((False,True),repeat=2)}
        assert orbit<=words
        words-=orbit
        result=solve(w)
        results[result]+=len(orbit)
        print('orbit',len(orbit),w,result,flush=True)
    print('coupled',sorted(results.items()),'subtotal',sum(v*n for v,n in results.items()),flush=True)

if __name__=='__main__':main()
