"""Exact normalization contraction for the six-factor transport chain."""
from collections import Counter
from itertools import combinations_with_replacement,product
from fractions import Fraction as F
from functools import cache
from l1_normalization_shared_transport import (
    TERMS,component_multisets,quat,adj,nodes,site,pair,
    R,diag,gamma,bilinear,add,scale,wedge,top_product,translate,
)

pairs=tuple(combinations_with_replacement(range(4),2))
weights={(i,j):int(i[0]==i[1] and j[0]==j[1])-int(i==j)*(1 if i[0]==i[1] else 2)
         for i,j in product(pairs,repeat=2)}
weights={k:v for k,v in weights.items() if v}
assert len(weights)==18

def sixth(comp):
    return (len(comp)==6 and len(set(comp))==3 and
            set(Counter(comp).values())=={2} and
            all(TERMS[i][2][1:3]==(2,3) for i in comp))

def shared_moment(x,d):
    """(96×8⁴) E[(T_x T_x)_p (T_y T_y)_q] for one physical link."""
    y=x^(1<<d)
    out={(p,q):{} for p,q in product(pairs,repeat=2)}
    for l,r,w in nodes():
        U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
        A=[add(bilinear(g*Ud,x,y),scale(bilinear(U*g,y,x),-1)) for g in gamma]
        B=[add(bilinear(Ud*g,x,y),scale(bilinear(g*U,y,x),-1)) for g in gamma]
        P={i:wedge(A[i[0]],A[i[1]]) for i in pairs}
        Q={i:wedge(B[i[0]],B[i[1]]) for i in pairs}
        for p,q in out:
            out[p,q]=add(out[p,q],scale(wedge(P[p],Q[q]),w))
    return out

def outer(axis):
    # Middle center 0. Its shared axis points to a distinct endpoint site.
    neighbor=1<<axis
    K=pair(neighbor,1-axis)
    H=shared_moment(0,axis)
    result={}
    for middle in pairs:
        result[middle]=add(*(scale(wedge(H[middle,p],K[q[0]][q[1]]),w) for (p,q),w in weights.items()))
    print('shared axis',axis,'nonempty moment entries',sum(map(bool,H.values())),
          'moment terms',sum(map(len,H.values())),'outer terms',sum(map(len,result.values())))
    return result

@cache
def chain():
    A,B=outer(0),outer(1)
    out=add(*(scale(wedge(A[p],B[q]),w) for (p,q),w in weights.items()))
    # Store the common covariance numerator as a separate scalar to
    # simplify every exterior coefficient and avoid polynomial blowup.
    denom=(96*8**4)**2*(8*4**2)**2*9**3
    return out,denom,16**3

def check_links(comp):
    ts=[TERMS[i][2] for i in sorted(set(comp))]
    active={t[0] for t in ts}
    # Each branch has both T legs, with two physical links shared
    # between the middle and one endpoint. No other overlaps exist.
    counts=Counter(e for x,k,l,u,v in ts for e in ((u,0),(v,1)))
    shared={e for e,n in counts.items() if n==2}
    assert len(shared)==2 and {d for x,d in shared}=={0,1}
    middle=[x for x in active if (x^1 in active and x^2 in active)]
    assert len(middle)==1
    return middle[0],(middle[0]^3)

def main():
    matching=[]
    for comps in component_multisets():
        if sorted(map(len,comps))!=[2,6]:continue
        small,big=sorted(comps,key=len)
        if not sixth(big):continue
        m,x=check_links(big)
        assert TERMS[small[0]][2][0]==x
        matching.append((comps,m,x))
    assert len({max(c,key=len) for c,m,x in matching})==64
    p,q,w=chain()
    print('chain effective exterior terms',len(p))
    total=F(0); reps=Counter()
    for comps,m,x in matching:
        assert all(n==2 for n in Counter(i for comp in comps for i in comp).values())
        chain_p=translate(p,lambda z:z^m)
        value=F(w*top_product((chain_p,site(x))),q*9216*16)
        reps[value]+=1
        total+=value
    print('complete matching multisets',len(matching),'representatives',dict(reps),'exact sector',total)
if __name__=='__main__':main()
