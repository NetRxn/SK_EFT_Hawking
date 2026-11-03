"""Exact normalization for mixed-plane size-six transport chains."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product
from l1_normalization_shared_transport import (
    TERMS, LINKS,component_multisets,R,add,scale,wedge,
    pair,local_pair,W,cross_weight,L,square,translate,site,top_product,
)
from l1_normalization_six_transport import pairs,weights,shared_moment

def classify(comp):
    if len(comp)!=6 or len(set(comp))!=3 or set(Counter(comp).values())!={2}:return None
    inds=sorted(set(comp))
    pure=[i for i in inds if TERMS[i][2][1:3]==(2,3)]
    if len(pure)!=1:return None
    C=pure[0]
    middles=[i for i in inds if i!=C and LINKS[i]&LINKS[C]]
    if len(middles)!=1:return None
    B=middles[0]
    A,=set(inds)-{B,C}
    a,k,l,u,v=TERMS[A][2];b,q,r,m,n=TERMS[B][2];c,*_=TERMS[C][2]
    shared1=LINKS[A]&LINKS[B]
    shared2=LINKS[B]&LINKS[C]
    if len(shared1)!=2 or len(shared2)!=1:return None
    assert k==q and k<2 and a^b==1<<k and b^c==1<<(1-k)
    assert all(d>=2 for x,d in shared1)
    assert next(iter(shared2))[1]==1-k
    return a,k,l==r

@cache
def mixed_open():
    """B=site1, only its local second moments retained."""
    S=local_pair(1)
    return {p:add(*(scale(S[q[0]][q[1]],w) for (t,q),w in weights.items() if t==p)) for p in pairs}

@cache
def same_open():
    """Open B square curvature basis, indexed by p and sorted (alpha,beta)."""
    S=local_pair(1)
    out={}
    for (c,d),ls in L.items():
        for (e,f),rs in L.items():
            p=tuple(sorted((c,e)))
            for a,v in ls:
                for b,z in rs:
                    k=p,tuple(sorted((a,b)))
                    out[k]=add(out.get(k,{}),scale(S[d][f],v*z))
    return out

@cache
def tail():
    H=shared_moment(1,1)
    K=pair(3,0)
    out={p:add(*(scale(wedge(H[p,r],K[s[0]][s[1]]),w)
                 for (r,s),w in weights.items())) for p in pairs}
    print('shared link terms',sum(map(len,H.values())),'tail terms',sum(map(len,out.values())))
    return out

@cache
def chain(same):
    K=tail()
    if same:
        A,B=W(0,1),same_open()
        middle={p:add(*(scale(wedge(v,w),cross_weight(a,b))
                        for a,v in A.items() for (q,b),w in B.items()
                        if p==q and cross_weight(a,b))) for p in pairs}
        den,n=128**4*(96*8**4)*81*48**2,16
    else:
        A,B=square(pair(0,1),local_pair(0)),mixed_open()
        middle={p:wedge(A,B[p]) for p in pairs}
        den,n=128**4*(96*8**4)*9,64
    out=add(*(wedge(K[p],middle[p]) for p in pairs))
    print('same singleton',same,'middle terms',sum(map(len,middle.values())),'chain terms',len(out))
    return out,den,n

def main():
    totals=Counter(); reps=Counter(); used=set()
    for comps in component_multisets():
        if sorted(map(len,comps))!=[2,6]:continue
        small,big=sorted(comps,key=len)
        got=classify(big)
        if got is None:continue
        a,k,same=got
        used.add(big)
        p,q,n=chain(same)
        pp=translate(p,lambda z:a ^ (((z&1)<<1)|((z&2)>>1)) if k else a^z)
        x=TERMS[small[0]][2][0]
        assert x==a^(1<<(1-k))
        coeff=F(n*top_product((pp,site(x))),q*9216*16)
        totals[same]+=coeff
        reps[same,coeff]+=1
    print('distinct components',len(used),'representatives',sorted(reps.items()))
    print('complete mixed-chain multisets',sum(reps.values()),'exact family sums',dict(totals),
          'exact sector',sum(totals.values()))
    assert len(used)==256
if __name__=='__main__':main()
