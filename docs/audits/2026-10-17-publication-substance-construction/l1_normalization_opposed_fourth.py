"""Exact normalization sector for two opposite-site fourth powers."""
from collections import Counter
from itertools import product,combinations_with_replacement,permutations
from fractions import Fraction as F
from math import factorial,prod
from functools import cache
from l1_direct_b_haar import R,I,eye,zeros,diag,pauli,gamma,bilinear,add,scale,wedge
from l1_normalization_disjoint_sector import quat, adj
from l1_normalization_support import normalization_support, TERMS

# Integer coordinate representatives for 2 q; weights are 96 times exact.
zero=(0,)*4
axes=[tuple(2*int(i==j) for i in range(4)) for j in range(4)]
def nodes():
    for x in axes:
        yield x,zero,-16
        yield zero,x,-16
    for s in product((-1,1),repeat=3):
        x=(1,*s)
        yield x,zero,8
        yield zero,x,8
    for x,y,s in product(axes,axes,(-1,1)):
        yield x,tuple(s*z for z in y),3
tuples=list(combinations_with_replacement(range(4),4))

def fourth_T(direction):
    y=1<<direction
    out={a:{} for a in tuples}
    for l,r,w in nodes():
        U=diag(quat(l),quat(r)); Ud=diag(quat(adj(l)),quat(adj(r)))
        T=[add(bilinear(g*Ud,0,y),scale(bilinear(U*g,y,0),-1)) for g in gamma]
        P={(a,b):wedge(T[a],T[b]) for a in range(4) for b in range(a,4)}
        for a,b,c,d in tuples:
            out[a,b,c,d]=add(out[a,b,c,d],scale(wedge(P[a,b],P[c,d]),w))
    # T stored as 8×physical T (coordinate reps are doubled).
    return out

@cache
def vec_moment(q):
    cnt=Counter(q)
    if any(k%2 for k in cnt.values()):return F(0)
    if len(q)==0:return F(1)
    if len(q)==2:return F(2,9)
    if len(q)==4:return F(8,225)*(3 if len(cnt)==1 else 1)
    raise AssertionError(q)

def curv_coeff():
    emb=[diag(p,zeros(2)) for p in pauli]+[diag(zeros(2),p) for p in pauli]
    g5=diag(1,1,-1,-1)
    out={}
    for a,b in product(range(4),repeat=2):
        if a==b:out[a,b]=[]
        else:
            out[a,b]=[(j,int((-I*p*gamma[a]*gamma[b]*g5).trace()))
                      for j,p in enumerate(emb) if (-I*p*gamma[a]*gamma[b]*g5).trace()!=0]
    return out
L=curv_coeff()
@cache
def curv_moment(pairs):
    if any(not L[p] for p in pairs):return 0
    ans=F(0)
    for terms in product(*(L[p] for p in pairs)):
        left=tuple(i for i,_ in terms if i<3);right=tuple(i-3 for i,_ in terms if i>=3)
        ans+=vec_moment(left)*vec_moment(right)*prod(c for _,c in terms)
    ans*=2025
    assert ans.denominator==1
    return int(ans)

def main():
    allsites=[ii for ii in normalization_support() if sorted(Counter(ii).values())==[4,4]]
    assert len(allsites)==32
    for ii in allsites:
        labels=[TERMS[i][2] for i in set(ii)]
        assert all(k==2 and l==3 for x,k,l,u,v in labels)
        assert labels[0][0]^labels[1][0]==3
        assert labels[0][3] != labels[1][3]
        assert labels[0][4] != labels[1][4]
    A,B=fourth_T(0),fourth_T(1)
    out={}
    n=0
    for a in tuples:
        mult=factorial(4)//prod(factorial(k) for k in Counter(a).values())
        for b in tuples:
            if not A[a] or not B[b]:continue
            w=sum(curv_moment(tuple(sorted(zip(a,x)))) for x in set(permutations(b)))
            if w:
                p={m:c for m,c in wedge(A[a],B[b]).items() if m&255==255}
                out=add(out,scale(p,mult*w))
                n+=bool(p)
    def translate(mask):
        return sum(((mask>>(8*x))&255)<<(8*(x^3)) for x in range(4))
    opposite={translate(m):v for m,v in out.items()}
    top=(1<<32)-1
    raw=R.zero
    for m,v in out.items():
        q=m^top
        if q in opposite:raw+=wedge({m:v},{q:opposite[q]}).get(top,R.zero)
    assert raw.is_ground and raw.const().y==0
    denom=2025*96**2*8**8
    coefficient=F(int(raw.const().x),denom**2*factorial(4)**2)
    print('nonzero transport moment supports',sum(map(bool,A.values())),sum(map(bool,B.values())))
    print('nonempty weighted center contractions',n,'center polynomial support',len(out))
    print('opposed fourth raw',raw,'representative',coefficient,'whole sector',32*coefficient)
if __name__=='__main__':main()
