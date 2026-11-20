"""Exact contribution from the link-disjoint transport-square sector."""
from itertools import product
from fractions import Fraction as F
from l1_direct_b_haar import R,I,eye,zeros,diag,pauli,gamma,bilinear,add,scale,wedge
from l1_normalization_support import normalization_support, TERMS

def quat(q):
    return q[0]*eye(2)-I*sum((p*x for p,x in zip(pauli,q[1:])),zeros(2))
def adj(q):
    return (q[0],*(-x for x in q[1:]))
def pair(x,d):
    """8 times the second moment of raw (4 T) in both gamma slots."""
    y=x^(1<<d)
    K=[[{} for _ in range(4)] for _ in range(4)]
    for j,s in product(range(4),(-1,1)):
        l=[int(k==j) for k in range(4)]
        r=[s*z for z in l]
        U=diag(quat(l),quat(r))
        Ud=diag(quat(adj(l)),quat(adj(r)))
        T=[add(bilinear(g*Ud,x,y),scale(bilinear(U*g,y,x),-1)) for g in gamma]
        for a,b in product(range(4),repeat=2):
            K[a][b]=add(K[a][b],wedge(T[a],T[b]))
    return K

def site(x):
    K,L=pair(x,0),pair(x,1)
    A=add(*(wedge(K[a][a],L[b][b]) for a,b in product(range(4),repeat=2)))
    B=add(*(wedge(K[a][b],L[b][a]) for a,b in product(range(4),repeat=2)))
    return add(A,scale(B,-1))

def disjoint_sector():
    for indices in normalization_support():
        distinct = set(indices)
        if len(distinct) != 4 or any(indices.count(i) != 2 for i in distinct):
            continue
        labels = [TERMS[i][2] for i in distinct]
        if {label[:3] for label in labels} != {(x, 2, 3) for x in range(4)}:
            continue
        if len({u for _, _, _, u, _ in labels}) == 4 and len(
                {v for _, _, _, _, v in labels}) == 4:
            yield indices


def main():
    sector = list(disjoint_sector())
    assert len(sector) == 16
    fs=[site(x) for x in range(4)]
    f01,f23=wedge(fs[0],fs[1]),wedge(fs[2],fs[3])
    raw=R.zero
    top=(1<<32)-1
    for u,v in f01.items():
        w=u^top
        if w in f23:
            raw=raw+wedge({u:v},{w:f23[w]}).get(top,R.zero)
    assert raw.is_ground and raw.const().y==0
    # Per-site scale (16/9 from curvature)/(8^2 * 4^4) = 1/9216.
    raw=int(raw.const().x)
    coefficient=F(raw,9216**4*2**4)
    print('site supports',list(map(len,fs)),'half supports',len(f01),len(f23),'integer top',raw)
    print('representative with exponent factorials',coefficient,'complete sector',len(sector)*coefficient)
if __name__=='__main__':main()
