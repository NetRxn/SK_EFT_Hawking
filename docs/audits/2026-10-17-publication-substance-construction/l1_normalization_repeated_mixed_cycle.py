from collections import Counter,defaultdict
from functools import cache
from itertools import product,combinations_with_replacement
from fractions import Fraction as F
import numpy as np
from scipy.sparse import coo_matrix
from l1_normalization_uniform_mixed_edge import t_basis,unit,moment
from l1_normalization_uniform_mixed_trace import multiply,trace4
from l1_normalization_correlated_contract import open_basis
from l1_normalization_shared_transport import TERMS,component_multisets
from l1_direct_b_haar import haar_moment
from l1_direct_a_haar import mul,adj
from l1_normalization_transport_cycle import poly_int,wedge_sign
from l1_normalization_mixed_cycle import plus

def cases():
    ans=Counter()
    for comps in component_multisets():
        ii=[i for g in comps for i in g]
        ts=[TERMS[i][2] for i in sorted(set(ii))]
        if len(ts)!=4 or set(Counter(ii).values())!={2}:continue
        if len({x for x,k,l,u,v in ts})!=4 or len({l for x,k,l,u,v in ts})!=1:continue
        xk={x:k for x,k,l,u,v in ts}
        if any(k>=2 for k in xk.values()):continue
        if xk[0]==xk[3] and xk[1]==xk[2] and xk[0]!=xk[1]:
            assert max(map(len,comps))==8
            ans[ts[0][2],xk[0]]+=1
    assert ans=={(2,0):16,(2,1):16,(3,0):16,(3,1):16}
    return ans

@cache
def p_coeff(alpha,a,b,closed_order=False):
    ch,v=divmod(alpha,3)
    X,Y=unit(a%4),unit(b%4)
    out=Counter()
    for i,j in product(range(4),repeat=2):
        q = (mul(mul(adj(X), adj(unit(i))), mul(Y, unit(j)))
             if closed_order else mul(mul(unit(i),Y),mul(adj(unit(j)),adj(X))))
        out[tuple(sorted((4*ch+i,4*ch+j)))]+=q[v+1]
    return tuple((z,w) for z,w in out.items() if w)

@cache
def qmoment(word):
    n=Counter(word);e=tuple(n[i] for i in range(8))
    return haar_moment(e[:4])*haar_moment(e[4:])

@cache
def projection(word):
    p=Counter(word)
    odd=[i for i,n in p.items() if n%2]
    out={}
    choices=([(i,i) for i in range(8)] if not odd
             else [tuple(odd),tuple(odd[::-1])] if len(odd)==2 else [])
    for i,j in choices:
        w=192*qmoment(tuple(sorted(word+(i,j))))
        if i==j:w+=48*qmoment(word)
        assert w.denominator==1
        if w:out[i,j]=int(w)
    return tuple(out.items())

@cache
def raw_edge_projection(a,b,x,y,closed_order=False):
    weights=Counter()
    for i,p in p_coeff(a,x[0],y[0],closed_order):
        for j,q in p_coeff(b,x[1],y[1],closed_order):
            for ij,w in projection(tuple(sorted(i+j))):
                weights[ij]+=p*q*w
    return tuple((k,z) for k,z in weights.items() if z)

@cache
def tt(i,j,p,q):
    from l1_direct_b_haar import wedge
    return poly_int(wedge(t_basis(i)[1][p],t_basis(j)[1][q]))

@cache
def edge(closed_order=False):
    out={}
    pairs=tuple(combinations_with_replacement(range(4),2))
    for a,b in combinations_with_replacement(range(6),2):
        xch,ych=a//3,b//3
        coord=tuple(product(range(4*xch,4*xch+4),range(4*ych,4*ych+4)))
        for x,y in product(coord,repeat=2):
            terms=raw_edge_projection(a,b,x,y,closed_order)
            if not terms:continue
            X,Y=tuple(sorted(x)),tuple(sorted(y))
            for p,q in pairs:
                for (i,j),w in terms:
                    for mask,(r,s) in tt(i,j,p,q).items():
                        A=((a,b),X,mask&255)
                        B=((p,q),Y,mask>>8)
                        plus(out,(A,B),w*r,w*s)
    return {k:v for k,v in out.items() if any(v)}

def parity(w):
    return (1<<w[0])^(1<<w[1])

def assemble(closed_order=False):
    E=edge(closed_order)
    a_labels=sorted({A for A,B in E})
    b_labels=sorted({B for A,B in E})
    ids=[{v:i for i,v in enumerate(rows)} for rows in (a_labels,b_labels)]
    local=defaultdict(dict)
    for (p,ab),q in open_basis(0).items():
        for m,(r,s) in poly_int(q).items():plus(local[tuple(sorted(p)),ab],m,r,s)
    groups=defaultdict(list)
    for a in a_labels:groups[parity(a[1])].append(a)
    V={}
    for B in b_labels:
        p,Y,m=B
        for A in groups[parity(Y)]:
            ab,X,n=A
            if m&n:continue
            z=local.get((p,ab),{}).get(255^(m|n))
            if not z:continue
            w=moment(*X,*Y)*wedge_sign(m,n)*wedge_sign(m|n,255^(m|n))
            plus(V,(B,A),w*z[0],w*z[1])
    def csr(m,i,j):
        rr=[(ids[i][a],ids[j][b],r,s) for (a,b),(r,s) in m.items()]
        p,q,r,s=map(np.array,zip(*rr))
        out=tuple(coo_matrix((x,(p,q)),shape=(len(ids[i]),len(ids[j])),dtype=np.int64).tocsr() for x in (r,s))
        for x in out:x.eliminate_zeros()
        return out
    A,B=csr(E,0,1),csr(V,1,0)
    print('boundary dims',len(a_labels),len(b_labels),'edge nnz',tuple(x.nnz for x in A),
          'vertex nnz',tuple(x.nnz for x in B),flush=True)
    return A,B

def run(closed_order=False):
    print('checkerboard repeated mixed census',cases(),flush=True)
    E,V=assemble(closed_order)
    T=multiply(E,V)
    z=trace4(T)
    # E joint/split moment denominator 192, two raw T factors /16.
    # V singleton-local T pair denominator 128 and common singleton
    # quartic moment denominator 48. 16 endpoint choices already summed;
    # four symmetry-related plane assignments and 2!^4 from repeats.
    den=(192*16*128*48)**4*16
    out=tuple(F(4*x,den) for x in z)
    print('raw exact Gaussian trace',z,'64-case checkerboard sector',out,flush=True)


if __name__ == "__main__":
    from argparse import ArgumentParser

    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--closed", action="store_true")
    args = parser.parse_args()
    run(args.closed)
