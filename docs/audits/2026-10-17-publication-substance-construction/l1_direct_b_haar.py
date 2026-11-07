from collections import defaultdict
from functools import cache
from fractions import Fraction
from itertools import product
from math import comb, prod
from time import perf_counter

from sympy import I, Matrix, diag, eye, zeros
from sympy.polys.domains import ZZ_I
from sympy.polys.rings import ring
from l1_reduced_wedge_reference import wedge_sign
from l1_direct_a_haar import haar_moment

R,*q=ring("l0,l1,l2,l3,r0,r1,r2,r3",ZZ_I)
ORDER=16
TOP=(1<<ORDER)-1
pauli=[Matrix([[0,1],[1,0]]),Matrix([[0,-I],[I,0]]),diag(1,-1)]
gamma=[zeros(2).row_join(-I*p).col_join((I*p).row_join(zeros(2))) for p in pauli]
gamma.append(zeros(2).row_join(eye(2)).col_join(eye(2).row_join(zeros(2))))
embeddings=[diag(p,zeros(2)) for p in pauli]+[diag(zeros(2),p) for p in pauli]


def add(*terms):
    out=defaultdict(lambda:R.zero)
    for poly in terms:
        for word,coef in poly.items():
            out[word]+=coef
    return {word:coef for word,coef in out.items() if coef}


def scale(poly, factor):
    return {word:coef*factor for word,coef in poly.items()}


def wedge(left,right):
    out=defaultdict(lambda:R.zero)
    for a,x in left.items():
        for b,y in right.items():
            if not a&b:
                out[a|b]+=x*y*wedge_sign(a,b)
    return {word:coef for word,coef in out.items() if coef}


def bilinear(matrix, bar, psi):
    out={}
    for i,j in product(range(4),repeat=2):
        expr=matrix[i,j].expand()
        if expr:
            left=1<<(8*bar+i)
            right=1<<(8*psi+4+j)
            out[left|right]=R.from_expr(expr)*wedge_sign(left,right)
    return out


def direct_curvature_covariance():
    gamma5=diag(1,1,-1,-1)
    l={}
    for c,d in product(range(4),repeat=2):
        antisymmetric=(gamma[c]*gamma[d]-gamma[d]*gamma[c])/2
        l[c,d]=tuple((-I*p*antisymmetric*gamma5).trace() for p in embeddings)
    return {
        (c,d,e,f):Fraction(int(2*sum(a*b for a,b in zip(l[c,d],l[e,f]))),9)
        for c,d,e,f in product(range(4),repeat=4)
    }


CURVATURE=direct_curvature_covariance()


def build_response(x, transport, *, direct):
    axial=[[bilinear(g*p+p*g,x,x) for p in embeddings] for g in gamma]
    K=[[scale(add(*(wedge(a,b) for a,b in zip(row,col))),-1)
        for col in axial] for row in axial]
    if direct:
        # Multiply by 9 to retain an integral coefficient ring.
        return add(*(scale(wedge(wedge(transport[c],transport[e]),K[d][f]),int(moment*9))
                     for (c,d,e,f),moment in CURVATURE.items() if moment))
    G=add(*(wedge(t,t) for t in transport))
    trace=add(*(K[d][d] for d in range(4)))
    second=add(*(wedge(wedge(transport[c],transport[e]),K[c][e])
                 for c,e in product(range(4),repeat=2)))
    return add(wedge(G,trace),scale(second,-1))


def response_polynomial(*, direct=False):
    l=R.symbols[:4]
    r=R.symbols[4:]
    quaternion=lambda a:a[0]*eye(2)-I*sum((a[j+1]*p for j,p in enumerate(pauli)),zeros(2))
    dagger=lambda a:quaternion((a[0],*(-v for v in a[1:])))
    C=diag(quaternion(l),quaternion(r))
    Cd=diag(dagger(l),dagger(r))
    t0=[add(bilinear(g*C,0,1),scale(bilinear(Cd*g,1,0),-1)) for g in gamma]
    t1=[add(bilinear(C*g,0,1),scale(bilinear(g*Cd,1,0),-1)) for g in gamma]
    r0,r1=build_response(0,t0,direct=direct),build_response(1,t1,direct=direct)
    top=wedge(r0,r1).get(TOP,R.zero)
    print("R0/R1 wedge populations",len(r0),len(r1),"top C monomials",len(top))
    assert all(sum(exponents)==4 for exponents in top)
    return top


@cache
def difference_moment(powers):
    # C=A†−B; conjugation preserves independent normalized Haar, but each
    # four-component factor uses the joint sphere moment.
    value=Fraction(0)
    for a in product(*(range(p+1) for p in powers)):
        b=tuple(p-k for p,k in zip(powers,a))
        value+=(-1)**sum(b)*prod(comb(p,k) for p,k in zip(powers,a))*haar_moment(a)*haar_moment(b)
    return value


def average(polynomial,moment):
    value=Fraction(0)
    for exponents,coeff in polynomial.items():
        assert coeff.y==0
        value+=int(coeff.x)*moment(exponents[:4])*moment(exponents[4:])
    return value/(256**2)


def main():
    start=perf_counter()
    top=response_polynomial()
    result=average(top,difference_moment)
    assert result==Fraction(999,16)
    B=Fraction(64,9)*result
    assert B==444
    raw_top=response_polynomial(direct=True)
    assert raw_top == 16**2*top
    raw=average(raw_top,difference_moment)/9**2
    assert Fraction(9,4)*raw == B
    print("direct 4-index curvature and transverse contraction average",raw,"× 9/4 =",B)
    # Distinct endpoint poison: setting B=0 uses one normalized endpoint
    # instead of a difference of two independent endpoints in each sector.
    wrong=average(top,haar_moment)
    assert wrong!=result
    assert average(top,difference_moment)==result
    print("exact Haar average",result,"B contribution",B)
    print("one endpoint omitted",wrong,"vs",result,"clean repeat PASS")
    print("elapsed seconds",round(perf_counter()-start,4))


if __name__=="__main__":
    main()
