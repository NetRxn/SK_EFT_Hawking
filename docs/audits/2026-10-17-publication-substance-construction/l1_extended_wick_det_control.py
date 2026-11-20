"""Formal Wick determinant vs direct exterior coefficient for two actual coframe endpoints."""
from functools import cache
from fractions import Fraction
from itertools import product
from math import factorial
from sympy import Matrix,Poly,conjugate,diag,symbols
from l1_direct_b_haar import add,bilinear,gamma,scale,wedge
from l1_normalization_disjoint_sector import quat
J=symbols('j0:4',real=True)
U=diag(quat((0,1,0,0)),quat((0,0,1,0)))
Ud=U.adjoint()
T=[add(bilinear(g*Ud,0,1),scale(bilinear(U*g,1,0),-1)) for g in gamma]
C=Matrix([[2,3,-1,4],[3,-3,2,1],[-1,2,5,2],[4,1,2,7]])
H=diag(2,-2,0,0)
def action(K):
    return add(*(scale(wedge(T[i],T[j]),int(K[i,j]) if i!=j else int(K[i,i])//2)
                 for i in range(4) for j in range(i,4)))
# Double base covariance to keep the tracked Gaussian-integer exterior ring.
C=2*C
S,D=action(C),action(H)
A=sum((j*g*Ud for j,g in zip(J,gamma)),Matrix.zeros(4))
p=Poly(A.det()*conjugate(A.det()),*J)
@cache
def moment(indices):
    if not indices:return (1,0,0)
    out=[0]*3
    for j in range(1,len(indices)):
        a,b=indices[0],indices[j]
        w=moment(indices[1:j]+indices[j+1:])
        for k in range(3):
            out[k]+=int(C[a,b])*w[k]+(int(H[a,b])*w[k-1] if k else 0)
    return tuple(out)
wick=[0]*3
for powers,v in p.terms():
    indices=tuple(i for i,count in enumerate(powers) for _ in range(count))
    for k,w in enumerate(moment(indices)):
        wick[k]+=int(v)*w
expected=[]
for k in range(3):
    out={0:1}
    for _ in range(4-k):out=wedge(out,S)
    for _ in range(k):out=wedge(out,D)
    value=out[(1<<16)-1].const()
    assert value.y==0
    expected.append(Fraction(int(value.x),factorial(4-k)*factorial(k)))
assert wick==expected
assert wick[2] and wick[0]
print('determinant monomials',len(p.terms()),'matching coefficients',wick)
