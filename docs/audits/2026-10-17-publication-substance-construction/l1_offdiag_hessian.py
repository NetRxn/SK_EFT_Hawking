from fractions import Fraction
from itertools import product
from l1_direct_b_haar import (
    R,TOP,I,diag,eye,zeros,pauli,gamma,embeddings,add,scale,wedge,bilinear,
    build_response,average,difference_moment,haar_moment,
)


def compute():
    def quaternion(a):
        return a[0]*eye(2)-I*sum((a[j+1]*p for j,p in enumerate(pauli)),zeros(2))

    def dagger(a):
        return quaternion((a[0],*(-v for v in a[1:])))

    l,r=R.symbols[:4],R.symbols[4:]
    C=diag(quaternion(l),quaternion(r))
    Cd=diag(dagger(l),dagger(r))
    t0=[add(bilinear(g*C,0,1),scale(bilinear(Cd*g,1,0),-1)) for g in gamma]
    t1=[add(bilinear(C*g,0,1),scale(bilinear(g*Cd,1,0),-1)) for g in gamma]
    axial=[[bilinear(g*p+p*g,0,0) for p in embeddings] for g in gamma]
    K=[[scale(add(*(wedge(a,b) for a,b in zip(row,col))),-1)
        for col in axial] for row in axial]
    source_sq=add(*(wedge(wedge(t0[c],t0[d]),K[c][d])
                    for c,d in product(range(4),repeat=2)))
    action_sq=build_response(1,t1,direct=True)
    top=wedge(source_sq,action_sq).get(TOP,R.zero)
    # As in the direct B reference, each local polynomial carries 256,
    # and direct curvature carries an additional 9 at site 1.
    avg=average(top,difference_moment)/9
    print("source-square/action-square populations",len(source_sq),len(action_sq),"top monomials",len(top))
    print("one complementary contraction",avg)
    result=Fraction(3,2)*avg
    print("Z_HH coefficient / g2^2",result,"log Z_HH * g2^2",result/3366)
    poison=Fraction(3,2)*average(top,haar_moment)/9
    print("endpoint poison coefficient",poison)
    assert result != poison
    assert result == Fraction(3,2)*average(top,difference_moment)/9

if __name__=='__main__':
    compute()
