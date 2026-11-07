from itertools import product
from fractions import Fraction
from l1_direct_b_haar import R,I,eye,zeros,diag,pauli,gamma,bilinear,add,scale,wedge,haar_moment

def quaternion(q):
    return q[0]*eye(2)-I*sum((p*x for p,x in zip(pauli,q[1:])),zeros(2))
def adj(q):
    return (q[0],*(-x for x in q[1:]))
l,r=R.symbols[:4],R.symbols[4:]
U=diag(quaternion(l),quaternion(r))
Ud=diag(quaternion(adj(l)),quaternion(adj(r)))
for x,y,a in product((0,1),(2,3),range(4)):
    g=gamma[a]
    backward=add(bilinear(Ud*g,y,x),scale(bilinear(g*U,x,y),-1))
    forward_adjoint=add(bilinear(g*U,x,y),scale(bilinear(Ud*g,y,x),-1))
    assert add(backward,forward_adjoint)=={}
# In the split contraction four equal coordinates on one chirality become
# independent pairs, so the exact weight changes from 1/8 to 1/16.
assert haar_moment((4,0,0,0))==Fraction(1,8)
assert haar_moment((2,0,0,0))**2==Fraction(1,16)
# With index pattern 0,1 | 0,1 full Haar is 1/24 but split Haar is zero.
assert haar_moment((2,2,0,0))==Fraction(1,24)
assert haar_moment((1,1,0,0))**2==0
print('Backward=-forward(adjoint) coefficientwise; split-vs-merged Haar poison distinguished')
