"""Compare shared-link quartic cubature with symbolic Haar moments."""
from fractions import Fraction as F
from l1_normalization_six_transport import (
    shared_moment,quat,adj,R,diag,gamma,bilinear,add,scale,wedge,
)
from l1_direct_b_haar import haar_moment
x,y=0,1
l,r=R.symbols[:4],R.symbols[4:]
U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
A=[add(bilinear(g*Ud,x,y),scale(bilinear(U*g,y,x),-1)) for g in gamma]
B=[add(bilinear(Ud*g,x,y),scale(bilinear(g*U,y,x),-1)) for g in gamma]
h=shared_moment(0,0)
counts=[]
for p,q in [((0,0),(0,0)),((0,1),(2,3)),((0,2),(0,2))]:
    actual=h[p,q]
    expected=wedge(wedge(A[p[0]],A[p[1]]),wedge(B[q[0]],B[q[1]]))
    for m in set(actual)|set(expected):
        re=im=F(0)
        for ex,c in expected.get(m,{}).items():
            w=haar_moment(ex[:4])*haar_moment(ex[4:])
            re+=int(c.x)*w; im+=int(c.y)*w
        a=actual.get(m,R.zero).const()
        # Raw T on symbolic unit q is 4T, raw T on nodes 8T.
        assert (re,im)==(F(int(a.x),96*2**4),F(int(a.y),96*2**4))
    counts.append((p,q,len(actual),len(expected)))
print('forward/backward shared quartic direct moment comparison',counts)
