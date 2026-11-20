from fractions import Fraction
from itertools import product
from l1_direct_b_haar import R,I,eye,zeros,diag,pauli,gamma,embeddings,bilinear,add,scale,wedge,haar_moment
T=255
axial=[[bilinear(g*p+p*g,0,0) for p in embeddings] for g in gamma]
K=[[scale(add(*(wedge(a,b) for a,b in zip(row,col))),-1)
    for col in axial] for row in axial]
def top(v):
    c=v.get(T,R.zero)
    assert c.is_ground
    return Fraction(int(c.const().x),256)
def average(v):
    p=v.get(T,R.zero)
    assert all(c.y==0 for c in p.values())
    return sum(Fraction(int(c.x),256)*haar_moment(e[:4])*haar_moment(e[4:]) for e,c in p.items())
def block(q):
    return q[0]*eye(2)-I*sum((p*x for p,x in zip(pauli,q[1:])),zeros(2))
def adj(q):
    return (q[0],*(-x for x in q[1:]))
l,r=R.symbols[:4],R.symbols[4:]
U=diag(block(l),block(r))
Ud=diag(block(adj(l)),block(adj(r)))
t=[bilinear(g*(Ud-U)+(Ud-U)*g,0,0) for g in gamma]
G=add(*(wedge(x,x) for x in t))
hsq=top(add(*(wedge(K[c][d],K[c][d]) for c,d in product(range(4),repeat=2))))
g4=average(wedge(G,G))
trace=add(*(K[c][c] for c in range(4)))
g22=top(wedge(trace,trace))
dsq=2*(g4-g22)
print('H^2, Gjj^2, Gjj Gkk, D^2:',hsq,g4,g22,dsq)
for n,v in [('H',hsq),('D',dsq)]:
    raw=54*v
    print(n,'Z_HH coefficient / g2^2',raw,'log Z_HH * g2^2',raw/3366)
from functools import cache
@cache
def cubature(e):
    axis = sum(Fraction(prod**k, 24)
        for j in range(4) for prod in (-1,1) for k in [e[j]]
        if all(e[i]==0 for i in range(4) if i!=j))
    cube = sum(Fraction((-1)**sum(k for k,s in zip(e,signs) if s),
                        24*2**sum(e))
               for signs in product((0,1),repeat=4))
    return axis+cube
poly=wedge(G,G)[T]
alternative=sum(Fraction(int(c.x),256)*cubature(e[:4])*cubature(e[4:])
                for e,c in poly.items())
assert all(sum(e[:4])<=4 and sum(e[4:])<=4 for e in poly)
assert alternative==g4==Fraction(75,2)
wrong_t=[bilinear(g*U-Ud*g,0,0) for g in gamma]
wrong_G=add(*(wedge(x,x) for x in wrong_t))
assert average(wedge(wrong_G,wrong_G))==Fraction(15,4)!=g4
print('Sphere degree-four cubature',alternative,'collapsed-endpoint formula poison',average(wedge(wrong_G,wrong_G)))
