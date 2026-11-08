"""Exact algebra controls only: synthetic signed ensemble, NOT L1 coefficients."""
import sympy as s
R=s.Rational
j=s.symbols('j', real=True)
K=s.Matrix([[3+j, R(1,3)], [R(1,3), 2+j*j]])
V=[s.Matrix([[1,j+1],[j+1,-1]]),s.Matrix([[0,2],[2,1+j]])]
W=[[s.Matrix([[1,0],[0,2]]),s.Matrix([[0,1],[1,0]])],
   [s.Matrix([[0,1],[1,0]]),s.Matrix([[2,1],[1,-1]])]]
qs=[(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1)]
weights=[1+j,1+j,-1,-1,2,2]
Z=sum(weights)
def avg(xs):
    z=s.zeros(*xs[0].shape) if isinstance(xs[0],s.MatrixBase) else 0
    return sum((w*x for w,x in zip(weights,xs)),z)/Z
H=K.inv()
A=s.Matrix(2,2,lambda a,b:avg([q[a]*q[b] for q in qs]))
T=[[W[a][b]-V[a]*s.trace(H*V[b])/2-V[a]*H*V[b] for b in range(2)] for a in range(2)]
Sigma=sum((A[a,b]*T[a][b] for a in range(2) for b in range(2)),s.zeros(2))
# Independent normalized determinant/inverse expansion, evaluated exactly at j=0.
K0=K.subs(j,0); H0=K0.inv(); vs=[v.subs(j,0) for v in V]
p=[s.sympify(w).subs(j,0)/s.sympify(Z).subs(j,0) for w in weights]
k1=[sum((vs[a]*q[a] for a in range(2)),s.zeros(2)) for q in qs]
k2=[sum((W[a][b]*q[a]*q[b] for a in range(2) for b in range(2)),s.zeros(2)) for q in qs]
r1=[-s.trace(H0*x)/2 for x in k1]
r2=[-s.trace(H0*y)/2+s.trace(H0*x*H0*x)/4+r*r/2 for x,y,r in zip(k1,k2,r1)]
c1=[-H0*x*H0 for x in k1]
c2=[H0*x*H0*x*H0-H0*y*H0 for x,y in zip(k1,k2)]
def E(xs):
    z=s.zeros(*xs[0].shape) if isinstance(xs[0],s.MatrixBase) else 0
    return sum((w*x for w,x in zip(p,xs)),z)
C1=E(c1)+H0*E(r1)-H0*E(r1)
C2=E([c+r*b+r2i*H0 for c,r,b,r2i in zip(c2,r1,c1,r2)])-H0*E(r2)
assert C1==s.zeros(2)
assert (-K0*C2*K0-Sigma.subs(j,0)).applyfunc(s.simplify)==s.zeros(2)
for a in range(2):
    mean1=E([s.Integer(q[a])*r for q,r in zip(qs,r1)])
    prediction=-sum(A[a,b].subs(j,0)*s.trace(H0*vs[b])/2 for b in range(2))
    assert s.simplify(mean1-prediction)==0
# Full source product rules, including source-dependent normalized weights.
for order in [1,2]:
    expected=sum((sum((s.binomial(order,k)*s.diff(A[a,b],j,k)*T[a][b].diff(j,order-k) for k in range(order+1)),s.zeros(2)) for a in range(2) for b in range(2)),s.zeros(2))
    assert (Sigma.diff(j,order).subs(j,0)-expected.subs(j,0)).applyfunc(s.simplify)==s.zeros(2)
assert (H.diff(j)+H*K.diff(j)*H).subs(j,0).applyfunc(s.simplify)==s.zeros(2)
assert (H.diff(j,2)-2*H*K.diff(j)*H*K.diff(j)*H+H*K.diff(j,2)*H).subs(j,0).applyfunc(s.simplify)==s.zeros(2)
# Metric density Taylor expansion, with noncommuting positive body and Q.
t=s.symbols('t'); g=s.Matrix([[2,1],[1,3]]); q=s.Matrix([[1,2],[2,-1]])
B=g.inv(); rho=s.sqrt(g.det()); tr=s.trace(B*q)
F2=rho*((tr**2/8-s.trace(B*q*B*q)/4)*B-tr*B*q*B/2+B*q*B*q*B)
F=s.sqrt((g+t*q).det())*(g+t*q).inv()
assert (F.diff(t,2).subs(t,0)/2-F2).applyfunc(s.simplify)==s.zeros(2)
print('PASS: determinant-normalized second-order kernel; induced mean; first/second full-source product rules; inverse-kernel source jets; ordered metric density Taylor coefficient.')
print('Synthetic signed ensemble Sigma(0) =',Sigma.subs(j,0))
print('Synthetic Sigma_prime(0) =',Sigma.diff(j).subs(j,0).applyfunc(s.simplify))
print('Synthetic Sigma_second(0) =',Sigma.diff(j,2).subs(j,0).applyfunc(s.simplify))
print('NOT a calculation of L1 A_ij, positivity, continuum locality, or a physical propagation cone.')
