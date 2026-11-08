"""Exact h-second source response of the identifiable partial scalar block.
Fixed bare coordinates and uniform A=exp(hP/2), P=diag(0,0,1,-1)/sqrt2.
Scalar vertices are exactly h-independent on the collapsed fixed regulator.
"""
import io,json
from contextlib import redirect_stdout
from fractions import Fraction as F
import sympy as s
with redirect_stdout(io.StringIO()):
    import known_block_kernel as body
Z8=F(1252309350145403,2123366400)
Wjj=F(954400425849600,113846304558673)
rows={}
for name,raw,raw_jj in [('D',F(10179913,32),F(1570968)),
                       ('H',F(17419143,128),F(673272)),
                       ('T',F(31250131,16),F(9650232))]:
    rows[name]=(raw_jj/Z8-raw/Z8*Wjj)/8
assert rows['D']==F(-33115793931313683139185868800,142570791678327415714294730219)
blind=-(body.rat(rows['D'])/8+body.rat(rows['H'])/2)*body.K0
trace=-body.rat(rows['T'])*sum((vx*s.trace(body.H0*vx)/2+vx*body.H0*vx for vx in body.V),s.zeros(4))
Sigma_hh=blind+trace
momenta=[]
for n0 in range(2):
 for n1 in range(2):
    v=s.Matrix([(-1)**(n0*(x&1)+n1*(x>>1)) for x in range(4)])
    eigen=(v.T*Sigma_hh*v)[0]/4
    assert Sigma_hh*v==eigen*v
    momenta.append({'n0':n0,'n1':n1,'g2_squared_partial_Sigma_second_h':str(eigen)})
print(json.dumps({'scope':'second h derivative of partial Sigma at lambda0 expansion; not full source response',
 'source':'fixed bareD,H,T; A=exp(jE),h=2sqrt2*j; full actioncontact and denominator response included',
 'g2_squared_local_variance_second_h':{k:str(v) for k,v in rows.items()},
 'first_derivative_this_block':0,'momenta':momenta},indent=2))
