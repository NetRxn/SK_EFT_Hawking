"""Exact partial Sigma from D²,H² and coincident T covariance at unit mass.
This identifiable additive block omits off-site T and all other active/mixed data.
"""
from fractions import Fraction as F
import sympy as s
import json
Z8=F(1252309350145403,2123366400)
AD=F(10179913,32)/Z8
AH=F(17419143,128)/Z8
AT=F(31250131,16)/Z8
rat=lambda x:s.Rational(x.numerator,x.denominator)
local=[]
for x in range(4):
    site=s.zeros(4,1);site[x]=1
    Kx=site*site.T
    for neighbor in (x^1,x^2):
        d=s.zeros(4,1);d[neighbor]=1;d[x]=-1
        Kx+=d*d.T
    local.append(Kx)
K0=sum(local,s.zeros(4));H0=K0.inv()
V=[Kx/2 for Kx in local]
assert all(s.trace(H0*vx)==s.Rational(1,2) for vx in V)
# T only: rho=sqrt[(1+lambda*T/2)^2]=1+lambda*T/2 near0,
# Factive=rho*I, so W_TT=0. All other channels are held separate.
contact=s.zeros(4)
determinant=-rat(AT)*sum((vx*s.trace(H0*vx)/2 for vx in V),s.zeros(4))
fluctuation=-rat(AT)*sum((vx*H0*vx for vx in V),s.zeros(4))
blind=-(rat(AD)/8+rat(AH)/2)*K0
Sigma=blind+contact+determinant+fluctuation
rows=[]
for n0 in range(2):
 for n1 in range(2):
    v=s.Matrix([(-1)**(n0*(x&1)+n1*(x>>1)) for x in range(4)])
    eig=lambda M:(v.T*M*v)[0]/4
    vals={'K0':eig(K0),'blind_DH':eig(blind),'T_determinant':eig(determinant),'T_fluctuation':eig(fluctuation),'known_block':eig(Sigma)}
    assert Sigma*v==vals['known_block']*v
    vals['known_block_over_K0']=vals['known_block']/vals['K0']
    rows.append({'n0':n0,'n1':n1,**{k:str(v) for k,v in vals.items()}})
assert rows[1]['known_block_over_K0']==rows[2]['known_block_over_K0']
assert rows[0]['known_block_over_K0']!=rows[1]['known_block_over_K0']
print(json.dumps({'scope':'partial Sigma times g2²; unit mass/spacing/weights; no full or physical conclusion',
 'unavailable':'offsite active covariance, other active and local/mixed channels, source jets',
 'momenta':rows},indent=2))
