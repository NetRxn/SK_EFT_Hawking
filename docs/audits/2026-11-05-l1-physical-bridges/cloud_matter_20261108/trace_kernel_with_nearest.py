"""Known D/H plus trace covariance with evaluated nearest entries.
Opposite-site trace covariance is left as an explicit unknown coefficient.
"""
import io,json
from contextlib import redirect_stdout
from fractions import Fraction as F
import sympy as s
with redirect_stdout(io.StringIO()):
    import known_block_kernel as base
    import known_block_source_jets as jets
R=142570791678327415714294730219
NEAREST=F(12641461862400,1252309350145403)
NEAREST_HH=F(-68943355850864697134284800,R)

def trace_sigma(local,nearest,opposite):
    result=s.zeros(4)
    for x in range(4):
     for y in range(4):
        distance=x^y
        cov=local if distance==0 else opposite if distance==3 else nearest
        result-=base.rat(cov)*(base.V[x]*s.trace(base.H0*base.V[y])/2+base.V[x]*base.H0*base.V[y])
    assert result==result.T
    return result

known=-(base.rat(base.AD)/8+base.rat(base.AH)/2)*base.K0+trace_sigma(base.AT,NEAREST,F(0))
known_hh=-(base.rat(jets.rows['D'])/8+base.rat(jets.rows['H'])/2)*base.K0+trace_sigma(jets.rows['T'],NEAREST_HH,F(0))
unknown_coefficient=trace_sigma(F(0),F(0),F(1))
rows=[]
for n0 in range(2):
 for n1 in range(2):
    v=s.Matrix([(-1)**(n0*(x&1)+n1*(x>>1)) for x in range(4)])
    eig=lambda M:(v.T*M*v)[0]/4
    for M in (known,known_hh,unknown_coefficient):assert M*v==eig(M)*v
    rows.append({'n0':n0,'n1':n1,'K0':str(eig(base.K0)),
       'known_g2_squared_Sigma':str(eig(known)),
       'opposite_trace_coefficient':str(eig(unknown_coefficient)),
       'known_g2_squared_Sigma_second_h':str(eig(known_hh))})
assert rows[1]['known_g2_squared_Sigma']==rows[2]['known_g2_squared_Sigma']
assert rows[1]['known_g2_squared_Sigma_second_h']==rows[2]['known_g2_squared_Sigma_second_h']
print(json.dumps({'scope':'D/H and trace-only finite kernel; other active/mixed channels omitted',
 'equation':'g2²Sigma_p=known_p+coefficient_p*d+other omitted channels; d=g2²<Tx T(x xor3)>',
 'source_equation':'same coefficient multiplies unknown d_hh; displayed source contribution uses fixed bare coordinates',
 'nearest_time_equals_space':'explicit axes0/1,sitebit exchange plus internalPin symmetry',
 'momenta':rows},indent=2))
