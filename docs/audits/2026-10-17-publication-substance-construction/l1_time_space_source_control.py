"""Exact source-only 2x2x1x1 support and connected-response control."""
from fractions import Fraction as F
from itertools import product
from sympy import Rational, diff, expand, log, symbols
from l1_transverse_top import hsq, dsq, g4, g22

# Each G_tt insertion gives 2 generators per time endpoint.
# Each TT cross insertion gives 4 at its own site; odd source powers
# vanish by independent transverse center flips.
survivors = [(a,h,k) for a,h,k in product(range(5),repeat=3)
             if 2*a+4*h==8 and 2*a+4*k==8 and h%2==0 and k%2==0]
assert survivors == [(0,2,2),(4,0,0)]
t,s,h,k,b,d,e=symbols('t s h k b d e', real=True)
u,v=t+s,t-s
q=(6477*u**4-522*u**2*v**2+45*v**4)/512
local=(g4+g22)*b**2+dsq*d**2/2+hsq*e**2/2
assert expand(local)==(129*b*b+21*d*d+9*e*e)/2
anchor=local.subs({b:1,d:0,e:0})
active=q+hsq**2*h*h*k*k/4
z=active*anchor**2
at={t:1,s:1,h:0,k:0}
assert z.subs(at)>0
assert diff(log(z),h,k).subs(at)==0
assert diff(log(z),h,2).subs(at)==0
cross4=diff(log(z),h,2,k,2).subs(at)
assert cross4==Rational(864,2159)
# Removing time-spanning sources and using local trace anchors on all sites
# gives a finite normalization and exact decoupling for all mixed derivatives.
factorized=(anchor+hsq*h*h/2)*(anchor+hsq*k*k/2)*anchor**2
assert diff(log(factorized),h,2,k,2).subs(at)==0
assert diff(log(factorized),h,2).subs(at)==Rational(6,43)
print('source support',survivors)
print('time source active column at t=s=1:',active.subs({t:1,s:1}))
print('time-separated TT derivatives: (1,1)=0; (2,2)=',cross4)
print('four-site local trace control: (1,1)=(2,2)=0, local (2,0)=6/43')
