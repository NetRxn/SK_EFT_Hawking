"""Bounded bare closed-L1 plus contribution; not the complete L1 kernel.
Input coefficients are reused accepted Haar results at scientific pin864f4ec.
This exact arithmetic/Taylor check is not a fresh full Haar evaluation.
"""
from fractions import Fraction as F
import json
import sympy as s

Z8=F(1252309350145403,2123366400)
raw_same=F(10179913,32)
raw_diag=F(-1171,1024)
coefficient=-raw_same/(8*Z8)  # multiplies lambda^2/g2^2 and all K0(p)
assert coefficient<0
# At fixed D, G=diag(0,0,D/2,-D/2). Scalar derivatives 2,3 vanish.
l,D=s.symbols('lambda D', real=True)
G=s.diag(0,0,D/2,-D/2)
M=s.eye(4)+l*G
rho=s.sqrt(M.det())
for expr in [rho, rho*M.inv()[0,0], rho*M.inv()[1,1]]:
    assert s.diff(expr,l).subs(l,0)==0
    assert s.diff(expr,l,2).subs(l,0)/2 == -D**2/8
# Build each local stiffness matrix explicitly. Independent site D_x coordinates
# have W_(D_x D_x)=-K_local_x/8, not the entire K0 at each site.
K_body=s.zeros(4)
local=[]
for x in range(4):
    site=s.zeros(4,1); site[x]=1
    K_x=site*site.T  # unit mass term
    for neighbor in (x^2,x^1):
        difference=s.zeros(4,1); difference[neighbor]=1; difference[x]=-1
        K_x += difference*difference.T
    local.append(K_x); K_body+=K_x
Sigma_site_sum=sum((-s.Rational(raw_same.numerator,raw_same.denominator)
                    /s.Rational(Z8.numerator,Z8.denominator)*K_x/8
                    for K_x in local),s.zeros(4))
assert Sigma_site_sum==s.Rational(coefficient.numerator,coefficient.denominator)*K_body
assert sorted(K_body.eigenvals().items())==[(1,1),(5,2),(9,1)]
# Exact finite 2x2 lattice forward-difference body, mass=spacing=weights=1.
# Uniform same-site covariance makes <K2>=coefficient*K0/g2^2.
# V_D=0 identically, so both determinant-linear and VHV terms vanish.
momenta=[]
for nt in range(2):
    for nx in range(2):
        K0=F(1+4*nt+4*nx)
        Sigma=coefficient*K0
        assert Sigma/K0 == coefficient
        momenta.append({'nt':nt,'nx':nx,'K0':str(K0),'g2_squared_Sigma_D':str(Sigma)})
# Spatial Fourier covariance readback reuses diagonal d; it does not enter this W.
characters={f'{nt}{nx}':str((raw_same+(-1)**(nt+nx)*raw_diag)/Z8)
            for nt in range(2) for nx in range(2)}
assert len(set(characters.values()))==2
result={'scope':'bare plus-sector contribution only; not full Sigma or physical propagation',
        'source_pin':'864f4ec25667e345b90e8a8570a00c10c17b198f',
        'Z8':str(Z8),'raw_same':str(raw_same),'raw_diag':str(raw_diag),
        'g2_squared_local_variance':str(raw_same/Z8),
        'g2_squared_kernel_multiplier':str(coefficient),
        'fourier_covariance_characters':characters,'unit_mass_momenta':momenta,
        'relative_gradient_or_mass_shift_from_this_contribution':False,
        'source_jets_evaluated':False,'full_covariance_evaluated':False}
print(json.dumps(result,indent=2))
