"""Exact Pin and closed adjoint-plaquette sector checks."""
from fractions import Fraction as F
from itertools import product
from sympy import diag, eye
from l1_direct_b_haar import gamma
from l1_interacting_support import forward

V=gamma[3]
chirality=diag(1,1,-1,-1)
assert V*V==eye(4) and V.det()**2==1
assert V*chirality*V==-chirality
signs=(-1,-1,-1,1)
assert all(V*g*V==s*g for g,s in zip(gamma,signs))
print('Pin reflection flips S2 and S4; metric G invariant:',signs)

# Torus tiling: distinct oriented links appear exactly twice with opposite
# signs. For a nonempty proper plaquette subset, at least one appears once.
def boundary(f):
    k,l=0,1
    return ((f,k,1),(forward(f,k),l,1),(forward(f,l),k,-1),(f,l,-1))
faces=tuple(boundary(x) for x in range(4))
for include in product((False,True),repeat=4):
    incidence={}
    for use,face in zip(include,faces):
        if use:
            for x,d,s in face:
                incidence.setdefault((x,d),[]).append(s)
    if all(include):
        assert len(incidence)==8 and all(sorted(ls)==[-1,1] for ls in incidence.values())
    elif any(include):
        assert any(len(ls)==1 for ls in incidence.values())
# Each of 8 integrations contributes 1/d and each of 4 vertex contractions
# contributes d. The only surviving irrep labelings are all-trivial and
# all-adjoint in exactly one of the two chiral factors.
d=3
adjoint_four=F(d**4,d**8)
spin4_average=F(3,2)**4+2*F(1,4)**4*adjoint_four
sector=F(24**4,2**4)*spin4_average
assert sector==104978
print('Closed adjoint four-face factor',adjoint_four,
      'local-pair sector with exponential factorials',sector)
