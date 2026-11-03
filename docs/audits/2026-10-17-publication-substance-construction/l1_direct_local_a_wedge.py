from itertools import combinations
from fractions import Fraction
from sympy import I, Matrix, diag, eye, zeros
from l1_reduced_wedge_reference import ZERO, add, bilinear, scale, wedge

pauli = [Matrix([[0,1],[1,0]]), Matrix([[0,-I],[I,0]]), diag(1,-1)]
gamma = [zeros(2).row_join(-I*p).col_join((I*p).row_join(zeros(2))) for p in pauli]
gamma.append(zeros(2).row_join(eye(2)).col_join(eye(2).row_join(zeros(2))))
embedded = [diag(p, zeros(2)) for p in pauli] + [diag(zeros(2),p) for p in pauli]
axial = [[bilinear(g*p+p*g, 0, 0, tuple(range(16))) for p in embedded] for g in gamma]
# Actual K is scaled by sixteen. Each transverse link is independent.
K = [[scale(add(*(wedge(x,y) for x,y in zip(a,b))), -1) for b in axial] for a in axial]


def local_top(entries):
    total = add(*(scale(wedge(K[c][e],K[d][f]),v*w)
                  for (c,d),v in entries.items() for (e,f),w in entries.items()))
    coeff = total.get(255,ZERO)
    assert coeff.y == 0
    return Fraction(int(coeff.x),256)


def antisymmetric(values):
    out = dict(values)
    out.update({(j,i):-v for (i,j),v in values.items()})
    return out


pairs = list(combinations(range(4),2))
for p in pairs:
    assert local_top(antisymmetric({p:1})) == 3
for p,q in combinations(pairs,2):
    assert local_top(antisymmetric({p:1,q:1})) == 6
sample = {p: i-2 for i,p in enumerate(pairs)}
assert local_top(antisymmetric(sample)) == 3*sum(v*v for v in sample.values())
poison = {(0,1):1}
assert local_top(poison) != 3
print('A local antisymmetric saturation: 6 basis norms=3; 15 pair sums=6; mixed norm',local_top(antisymmetric(sample)))
print('orientation omission poison:',local_top(poison),'vs 3; unpoisoned repeat', local_top(antisymmetric(poison)))
