"""Insert only the completed128-word diagonalT subsum; the g2²-scaled182-word residual staysunknown."""
import io,json
from contextlib import redirect_stdout
import sympy as s
with redirect_stdout(io.StringIO()):
    import trace_kernel_with_nearest as earlier
known=earlier.known+earlier.base.rat(earlier.NEAREST)*earlier.unknown_coefficient
known_hh=earlier.known_hh+earlier.base.rat(earlier.NEAREST_HH)*earlier.unknown_coefficient
rows=[]
for n0 in range(2):
 for n1 in range(2):
    v=s.Matrix([(-1)**(n0*(x&1)+n1*(x>>1)) for x in range(4)])
    eig=lambda M:(v.T*M*v)[0]/4
    for M in (known,known_hh):assert M*v==eig(M)*v
    rows.append({'n0':n0,'n1':n1,'known_g2_squared_Sigma':str(eig(known)),
      'coefficient_of_remaining_diagonal_T':str(eig(earlier.unknown_coefficient)),
      'known_g2_squared_Sigma_second_h':str(eig(known_hh))})
assert rows[1]['known_g2_squared_Sigma']==rows[2]['known_g2_squared_Sigma']
print(json.dumps({'scope':'knownD/H+Tlocal/nearest+128of310diagonalTwords;notfullkernel',
 'equation':'g2²Sigma=known+c*d_remaining+otheractive/mixed;d_remaining=g2² times normalized182-word residual',
 'source_equation':'samec multiplies unknown residualsourcejet; noomittedtermsetzero',
 'momenta':rows},indent=2))
