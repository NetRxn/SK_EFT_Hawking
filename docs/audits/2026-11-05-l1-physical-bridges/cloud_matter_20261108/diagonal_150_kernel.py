"""Insert only the reviewed disjoint 128+22 diagonal trace words."""
import io, json
from contextlib import redirect_stdout
from fractions import Fraction as F
import sympy as s
with redirect_stdout(io.StringIO()):
    import trace_kernel_with_nearest as earlier
Z8 = F(1252309350145403,2123366400)
LOGZ_JJ = F(954400425849600,113846304558673)
SIMPLE_RAW, BOTH_UNUSED_RAW = F(11907,2), F(37152,5)
PARTIAL_RAW = SIMPLE_RAW + BOTH_UNUSED_RAW
assert PARTIAL_RAW == F(133839,10)
PARTIAL_PAIR = PARTIAL_RAW / Z8
# The simple subset has raw N_jj=8*N; the added subset has source charge zero.
PARTIAL_PAIR_HH = (8*SIMPLE_RAW/Z8 - PARTIAL_PAIR*LOGZ_JJ)/8
known = earlier.known + earlier.base.rat(PARTIAL_PAIR)*earlier.unknown_coefficient
known_hh = earlier.known_hh + earlier.base.rat(PARTIAL_PAIR_HH)*earlier.unknown_coefficient
rows = []
for n0 in range(2):
    for n1 in range(2):
        v = s.Matrix([(-1)**(n0*(x&1)+n1*(x>>1)) for x in range(4)])
        eig = lambda M: (v.T*M*v)[0]/4
        for M in (known,known_hh,earlier.unknown_coefficient):
            assert M*v == eig(M)*v
        rows.append({'n0':n0,'n1':n1,'known_g2_squared_Sigma':str(eig(known)),
            'coefficient_of_remaining_diagonal_T':str(eig(earlier.unknown_coefficient)),
            'known_g2_squared_Sigma_second_h':str(eig(known_hh))})
assert rows[1]['known_g2_squared_Sigma'] == rows[2]['known_g2_squared_Sigma']
assert rows[1]['known_g2_squared_Sigma_second_h'] == rows[2]['known_g2_squared_Sigma_second_h']
print(json.dumps({'scope':'known D/H and trace local/nearest plus 150 of 310 diagonal trace words; not full kernel',
    'raw_diagonal_partial':str(PARTIAL_RAW),'normalized_diagonal_partial_g2_squared':str(PARTIAL_PAIR),
    'normalized_diagonal_partial_hh_g2_squared':str(PARTIAL_PAIR_HH),
    'equation':'g2^2 Sigma = known + c*d_remaining + other active/mixed; d_remaining is the normalized 160-word residual times g2^2',
    'source_equation':'same c multiplies the unknown residual second h jet; every omitted input remains unknown',
    'momenta':rows},indent=2))
