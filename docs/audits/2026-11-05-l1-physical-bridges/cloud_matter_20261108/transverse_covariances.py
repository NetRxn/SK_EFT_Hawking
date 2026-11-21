"""Exact closed four-site local H² and transverse-trace² using archived gravity tensors.
H=G23, T=G22+G33, D=G22-G33; all are bare composite coordinates.
No physical normalization, positivity or complete active covariance is supplied.
"""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"2026-10-17-publication-substance-construction"))
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product
from l1_transverse_top import t
from l1_direct_b_haar import wedge
from l1_reduced_wedge_reference import wedge_sign
import l1_equal_time_joint_source_weights as source
import l1_equal_time_coupled as coupled

# Raw t is4 times the coframe; each metric is a raw pair divided by16.
PAIRS=source.PAIRS
frame_pairs={(a,b):wedge(t[a],t[b]) for a,b in product(range(4),repeat=2)}
@cache
def weighted_pair(a,b,indices):
    weight=source.powers(indices);out={}
    for mask,poly in frame_pairs[a,b].items():
        real=imag=F(0)
        for exponent,coefficient in poly.items():
            moment=source.avg(tuple(i+j for i,j in zip(exponent,weight)))
            real+=int(coefficient.x)*moment
            imag+=int(coefficient.y)*moment
        if real or imag:out[mask]=(real,imag)
    return out

def top_product(A,B):
    real=imag=F(0)
    for mask,(r,i) in A.items():
        if source.T^mask not in B:continue
        u,v=B[source.T^mask];sign=wedge_sign(mask,source.T^mask)
        real+=sign*(r*u-i*v);imag+=sign*(r*v+i*u)
    assert imag==0
    return real

@cache
def kernel_H(a,b):
    # H²=sum_ij T2_i T2_j T3_i T3_j, since degree-two frames commute.
    return sum((top_product(weighted_pair(i,j,a),weighted_pair(i,j,b))
                for i,j in frame_pairs),F(0))/256

@cache
def kernel_T(a,b):
    # T²=G22²+G33²+2G22G33; D² has the opposite cross sign.
    ea,eb=source.powers(a),source.powers(b)
    squares=source.coeff(source.square,ea)*source.avg(eb)+source.coeff(source.square,eb)*source.avg(ea)
    return 2*squares-source.kernel(a,b)

for name,kernel,moment in [('D',source.kernel,F(21)),('H',kernel_H,F(9)),('T',kernel_T,F(129))]:
    for a,b in product(PAIRS,repeat=2):assert kernel(a,b)==kernel(b,a)
    for ch1,ch2 in product((0,4),repeat=2):
        assert sum(kernel((i,i),(j,j)) for i,j in product(range(ch1,ch1+4),range(ch2,ch2+4)))==moment
    print('local source moment control',name,moment,flush=True)
assert kernel_H((1,2),(1,2))==F(1,24)  # retained offdiagonal source-link kernel

# TYPES are two indices across source links at ONE action center. Source.kernel
# PAIRS are indices across TWO centers within ONE source link. Retain both.
def mixer(kernel):
    @cache
    def mix(t,u):
        return sum(kernel(tuple(sorted((i,a))),tuple(sorted((j,b))))
                   for (i,j),(a,b) in product(coupled.MEMBERS[t],coupled.MEMBERS[u]))
    return mix

mixers={name:mixer(kernel) for name,kernel in [('D',source.kernel),('H',kernel_H),('T',kernel_T)]}
words={tuple(sorted(w)) for w in coupled.same_site_quadratic_support() if not coupled.reduce_source_dependence(w)[1]}
assert len(words)==40
histograms={name:Counter() for name in mixers}
while words:
    word=min(words)
    orbit={tuple(sorted(coupled.transform(term,a,b) for term in word)) for a,b in product((False,True),repeat=2)}
    assert orbit<=words
    words-=orbit
    row={}
    for name,mix in mixers.items():
        coupled.source_mix=mix
        value=coupled.solve(word,closed=True)
        histograms[name][value]+=len(orbit);row[name]=str(value)
    print('orbit',len(orbit),word,row,flush=True)
subtotals={name:sum(value*n for value,n in hist.items()) for name,hist in histograms.items()}
assert subtotals['D']==F(-23063,32)
# The other145 source-decoupled words share the same source-independent action
# contractions; their source Haar moments alone change21→9 or129.
private_D=F(318843)
Z8=F(1252309350145403,2123366400)
for name,moment in [('D',F(21)),('H',F(9)),('T',F(129))]:
    private=private_D*moment/21
    raw=private+subtotals[name]
    assert sum(histograms[name].values())==40
    print('RESULT',name,'private',private,'coupled',subtotals[name],
          'raw_g2_6',raw,'normalized_g2_squared',raw/Z8,
          'histogram',sorted(histograms[name].items()),flush=True)
