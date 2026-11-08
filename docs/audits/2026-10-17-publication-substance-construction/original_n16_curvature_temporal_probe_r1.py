"""Bounded exact reconstruction of the local covariance and temporal factor."""
from fractions import Fraction as F
from itertools import product
import json
from src.core import formulas as f
from src.vestigial import original_coefficients as o

mul = o.matrix_multiply
q = o.QComplex
poly = o.Polynomial
zero = o.ExteriorPolynomial()

def integrate_poly(polynomial):
    return sum((value * o.quaternion_key_moment(key) for key, value in polynomial.terms), q())

def integrate_exterior(form):
    return o.ExteriorPolynomial(tuple(
        (mask, poly.scalar(integrate_poly(value))) for mask, value in form.terms
    ))

def curvature_covariance(reg):
    base = reg.sites[0]
    holonomy = f.original_spin4_link(*(
        tuple(poly.variable(o.Symbol("q", (base, 0, chi, k))) for k in range(4))
        for chi in ("L", "R")
    ))
    gamma = reg.gamma
    gamma5 = reg.gamma5
    trace = {}
    for a, b in product(range(4), repeat=2):
        antisymmetric = o.matrix_scale(
            o.matrix_add(mul(gamma[a], gamma[b]), o.matrix_scale(mul(gamma[b], gamma[a]), -1)),
            F(1, 2),
        )
        h_a = mul(holonomy, mul(antisymmetric, gamma5))
        trace[a,b] = sum((h_a[i][i] for i in range(4)), poly())
    assert all(integrate_poly(t) == q() for t in trace.values())
    for a,b,c,d in product(range(4), repeat=4):
        expected = 2*(int(a==c and b==d)-int(a==d and b==c))
        assert integrate_poly(trace[a,b]*trace[c,d]) == q(expected),(a,b,c,d)
    return {"mean_entries":len(trace),"covariance_entries":len(trace)**2}

def temporal_covariance(reg):
    basis = {}
    gen = o.ExteriorPolynomial.generator
    for site in range(2):
        for ch in range(2):
            b0,b1,p0,p1=(gen(site*8+ch*4+i) for i in range(4))
            basis[site,ch] = (b0*p0+b1*p1,b0*b1,p0*p1)
    sewing = sum((
        basis[0,ch][0]*basis[1,1-ch][0]
        + (basis[0,ch][1]*basis[1,1-ch][2])*(-2)
        + (basis[0,ch][2]*basis[1,1-ch][1])*(-2)
        for ch in range(2)
    ),zero)
    assert sewing != zero
    expected = sewing * poly.scalar(F(1,8))
    observed_anchors = set()
    for site in reg.sites:
        terms = []
        for a in range(4):
            blocks = f.original_coframe_blocks(reg,(site,reg.temporal_axis,a))
            observed_anchors.update(block.anchor for block in blocks)
            terms.append(o.assemble_coframe(reg,blocks).to_exterior(reg))
        for a,b in product(range(4),repeat=2):
            result = integrate_exterior(terms[a]*terms[b])
            assert result == (expected if a==b else zero),(site,a,b)
    assert observed_anchors == {(site,reg.temporal_axis) for site in reg.sites}
    return {"covariance_entries":32,"anchor_count":len(observed_anchors),
            "Q00_sewing_factor":"1/2","area_sewing_factor":"3/8"}

result = {}
for convention,axis in (("source_C",3),("metric_M",0)):
    reg=o.OriginalRegulator(tuple(2 if j==axis else 1 for j in range(4)),convention=convention)
    result[convention]={"curvature":curvature_covariance(reg),"temporal":temporal_covariance(reg)}
print(json.dumps(result,indent=2))
