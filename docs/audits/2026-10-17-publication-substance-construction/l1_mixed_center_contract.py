from fractions import Fraction
from itertools import product
from re import search
from sys import argv
from l1_transverse_top import G,haar_moment
from l1_reduced_wedge_reference import wedge_sign

def avg(e):
    return haar_moment(e[:4])*haar_moment(e[4:])

def source(mask,i,j):
    ej=tuple(int(i==k)+int(j==k) for k in range(8))
    real = imag = Fraction(0)
    for e, c in G.get(mask, {}).items():
        weight = avg(tuple(a + b for a, b in zip(e, ej))) - avg(e) * avg(ej)
        real += int(c.x) * weight
        imag += int(c.y) * weight
    return real, imag
def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]

def read(path):
    for line in open(path):
        m=search(r'exact slice (\d+) (\d+) (\d+) (\d+) scaled Gaussian \((-?\d+),(-?\d+)\)/5308416',line)
        if m:
            a,b,u,v,r,i=map(int,m.groups())
            if r or i:yield a,b,u,v,(r,i)
if __name__=='__main__':
    items=list(read(argv[1]))
    out=[Fraction(0),Fraction(0)]
    matched=0
    for (a,b,u,v,c),(d,e,w,z,f) in product(items,repeat=2):
        if u&w or v&z:continue
        j0=255^(u|w);j3=255^(v|z)
        source_product = mul(source(j0, a, d), source(j3, b, e))
        sign = (wedge_sign(u, w) * wedge_sign(v, z) *
                wedge_sign(u | w, j0) * wedge_sign(v | z, j3))
        if any(source_product):
            matched += 1
            for component, value in enumerate(mul(source_product, mul(c, f))):
                out[component] += sign * value
    # B2 acquires a minus under time-space interchange, canceled by the
    # site-3 D sign (its shared link sits on the opposite singleton axis).
    # Each of eight degree-four factors was scaled by 4^2.
    out=[x/(48**8*16**8) for x in out]
    print('nonzero center entries',len(items),'matched ordered slice pairs',matched,'exact orbit scalar',out)
