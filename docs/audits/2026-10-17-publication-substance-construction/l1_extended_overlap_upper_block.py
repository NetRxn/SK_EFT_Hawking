"""Local upper pair block; sites 0,1 low and 2,3 upper."""
from itertools import product
from collections import Counter
from functools import cache
from l1_normalization_disjoint_sector import pair
from l1_normalization_opposed_fourth import L
from l1_equal_time_int_contract import sparse_int
from l1_direct_b_haar import add,scale,wedge
from l1_reduced_wedge_reference import wedge_sign
pair=cache(pair)

@cache
def frame_pair(site, a, b):
    first,second=pair(site,0),pair(site,1)
    polys=[]
    for (g,h),(j,k) in product(L,repeat=2):
        av=dict(L[g,h]).get(a,0)
        bv=dict(L[j,k]).get(b,0)
        if av and bv:
            polys.append(scale(wedge(first[g][j],second[h][k]),av*bv))
    return sparse_int(add(*polys))

def block(a,b,c,d):
    result=Counter()
    for x,(r,s) in frame_pair(2,a,b).items():
        for y,(u,v) in frame_pair(3,c,d).items():
            if x&y: continue
            sign=wedge_sign(x,y)
            result[x|y,0]+=sign*(r*u-s*v)
            result[x|y,1]+=sign*(r*v+s*u)
    out={k:v for k,v in result.items() if v}
    assert all(tuple(((m>>(8*i))&255).bit_count() for i in range(4))==(2,2,6,6) for m,_ in out)
    return out

if __name__ == "__main__":
    from fractions import Fraction
    from itertools import combinations_with_replacement

    channels = tuple(combinations_with_replacement(range(6), 2))
    reference = block(0, 0, 0, 0)
    assert len(reference) == 216
    surviving = 0
    for (a, b), (c, d) in product(channels, repeat=2):
        expected = reference if a == b and c == d else {}
        observed = block(a, b, c, d)
        assert observed == expected, (a, b, c, d)
        surviving += bool(observed)
    sheet = Fraction(6, 4)**4 + 2 * Fraction(1, 4)**4 / 3**4
    print(f"{surviving}/{len(channels)**2} channels, {len(reference)} entries, sheet {sheet}")
