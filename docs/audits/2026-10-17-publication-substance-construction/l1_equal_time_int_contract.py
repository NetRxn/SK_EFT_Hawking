from functools import cache
from l1_equal_time_private_pairs import TOP,wedge_sign

def sparse_int(poly):
    ans={}
    for mask,value in poly.items():
        assert value.is_ground
        z=value.const()
        ans[mask]=(int(z.x),int(z.y))
    return ans

def triple(A,B,C):
    A,B,C=sorted((A,B,C),key=len)
    total_real=0
    total_imag=0
    for a,(ar,ai) in A.items():
        for b,(br,bi) in B.items():
            if a&b:continue
            c=TOP^(a|b)
            z=C.get(c)
            if z is None:continue
            cr,ci=z
            u,v=ar*br-ai*bi,ar*bi+ai*br
            sign=wedge_sign(a,b)*wedge_sign(a|b,c)
            total_real+=sign*(u*cr-v*ci)
            total_imag+=sign*(u*ci+v*cr)
    assert total_imag==0
    return total_real
