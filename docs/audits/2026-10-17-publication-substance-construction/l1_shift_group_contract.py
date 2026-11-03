from pathlib import Path
from fractions import Fraction
from itertools import product
from functools import cache
from l1_mixed_center_contract import read, source, mul, wedge_sign
from l1_two_center_shift_groups import groups

source=cache(source)
@cache
def get(family,shift):
    if shift==0:
        return [] if family=='same' else list(read(str(Path(__file__).with_name('l1_sparse_mixed_projection_indexed.txt'))))
    code=int(family=='mixed')
    return list(read(str(Path(__file__).with_name(f'l1_shift_{code}_{shift}.out.txt'))))

def contract(family,s,t):
    out=[Fraction(0),Fraction(0)]
    matched=0
    for (a,b,u,v,c),(d,e,w,z,f) in product(get(family,s),get(family,t)):
        if u&w or v&z:continue
        j0=255^(u|w);j3=255^(v|z)
        sign=(1 if family=='mixed' else -1)*wedge_sign(u,w)*wedge_sign(v,z)*wedge_sign(u|w,j0)*wedge_sign(v|z,j3)
        src=mul(source(j0,a,d),source(j3,b,e))
        if any(src):
            matched+=1
            for j,r in enumerate(mul(src,mul(c,f))):
                out[j]+=sign*r
    return tuple(a/(48**8*16**8) for a in out),matched

if __name__=='__main__':
    total=[Fraction(0),Fraction(0)]
    for (f,s,t),n in sorted(groups.items()):
        z,k=contract(f,s,t)
        assert z==contract(f,t,s)[0]
        for j,x in enumerate(z):total[j]+=n*x
        print(f,s,t,'multiplicity',n,'nonzero entries',len(get(f,s)),len(get(f,t)),
              'matched pairs',k,'coefficient',z)
    print('complete two-center group contribution',tuple(total))
