"""Post-Haar sparse bounded layer: all frame anchors, fixed opposing centers."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations,permutations
from math import factorial,prod
from time import perf_counter
from l1_extended_opposed import curvature
from l1_normalization_opposed_fourth import fourth_T,tuples
from l1_normalization_disjoint_sector import pair
from l1_direct_b_haar import R,add,scale,wedge

def clean(poly):
    return {m:z for m,z in poly.items() if z}

def full_fourth(direction, summed):
    old=fourth_T(direction)
    if not summed:
        return {k:clean(p) for k,p in old.items()}
    second=pair(0,direction)
    out={}
    for indices,p in old.items():
        cross=[]
        for subset in combinations(range(4),2):
            rest=tuple(i for i in range(4) if i not in subset)
            a,b=(tuple(indices[i] for i in group) for group in (subset,rest))
            cross.append(wedge(second[a[0]][a[1]],second[b[0]][b[1]]))
        out[indices]=clean(add(scale(p,2),scale(add(*cross),24)))
    return out

def contract(summed):
    start=perf_counter()
    A,B=(full_fourth(d,summed) for d in (0,1))
    raw_center={}
    weighted=0
    peak=0
    for a in tuples:
        mult=factorial(4)//prod(factorial(n) for n in Counter(a).values())
        for b in tuples:
            w=sum(curvature(tuple(sorted(zip(a,p)))) for p in set(permutations(b)))
            if w:
                term=clean(wedge(A[a],B[b]))
                peak=max(peak,len(term))
                raw_center=add(raw_center,scale(term,mult*w))
                weighted+=bool(term)
    raw_center=clean(raw_center)
    center={m:z for m,z in raw_center.items() if m&255==255}
    def shift(mask):
        return sum(((mask>>(8*x))&255)<<(8*(x^3)) for x in range(4))
    opposite={shift(m):z for m,z in center.items()}
    top=(1<<32)-1
    matches=0
    result=R.zero
    for m,z in center.items():
        comp=top^m
        if comp in opposite:
            result+=wedge({m:z},{comp:opposite[comp]}).get(top,R.zero)
            matches+=1
    assert result.is_ground and not result.const().y
    den=48*(96*8**4)**2
    value=F(int(result.const().x),den**2*factorial(4)**2)
    print('summed anchors',summed,'post-Haar edge entries',sum(map(len,A.values())),sum(map(len,B.values())),
          'max edge mask',max(map(len,A.values())),max(map(len,B.values())),flush=True)
    print('nonzero weighted tuple blocks',weighted,'peak joined masks',peak,
          'raw center masks',len(raw_center),'saturated center masks',len(center),
          'complement joins',matches,'value',value,'seconds',perf_counter()-start,flush=True)
    return value

if __name__=='__main__':
    assert contract(False)==F(61875,262144)
    print('anchor-summed exact layer',contract(True))
