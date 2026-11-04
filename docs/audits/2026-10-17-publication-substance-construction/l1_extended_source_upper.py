"""Exact upper complement with two same-site composite source factors."""
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement,product
from l1_extended_overlap_upper_block import frame_pair,block,pair
from l1_equal_time_int_contract import sparse_int
from l1_direct_b_haar import add,wedge
from l1_reduced_wedge_reference import wedge_sign

def source_product(site):
    first,second=pair(site,0),pair(site,1)
    return sparse_int(add(*(wedge(first[g][g],second[h][h])
                            for g,h in product(range(4),repeat=2))))

def join(A,B):
    out=Counter()
    for m,(r,i) in A.items():
        for n,(s,j) in B.items():
            if m&n:continue
            w=wedge_sign(m,n)
            out[m|n,0]+=w*(r*s-i*j)
            out[m|n,1]+=w*(r*j+i*s)
    return {k:v for k,v in out.items() if v}

if __name__=='__main__':
    baseline=block(0,0,0,0)
    src=source_product(2)
    print('source polynomial masks',len(src))
    for a,b in combinations_with_replacement(range(6),2):
        res=join(src,frame_pair(3,a,b))
        ratios={Fraction(v,baseline[k]) for k,v in res.items() if k in baseline}
        print((a,b),'rows',len(res),'baseline support',res.keys()==baseline.keys(),
              'ratio',sorted(ratios),flush=True)
