"""Source-0 tensor from the closed residual commutator-source Haar kernel."""
from functools import cache
from itertools import product
from math import lcm
import sys
from contextlib import redirect_stdout

with redirect_stdout(sys.stderr):
    from l1_equal_time_shared_quadratic_pair import fixed_frame
    from l1_equal_time_int_contract import sparse_int
    from l1_residual_sparse_sources import source_table
    from l1_direct_b_haar import wedge
    from l1_reduced_wedge_reference import wedge_sign

Q = range(8)

def add(poly,k,r,i):
    ar,ai=poly.get(k,(0,0))
    poly[k]=ar+r,ai+i

@cache
def pair(mode,e,f,a,b):
    # source axis 0 to site 1 and axis 1 to site 2
    # mode bit d indicates the two frames use the mixed center's anchor
    return sparse_int(wedge(fixed_frame(0,0,1 if mode&1 else 0,e)[a],
                            fixed_frame(0,1,2 if mode&2 else 0,f)[b]))

def tensor(mode):
    table=source_table(True)
    den=lcm(*(q.denominator for v in table.values() for q in v))
    assert den==18
    out={}
    for (m,y,z,a,b),value in table.items():
        ar,ai=(int(den*q) for q in value)
        for e,f in product(Q,repeat=2):
            for g,h,flip in ((a,b,1),(b,a,-1)):
                for p,(br,bi) in pair(mode,e,f,g,h).items():
                    if p&m:continue
                    s=flip*wedge_sign(m,p)
                    add(out,(e,f,y,z,m|p),s*(ar*br-ai*bi),s*(ar*bi+ai*br))
    out={k:v for k,v in out.items() if any(v)}
    assert all((m&255).bit_count()==6 and ((m>>8)&255).bit_count()==1 and
               ((m>>16)&255).bit_count()==1 and (m>>24)==0 for *_,m in out)
    return out,den*4**4
if __name__=='__main__':
    for mode in range(4):
        rows,den=tensor(mode)
        assert len(rows) == 19200 and den == 4608
        print(mode,len(rows),den,file=sys.stderr,flush=True)
        for k,(r,i) in sorted(rows.items()):print(mode,*k,r,i)
