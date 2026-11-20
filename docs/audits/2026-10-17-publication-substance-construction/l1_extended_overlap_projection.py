"""One exact shared curvature/frame Haar link inside a saturated 2^4 motif."""
from collections import Counter,defaultdict
from itertools import combinations_with_replacement,product
from time import perf_counter
from sympy import Matrix,I
from l1_equal_time_shared_quadratic_pair import fixed_frame
from l1_equal_time_int_contract import sparse_int
from l1_direct_b_haar import wedge
from l1_normalization_uniform_mixed_edge import moment

def geometry():
    c=Counter();p=Counter();t=Counter()
    for x in range(16):
        planes=((0,1),(0,2)) if not x&8 else ((0,1),(0,1))
        for k,l in planes:
            p.update(((x,k),(x^(1<<k),l),(x^(1<<l),k),(x,l)))
            c[x]+=2
            for d in set(range(4))-{k,l}:
                y=x^(1<<d)
                c[y]+=1
                t[min(x,y) if not x&8 and d in (1,2) else x,d]+=1
    assert c==Counter({x:8 for x in range(16)})
    assert all((p[k]+t[k])%2==0 for k in p.keys()|t.keys())
    assert min(p.values())==2
    print('shared links',sorted(p.keys()&t.keys()))
    print('incidence histogram',Counter((p[k],t[k]) for k in p.keys()|t.keys()))

def tensor():
    # Shared link (0,1) between base 0 and 2. Its two T uses are
    # the mixed (0,2) action frames at those two bases.
    pairs=tuple(combinations_with_replacement(range(8),2))
    frames=defaultdict(Counter)
    for i,j in product(range(8),repeat=2):
        x=fixed_frame(0,1,0,i)
        y=fixed_frame(2,1,0,j)
        pair=tuple(sorted((i,j)))
        for g,h in product(range(4),repeat=2):
            for mask,(r,s) in sparse_int(wedge(x[g],y[h])).items():
                if r:frames[pair][g,h,mask,0]+=r
                if s:frames[pair][g,h,mask,1]+=s
    rows=sorted({key[:3] for values in frames.values() for key,z in values.items() if z})
    F=Matrix([[frames[p][(*key,0)]+I*frames[p][(*key,1)] for key in rows] for p in pairs])
    H=Matrix([[moment(*p,*q) for q in pairs] for p in pairs])
    P=H*F
    # Each output is 48 times the Haar projection of raw 4T on each frame.
    active=[k for k in range(len(rows)) if any(P[i,k] for i in range(36))]
    frames_rank=F.rank()
    projected_rank=P.rank()
    null=Matrix([int(i==j and i<4)-int(i==j and i>=4) for i,j in pairs])
    assert H*null==Matrix.zeros(36,1)
    print('Haar moment matrix nnz/rank',sum(bool(x) for x in H),H.rank())
    print('frame boundary labels',len(rows),'unprojected nnz/rank',sum(bool(x) for x in F),frames_rank)
    print('projected boundary labels',len(active),'nnz/rank',sum(bool(x) for x in P),projected_rank)
    print('projected nonzero curvature rows',sum(any(P[i,k] for k in active) for i in range(36)))
    print('maximum Gaussian component',max(max(abs(z.as_real_imag()[0]),abs(z.as_real_imag()[1])) for z in P))
    assert projected_rank and projected_rank < 36
if __name__=='__main__':
    start=perf_counter()
    geometry()
    tensor()
    print('seconds',perf_counter()-start)
