"""Exact scheduler quotient by independently verified signed frame rotations."""
from collections import Counter
from functools import cache
from sys import argv
from itertools import permutations,product
from l1_extended_overlap_scheduler import exterior,jobs,assignments

PERMS=tuple(permutations((1,2,3)))
@cache
def orbit(q,r):
    out=set()
    for a,b in product(PERMS,repeat=2):
        m=(0,*a,4,*(4+i for i in b))
        out.add((tuple(sorted(m[i] for i in q)),tuple(sorted(m[i] for i in r))))
    return sorted(out)

def selected(plan):
    for a,b,c,s,q,t,r in plan:
        # Global chiral exchange has no fixed signature.
        if s[0]:continue
        im=orbit(q,r)
        if (q,r)==im[0]:
            yield (a,b,c,s,q,t,r),2*len(im)

if __name__=='__main__':
    G=exterior(argv[1]);J=jobs(G);reps=list(selected(J))
    assert sum(n for _,n in reps)==len(J)
    assert sum(n*len(G[s,q])*len(G[t,r]) for (_,_,_,s,q,t,r),n in reps)==94748063904
    L=set();R=set();pairs=0
    for (a,b,c,s,q,t,r),n in reps:
        L.add((a,b));R.add((c,assignments(q,r,s[5],t[5]),s[7]))
        pairs+=len(G[s,q])*len(G[t,r])
    print('orbit representatives',len(reps),'weighted block total',len(J),
          'replayed pairs',pairs,'left kernels',len(L),'right kernels',len(R),
          'orbit multiplicities',sorted(Counter(n for _,n in reps).items()))
