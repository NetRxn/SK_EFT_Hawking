from collections import defaultdict
from itertools import combinations_with_replacement
from l1_interacting_support import TERMS
half=defaultdict(list)
for inds in combinations_with_replacement(range(len(TERMS)),3):
    p=0;c=[0]*4
    for i in inds:
        q,d,l=TERMS[i];p^=q
        for x in range(4):c[x]+=d[x]
    if all(a<=b for a,b in zip(c,(4,4,8,8))):
        half[p,tuple(c)].append(inds)
out=[]
for (p,c),aa in half.items():
    for a in aa:
        for b in half.get((p,tuple(x-y for x,y in zip((4,4,8,8),c))),()):
            if a[-1]<=b[0]:
                out.append(a+b)
print(len(out))
for inds in out[:20]: print(tuple(TERMS[i][2] for i in inds))
from l1_interacting_support import forward
from collections import Counter
def labels(i):
    x,k,l,u,v=TERMS[i][2]
    mu,nu=[d for d in range(4) if d not in (k,l)]
    return {(x,k),(forward(x,k),l),(forward(x,l),k),(x,l),(u,mu),(v,nu)}
def links(inds):
    return set().union(*(labels(i) for i in inds))
print('source link incidence',Counter(tuple(sum((x,d) in links(inds) for d in (2,3))
                                            for x in (0,1)) for inds in out))
remain=[ii for ii in out if all(any((x,d) in links(ii) for d in (2,3)) for x in (0,1))]
print('remaining',len(remain))
for ii in remain[:20]: print('remaining sample',tuple(TERMS[i][2] for i in ii))
from math import factorial, prod
id_of={label:i for i,(_,_,label) in enumerate(TERMS)}
def transform(ii, dx, swap):
    out=[]
    def a(d): return 5-d if swap and d>=2 else d
    for i in ii:
        x,k,l,u,v=TERMS[i][2]
        mu,nu=[d for d in range(4) if d not in (k,l)]
        a0,a1=sorted((a(k),a(l)))
        b0,b1=(u^dx,v^dx) if a(mu)<a(nu) else (v^dx,u^dx)
        out.append(id_of[x^dx,a0,a1,b0,b1])
    return tuple(sorted(out))
out_set=set(out)
assert all(transform(ii,dx,s) in out_set for ii in out for dx in (0,1) for s in (0,1))
orbits={min(transform(ii,dx,s) for dx in (0,1) for s in (0,1)) for ii in out}
assert len(out_set)==128 and len(orbits)==32
assert sum(factorial(6)//prod(factorial(n) for n in Counter(ii).values()) for ii in out)==11520
assert Counter(tuple(sum((x,d) in links(ii) for d in (2,3)) for x in (0,1))
               for ii in out)=={(2,0):64,(0,2):64}
print('32 orbits under temporal translation and transverse exchange; all canceled')
