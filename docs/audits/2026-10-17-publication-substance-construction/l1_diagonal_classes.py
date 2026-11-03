from collections import defaultdict
from itertools import combinations_with_replacement
from l1_interacting_support import TERMS
half=defaultdict(list)
for inds in combinations_with_replacement(range(len(TERMS)),3):
    p=0;c=[0]*4
    for i in inds:
        q,d,l=TERMS[i];p^=q
        for x in range(4):c[x]+=d[x]
    if all(a<=b for a,b in zip(c,(4,8,8,4))):
        half[p,tuple(c)].append(inds)
out=[]
for (p,c),aa in half.items():
    for a in aa:
        for b in half.get((p,tuple(x-y for x,y in zip((4,8,8,4),c))),()):
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
                                            for x in (0,3)) for inds in out))
remain=[ii for ii in out if all(any((x,d) in links(ii) for d in (2,3)) for x in (0,3))]
print('remaining',len(remain))
for ii in remain[:20]: print('remaining sample',tuple(TERMS[i][2] for i in ii))
from math import factorial, prod
id_of={label:i for i,(_,_,label) in enumerate(TERMS)}
def transform(ii, dx, swap_t, swap_tt):
    def a(d):
        return (1-d if swap_t else d) if d<2 else (5-d if swap_tt else d)
    def vtx(v):
        return dx ^ (((v&1)<<1)|((v&2)>>1) if swap_t else v)
    out=[]
    for i in ii:
        x,k,l,u,v=TERMS[i][2]
        mu,nu=[d for d in range(4) if d not in (k,l)]
        a0,a1=sorted((a(k),a(l)))
        b0,b1=(vtx(u),vtx(v)) if a(mu)<a(nu) else (vtx(v),vtx(u))
        out.append(id_of[vtx(x),a0,a1,b0,b1])
    return tuple(sorted(out))
remain_set=set(remain)
assert all(transform(ii,dx,s,t) in remain_set for ii in remain for dx in (0,3) for s in (0,1) for t in (0,1))
orbits=defaultdict(set)
for ii in remain:
    images={transform(ii,dx,s,t) for dx in (0,3) for s in (0,1) for t in (0,1)}
    orbits[min(images)].update(images)
print('orbit count',len(orbits),Counter(map(len,orbits.values())))
for ii, images in sorted(orbits.items()):
    print(len(images), tuple(TERMS[i][2] for i in ii))
def multiplicities(ii):
    out=Counter()
    for i in ii:
        x,k,l,u,v=TERMS[i][2]
        mu,nu=[d for d in range(4) if d not in (k,l)]
        out.update([(x,k),(forward(x,k),l),(forward(x,l),k),(x,l),(u,mu),(v,nu)])
    return out
for ii, images in sorted(orbits.items()):
    m=multiplicities(ii)
    print('profile',len(images),len(m),Counter(m.values()), tuple(m[x,d] for x in (0,3) for d in (2,3)))
def two_edge_zero(ii,x):
    m=multiplicities(ii)
    for i in ii:
        site,k,l,u,v=TERMS[i][2]
        if (site,k,l)!=(x,2,3):
            continue
        needed={(u,0),(v,1)}
        if any(m[z]!=2 for z in needed): continue
        others=set()
        for j in ii:
            if j==i: continue
            y,k,l,a,b=TERMS[j][2]
            axes=[d for d in range(4) if d not in (k,l)]
            for z,d in zip((a,b),axes):
                if (z,d) in needed and y==forward(x,d):
                    others.add((z,d))
        if others==needed:return True
zero=[ii for ii in remain if any(two_edge_zero(ii,x) for x in (0,3))]
print('two edge local tensor zero:',len(zero),'of',len(remain),'; remaining orbits',
      sum(ii not in zero for ii in orbits))
