from collections import Counter
from l1_sparse_center_cancellations import *
from l1_diagonal_classes import forward
def signature(ii):
    ds=[TERMS[i][2] for i in ii]
    if Counter(x for x,*_ in ds)!={1:3,2:3}:return None
    def center(x):
        terms=[(k,l,u,v) for y,k,l,u,v in ds if y==x]
        ks=[(k,l) for k,l,*_ in terms]
        if sorted(k for k,l in ks)!=[0,1,2] or any(l<2 for k,l in ks):return None
        ls=tuple(next(l for j,l in ks if j==k) for k in (0,1))
        flags=0
        for d in (0,1):
            endpoints=[]
            for k,l,u,v in terms:
                ts=[e for e in range(4) if e not in (k,l)]
                if d in ts:endpoints.append((u,v)[ts.index(d)])
            if endpoints not in ([x,x],[forward(x,d)]*2):return None
            flags|=(endpoints[0]!=x)<<d
        return ls,flags
    a,b=center(1),center(2)
    if not a or not b or a[0]!=b[0][::-1]:return None
    p=a[1]
    q=((b[1]&1)<<1)|((b[1]&2)>>1)
    return ('mixed' if a[0][0]!=a[0][1] else 'same',min(p,q),max(p,q))

groups=Counter()
for ii,images in orbits.items():
    if ii in zero or ii in more:continue
    key=signature(ii)
    if not key:continue
    groups[key]+=len(images)
    print(key,len(images),tuple(TERMS[i][2] for i in ii))
print('two-center groups',groups)
