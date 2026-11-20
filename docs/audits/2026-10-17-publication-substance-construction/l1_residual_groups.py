from collections import Counter
from l1_two_center_shift_groups import *
from l1_diagonal_classes import forward
def residual_sig(ii):
    ds=[TERMS[i][2] for i in ii]
    assert Counter(x for x,*_ in ds)=={0:1,1:2,2:2,3:1}
    src={x:(u,v) for x,k,l,u,v in ds if x in (0,3)}
    assert all((k,l)==(2,3) for x,k,l,*_ in ds if x in (0,3))
    def center(x):
        terms=[(k,l,u,v) for y,k,l,u,v in ds if y==x]
        ls=tuple(next(l for j,l,_,_ in terms if j==k) for k in (0,1))
        flags=0
        for d in (0,1):
            term=next((k,l,u,v) for k,l,u,v in terms if k!=d)
            k,l,u,v=term
            ts=[e for e in range(4) if e not in (k,l)]
            e=(u,v)[ts.index(d)]
            y=forward(x,d)
            assert e in (x,y) and src[y][d]==e
            flags|=(e!=x)<<d
        return ls,flags
    a,b=center(1),center(2)
    assert a[0]==b[0][::-1]
    p=a[1]
    q=((b[1]&1)<<1)|((b[1]&2)>>1)
    return ('mixed' if a[0][0]!=a[0][1] else 'same',min(p,q),max(p,q))
residual=Counter()
for ii,images in orbits.items():
    if ii in zero or ii in more or signature(ii):continue
    key=residual_sig(ii)
    residual[key]+=len(images)
    print('residual orbit',key,len(images))
print('residual groups',residual)
