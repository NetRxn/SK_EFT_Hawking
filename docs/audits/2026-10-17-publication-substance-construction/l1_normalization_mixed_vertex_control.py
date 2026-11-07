from collections import Counter,defaultdict
from itertools import product
from l1_normalization_mixed_cycle import owned_edge,vertex,parity,trace_to_local,local_t
from l1_normalization_shared_transport import nodes,R,add,scale,wedge
from l1_normalization_uniform_mixed_edge import unit
from l1_normalization_transport_cycle import poly_int,wedge_sign

def nodes2():
    for i,s in product(range(4),(-1,1)):
        q=tuple(2*z for z in unit(i))
        yield q,tuple(s*z for z in q),1

def build_t(q,d):
    return add(*(scale(local_t(i)[d],w) for i,w in enumerate(q) if w))

labels=sorted({z for lx,ly in ((2,2),(2,3),(3,2),(3,3)) for k in owned_edge(lx,ly) for z in k})
# Deterministic subset samples across the global label order.
test=labels[::31]
groups=defaultdict(list)
for a in test:groups[parity(a[2])].append(a)
V=vertex(test,groups,2,3)
assert V
used=set()
for (A,B),expected in V.items():
    a,t,x,m=A;b,u,y,n=B
    z=Counter(d for d,q in x+y+((3,0),(2,0)))
    if sorted(z.values())!=[2,4]:continue
    kind=(z[2],bool(expected[1]))
    if kind in used:continue
    used.add(kind)
    d,s=trace_to_local()[a,u];e,w=trace_to_local()[b,t]
    rest=255^(m|n)
    total=(0,0)
    for (l,r,f),(p,q,g) in product(nodes() if z[2]==4 else nodes2(),nodes() if z[3]==4 else nodes2()):
        qs={2:l+r,3:p+q}
        weight=s*w*f*g*wedge_sign(m,n)*wedge_sign(m|n,rest)
        for ax,i in x+y:weight*=qs[ax][i]
        if not weight:continue
        K=wedge(build_t(qs[3],d),build_t(qs[2],e)).get(rest,R.zero).const()
        total=(total[0]+int(K.x)*weight,total[1]+int(K.y)*weight)
    assert total==tuple(256*z for z in expected)
    print('direct local mixed-link quadrature control',kind,expected)
    if len(used)==4:break
assert len(used)==4,used
