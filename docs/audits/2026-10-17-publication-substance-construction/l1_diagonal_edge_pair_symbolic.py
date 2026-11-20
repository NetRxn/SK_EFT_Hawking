from itertools import product, combinations
from l1_direct_b_haar import R,I,eye,zeros,diag,pauli,gamma,bilinear,add,scale,wedge
def quaternion(q):
    return q[0]*eye(2)-I*sum((p*x for p,x in zip(pauli,q[1:])),zeros(2))
def dag(q):
    return (q[0],*(-x for x in q[1:]))
def endpoints(y,a,U,Ud):
    g=gamma[a]
    # Same link leaving site 0, contributing to T_0 and T_y respectively.
    return (add(bilinear(g*Ud,0,y),scale(bilinear(U*g,y,0),-1)),
            add(bilinear(Ud*g,0,y),scale(bilinear(g*U,y,0),-1)))
def averaged_pairs(y):
    ans={(a,b):{} for a,b in product(range(4),repeat=2)}
    for j,s in product(range(4),(-1,1)):
        l=[int(j==k) for k in range(4)];r=[s*x for x in l]
        U=diag(quaternion(l),quaternion(r)); Ud=diag(quaternion(dag(l)),quaternion(dag(r)))
        T=[endpoints(y,a,U,Ud) for a in range(4)]
        for a,b in ans:
            ans[a,b]=add(ans[a,b],wedge(T[a][0],T[b][1]))
    return ans
L=averaged_pairs(1)
R2=averaged_pairs(2)
def rho(q):
    return quaternion(dag(q))-quaternion(q)
delta=diag(rho(R.symbols[:4]),rho(R.symbols[4:]))
t=[bilinear(g*delta+delta*g,0,0) for g in gamma]
G=add(*(wedge(x,x) for x in t))
n=0; first=None
for (c,d),e,f in product(combinations(range(4),2),range(4),range(4)):
    p=add(wedge(L[c,e],R2[d,f]),scale(wedge(L[d,e],R2[c,f]),-1))
    out={m:v for m,v in wedge(G,p).items() if m&255==255}
    if out:
        n+=1
        if first is None: first=((c,d,e,f),len(out))
print('exact antisymmetric tensor components nonzero after local source',n,'first',first)
assert n==0
