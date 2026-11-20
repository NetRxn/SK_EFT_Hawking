from collections import defaultdict,Counter
from functools import cache
from itertools import product
from fractions import Fraction as F
from l1_normalization_shared_transport import quat,adj
from l1_direct_b_haar import R,diag,gamma,bilinear,add,scale,wedge,haar_moment
from l1_direct_a_haar import mul,adj as qadj

@cache
def unit(i):
    return tuple(int(i==j) for j in range(4))

@cache
def t_basis(i):
    l=unit(i) if i<4 else (0,)*4
    r=unit(i-4) if i>=4 else (0,)*4
    U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
    a=[add(bilinear(g*Ud,0,1),scale(bilinear(U*g,1,0),-1)) for g in gamma]
    b=[add(bilinear(Ud*g,0,1),scale(bilinear(g*U,1,0),-1)) for g in gamma]
    return a,b

@cache
def moment(i,j,s,t):
    n=Counter((i,j,s,t))
    ex=tuple(n[k] for k in range(8))
    q=48*haar_moment(ex[:4])*haar_moment(ex[4:])
    assert q.denominator==1
    return int(q)

@cache
def projection(alpha,a,b,i,j):
    ch,v=divmod(alpha,3)
    assert a//4==b//4==ch
    X,Y=unit(a%4),unit(b%4)
    total=0
    for s,t in product(range(4),repeat=2):
        w=moment(i,j,4*ch+s,4*ch+t)
        if w:
            q=mul(mul(unit(s),Y),mul(qadj(unit(t)),qadj(X)))
            total+=w*q[v+1]
    return total

@cache
def tt(i,j,t,u):
    a,b=t_basis(i),t_basis(j)
    return wedge(a[0][t],b[1][u])

@cache
def edge():
    out={}
    for alpha in range(6):
        ch=alpha//3
        for a,b in product(range(4*ch,4*ch+4),repeat=2):
            terms=[(i,j,w) for i,j in product(range(8),repeat=2)
                   if (w:=projection(alpha,a,b,i,j))]
            if not terms:continue
            for beta,t,u in product(range(6),range(4),range(4)):
                cb,v=divmod(beta,3)
                x=tuple(sorted((a,4*cb)))
                y=tuple(sorted((b,4*cb+v+1)))
                p=add(*(scale(tt(i,j,t,u),-w) for i,j,w in terms))
                if p:
                    key=(alpha,beta,t,u,x,y)
                    out[key]=add(out.get(key,{}),p)
    return {k:v for k,v in out.items() if v}

if __name__=='__main__':
    E=edge()
    print('exact uniform-mixed edge rows',len(E),'exterior terms',sum(map(len,E.values())),
          'max row',max(map(len,E.values())))
    assert all((m&255).bit_count()==2 and (m>>8).bit_count()==2 for p in E.values() for m in p)
    print('site boundary labels',*[len({(k[z],k[2+z],k[4+z],(m>>(8*z))&255)
                                        for k,p in E.items() for m in p}) for z in (0,1)])
