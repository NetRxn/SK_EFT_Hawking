from collections import defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from re import search
from l1_transverse_top import G,haar_moment
from l1_direct_b_haar import I,eye,zeros,diag,pauli,gamma
from l1_reduced_wedge_reference import wedge_sign

zero=(F(0),F(0))
def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def moments(e):
    return haar_moment(e[:4])*haar_moment(e[4:])
def add_indices(e,*inds):
    return tuple(x+inds.count(i) for i,x in enumerate(e))
empty=(0,)*8

@cache
def curv(a,b):
    if a==b:return ()
    basis=[eye(2)]+[-I*p for p in pauli]
    dag=[eye(2)]+[I*p for p in pauli]
    g5=diag(1,1,-1,-1)
    test=gamma[a]*gamma[b]*g5
    out=[]
    for ch in range(2):
        cut=test[2*ch:2*ch+2,2*ch:2*ch+2]
        for i,j,k,l in product(range(4),repeat=4):
            z=(basis[i]*basis[j]*dag[k]*dag[l]*cut).trace().expand()
            if not z:continue
            x=add_indices(empty,4*ch+i,4*ch+k)
            y=add_indices(empty,4*ch+j,4*ch+l)
            out.append((x,y,(int(z.as_real_imag()[0]),int(z.as_real_imag()[1]))))
    return tuple(out)

@cache
def source(mask,i,j,a,b):
    """E[X_i X_j (G_X−G_Y) L_ab(U_X U_Y U_X† U_Y†)]."""
    total=[F(0),F(0)]
    if a==b:return tuple(total)
    for x,y,z in curv(a,b):
        x=add_indices(x,i,j)
        for e,c in G.get(mask,{}).items():
            x_e=tuple(s+t for s,t in zip(x,e))
            y_e=tuple(s+t for s,t in zip(y,e))
            w=moments(x_e)*moments(y)-moments(x)*moments(y_e)
            if w:
                for k,r in enumerate(mul((int(c.x),int(c.y)),z)):
                    total[k]+=w*r
    return tuple(total)

def read(path):
    for line in open(path):
        m=search(r'exact slice (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) scaled Gaussian \((-?\d+),(-?\d+)\)/5308416',line)
        if m:
            a,b,u,v,c,d,r,i=map(int,m.groups())
            if r or i:yield a,b,u,v,c,d,(r,i)

def contract(left,right):
    out=[F(0),F(0)]
    pairs=0
    for (i,j,u,v,a,d,L),(k,l,w,z,b,c,R) in product(left,right):
        if u&w or v&z or a==b or c==d:continue
        j0=255^(u|w);j3=255^(v|z)
        src=mul(source(j0,i,k,a,b),source(j3,j,l,c,d))
        if not any(src):continue
        pairs+=1
        # All center and boundary degrees are even, so their site reorders
        # introduce no further sign. The two center action epsilons are even
        # under time/space exchange. Source axis exchange reverses both D and L.
        sign=wedge_sign(u,w)*wedge_sign(v,z)*wedge_sign(u|w,j0)*wedge_sign(v|z,j3)
        for t,r in enumerate(mul(src,mul(L,R))):out[t]+=sign*r
    return tuple(q/(48**8*16**8) for q in out),pairs

if __name__=='__main__':
    from sys import argv
    a,b=map(lambda p:list(read(p)),argv[1:3])
    print('center nonzeros',len(a),len(b),'residual representative',contract(a,b))
