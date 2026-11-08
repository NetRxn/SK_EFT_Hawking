"""Exact whole-column temporal Haar join, mixed spatial legs retained."""
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations_with_replacement, product
from sys import argv
from time import perf_counter
import numpy as np
from scipy.sparse import csr_matrix
from l1_normalization_uniform_mixed_edge import moment, mul, qadj, unit

PAIRS=tuple(combinations_with_replacement(range(8),2))
PID={p:i for i,p in enumerate(PAIRS)}
H=np.array([[moment(*p,*q) for q in PAIRS] for p in PAIRS],dtype=np.int64)
fixed=np.array([int(all(i%4==0 for i in p)) for p in PAIRS],dtype=np.int64)
ROOT=48*np.outer(fixed,fixed)

@cache
def coeff(i,j,own=None,other=None):
    # Q = own† U_z† other U_y; omit spatial factors for identity.
    if own is None:return tuple(mul(qadj(unit(j)),unit(i)))[1:]
    return tuple(mul(mul(qadj(unit(own)),qadj(unit(j))),mul(unit(other),unit(i))))[1:]

@cache
def edge(alpha,beta,own=None,other=None):
    ca,a=divmod(alpha,3);cb,b=divmod(beta,3)
    K=np.zeros((36,36),dtype=np.int64)
    for i,j,k,l in product(range(4),repeat=4):
        # Forward face uses U_y[i], U_z[j]; backward face uses U_z[k], U_y[l].
        z=coeff(i,j,own,other)[a]*coeff(k,l)[b]
        if z:
            x=PID[tuple(sorted((4*ca+i,4*cb+l)))]
            y=PID[tuple(sorted((4*ca+j,4*cb+k)))]
            K[x,y]+=z
    return K

def paths(a,b,c,d,e,f,fixroot):
    return H @ edge(a,b) @ (ROOT if fixroot else H) @ edge(c,d) @ H @ edge(e,f) @ H

def temporal_tables():
    special=csr_matrix(np.stack([edge(u,v,x,y).ravel()
                                  for u,v in product(range(6),repeat=2)
                                  for x,y in product(range(4),repeat=2)]))
    table=np.zeros((2,6**6,36,16),dtype=np.int32)
    live=0
    for p,labels in enumerate(product(range(6),repeat=6)):
        for col in (0,1):
            r=paths(*labels,col==0)
            if not np.any(r):continue
            out=(special @ r.ravel()).reshape(36,16)
            assert np.max(np.abs(out))<=48**4
            table[col,p]=out
            live+=np.count_nonzero(out)
    print('exact temporal table entries',live,flush=True)
    return table

def digits(key):
    a=[0]*8
    for i in range(7,-1,-1):key,a[i]=divmod(key,6)
    assert not key
    return a

def build(path):
    table=temporal_tables()
    out=[Counter(),Counter()]
    admitted=0
    with open(path) as f:
        for line in f:
            i,j,key,r,s=map(int,line.split())
            assert not s
            M4,M6,M0,M2,O0,O4,O2,O6=digits(key)
            p=0
            for a in (M4,M0,O0,O2,M2,M6):p=6*p+a
            ch=4*(O4//3)
            live=False
            for col in (0,1):
                weights=table[col,p,6*O4+O6]
                for k in weights.nonzero()[0]:
                    u,v=divmod(int(k),4)
                    out[col][i,j,ch+u,ch+v]+=r*int(weights[k])
                    live=True
            admitted+=live
    print('alpha rows with nonzero temporal coefficient',admitted,flush=True)
    return [{k:z for k,z in r.items() if z} for r in out]

def join(C):
    total=0
    n=0
    for a,b,c,d in product(range(8),repeat=4):
        # column even: raw A coordinate a, B coordinate b.
        # column odd: raw A coordinate c, B coordinate d.
        qa=tuple(sorted((a,c)));qb=tuple(sorted((b,d)))
        x=C[0].get((*qa,a,b),0)
        y=C[1].get((*qb,d,c),0)
        if x and y:n+=1;total+=x*y
    print('live mixed join assignments',n,'of 4096',flush=True)
    return total

if __name__=='__main__':
    start=perf_counter()
    path=argv[1]
    C=build(path)
    print('nonzero even/odd boundary entries',*[len(c) for c in C],flush=True)
    # Exterior numerators retain 48 and frame factors; this denominator
    # here is only the eight projected temporal moments.
    raw=join(C)
    print('specialized full contraction numerator',raw,flush=True)
    print('after temporal denominator',Fraction(raw,48**8),flush=True)
    print('seconds',perf_counter()-start,flush=True)
