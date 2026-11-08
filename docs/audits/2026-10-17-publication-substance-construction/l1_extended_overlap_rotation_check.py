"""Check exact signed chiral quaternion-permutation covariance of all exterior rows."""
import numpy as np
from time import perf_counter
from sys import argv
N=2321664
SIZE=6**8

def load():
    q=np.empty((2,N),dtype=np.int8)
    a=np.empty((8,N),dtype=np.int8)
    high=np.empty(N,dtype=np.uint64);low=high.copy()
    neg=np.empty(N,dtype=bool)
    code=np.empty(N,dtype=np.int64)
    with open(argv[1]) as f:
        for n,line in enumerate(f):
            i,j,k,r,s=map(int,line.split())
            assert not s
            q[:,n]=(i,j);neg[n]=r<0
            rr=abs(r);high[n]=rr>>64;low[n]=rr&((1<<64)-1)
            code[n]=(8*i+j)*SIZE+k
            for m in range(7,-1,-1):k,a[m,n]=divmod(k,6)
    assert n+1==N
    order=np.argsort(code)
    return q,a,high,low,neg,code[order],order

def check(data,ch,per,sg):
    q,a,high,low,neg,keys,order=data
    aq=np.arange(8,dtype=np.int8);ap=np.arange(6,dtype=np.int8)
    sq=np.zeros(8,dtype=bool);sp=np.zeros(6,dtype=bool)
    for v in range(3):
        aq[4*ch+v+1]=4*ch+per[v]+1
        ap[3*ch+v]=3*ch+per[v]
        sq[4*ch+v+1]=sp[3*ch+v]=sg[v]<0
    dest=np.sort(aq[q],axis=0)
    key=(8*dest[0].astype(np.int64)+dest[1])*SIZE
    sign=neg^sq[q[0]]^sq[q[1]]
    for j in range(8):
        key+=ap[a[j]].astype(np.int64)*6**(7-j)
        sign^=sp[a[j]]
    idx=np.searchsorted(keys,key)
    assert np.all(idx<N) and np.all(keys[idx]==key)
    idx=order[idx]
    bad=np.count_nonzero((high[idx]!=high)|(low[idx]!=low)|(neg[idx]!=sign))
    print('chiral rotation',ch,per,sg,'exact failures',bad,flush=True)
    assert bad==0

if __name__=='__main__':
    start=perf_counter()
    D=load()
    for ch in range(2):
        check(D,ch,(1,2,0),(1,1,1))
        check(D,ch,(1,0,2),(1,1,-1))
    print('seconds',perf_counter()-start)
