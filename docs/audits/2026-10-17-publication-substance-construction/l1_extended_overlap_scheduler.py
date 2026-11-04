"""Signed exact contraction scheduler for every compatible exterior block."""
import argparse
from collections import Counter,defaultdict
from functools import cache,lru_cache
from itertools import product,permutations
from time import perf_counter
import numpy as np
from scipy.sparse import csr_matrix,kron,vstack
from l1_extended_overlap_pure_strip import strip,vector,qproduct,pair,P,Q
from l1_normalization_uniform_mixed_edge import moment

N=36**2
EXTERIOR_FACTOR=23906980319527578894336

def flat(digits,base):
    n=0
    for a in digits:n=n*base+a
    return n

def coords(n,base,length):
    d=[0]*length
    for i in range(length-1,-1,-1):n,d[i]=divmod(n,base)
    return tuple(d)

def matrix(rows):
    if not rows:return csr_matrix((N,N),dtype=np.int64)
    x,y,z=zip(*rows)
    return csr_matrix((z,(x,y)),shape=(N,N),dtype=np.int64)

@cache
def regular():
    S,_=strip()
    grouped=defaultdict(list)
    for (p,a),v in S.items():
        i,j,k,l=p
        grouped[a].append((36*i+j,36*k+l,v))
    return {a:matrix(rows) for a,rows in grouped.items()}

def alpha_bank(sig):
    M=regular()
    zero=matrix(())
    return [M.get(tuple(3*c+x for c,x in zip(sig,a)),zero)
            for a in product(range(3),repeat=4)]

@lru_cache(maxsize=12)
def special_assignment(a,b,c,d,cp):
    # a,b are A/B on even face; c,d are A/B on odd face.
    ce,co=a//4,d//4
    assert b//4==ce and c//4==co
    grouped=defaultdict(Counter)
    for x,y,t in product(Q,repeat=3):
      scalar=qproduct(-x-1,-x-1)[0]
      for i in range(3):
        w=vector(qproduct(y+1,i+2,t+1))
        if w is None:continue
        j,v=w
        for X,Y,Z,T in product(Q,repeat=4):
            p=vector(qproduct(-(a%4)-1,-Y-1,b%4+1,X+1))
            q=vector(qproduct(-(d%4)-1,-T-1,c%4+1,Z+1))
            if p is None or q is None:continue
            u,r=p;h,s=q
            row=36*pair(4*cp+x,4*ce+X)+pair(4*cp+x,4*co+Z)
            col=36*pair(4*cp+y,4*ce+Y)+pair(4*cp+t,4*co+T)
            grouped[flat((u,h,i,j),3)][row,col]-=scalar*v*r*s
    return tuple(matrix([(r,c,v) for (r,c),v in grouped[k].items() if v]) for k in range(81))

def assignments(q0,q1,c,d):
    # For A and B independently assign its unordered pair to even/odd.
    return tuple((a,b,c0,d0) for (a,c0),(b,d0) in
                 product(sorted(set(permutations(q0))),sorted(set(permutations(q1))))
                 if a//4==b//4==c and c0//4==d0//4==d)

def special_bank(raw,cp):
    tables=[special_assignment(*q,cp) for q in raw]
    assert tables
    return [sum((b[i] for b in tables[1:]),tables[0][i].copy()) for i in range(81)]

@cache
def haar():
    H=csr_matrix(np.array([[moment(*a,*b) for b in P] for a in P],dtype=np.int64))
    f=np.array([all(q%4==0 for q in p) for p in P],dtype=np.int64)
    F=csr_matrix(48*np.outer(f,f))
    return kron(H,H,format='csr'),kron(F,H,format='csr')

def norm(A):
    return int(abs(A).sum(axis=1).max()) if A.nnz else 0

def checked(A,B):
    if norm(A)*norm(B)>=2**63:raise OverflowError('int64 sparse product bound')
    return A@B

def pack(rows):
    vals=[];indices=[];ptr=[0]
    for row in rows:
        a,b=row.nonzero()
        vals.extend(np.asarray(row[a,b]).ravel())
        indices.extend(a*N+b)
        ptr.append(len(vals))
    return csr_matrix((np.array(vals,dtype=np.int64),np.array(indices,dtype=np.int32),np.array(ptr,dtype=np.int32)),
                      shape=(6561,N*N))

@lru_cache(maxsize=1)
def left(path3,path0):
    H,F=haar()
    a=[checked(checked(H,s.T),F) for s in alpha_bank(path3)]
    b=[checked(s,H) for s in alpha_bank(path0)]
    return pack(checked(x,y) for x,y in product(a,b))

@lru_cache(maxsize=1)
def right(path1,raw,cp):
    H,_=haar()
    a=[checked(s,H) for s in special_bank(raw,cp)]
    b=[s.T for s in alpha_bank(path1)]
    return pack(checked(x,y) for x,y in product(a,b))

def exterior(path):
    out=defaultdict(list)
    with open(path) as stream:
        for line in stream:
            i,j,key,r,s=map(int,line.split())
            assert not s
            a=coords(key,6,8)
            sig=tuple(v//3 for v in a)
            comp=tuple(v%3 for v in a)
            out[sig,(i,j)].append((comp,r))
    return out

def jobs(groups):
    by=defaultdict(list)
    for sig,q in groups:
        by[(tuple(sig[k] for k in (0,1,6,7)),sig[5],(q[0]//4,q[1]//4))].append((sig,q))
    # Root-side path keys first for reuse of all fixed factors.
    out=[]
    for (pure,c,qch),items in by.items():
        for d in range(2):
            m=tuple(sorted((c,d)))
            if qch!=m:continue
            for (sig,q),(sig2,q2) in product(items,by[pure,d,m]):
                x=paths(sig,sig2)
                out.append((x[0],x[1],x[2],sig,q,sig2,q2))
    return sorted(out)

def paths(a,b):
    # For each edge: (nonpure even, nonpure odd, pure even, pure odd).
    return tuple(tuple(v for n in (nonpure,pure) for v in (a[n],b[n]))
                 for pure,nonpure in ((0,2),(6,4),(1,3)))

def indices(a,b,pure,nopure):
    x,y=a[:,nopure],a[:,pure]
    u,v=b[:,nopure],b[:,pure]
    return (((x[:,None]*3+u)*3+y[:,None])*3+v).astype(np.int32)

def exact_vector_sum(gauge, a, b):
    if not len(gauge):return 0
    product_bound=int(np.max(np.abs(gauge)))*int(np.max(np.abs(a)))*int(np.max(np.abs(b)))
    if product_bound>=2**63:
        return sum(int(x)*int(y)*int(z) for x,y,z in zip(gauge,a,b,strict=True))
    if not product_bound:return 0
    values=gauge*a*b
    batch=min(len(values),(2**63-1)//product_bound)
    count=len(values)//batch
    bulk=values[:count*batch].reshape(count,batch).sum(axis=1,dtype=np.int64)
    return sum(map(int,bulk))+int(values[count*batch:].sum(dtype=np.int64))


def kernel(L,R,A,B):
    a=np.array([x for x,_ in A],dtype=np.int16)
    b=np.array([x for x,_ in B],dtype=np.int16)
    s3,s0,s2,s1=(indices(a,b,p,n) for p,n in ((0,2),(6,4),(7,5),(1,3)))
    u=(81*s3+s0).ravel();v=(81*s2+s1).ravel()
    order=np.argsort(u,kind='stable')
    U=u[order];V=v[order]
    total=0;live=0;peak=0
    weights = [[divmod(w, EXTERIOR_FACTOR) for _, w in column] for column in (A, B)]
    assert all(rest == 0 and abs(value) <= 3264 for column in weights for value, rest in column)
    wa, wb = (np.array([value for value, _ in column], dtype=np.int64) for column in weights)
    assert norm(L)*norm(R)<2**63
    for i in range(0,6561,128):
        j=min(i+128,6561);lo,hi=np.searchsorted(U,[i,j])
        if lo==hi:continue
        G=L[i:j]@R.T
        peak=max(peak,G.nnz)
        values=np.asarray(G[U[lo:hi]-i,V[lo:hi]]).ravel()
        flat_pos=order[lo:hi]
        total+=exact_vector_sum(values,wa[flat_pos//len(B)],wb[flat_pos%len(B)])
        live+=int(np.count_nonzero(values))
    return total*EXTERIOR_FACTOR**2,len(U),live,peak

def main():
    p=argparse.ArgumentParser()
    p.add_argument('column_rows')
    p.add_argument('--signature',nargs=2)
    p.add_argument('--limit',type=int)
    p.add_argument('--start',type=int,default=0)
    args=p.parse_args()
    start=perf_counter();groups=exterior(args.column_rows);plan=jobs(groups)
    assert sum(len(groups[s,q])*len(groups[t,r]) for _,_,_,s,q,t,r in plan)==94748063904
    print('coverage plan',len(plan),'blocks; signed pairs 94748063904',flush=True)
    if args.signature:
        s,t=(tuple(map(int,a)) for a in args.signature)
        plan=[x for x in plan if x[3]==s and x[5]==t]
        plan.sort(key=lambda x:(x[4],x[6]))
    plan=plan[args.start:]
    if args.limit is not None:plan=plan[:args.limit]
    total=0;attempted=0
    for a,b,c,s,q,t,r in plan:
        tick=perf_counter()
        raw=assignments(q,r,s[5],t[5])
        L=left(a,b);R=right(c,raw,s[7])
        value,count,live,peak=kernel(L,R,groups[s,q],groups[t,r])
        total+=value;attempted+=count
        print('block',flat(s,2),q,flat(t,2),r,'mixed placements',len(raw),
              'pairs/live/peak',count,live,peak,'raw',value,
              'seconds',perf_counter()-tick,flush=True)
    print('completed',len(plan),'blocks',attempted,'pairs','raw subtotal',total,
          'left reuse',left.cache_info(),'right reuse',right.cache_info(),
          'seconds',perf_counter()-start,flush=True)
if __name__=='__main__':main()
