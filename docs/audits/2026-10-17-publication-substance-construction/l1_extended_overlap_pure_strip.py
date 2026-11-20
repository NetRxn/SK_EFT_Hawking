"""Exact two-column strip after its pure transverse anchor pair is projected."""
from collections import Counter,defaultdict
from itertools import combinations_with_replacement,product
from functools import cache
from time import perf_counter
from l1_normalization_uniform_mixed_edge import unit,mul,qadj

Q=range(4)
P=tuple(combinations_with_replacement(range(8),2))
PID={k:i for i,k in enumerate(P)}
def pair(a,b):return PID[tuple(sorted((a,b)))]

@cache
def qproduct(*args):
    out=unit(0)
    for k in args:
        q=unit(abs(k)-1)
        out=tuple(mul(out,qadj(q) if k<0 else q))
    return out

def vector(q):
    return next(((i,v) for i,v in enumerate(q[1:]) if v),None)

def strip(mixed=False):
    # End 0 is the nonpure anchor; end 1 is the pure anchor.
    # Each row retains time pair indices at ends 0/1 in both columns.
    out=Counter()
    raw=0
    for c,ce,co in product(range(2),repeat=3):
      for x,z in product(Q,repeat=2):
        # scalar(W_0† U_0†) vanishes unless coordinates coincide.
        if x!=z:continue
        scalar=qproduct(-z-1,-x-1)[0]
        for y,t,i in product(Q,Q,range(3)):
          b=vector(qproduct(y+1,i+2,t+1))
          if b is None:continue
          j,v=b
          for X,Y,Z,T in product(Q,repeat=4):
            ends=(pair(4*c+x,4*ce+X),pair(4*c+z,4*co+Z),
                  pair(4*c+y,4*ce+Y),pair(4*c+t,4*co+T))
            if mixed:
                # At end 0 the even/odd nonpure face uses own† U1† other U0.
                # Preserve its two spatial coordinates independently for A/B.
                for a,b,d,e in product(Q,repeat=4):
                    p=vector(qproduct(-a-1,-Y-1,b+1,X+1))
                    q=vector(qproduct(-d-1,-T-1,e+1,Z+1))
                    if p is None or q is None:continue
                    u,r=p;w,s=q
                    out[ends,(3*ce+u,3*co+w,3*c+i,3*c+j),
                        (4*ce+a,4*ce+b,4*co+e,4*co+d)]-=scalar*v*r*s
                    raw+=1
            else:
                p=vector(qproduct(-Y-1,X+1));q=vector(qproduct(-T-1,Z+1))
                if p is None or q is None:continue
                u,r=p;w,s=q
                out[ends,(3*ce+u,3*co+w,3*c+i,3*c+j)]-=scalar*v*r*s
                raw+=1
    return {k:v for k,v in out.items() if v},raw

if __name__=='__main__':
    start=perf_counter()
    S,raw=strip()
    grouped=defaultdict(Counter)
    for (ends,alphas),v in S.items():grouped[alphas][ends]=v
    print('pure-pair /4 strip','raw',raw,'exact rows',len(S),'alpha patterns',len(grouped),
          'peak per alpha',max(map(len,grouped.values())),
          'paired endpoint states',len({e[:2] for e,a in S}),len({e[2:] for e,a in S}),
          'coefficient histogram',dict(sorted(Counter(S.values()).items())),
          'seconds',perf_counter()-start)
