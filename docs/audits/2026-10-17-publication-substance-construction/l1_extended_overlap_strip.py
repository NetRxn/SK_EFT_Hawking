"""Tree-fixed two-mixed-link strip in the saturated 2^4 motif."""
from collections import Counter,defaultdict
from itertools import combinations_with_replacement, product
from functools import cache
from time import perf_counter
from l1_normalization_uniform_mixed_edge import unit,mul,qadj,moment

Q=range(4)
PAIRS=tuple(combinations_with_replacement(range(8),2))
HAAR={p:tuple((j,z) for j,q in enumerate(PAIRS) if (z:=moment(*p,*q)))
      for p in PAIRS}

@cache
def vector(a,b,c,d):
    q=mul(mul(qadj(unit(a)),qadj(unit(b))),mul(unit(c),unit(d)))
    return q[1:]

def rows():
    # Faces (4,0,1) and (5,0,1). Let A=U(4,1), B=U(5,1).
    # Closed loops A† U(6,0)† B U(4,0), B† U(7,0)† A U(5,0).
    for ca,cb in product(range(2),repeat=2):
        for u,v,w,x in product(Q,repeat=4):
            channels=[Counter() for _ in range(9)]
            for a,b,c,d in product(Q,repeat=4):
                alpha=vector(a,v,b,u)
                beta=vector(d,x,c,w)
                if not any(alpha) or not any(beta):continue
                pa=tuple(sorted((4*ca+a,4*cb+c)))
                pb=tuple(sorted((4*ca+b,4*cb+d)))
                for i,va in enumerate(alpha):
                    if not va:continue
                    for j,vb in enumerate(beta):
                        if not vb:continue
                        for r,z in HAAR[pa]:
                            for s,t in HAAR[pb]:
                                channels[3*i+j][r,s]+=va*vb*z*t
            for i,c in enumerate(channels):
                nz={key:w for key,w in c.items() if w}
                if nz:yield (ca,cb,u,v,w,x,i),nz

def fixed_tree():
    t={(x,3) for x in range(8)}|{(0,0)}
    for x in (0,1):t.update(((x,1),(x,2),(x^2,2)))
    graph=defaultdict(set)
    for x,d in t:
        y=x^(1<<d)
        graph[x].add(y);graph[y].add(x)
    reach={0}
    while True:
        nxt=reach|set().union(*(graph[x] for x in reach))
        if nxt==reach:break
        reach=nxt
    assert len(reach)==16 and len(t)==15
    return t

def pure_patch():
    # Exact degree-four integration of U(2,0) on a physical slice.
    # Set other transverse cycle links to identity, leave U(6,0)
    # symbolic in one unit coordinate. Product of four vector insertions.
    counts=Counter()
    coefficients=Counter()
    identity=unit(0)
    for sectors in product(range(2),repeat=4):
        for i in Q:
            out=Counter()
            for q in product(Q,repeat=4):
                w=moment(*(4*c+j for c,j in zip(sectors,q)))
                if not w:continue
                a,b,c,d=map(unit,q)
                # (0,0,1), (2,0,1), (2,0,2), (6,0,2).
                vs=(qadj(a)[1:], b[1:], mul(qadj(unit(i)),c)[1:],
                    mul(qadj(d),unit(i))[1:])
                for v in product(range(3),repeat=4):
                    k=w
                    for a,j in zip(vs,v):k*=a[j]
                    if k:out[v]+=k
            nz=[v for v in out.values() if v]
            counts[sectors]+=len(nz)
            coefficients.update(nz)
    print('curvature-only link projected slice supports',sum(counts.values()),
          'nonzero chirality assignments',sum(bool(x) for x in counts.values()),
          'coefficient histogram',dict(sorted(coefficients.items())),flush=True)

if __name__=='__main__':
    start=perf_counter()
    print('tree',sorted(fixed_tree()),flush=True)
    pop=Counter(); columns=defaultdict(set);peak=0
    values=Counter()
    for key,row in rows():
        ch=key[:2]
        pop[ch,'rows']+=1
        pop[ch,'nnz']+=len(row)
        columns[ch].update(row)
        peak=max(peak,len(row))
        values.update(row.values())
    print('strip row/entry populations',dict(sorted(pop.items())),flush=True)
    print('strip nonzero frame column pairs',{k:len(v) for k,v in columns.items()},'max row',peak,flush=True)
    print('strip exact coefficient histogram',dict(sorted(values.items())),flush=True)
    pure_patch()
    print('seconds',perf_counter()-start)
