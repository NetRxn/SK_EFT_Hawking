"""Bounded 2^4 mixed-plane inter-sheet contraction after private Haar projection."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from itertools import permutations
from math import factorial,prod
from time import perf_counter
from l1_extended_split_layer import curvature,full_fourth,tuples,clean
from l1_direct_b_haar import add,scale,wedge
from l1_reduced_wedge_reference import wedge_sign

ACTIVE=tuple(x for x in range(16) if x.bit_count()%2==0)
DEN=48*(96*8**4)**2*factorial(4)

def centers(summed):
    A,B=(full_fourth(d,summed) for d in (0,1))
    C={}
    for a in tuples:
        mult=factorial(4)//prod(factorial(n) for n in Counter(a).values())
        for b in tuples:
            weight=sum(curvature(tuple(sorted(zip(a,y)))) for y in set(permutations(b)))
            if weight:
                C=add(C,scale(wedge(A[a],B[b]),mult*weight))
    out={}
    for mask,value in clean(C).items():
        if mask&255!=255:continue
        assert mask>>24==0 and ((mask>>8)&255).bit_count()==((mask>>16)&255).bit_count()==4
        assert value.is_ground and value.const().y==0
        out[(mask>>8)&255,(mask>>16)&255]=int(value.const().x)
    return out

def setup(flipped):
    graph=defaultdict(list)
    frames=set()
    curves={}
    for x in ACTIVE:
        k,l=(0,2) if x in flipped else (0,1)
        a,b=(axis for axis in range(4) if axis not in (k,l))
        u,v=x^(1<<a),x^(1<<b)
        graph[u].append((v,x,False))
        graph[v].append((u,x,True))
        frames.update(((x,a),(u,a),(x,b),(v,b)))
        curves[x]={(x,k),(x^(1<<k),l),(x^(1<<l),k),(x,l)}
    all_curves=set().union(*curves.values())
    assert len(all_curves)==4*len(ACTIVE)
    # These active-base ports never occur in any allowed frame anchor,
    # including in the mixed sector where some other ports are shared.
    for x,p in curves.items():
        assert any(y==x and (y,d) not in frames for y,d in p)
    print('planes switched at',sorted(flipped),'curvature/frame shared links',
          len(frames & all_curves),flush=True)
    assert all(len(g)==2 for g in graph.values())
    return graph

def cycle_tables(graph):
    remaining=set(graph)
    while remaining:
        start=min(remaining)
        path=[]
        current=start
        incoming=None
        while True:
            destination,center,reverse=next(e for e in graph[current] if e[1]!=incoming)
            path.append((center,reverse))
            remaining.discard(current)
            current,incoming=destination,center
            if current==start:break
        yield path

def cycle_contraction(path,tensor):
    def directed(reverse):
        return {(b,a) if reverse else (a,b):v for (a,b),v in tensor.items()}
    live=directed(path[0][1])
    counts=[len(live)]
    for _,reverse in path[1:]:
        right=defaultdict(list)
        for (m,n),w in directed(reverse).items():
            right[m].append((n,w))
        out=Counter()
        for (first,last),z in live.items():
            other=255^last
            sign=wedge_sign(last,other)
            for end,w in right.get(other,()):
                out[first,end]+=sign*z*w
        live={k:v for k,v in out.items() if v}
        counts.append(len(live))
    raw=sum(w*wedge_sign(b,a) for (a,b),w in live.items() if (a^b)==255)
    return F(raw,DEN**len(path)),counts

def evaluate(flipped,tensor):
    values=[]
    for path in cycle_tables(setup(flipped)):
        val,counts=cycle_contraction(path,tensor)
        print('cycle',path,'boundary entries',counts,'exact',val,flush=True)
        values.append(val)
    print('exact bounded subnetwork',prod(values),flush=True)
    return values

if __name__=='__main__':
    start=perf_counter()
    C=centers(True)
    print('post-Haar center rows',len(C),flush=True)
    assert evaluate(set(),C)==[F(9995625,131072)]*4
    V=evaluate({0,6},C)
    assert sorted(V.count(v) for v in set(V))==[1,2] and all(V)
    print('seconds',perf_counter()-start)
