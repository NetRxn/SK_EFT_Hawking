from collections import defaultdict,Counter
from fractions import Fraction as F
from functools import cache
from itertools import product,combinations
from math import lcm
from re import search
from l1_residual_source_contract import G,curv,mul,add_indices,wedge_sign
from l1_residual_source_contract import moments as raw_moments
from l1_residual_groups import residual

moments=cache(raw_moments)
@cache
def external_moments(x):
    out=[]
    for i,j in product(range(8),repeat=2):
        z=moments(add_indices(x,i,j))
        if z:out.append((i,j,z))
    return tuple(out)

def source_table():
    table=defaultdict(lambda:[F(0),F(0)])
    for a,b in combinations(range(4),2):
        for x,y,z in curv(a,b):
            ey=moments(y)
            for m,g in G.items():
                for e,c in g.items():
                    value=mul((int(c.x),int(c.y)),z)
                    if ey:
                        for i,j,v in external_moments(tuple(t+u for t,u in zip(x,e))):
                            r=table[m,i,j,a,b]
                            for k,w in enumerate(value):r[k]+=ey*v*w
                    ey_g=moments(tuple(t+u for t,u in zip(y,e)))
                    if ey_g:
                        for i,j,v in external_moments(x):
                            r=table[m,i,j,a,b]
                            for k,w in enumerate(value):r[k]-=ey_g*v*w
    return {k:tuple(v) for k,v in table.items() if any(v)}

def adjacency(table):
    den=lcm(*(w.denominator for v in table.values() for w in v))
    out=defaultdict(list)
    for (m,i,j,a,b),v in table.items():
        assert m.bit_count()==4
        others=[1<<d for d in range(8) if not m>>d&1]
        for r,s in combinations(others,2):
            u=r|s;w=255^(m|u)
            sg=wedge_sign(u,w)*wedge_sign(u|w,m)
            val=tuple(int(sg*z*den) for z in v)
            out[i,u,a].append(((j,w,b),val))
            out[i,u,b].append(((j,w,a),tuple(-z for z in val)))
    return out,den

def read(family):
    tensors=defaultdict(dict)
    for line in open('l1_residual_batched_'+family+'.out'):
        m=search(r'variant (\d+) exact slice (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) scaled Gaussian \((-?\d+),(-?\d+)\)/5308416',line)
        assert m
        v,a,b,u,w,c,d,r,i=map(int,m.groups())
        key=((a,u,c),(b,w,d))
        assert key not in tensors[v]
        tensors[v][key]=(r,i)
    return tensors
def contract(A,B,links,den):
    total=[0,0]
    found=0
    for (a,b),v in A.items():
        for c,s0 in links[a]:
            for d,s3 in links[b]:
                w=B.get((c,d))
                if w is None:continue
                found+=1
                # Site 3 orders curvature gamma indices (right,left).
                for k,z in enumerate(mul(mul(v,w),mul(s0,s3))):
                    total[k]-=z
    return tuple(F(x,48**8*16**8*den**2) for x in total),found

if __name__=='__main__':
    table=source_table()
    links,den=adjacency(table)
    print('source covariance entries',len(table),'denominator',den,'adjacency edges',sum(map(len,links.values())))
    data={f:read(f) for f in ('same','mixed')}
    total=[F(0),F(0)]
    for (f,s,t),n in sorted(residual.items()):
        a,b=data[f][s],data[f][t]
        ans,m=contract(a,b,links,den)
        assert ans==contract(b,a,links,den)[0]
        print(f,s,t,'centers',len(a),len(b),'pairs',m,'multiplicity',n,'representative',ans)
        for k,z in enumerate(ans):total[k]+=n*z
    print('residual total',tuple(total))
    print('full diagonal plus numerator coefficient',total[0]+F(25,1536),total[1])
