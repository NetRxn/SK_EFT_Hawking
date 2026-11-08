"""Exact full factored U(6,0) projection with both remaining closed faces."""
from collections import Counter,defaultdict
from itertools import product
from time import perf_counter
from sys import argv
from l1_normalization_uniform_mixed_edge import moment,mul,qadj,unit

Q=range(4)
S=range(8)

def project_left():
    weights={(i,j):[(a,b,w) for a,b in product(S,repeat=2) if (w:=moment(i,j,a,b))]
             for i,j in product(S,repeat=2) if i<=j}
    data=defaultdict(Counter)
    source=Counter()
    with open(argv[1]) as f:
        for line in f:
            boundary,curv,value=map(int,line.split())
            i,j=(boundary>>3)&7,boundary&7
            left=boundary>>6
            source[left,curv,i,j]+=value
            for a,b,w in weights[i,j]:
                data[a,b][left,curv]+=w*value
    return source,{k:{key:z for key,z in row.items() if z} for k,row in data.items()}

def build_right():
    # E=(4,0,1), F=(6,0,1). The retained port order:
    # (4,1), (5,1), (6,1), (7,1), and a sorted pair for (4,0).
    # E=A† U6† B U4, F=C† U4† D U6.
    out={}
    for a,b in product(S,repeat=2):
        c,d=a//4,b//4
        E=tuple(qadj(unit(a%4)))
        F=unit(b%4)
        rows=Counter()
        for A,B,C,D,i,j in product(Q,repeat=6):
            p=mul(mul(qadj(unit(A)),E),mul(unit(B),unit(i)))
            q=mul(mul(qadj(unit(C)),qadj(unit(j))),mul(unit(D),F))
            if not any(p[1:]) or not any(q[1:]):continue
            i,j=sorted((4*c+i,4*d+j))
            key=(4*c+A,4*c+B,4*d+C,4*d+D,i,j)
            for u,v in product(range(3),repeat=2):
                z=p[u+1]*q[v+1]
                if z:rows[key,6*(3*c+u)+3*d+v]+=z
        out[a,b]={k:z for k,z in rows.items() if z}
    return out

def check_identity(source,A,B):
    # Compare direct shared Haar of raw coefficients with independently
    # specialized right tensor at all retained right links = Spin(4) identity.
    right={}
    for ab,row in B.items():
        values=Counter()
        for (ports,curv),z in row.items():
            if all(i%4==0 for i in ports):values[curv]+=z
        right[ab]=values
    direct=Counter()
    factored=Counter()
    # Select A's physical identity boundary for its four retained links.
    lefts={key[:2] for key in source if all((key[0]>>s)&3==0 for s in (0,3,6,9))}
    for (left,curv,i,j),z in source.items():
        if (left,curv) not in lefts:continue
        for (a,b),row in right.items():
            h=moment(i,j,a,b)
            if h:
                for e,f in row.items():direct[left,curv,e]+=z*h*f
    for ab,row in A.items():
        for (left,curv),z in row.items():
            if (left,curv) not in lefts:continue
            for e,f in right[ab].items():factored[left,curv,e]+=z*f
    assert {k:v for k,v in direct.items() if v}=={k:v for k,v in factored.items() if v}
    print('independent direct identity-boundary control',sum(bool(z) for z in direct.values()),flush=True)

if __name__=='__main__':
    start=perf_counter()
    source,A=project_left()
    B=build_right()
    check_identity(source,A,B)
    usable=set(A)&set(B)
    print('live ordered U6 slots',len(usable),flush=True)
    print('left projected entries',sum(map(len,A.values())),'peak slot',max(map(len,A.values())),flush=True)
    print('right exact entries',sum(map(len,B.values())),'peak slot',max(map(len,B.values())),flush=True)
    print('raw outer products in dense fusion',sum(len(A[k])*len(B[k]) for k in usable),flush=True)
    print('seconds',perf_counter()-start)
