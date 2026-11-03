from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from dataclasses import dataclass
from l1_normalization_shared_transport import pair,local_pair,L,add,wedge,scale,cross_weight
from l1_normalization_transport_cycle import ORDERED,M,edge_base,DIM,poly_int,signed_mul,wedge_sign
from l1_normalization_correlated_cases import census, size_six_census

TOP=(1<<32)-1
ONE={0:(1,0)}
counts=Counter()

def plus(dst,word,val):
    if not any(val):return
    z=dst.get(word,(0,0))
    dst[word]=z[0]+val[0],z[1]+val[1]

def cleaned(p):
    return {k:v for k,v in p.items() if any(v)}

def join(dst,A,B,weight=1,saturate=0,buckets=None):
    if not A or not B:return
    if saturate and buckets is None:
        buckets=defaultdict(list)
        for m,v in B.items():buckets[m&saturate].append((m,v))
    for m,v in A.items():
        right=B.items() if not saturate else buckets.get((m&saturate)^saturate,())
        for n,w in right:
            if m&n:continue
            counts['exterior products']+=1
            plus(dst,m|n,signed_mul(v,w,weight*wedge_sign(m,n)))

def wprod(A,B):
    out={}
    join(out,A,B)
    return cleaned(out)

@dataclass
class Factor:
    wires: tuple
    data: dict

def finish(wires,rows):
    out={k:p for k,v in rows.items() if (p:=cleaned(v))}
    return Factor(wires,out)

@cache
def local(x,d,tag):
    K=pair(x,d) if d<2 else local_pair(x)
    return poly_int(K[tag[0]][tag[1]])

@cache
def open_basis(x):
    K=local_pair(x)
    out={}
    for (c,d),ls in L.items():
        for (e,f),rs in L.items():
            p=(c,e)
            for a,v in ls:
                for b,z in rs:
                    k=p,tuple(sorted((a,b)))
                    out[k]=add(out.get(k,{}),scale(K[d][f],v*z))
    return out

@cache
def base_j():
    A,B=open_basis(0),open_basis(1)
    out=defaultdict(dict)
    for (p,i),a in A.items():
        for (q,j),b in B.items():
            w=cross_weight(i,j)
            if w:out[p,q]=add(out[p,q],scale(wedge(a,b),w))
    return {k:poly_int(p) for k,p in out.items()}

def move_word(mask,move):
    return sum(((mask>>(8*x))&255)<<(8*move(x)) for x in range(4))

@cache
def j_tensor(x,y):
    axis=0 if x^y==1 else 1
    assert x^y in (1,2)
    def move(z):
        return x ^ ((((z&1)<<1)|((z&2)>>1)) if axis else z)
    return {k:{move_word(m,move):v for m,v in p.items()} for k,p in base_j().items()}

@cache
def transport(x,d,kind):
    def move(z):
        return x ^ ((((z&1)<<1)|((z&2)>>1)) if d else z)
    return {k:{move_word(m,move):v for m,v in poly_int(p).items()}
            for k,p in edge_base(kind).items()}

def pair_factor(plan,x,y):
    a,b=plan[x][0],plan[y][0]
    assert a[0]==b[0]<2 and plan[x][1][0]==plan[y][1][0]==2
    J=j_tensor(x,y)
    wires=tuple((z,d) for z,(d,u,k) in ((x,a),(y,b)) if u>=0)
    out=defaultdict(dict)
    for p,q in product(ORDERED,repeat=2):
        z=J.get((p,q),{})
        slots=[]
        for site,(d,u,k),tag in ((x,a,p),(y,b,q)):
            if u>=0:slots.append(tag)
            else:z=wprod(z,local(site,d,tag))
        for m,v in z.items():plus(out[tuple(slots)],m,v)
    return finish(wires,out)

def singleton_factor(plan,x):
    wires=tuple((x,d) for d,y,k in plan[x] if y>=0)
    out=defaultdict(dict)
    for (p,q),w in M.items():
        slots=[];z=ONE
        for (d,y,k),tag in zip(plan[x],(p,q)):
            if y>=0:slots.append(tag)
            else:z=wprod(z,local(x,d,tag))
        for m,v in z.items():plus(out[tuple(slots)],m,(w*v[0],w*v[1]))
    return finish(wires,out)

def attach(Fac,x,y,d,k):
    old=(x,d);new=(y,d)
    assert old in Fac.wires and new not in Fac.wires
    i=Fac.wires.index(old)
    wires=tuple(sorted((set(Fac.wires)-{old})|{new}))
    pos={z:j for j,z in enumerate(wires)}
    move=[pos[z if z!=old else new] for z in Fac.wires]
    H=transport(x,d,k)
    sat=255<<(8*x)
    # Every row has fixed exterior site degree. A degree-4 source closes
    # this site when the shared edge contributes its four generators.
    if not Fac.data or (next(iter(next(iter(Fac.data.values()))))&sat).bit_count()!=4:
        sat=0
    buckets={}
    if sat:
        for key,poly in H.items():
            rows=defaultdict(list)
            for m,v in poly.items():rows[m&sat].append((m,v))
            buckets[key]=rows
    out=defaultdict(dict)
    for tags,p in Fac.data.items():
        q0=tags[i]
        t=[None]*len(wires)
        for j,tag in enumerate(tags):t[move[j]]=tag
        for q1 in ORDERED:
            t[pos[new]]=q1
            key=q0,q1
            join(out[tuple(t)],p,H[key],saturate=sat,buckets=buckets.get(key))
    counts['max attach terms']=max(counts['max attach terms'],sum(map(len,out.values())))
    return finish(wires,out)

def combine(A,B):
    common=tuple(sorted(set(A.wires)&set(B.wires)))
    final=tuple(sorted(set(A.wires)^set(B.wires)))
    out=defaultdict(dict)
    ai=[A.wires.index(w) for w in common];bi=[B.wires.index(w) for w in common]
    groups=defaultdict(list)
    for vals,p in B.data.items():groups[tuple(vals[i] for i in bi)].append((vals,p))
    for vals,p in A.data.items():
        for other,q in groups.get(tuple(vals[i] for i in ai),()):
            d=dict(zip(A.wires,vals));d.update(zip(B.wires,other))
            join(out[tuple(d[w] for w in final)],p,q)
    return finish(final,out)

def top(A,B):
    assert A.wires==B.wires
    val=(0,0)
    for vals,p in A.data.items():
        q=B.data.get(vals,{})
        for m,v in p.items():
            n=m^TOP
            if n in q:
                z=signed_mul(v,q[n],wedge_sign(m,n));val=val[0]+z[0],val[1]+z[1]
                counts['final top joins']+=1
    assert val[1]==0
    return val[0]

@cache
def scalar(plan,pairs):
    x,y=pairs[0]
    A=pair_factor(plan,x,y)
    for z in (x,y):
        d,u,k=plan[z][0]
        if u>=0:A=attach(A,z,u,d,k)
    if len(pairs)==2:
        B=pair_factor(plan,*pairs[1])
    else:
        c,d=sorted(set(range(4))-{x,y})
        C,D=singleton_factor(plan,c),singleton_factor(plan,d)
        for a,v,k in plan[c]:
            if v==d:C=attach(C,c,d,a,k)
        B=combine(C,D)
    raw=top(A,B)
    nshared=sum(y>=0 for row in plan for d,y,k in row)//2
    denom=128**(8-2*nshared)*DIM**nshared*(9*48**2)**len(pairs)
    return F(raw,denom),sum(map(len,A.data.values())),sum(map(len,B.data.values()))

def main():
    cases=census();total=F(0);parts=Counter()
    for ((plan,ps),h,c,f),n in sorted(cases.items()):
        value,a,b=scalar(plan,ps)
        v=value*2**h*F(16,9)**c/f
        total+=n*v;parts[len(ps)]+=n*v
        print('paired blocks',len(ps),'multiplicity',n,'factorial',f,'terms',a,b,
              'representative',v,flush=True)
    print('parts',parts,'total',total,'counts',counts,flush=True)
def size_six_total():
    total = F(0)
    cases = size_six_census()
    for ((plan, pairs), haar, commutator, weight), population in cases.items():
        value, _, _ = scalar(plan, pairs)
        total += population * value * 2**haar * F(16, 9)**commutator / weight
    return sum(cases.values()), total


if __name__=='__main__':main()
