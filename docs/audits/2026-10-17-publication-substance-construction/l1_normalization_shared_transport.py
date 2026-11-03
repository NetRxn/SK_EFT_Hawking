"""Exact L1 normalization terms with one shared transport link."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product,permutations
from math import factorial,prod
from l1_normalization_disjoint_sector import quat,adj,pair,site
from l1_normalization_opposed_fourth import (
    nodes,tuples,fourth_T,curv_moment,L,vec_moment,
)
from l1_normalization_support import TERMS, forward, normalization_support
from l1_direct_b_haar import R,diag,gamma,bilinear,add,scale,wedge,haar_moment

def factor_links(label):
    x, k, l, u, v = label
    mu, nu = (axis for axis in range(4) if axis not in (k, l))
    return {(x, k), (forward(x, k), l), (forward(x, l), k), (x, l),
            (u, mu), (v, nu)}


LINKS = tuple(factor_links(label) for _, _, label in TERMS)


def component_multisets():
    for indices in normalization_support():
        groups = []
        for index in indices:
            links = set(LINKS[index])
            factors = [index]
            for group in tuple(groups):
                if links & group[0]:
                    groups.remove(group)
                    links.update(group[0])
                    factors.extend(group[1])
            groups.append((links, factors))
        yield tuple(sorted(tuple(sorted(factors)) for _, factors in groups))


def supported(component):
    if len(component) == len(set(component)) == 4:
        return True
    if mixed_links(component) or same_links(component) or comm_links(component):
        return True
    counts = Counter(component)
    labels = tuple(counts)
    if any(TERMS[index][2][1:3] != (2, 3) for index in labels):
        return False
    if len(labels) == 1:
        return len(component) in (2, 4)
    return (sorted(counts.values()) == [2, 2]
            and len(LINKS[labels[0]] & LINKS[labels[1]]) == 1)


def translate(p,move):
    # Moving whole site blocks is signless when each degree is even.
    assert all(((mask >> (8*x)) & 255).bit_count() % 2 == 0
               for mask, value in p.items() if value for x in range(4))
    return {sum(((mask>>(8*x))&255)<<(8*move(x)) for x in range(4)):val
            for mask,val in p.items() if val}

@cache
def quartic_component():
    A,B=fourth_T(0),fourth_T(1)
    out={}
    for a in tuples:
        mult=factorial(4)//prod(factorial(k) for k in Counter(a).values())
        for b in tuples:
            if not A[a] or not B[b]:continue
            w=sum(curv_moment(tuple(sorted(zip(a,x)))) for x in set(permutations(b)))
            if w:
                p={m:c for m,c in wedge(A[a],B[b]).items() if m&255==255}
                out=add(out,scale(p,mult*w))
    return out,2025*96**2*8**8

def transform_label(t,shift,swap):
    x,k,l,u,v=t
    assert (k,l)==(2,3)
    def transform(x):
        return shift ^ (((x&1)<<1)|((x&2)>>1) if swap else x)
    return (transform(x),k,l,transform(v if swap else u),transform(u if swap else v))

def label_orbit(labels):
    return {tuple(sorted(transform_label(a,s,t) for a in labels)):(s,t)
            for s,t in product(range(4),(False,True))}

def translate_inverse(s,t):
    return lambda x: ((((x^s)&1)<<1)|(((x^s)&2)>>1)) if t else x^s

def pair_fixed(x,d,linksite,U,Ud):
    y=x^(1<<d)
    if linksite==x:
        T=[add(bilinear(g*Ud,x,y),scale(bilinear(U*g,y,x),-1)) for g in gamma]
    else:
        assert linksite==y
        T=[add(bilinear(Ud*g,y,x),scale(bilinear(g*U,x,y),-1)) for g in gamma]
    return [[wedge(a,b) for b in T] for a in T]

def square(K,L):
    return add(*(add(wedge(K[a][a],L[b][b]),scale(wedge(K[a][b],L[b][a]),-1))
                 for a,b in product(range(4),repeat=2)))

@cache
def shared_component(labels):
    links=[{(u,0),(v,1)} for x,k,l,u,v in labels]
    (shared,)=links[0]&links[1]
    z,d=shared
    x,y=labels[0][0],labels[1][0]
    private_x,private_y=pair(x,1-d),pair(y,1-d)
    out={}
    for l,r,w in nodes():
        U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
        a=square(pair_fixed(x,d,z,U,Ud),private_x)
        b=square(pair_fixed(y,d,z,U,Ud),private_y)
        out=add(out,scale(wedge(a,b),w))
    # Each local square has curvature 16/9, one private 8-node mean
    # with raw factor 4T, and one shared polynomial in raw 8T.
    return out,4608**2*96

def mixed_links(comp):
    if sorted(Counter(comp).values()) != [2, 2]:
        return False
    a,b=sorted(set(comp))
    x,k,l,u,v=TERMS[a][2];y,q,r,m,n=TERMS[b][2]
    shared=LINKS[a]&LINKS[b]
    return k==q and k<2 and l!=r and x^y==1<<k and shared=={(x,r),(y,l)}

def same_links(comp):
    if sorted(Counter(comp).values()) != [2, 2]:
        return False
    a,b=sorted(set(comp))
    x,k,l,u,v=TERMS[a][2];y,q,r,m,n=TERMS[b][2]
    shared=LINKS[a]&LINKS[b]
    return k==q and k<2 and l==r and x^y==1<<k and shared=={(x,l),(y,l)}

@cache
def local_pair(x):
    K=[[{} for _ in range(4)] for _ in range(4)]
    for j,s in product(range(4),(-1,1)):
        l=[int(k==j) for k in range(4)]
        r=[s*z for z in l]
        U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
        delta=Ud-U
        T=[bilinear(g*delta+delta*g,x,x) for g in gamma]
        for a,b in product(range(4),repeat=2):
            K[a][b]=add(K[a][b],wedge(T[a],T[b]))
    return K

@cache
def mixed_component(labels):
    x,k,l,*_=labels[0];y,_,r,*_=labels[1]
    a=square(pair(x,1-k),local_pair(x))
    b=square(pair(y,1-k),local_pair(y))
    # Curvature Haar covariance 2, two private/shared independent link
    # quadratics each divided by 8, four T factors each divided by 4.
    return wedge(a,b),8192**2

@cache
def W(x,axis):
    K,T=pair(x,axis),local_pair(x)
    poly={}
    for (c,d),ls in L.items():
        for (e,f),rs in L.items():
            for a,v in ls:
                for b,z in rs:
                    k=tuple(sorted((a,b)))
                    poly[k]=add(poly.get(k,{}),scale(wedge(K[c][e],T[d][f]),v*z))
    return poly

def conditional(a,b):
    """Three times E[p_a p_b | X,Y], sparse list of (X,Y coordinate words)."""
    v=(a//3)*4+a%3+1
    z=(b//3)*4+b%3+1
    s=(a//3)*4
    t=(b//3)*4
    if s!=t:return [((v,z),(s,t),3)]
    out=[((v,z),(s,s),4),((v,z),(),-1)]
    if a==b:out += [((),(),1),((),(s,s),-1)]
    return out

@cache
def wordmoment(word):
    m=tuple(word.count(i) for i in range(8))
    return haar_moment(m[:4])*haar_moment(m[4:])

@cache
def cross_weight(k,l):
    t=F(0)
    for x,y,a in conditional(*k):
        for u,v,b in conditional(*l):
            t+=a*b*wordmoment(tuple(sorted(x+v)))*wordmoment(tuple(sorted(y+u)))
    t*=48**2
    assert t.denominator==1
    return int(t)

@cache
def same_component(x,y,k):
    A,B=W(x,1-k),W(y,1-k)
    out=add(*(scale(wedge(a,b),cross_weight(i,j)) for i,a in A.items() for j,b in B.items()
              if cross_weight(i,j)))
    # Per square, both T second moments were stored with denominator
    # 8²×4⁴ and conditional covariance with denominator 3. Shared X/Y
    # integration is stored with denominator 48².
    return out,(8**2*4**4*3)**2*48**2

def comm_links(comp):
    if sorted(Counter(comp).values()) != [2, 2]:
        return False
    a,b=sorted(set(comp))
    x,k,l,u,v=TERMS[a][2];y,q,r,m,n=TERMS[b][2]
    return x==y and (k,l,q,r)==(2,3,2,3)

def curvature_basis(K,T):
    poly={}
    for (c,d),ls in L.items():
        for (e,f),rs in L.items():
            for a,v in ls:
                for b,z in rs:
                    k=tuple(sorted((a,b)))
                    poly[k]=add(poly.get(k,{}),scale(wedge(K[c][e],T[d][f]),v*z))
    return poly

@cache
def W(x,axis):
    return curvature_basis(pair(x,axis),local_pair(x))

@cache
def comm_weight(ab,cd):
    q=ab+cd
    l=tuple(z for z in q if z<3);r=tuple(z-3 for z in q if z>=3)
    if len(l)%2:return 0
    t=2025*vec_moment(l)*vec_moment(r)
    assert t.denominator==1
    return int(t)

def comm_square(A):
    # At the same center the two factors each use four generators there.
    # Discard duplicate masks before the quartic curvature pairing.
    return add(*(scale(wedge(a,b),comm_weight(i,j)) for i,a in A.items()
                 for j,b in A.items() if comm_weight(i,j)))

@cache
def comm_base(shared):
    x=0
    if not shared:
        return comm_square(curvature_basis(pair(x,0),pair(x,1))),2025*(8**2*4**4)**2
    out={}
    K=pair(x,1)
    for l,r,w in nodes():
        U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
        T=pair_fixed(x,0,x,U,Ud)
        out=add(out,scale(comm_square(curvature_basis(T,K)),w))
    return out,2025*(8*4**2*8**2)**2*96

@cache
def comm_component(labels):
    x,k,l,u,v=labels[0];_,_,_,a,b=labels[1]
    assert (u,v)!=(a,b)
    shared=(u==a or v==b)
    p,q=comm_base(shared)
    return translate(p,lambda z:x ^ (((z&1)<<1)|((z&2)>>1)) if v==b else x^z),q

def canonical_2x2(a,b,c,d):
    return tuple(sorted((tuple(sorted((a,b))),tuple(sorted((c,d))))))

@cache
def distinct_center_base():
    K,L1=pair(0,0),pair(0,1)
    weights=Counter()
    # 2x2 endpoint grid: first transport pairs by row, second by column.
    for labs in product((p for p in L if L[p]),repeat=4):
        w=curv_moment(tuple(sorted(labs)))
        if not w:continue
        a,b=zip(*labs)
        weights[canonical_2x2(*a),canonical_2x2(b[0],b[2],b[1],b[3])]+=w
    @cache
    def merge(Kaxis,tag):
        M=K if Kaxis==0 else L1
        a,b=tag
        return wedge(M[a[0]][a[1]],M[b[0]][b[1]])
    out=add(*(scale({m:v for m,v in wedge(merge(0,a),merge(1,b)).items() if m&255==255},w)
              for (a,b),w in weights.items() if w))
    return out,2025*(8*4**2)**4

@cache
def cross_pair(x,axis):
    y=x^(1<<axis)
    K=[[{} for _ in range(4)] for _ in range(4)]
    for j,s in product(range(4),(-1,1)):
        l=[int(k==j) for k in range(4)]
        r=[s*z for z in l]
        U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
        T=[add(bilinear(g*Ud,x,y),scale(bilinear(U*g,y,x),-1)) for g in gamma]
        S=[add(bilinear(Ud*g,x,y),scale(bilinear(g*U,y,x),-1)) for g in gamma]
        for a,b in product(range(4),repeat=2):
            K[a][b]=add(K[a][b],wedge(T[a],S[b]))
    return K

@cache
def distinct_pair_base():
    K,L1=cross_pair(0,0),cross_pair(1,0)
    M,N=pair(0,1),pair(1,1)
    out={}
    @cache
    def shared(a,c,g,e):
        return wedge(K[a][c],L1[g][e])
    @cache
    def private(b,f,d,h):
        return wedge(M[b][f],N[d][h])
    for a,b,c,d in product(range(4),repeat=4):
        if a==b or c==d:continue
        for (e,f,sg),(g,h,sh) in product(((a,b,1),(b,a,-1)),((c,d,1),(d,c,-1))):
            out=add(out,scale(wedge(shared(a,c,g,e),private(b,f,d,h)),sg*sh))
    # Independent curvature covariances (16/9)^2; all four T links have
    # second-moment 8-node normalization and eight factors of 1/4.
    return out,81*1048576

@cache
def distinct_component(labels):
    x=labels[0][0]
    sites=set(t[0] for t in labels)
    assert all(t[1:3]==(2,3) for t in labels)
    if len(sites)==1:
        assert {(t[3],t[4]) for t in labels}==set(product((x,x^1),(x,x^2)))
        p,q=distinct_center_base()
        return translate(p,lambda z:z^x),q
    y,=sites-{x}
    assert x^y in (1,2)
    axis=0 if x^y==1 else 1
    for z in sites:
        ends=[t[3:] for t in labels if t[0]==z]
        assert len(ends)==2 and {e[axis] for e in ends}=={x,y}
        assert len({e[1-axis] for e in ends})==1
    p,q=distinct_pair_base()
    return translate(p,lambda z:x ^ (((z&1)<<1)|((z&2)>>1)) if axis else x^z),q

@cache
def component(comp):
    labels=tuple(TERMS[i][2] for i in sorted(set(comp)))
    if len(comp)==2:return site(labels[0][0]),9216
    if len(labels)==1:
        p,q=quartic_component()
        return translate(p,lambda x:x^labels[0][0]),q
    if len(labels) == 4:
        return distinct_component(labels)
    if comm_links(comp):
        return comm_component(labels)
    if mixed_links(comp):
        return mixed_component(labels)
    if same_links(comp):
        return same_component(labels[0][0], labels[1][0], labels[0][1])
    orb=label_orbit(labels)
    rep=min(orb)
    p,q=shared_component(rep)
    return translate(p,translate_inverse(*orb[rep])),q

def top_product(polys):
    if len(polys)==4:
        a,b,c,d=polys
        polys=[wedge(a,b),wedge(c,d)]
    elif len(polys)==3:
        a,b,c=polys
        polys=[wedge(a,b),c]
    a,b=polys
    top=(1<<32)-1
    total=R.zero
    for u,v in a.items():
        w=u^top
        if w in b:
            total+=wedge({u:v},{w:b[w]}).get(top,R.zero)
    assert total.is_ground and total.const().y==0
    return int(total.const().x)

def main():
    totals=Counter()
    pop=Counter()
    for comps in component_multisets():
        if not all(map(supported,comps)):continue
        w=prod(factorial(n) for n in Counter(i for comp in comps for i in comp).values())
        ps,qs=zip(*map(component,comps))
        t=F(top_product(ps),w*prod(qs))
        shape=tuple(sorted(map(len,comps)))
        family = ("four distinct labels" if any(len(set(c)) == 4 for c in comps)
                  else "shared commutator" if any(map(comm_links, comps))
                  else "same singleton" if any(map(same_links, comps))
                  else "mixed singleton" if any(map(mixed_links, comps))
                  else "one shared link" if any(len(set(c)) == 2 for c in comps)
                  else "disjoint")
        key = shape, family
        totals[key]+=t
        pop[key]+=1
    for key,n in sorted(pop.items()):
        print('component sizes; shared-label case',key,'multisets',n,'exact signed sum',totals[key])
    print('total covered', sum(pop.values()), 'exact signed sum', sum(totals.values()))
    print('cached shared representatives',shared_component.cache_info())
if __name__=='__main__':main()
