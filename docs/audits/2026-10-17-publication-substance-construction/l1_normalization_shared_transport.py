"""Exact L1 normalization terms with one shared transport link."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product,permutations
from math import factorial,prod
from l1_normalization_disjoint_sector import quat,adj,pair,site
from l1_normalization_opposed_fourth import (
    nodes,tuples,fourth_T,curv_moment,
)
from l1_normalization_support import TERMS, forward, normalization_support
from l1_direct_b_haar import R,diag,gamma,bilinear,add,scale,wedge

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

@cache
def component(comp):
    labels=tuple(TERMS[i][2] for i in sorted(set(comp)))
    if len(comp)==2:return site(labels[0][0]),9216
    if len(labels)==1:
        p,q=quartic_component()
        return translate(p,lambda x:x^labels[0][0]),q
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
        key=(shape,any(len(set(c))==2 for c in comps))
        totals[key]+=t
        pop[key]+=1
    for key,n in sorted(pop.items()):
        print('component sizes; shared-label case',key,'multisets',n,'exact signed sum',totals[key])
    print('new exact tranche',sum(total for k,total in totals.items() if k[1]))
    print('cached shared representatives',shared_component.cache_info())
if __name__=='__main__':main()
