"""Pure-g2 center/saturation support for the original 2x2x1x1 torus."""
from collections import Counter
from itertools import combinations, product

SITES=range(4)
AXES=range(4)
def forward(x,d):
    return x ^ (1<<d) if d<2 else x
def link(x,d):
    return 1<<(4*x+d)
def mask(items):
    m=0
    for x,d in items:
        m^=link(x,d)
    return m
def t_terms(x,d):
    y=forward(x,d)
    if x==y:
        return [(link(x,d),(x,x),x)]
    return [(link(z,d),(x,y),z) for z in (x,y)]
def action_terms():
    terms=[]
    for x in SITES:
        for k,l in combinations(AXES,2):
            mu,nu=(d for d in AXES if d not in (k,l))
            p=mask([(x,k),(forward(x,k),l),(forward(x,l),k),(x,l)])
            for (q,a,u),(r,b,v) in product(t_terms(x,mu),t_terms(x,nu)):
                sites=Counter(a+b)
                c=tuple(sites[y] for y in SITES)
                terms.append((p^q^r,c,(x,k,l,u,v)))
    return terms
TERMS=action_terms()
assert len(TERMS)==52
def half(deg):
    pop=Counter({(0,(0,0,0,0)):1})
    witness={(0,(0,0,0,0)):()}
    for _ in range(deg):
        next_pop=Counter()
        next_witness={}
        for (p,c),w in pop.items():
            for q,d,label in TERMS:
                n=tuple(x+y for x,y in zip(c,d))
                if max(n)>8:
                    continue
                key=(p^q^0,n)
                next_pop[key]+=w
                next_witness.setdefault(key,witness[(p,c)]+(label,))
        pop,witness=next_pop,next_witness
    return pop,witness
def match(halves,target_parity,target_counts):
    pop,witness=halves
    total=0
    first=None
    for (p,c),w in pop.items():
        needed=(p^target_parity,tuple(t-x for t,x in zip(target_counts,c)))
        if needed in pop:
            total+=w*pop[needed]
            if first is None:
                first=witness[(p,c)]+witness[needed]
    return total,first

def main():
    halves3=half(3)
    halves4=half(4)
    print('half-state counts',len(halves3[0]),len(halves4[0]))
    norm=match(halves4,0,(8,)*4)
    print('Z pure-g2^8',norm)
    def shear(x):
        return link(x,2)^link(x,3)
    for b in SITES:
        target=tuple(8-4*(x==0)-4*(x==b) for x in SITES)
        for name,m in [('cross-cross',shear(0)^shear(b)),('plus-plus',0),
                       ('cross-plus',shear(0))]:
            result=match(halves3,m,target)
            print(b,name,result)
if __name__=='__main__':
    main()
    p3,w3=half(3)
    p4,w4=half(4)
    for m in [0,link(0,2)^link(0,3)]:
        target=(4,8,8,8)
        total=sum(w*p4[(p^m,tuple(t-x for t,x in zip(target,c)))]
                  for (p,c),w in p3.items())
        print('linear source mask',m,total)
