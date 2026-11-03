"""Support-only census of L_0 S4 (∂_a S2) S2^4 / 4!."""
from collections import Counter,defaultdict
from fractions import Fraction
from itertools import combinations_with_replacement,product
from math import factorial,prod
from time import perf_counter

from l1_interacting_support import TERMS,SITES,AXES,forward,t_terms

TARGET=(4,8,8,8)

def determinant_terms():
    for site in SITES:
        for slots in product(*(t_terms(site,d) for d in AXES)):
            parity=0
            counts=Counter()
            for p,ends,_ in slots:
                parity^=p
                counts.update(ends)
            yield parity,tuple(counts[x] for x in SITES),(site,*(z for _,_,z in slots))

def s2_signature(indices):
    parity=0
    counts=[0]*4
    for i in indices:
        p,degrees,_=TERMS[i]
        parity^=p
        for j,n in enumerate(degrees):counts[j]+=n
    return parity,tuple(counts)

def tags(indices):
    signed=[]
    for i in indices:
        x,k,l,_,_=TERMS[i][2]
        signed.append((int(l==3)-int(l==2)) if x&1 and k<2<=l else 0)
    return signed

def support():
    triples=defaultdict(list)
    for inds in combinations_with_replacement(range(len(TERMS)),3):
        parity,counts=s2_signature(inds)
        if all(x<=y for x,y in zip(counts,TARGET)):
            triples[parity,counts].append(inds)
    pairs=[(inds,*s2_signature(inds)) for inds in combinations_with_replacement(range(len(TERMS)),2)]
    for p4,d4,det in determinant_terms():
        for ij,p2,d2 in pairs:
            remain=tuple(t-a-b for t,a,b in zip(TARGET,d4,d2))
            if min(remain)<0:continue
            for rest in triples.get((p4^p2,remain),()):
                if ij[-1]<=rest[0]:
                    yield det,ij+rest

def composite_link_incidence(det, word):
    links = set(zip(det[1:], AXES))
    for i in word:
        x, k, l, u, v = TERMS[i][2]
        m, n = (axis for axis in AXES if axis not in (k, l))
        links.update(((x, k), (forward(x, k), l), (forward(x, l), k),
                      (x, l), (u, m), (v, n)))
    return (0, 2) in links, (0, 3) in links


def main():
    start=perf_counter()
    populations=Counter()
    signed_weights=Counter()
    tagged_ordered=Counter()
    ordered=Counter()
    examples={}
    incidence=Counter()
    for det,word in support():
        weights=tags(word)
        total=sum(weights)
        tag_count=sum(bool(w) for w in weights)
        f=prod(factorial(n) for n in Counter(word).values())
        populations[tag_count,total]+=1
        signed_weights[total]+=Fraction(total,f)
        ordered[bool(total)]+=factorial(5)//f
        tagged_ordered[0]+=factorial(4)*tag_count//f
        if total:
            incidence[composite_link_incidence(det, word)] += 1
            examples.setdefault(total, (det, tuple(TERMS[i][2] for i in word)))
    assert incidence == {(False, False): 64, (True, True): 32}
    print('weighted source-link incidence', dict(incidence))
    print('fixed composite site 0; dressed slice 1,3; determinant labels',len(list(determinant_terms())))
    print('populations (eligible tags, net signed weight)',sorted(populations.items()))
    print('multisets',sum(populations.values()),'weighted support',sum(n for (m,s),n in populations.items() if s))
    print('ordered by net weighted support',dict(ordered),'ordered tagged placements',tagged_ordered[0])
    print('signed factorial sums by weight',sorted(signed_weights.items()))
    print('witnesses',examples)
    print('elapsed seconds',perf_counter()-start)

if __name__=='__main__':main()
