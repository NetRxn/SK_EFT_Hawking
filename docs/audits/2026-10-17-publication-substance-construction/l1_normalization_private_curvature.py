from collections import Counter
from l1_normalization_shared_transport import TERMS,component_multisets,forward
from l1_normalization_transport_cycle import pattern

def classify(ii):
    multiplicity=Counter(ii)
    if sorted(multiplicity.values())!=[2]*4:return None
    labels=[TERMS[i][2] for i in sorted(multiplicity)]
    if len({v[0] for v in labels})!=4:return None
    remaining={}
    current=Counter()
    T=[]
    for j,(x,k,l,u,v) in enumerate(labels):
        mu,nu=[a for a in range(4) if a not in (k,l)]
        t=((u,mu),(v,nu));T.extend(t);current.update(t)
        p=Counter(((x,k),(forward(x,k),l),(forward(x,l),k),(x,l)))
        remaining[j]=p
        current.update(p)
    reduced={}
    while remaining:
        for j,p in remaining.items():
            unique=any(n==1 and current[k]==1 for k,n in p.items())
            comm=(all(n==2 for n in p.values()) and all(current[k]==n for k,n in p.items()))
            if unique or comm:
                current.subtract(p);reduced[j]='Haar' if unique else 'comm'
                del remaining[j];break
        else:return None
    return tuple(reduced[x] for x in range(4))
if __name__=='__main__':
    counts=Counter()
    for comps in component_multisets():
        ii=[i for c in comps for i in c]
        if pattern(ii) is not None:continue
        p=classify(ii)
        if p is None:continue
        counts[tuple(sorted(map(len,comps))),p.count('Haar')]+=1
    print(counts,sum(counts.values()))
