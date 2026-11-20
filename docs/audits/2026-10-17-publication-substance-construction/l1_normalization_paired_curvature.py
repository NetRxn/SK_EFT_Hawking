from collections import Counter,defaultdict
from l1_normalization_shared_transport import TERMS,component_multisets,forward
from l1_normalization_transport_cycle import pattern

def classify(ii):
    rows=defaultdict(list)
    for i in ii:
        t=TERMS[i][2]
        rows[t[0]].append(t)
    if any(len(rows[x])!=2 or rows[x][0][1:3]!=rows[x][1][1:3] for x in range(4)):return None
    remaining={};current=Counter()
    for x,ts in rows.items():
        for y,k,l,u,v in ts:
            mu,nu=[d for d in range(4) if d not in (k,l)]
            current.update(((u,mu),(v,nu)))
        y,k,l,u,v=ts[0]
        p=Counter(((x,k),(forward(x,k),l),(forward(x,l),k),(x,l)))
        remaining[x]=p
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
        counts[tuple(sorted(map(len,comps))),max(Counter(ii).values()),len(set(ii)),p.count('Haar')]+=1
    print(counts,sum(counts.values()))
