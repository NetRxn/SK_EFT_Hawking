from collections import Counter,defaultdict
from itertools import product
from math import prod,factorial
from l1_normalization_shared_transport import TERMS,component_multisets,forward
from l1_normalization_paired_paths import plan_for

def components(edges):
    groups = []
    for index, edge in enumerate(edges):
        members = {index}
        for group in tuple(groups):
            if edge & group[0]:
                groups.remove(group)
                edge |= group[0]
                members |= group[1]
        groups.append((edge, members))
    return groups


def classify(ii):
    rows=defaultdict(list)
    for i in ii:
        t=TERMS[i][2]
        rows[t[0]].append(t)
    if any(len(rows[x])!=2 or rows[x][0][1:3]!=rows[x][1][1:3] for x in range(4)):return
    remaining={};current=Counter();T=set();h=0;c=0
    for x,ts in rows.items():
        for y,k,l,u,v in ts:
            mu,nu=[d for d in range(4) if d not in (k,l)]
            current.update(((u,mu),(v,nu)));T.update(((u,mu),(v,nu)))
        y,k,l,u,v=ts[0]
        p=Counter(((x,k),(forward(x,k),l),(forward(x,l),k),(x,l)))
        remaining[x]=p
        current.update(p)
    while remaining:
        for j,p in remaining.items():
            unique=any(n==1 and current[k]==1 for k,n in p.items())
            comm=(all(n==2 for n in p.values()) and all(current[k]==n for k,n in p.items()))
            if unique or comm:
                current.subtract(p);del remaining[j]
                h+=unique;c+=comm and not unique
                break
        else:break
    if not remaining:return
    items=list(remaining.items())
    pairs=[]
    for E,g in components([set(p) for x,p in items]):
        if len(g)!=2 or E&T:return
        x,y=sorted(items[i][0] for i in g)
        _,k,l,*_=rows[x][0]
        _,q,r,*_=rows[y][0]
        if not(k==q and k<2 and l==r and l>=2 and x^y==1<<k):return
        pairs.append((x,y))
    return tuple(sorted(pairs)),h,c

def canonical(plan,pairs):
    ans=[]
    for shift,swap in product(range(4),(False,True)):
        def site(x):
            return shift ^ ((((x&1)<<1)|((x&2)>>1)) if swap else x)
        rows=[None]*4
        for x,row in enumerate(plan):
            rows[site(x)]=tuple(sorted((2 if d>=2 else d^int(swap),site(y) if y>=0 else y,k) for d,y,k in row))
        ps=tuple(sorted(tuple(sorted(map(site,p))) for p in pairs))
        ans.append((tuple(rows),ps))
    return min(ans)

def census():
    n=Counter()
    for comps in component_multisets():
        if max(map(len,comps))!=8:continue
        ii=[i for c in comps for i in c]
        r=classify(ii)
        if not r:continue
        p,h,c=r
        n[canonical(plan_for(ii),p),h,c,prod(factorial(k) for k in Counter(ii).values())]+=1
    return n
def size_six_census():
    from l1_normalization_six_mixed_chain import classify as mixed_chain

    cases = Counter()
    for components in component_multisets():
        if sorted(map(len, components)) != [2, 6]:
            continue
        if mixed_chain(max(components, key=len)) is not None:
            continue
        indices = [index for part in components for index in part]
        classification = classify(indices)
        if classification is None:
            continue
        pairs, haar, commutator = classification
        weight = prod(factorial(n) for n in Counter(indices).values())
        cases[canonical(plan_for(indices), pairs), haar, commutator, weight] += 1
    return cases


if __name__=='__main__':
    n=census()
    print('cases',sum(n.values()),'canonical plans',len({k[0] for k in n}),'rows',len(n))
    print(Counter({z:sum(v for ((pl,ps),h,c,f),v in n.items() if len(ps)==z) for z in (1,2)}))
