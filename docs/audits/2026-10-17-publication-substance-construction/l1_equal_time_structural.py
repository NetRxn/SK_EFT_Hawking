from collections import Counter

from l1_interacting_support import AXES, forward, same_site_quadratic_support


def incidence(x, k, l):
    return ((x, k), (forward(x, k), l), (forward(x, l), k), (x, l))


def profile(word):
    return Counter(link for x,k,l,u,v in word for link in incidence(x,k,l))


def erase(word):
    planes = Counter(t[:3] for t in word)
    uses = Counter()
    for x,k,l,u,v in word:
        m,n = (d for d in AXES if d not in (k,l))
        uses.update(((u,m),(v,n)))
    # Both local source link variables can enter D^2.
    uses.update(((0,2),(0,3)))
    edges = {plane:Counter(incidence(*plane)) for plane in planes}
    for counts in edges.values():
        uses.update(counts)
    removed=[]
    while edges:
        for plane, counts in edges.items():
            unique = any(n == 1 and uses[link] == 1 for link,n in counts.items())
            comm = (plane[1:] == (2,3)
                    and all(uses[link] == n for link,n in counts.items()))
            if unique or comm:
                removed.append((plane,planes[plane],unique))
                if planes[plane] % 2:
                    return removed
                uses.subtract(counts)
                del edges[plane]
                break
        else:
            return None
    return None


if __name__ == "__main__":
    rows=Counter()
    examples={}
    for word in same_site_quadratic_support():
        counts=profile(word)
        key=tuple(sorted((counts[0,2],counts[0,3])))
        erased=erase(word)
        rows[key,erased is not None]+=1
        if erased is not None:
            examples.setdefault(key,(word,erased))
    print(sorted(rows.items()))
    print(examples)

def reduce_source_dependence(word):
    frames=Counter()
    for x,k,l,u,v in word:
        m,n=(d for d in AXES if d not in (k,l))
        frames.update(((u,m),(v,n)))
    planes={plane:Counter(incidence(*plane)) for plane in {t[:3] for t in word}}
    use=frames.copy()
    use.update(((0,2),(0,3)))
    for edges in planes.values():
        use.update(edges)
    history=[]
    while planes:
        for plane,edges in sorted(planes.items()):
            if any(n==1 and use[key]==1 for key,n in edges.items()):
                use.subtract(edges)
                del planes[plane]
                history.append(plane)
                break
        else:
            break
    return (use[0,2]-1,use[0,3]-1),history

classes=Counter()
examples={}
for word in same_site_quadratic_support():
    counts=profile(word)
    before=tuple(sorted((counts[0,2],counts[0,3])))
    after,history=reduce_source_dependence(word)
    key=before,tuple(sorted(after))
    classes[key]+=1
    if key not in examples:
        examples[key]=(word,history)
print("independent conditional Haar source reduction",sorted(classes.items()))
for k,example in sorted(examples.items()):
    print(k,example)

p=Counter()
for w in same_site_quadratic_support():
    src, h=reduce_source_dependence(w)
    planes=Counter(t[:3] for t in w)
    remaining=tuple(sorted((key,occ) for key,occ in planes.items() if key not in h))
    signature=(tuple(sorted((key[1:],occ) for key,occ in remaining)), tuple(sorted(src)))
    p[signature]+=1
for key,n in p.most_common(): print(n,key)

def frame_links(w):
    result=Counter()
    for x,k,l,u,v in w:
        m,n=(d for d in AXES if d not in (k,l))
        result.update(((u,m),(v,n)))
    return result
counts=Counter()
ex={}
for w in same_site_quadratic_support():
    src,h=reduce_source_dependence(w)
    remaining=set(t[:3] for t in w)-set(h)
    f=frame_links(w)
    comm=set(key for p in remaining for key in incidence(*p))
    shape=(len(remaining),tuple(sorted(f.values())),bool(comm&f.keys()))
    counts[shape]+=1
    ex.setdefault(shape,w)
for k,n in counts.most_common(): print(k,n,ex[k])

def private_groups(word):
    p=Counter()
    for t in word:
        x,k,l,u,v=t
        m,n=(d for d in AXES if d not in (k,l))
        p[t[:3],(u,m)]+=1
        p[t[:3],(v,n)]+=1
    return all(n==2 for n in p.values()) and all(n==2 for n in frame_links(word).values())
s=Counter()
for w in same_site_quadratic_support():
    src,h=reduce_source_dependence(w)
    if len(h)<2:continue
    s[(len(h),private_groups(w))]+=1
print('private fully paired:',s)
