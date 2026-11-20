"""Anchor-marginalized exact ordered structural census on length-1/2 tori."""
from collections import Counter
from itertools import combinations,combinations_with_replacement
from math import factorial,prod

def labels(nsites,extended):
    return [(x,k,l) for x in range(nsites) for k,l in combinations(range(4),2)]

def anchor_multiplicity(word,nsites,extended):
    degree=[0]*nsites
    curvature=Counter()
    frame=Counter()
    def forward(x,i):return x^(1<<i) if i<extended else x
    for x,k,l in word:
        curvature.update(((x,k),(forward(x,k),l),(forward(x,l),k),(x,l)))
        degree[x]+=2
        for i in range(4):
            if i in (k,l):continue
            y=forward(x,i)
            degree[y]+=1
            frame[min(x,y),i]+=1
    weight=1
    for x in range(nsites):
        for i in range(4):
            y=forward(x,i)
            if y<x:continue
            f=frame[x,i]
            p=curvature[x,i]%2
            if x==y:
                if (p+f)%2:return degree,0
                continue
            q=curvature[y,i]%2
            if (p+q+f)%2 or (not f and p):return degree,0
            if f:weight<<=f-1
    return degree,weight

def count_ordered(nsites,extended,actions,target,choices=None):
    terms=labels(nsites,extended) if choices is None else choices
    total=patterns=0
    for word in combinations_with_replacement(terms,actions):
        degree,w=anchor_multiplicity(word,nsites,extended)
        if not w or degree!=target:continue
        patterns+=1
        total+=w*factorial(actions)//prod(factorial(n) for n in Counter(word).values())
    return total,patterns

if __name__=='__main__':
    print('collapsed 2x2x1x1 six-action local source',count_ordered(4,2,6,[0,8,8,8]))
    # Exact full 16-site census within one fixed curvature plane and with two
    # actions at every center. Pattern multiplicity has no chosen anchors.
    word=[(x,0,1) for x in range(16) for _ in range(2)]
    degree,w=anchor_multiplicity(word,16,4)
    assert degree==[8]*16
    print('extended fixed pattern anchor assignments',w,'ordered',w*factorial(32)//2**16)
