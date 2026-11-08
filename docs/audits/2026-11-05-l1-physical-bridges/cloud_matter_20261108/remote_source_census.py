"""Exact necessary source-resolved support; no Haar amplitude is computed."""
import sys,json
from pathlib import Path
from collections import Counter,defaultdict
from itertools import combinations_with_replacement,product
from math import factorial,prod
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'2026-10-17-publication-substance-construction'))
import l1_interacting_support as S
triples=defaultdict(list)
for indices in combinations_with_replacement(range(len(S.TERMS)),3):
    parity=0;degrees=[0]*4
    for i in indices:
        p,d,_=S.TERMS[i];parity^=p;degrees=[x+y for x,y in zip(degrees,d)]
    if max(degrees)<=8:triples[parity,tuple(degrees)].append(indices)
ordered=S.half(3)
output=[];pilot_roster=None
for name,target,choices in [('G02_squared',(2,6,8,8),((0,1),(0,1))),
                            ('G02_G12',(2,7,7,8),((0,1),(0,2)))]:
    for z0,z1 in product(*choices):
        parity=S.link(z0,0)^S.link(z1,0 if name=='G02_squared' else 1)
        found=[]
        for (p,c),lefts in triples.items():
            rem=tuple(t-d for t,d in zip(target,c))
            if min(rem)<0:continue
            for a in lefts:
                for b in triples.get((p^parity,rem),()):
                    if a[-1]<=b[0]:found.append(a+b)
        assert len(found)==len(set(found))
        weighted=sum(factorial(6)//prod(factorial(n) for n in Counter(word).values()) for word in found)
        independent,_=S.match(ordered,parity,target)
        assert weighted==independent
        output.append({'source':name,'anchors':[z0,z1],'multisets':len(found),'ordered_words':weighted,'action_degrees':target})
        if name=='G02_squared' and (z0,z1)==(0,0):pilot_roster=found
assert [x['multisets'] for x in output]==[272,118,118,272,0,12,12,24]
assert [x['ordered_words'] for x in output]==[43560,37800,37800,43560,0,5760,5760,11520]
def incidence(word):
    count=Counter({(0,0):2,(0,2):2})
    for i in word:
        x,k,l,u,v=S.TERMS[i][2];m,n=(a for a in range(4) if a not in (k,l))
        count.update(((x,k),(S.forward(x,k),l),(S.forward(x,l),k),(x,l),(u,m),(v,n)))
    return count
def score(word):
    counts=incidence(word);return max(counts.values()),sum(n*n for n in counts.values()),word
pilot=min(pilot_roster,key=score);assert pilot==(16,16,27,27,44,44)
assert score(pilot)[:2]==(4,120)
print(json.dumps({'scope':'necessary support only, not coefficient completion','signatures':output,
 'prospective_pilot_indices':pilot,'selection_score':score(pilot),
 'pilot_incidence':[[list(edge),n] for edge,n in sorted(incidence(pilot).items())]},indent=2))
