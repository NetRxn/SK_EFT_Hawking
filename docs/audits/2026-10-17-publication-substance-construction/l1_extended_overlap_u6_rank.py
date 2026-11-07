from collections import Counter,defaultdict
from sympy import QQ
from sympy.polys.matrices import DomainMatrix
from l1_extended_overlap_u6 import project_left,build_right
_,A=project_left();B=build_right()
L={};R=defaultdict(Counter)
for (a,b),row in A.items():
    k=tuple(sorted((a,b)))
    if k in L:assert L[k]==row
    L[k]=row
for (a,b),row in B.items():
    R[tuple(sorted((a,b)))].update(row)
R={k:{j:v for j,v in row.items() if v} for k,row in R.items()}

def rank(t):
    rows=defaultdict(dict)
    for col,items in enumerate(t.values()):
        for key,val in items.items():rows[key][col]=QQ(val)
    reduced={tuple(sorted(row.items())) for row in rows.values()}
    matrix=DomainMatrix({i:dict(row) for i,row in enumerate(reduced)},(len(reduced),len(t)),QQ)
    return len(rows),len(reduced),matrix.rank()

print('channels',len(L),len(R),'left entries',sum(map(len,L.values())),'right entries',sum(map(len,R.values())))
print('left distinct/rank',rank(L),'right distinct/rank',rank(R))
print('raw products after ordered-pair collapse',sum(len(L[k])*len(R[k]) for k in L))
# The common-radius null vector gives L_77=sum L_ii(i<4)-sum L_ii(4<=i<7).
drop=L.pop((7,7))
right=R.pop((7,7))
for i in range(7):
    row=R[i,i]
    sign=1 if i<4 else -1
    for k,v in right.items():row[k]=row.get(k,0)+sign*v
    R[i,i]={k:v for k,v in row.items() if v}
control=Counter()
for i in range(7):
    for k,v in L[i,i].items():control[k]+=v if i<4 else -v
assert {k:v for k,v in control.items() if v}==drop
print('rank-minimal factors',len(L),'left entries',sum(map(len,L.values())),
      'right entries',sum(map(len,R.values())),'raw products',sum(len(L[k])*len(R[k]) for k in L))
