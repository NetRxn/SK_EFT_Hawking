"""Exact independent conjugation check of retained within-center source types."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"2026-10-17-publication-substance-construction"))
from fractions import Fraction as F
from itertools import product
from l1_normalization_opposed_fourth import nodes
from l1_direct_a_haar import qproduct,adj
unit=tuple(tuple(int(i==j) for i in range(4)) for j in range(4))
rot=[([qproduct(adj((l,r)[i//4]),unit[i%4],(l,r)[i//4]) for i in range(8)],w) for l,r,w in nodes()]
retained=[]
for i,j in product(range(8),repeat=2):
    C=tuple(F(sum(w*v[i][a]*v[j][b] for v,w in rot),96*16) for a,b in product(range(4),repeat=2))
    E=[F(0)]*16
    if i%4==j%4==0:E[0]=F(1)
    elif i//4==j//4 and i%4==j%4:
        for a in range(1,4):E[4*a+a]=F(1,3)
    assert C==tuple(E),(i,j,C,E)
    if any(C):retained.append((i,j))
assert retained==[(0,0),(0,4),(1,1),(2,2),(3,3),(4,0),(4,4),(5,5),(6,6),(7,7)]
print('All64 exact conjugation tensors PASS',retained)
