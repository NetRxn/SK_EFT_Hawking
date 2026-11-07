"""Check the exact rank of dumped four-face projection rows."""
from collections import defaultdict
from sys import argv
from sympy import QQ
from sympy.polys.matrices import DomainMatrix
r=defaultdict(list)
with open(argv[1]) as f:
    for line in f:
        b,c,v=map(int,line.split());r[b].append((c,v))
blocks=defaultdict(set)
def block(c):
    out=0
    for i in range(4):
        out|=((c%6)//3)<<i
        c//=6
    return out
for row in r.values():
    row=tuple(sorted(row))
    b=block(row[0][0])
    assert all(block(c)==b for c,_ in row)
    blocks[b].add(row if row[0][1]>0 else tuple((c,-v) for c,v in row))
total=0
for b,rows in sorted(blocks.items()):
    cols=sorted({c for row in rows for c,_ in row})
    idx={c:i for i,c in enumerate(cols)}
    m=DomainMatrix({i:{idx[c]:QQ(v) for c,v in row} for i,row in enumerate(sorted(rows))},(len(rows),len(cols)),QQ)
    rank=m.rank();total+=rank
    print(b,len(rows),len(cols),rank)
print('total exact rank',total)
assert total == 336
