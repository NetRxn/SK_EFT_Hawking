from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from collections import Counter
from math import prod
from l1_direct_a_haar import haar_moment
z=(F(0),)*4
axes=[tuple(F(i==j) for i in range(4)) for j in range(4)]
nodes=[]
for a in axes:
    nodes.extend([(a+z,F(-1,6)),(z+a,F(-1,6))])
for sign in product((-1,1),repeat=3):
    h=(F(1,2),)+tuple(F(s,2) for s in sign)
    nodes.extend([(h+z,F(1,12)),(z+h,F(1,12))])
for l,r,s in product(axes,axes,(-1,1)):
    nodes.append((l+tuple(s*v for v in r),F(1,32)))
assert len(nodes)==56
count=0
for coords in combinations_with_replacement(range(8),4):
    e=Counter(coords)
    actual=sum(w*prod(x[i] for i in coords) for x,w in nodes)
    expected=haar_moment(tuple(e[i] for i in range(4)))*haar_moment(tuple(e[i] for i in range(4,8)))
    assert actual==expected, (coords,actual,expected)
    count+=1
print('exact homogeneous-degree-four Spin(4) rule:',len(nodes),'nodes;',count,'monomial moments agree')
