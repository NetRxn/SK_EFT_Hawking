"""Exact local polynomial controls for the pure-g2 Pin selection rule."""
from itertools import product
from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_opposed_source import action_frame, frame
from l1_normalization_opposed_fourth import L
from l1_extended_mixed_frame_moment import moment

def reflect(poly):
    out={}
    for mask,c in poly.items():
        indices=[i^2 for i in range(mask.bit_length()) if mask>>i&1]
        sign=(-1)**sum(a>b for i,a in enumerate(indices) for b in indices[i+1:])
        mapped=sum(1<<i for i in indices)
        assert mapped not in out
        out[mapped]=sign*c
    return out

def unit(i):
    return tuple(int(j==i) for j in range(4))

def gamma_sign(i):
    return -1 if i<3 else 1

identity=(1,0,0,0)
top=(1<<128)-1
assert reflect({top:R.one})=={top:R.one}
assert reflect({255:R.one})=={255:R.one}

# Each quaternion block is independent. Check the eight basis coordinates,
# both directed frame anchors, all four world directions and Dirac indices.
nframe=0
for axis,anchor,q in product(range(4),range(2),range(8)):
    ql,qr=(unit(q), (0,)*4) if q<4 else ((0,)*4,unit(q-4))
    for fun in (action_frame,frame):
        native=fun(axis,anchor,ql,qr)
        moved=fun(axis,anchor,qr,ql)
        for i in range(4):
            assert reflect(native[i])==scale(moved[i],gamma_sign(i))
            nframe+=1

# Composite G_{mu nu} is invariant, including the off-diagonal source.
# Independent left/right unit-quaternion input on the two source edges.
nmetric=0
quats=[unit(i) for i in range(4)]
for mu,nu,al,ar,bl,br in product((2,3),(2,3),quats,quats,quats,quats):
    if mu==nu and (al,ar)!=(bl,br):
        continue
    first=frame(mu,False,al,ar)
    second=frame(nu,False,bl,br)
    first_m=frame(mu,False,ar,al)
    second_m=frame(nu,False,br,bl)
    assert reflect(add(*(wedge(a,b) for a,b in zip(first,second,strict=True))))==add(
        *(wedge(a,b) for a,b in zip(first_m,second_m,strict=True)))
    nmetric+=1

# For each of the six chiral imaginary coordinates, check the actual
# curvature trace contracted with the two reflected internal frame indices.
nvertex=0
for (a,b),terms in L.items():
    d=dict(terms)
    for i in range(6):
        j=(i+3)%6
        assert gamma_sign(a)*gamma_sign(b)*d.get(j,0)==-d.get(i,0)
        nvertex+=1
assert moment((0,0,1,1))==moment((4,4,5,5))
print('top form determinant +1; frame, source, and curvature checks',
      nframe,nmetric,nvertex)
print('quartic insertions 0,1,2 require action powers',
      [((16*8)-4*n)//4 for n in range(3)])
