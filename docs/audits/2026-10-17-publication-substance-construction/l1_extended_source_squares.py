"""Direct Haar-four controls for the fixed upper double-vertex replacement."""
from collections import Counter
from itertools import combinations_with_replacement
from l1_direct_b_haar import add,bilinear,diag,gamma,scale,wedge
from l1_equal_time_int_contract import sparse_int
from l1_extended_overlap_upper_block import frame_pair
from l1_normalization_disjoint_sector import adj,quat
from l1_normalization_opposed_fourth import nodes
from l1_extended_source_upper import join

def source_square(site,axis):
    neighbor=site^(1<<axis)
    out={}
    for left,right,weight in nodes():
        U=diag(quat(left),quat(right))
        Ud=diag(quat(adj(left)),quat(adj(right)))
        T=[add(bilinear(g*Ud,site,neighbor),
               scale(bilinear(U*g,neighbor,site),-1)) for g in gamma]
        G=add(*(wedge(t,t) for t in T))
        out=add(out,scale(wedge(G,G),weight))
    # q is doubled in nodes(), T here is 8 T_phys; weights are 96 Haar.
    return sparse_int(out)

def grades(poly,joined=False):
    masks=(k[0] if joined else k for k in poly)
    return Counter(tuple(((mask>>(8*i))&255).bit_count() for i in range(4))
                   for mask in masks)

if __name__=='__main__':
    expected={
        (2,0):(0,2,6,8),(2,1):(4,2,6,4),
        (3,0):(2,0,8,6),(3,1):(2,4,4,6),
    }
    for site in (2,3):
        for axis in (0,1):
            square=source_square(site,axis)
            assert square
            observed=Counter()
            for a,b in combinations_with_replacement(range(6),2):
                other=frame_pair(5-site,a,b)
                block=join(square,other) if site==2 else join(other,square)
                observed.update(grades(block,True))
            assert set(observed)=={expected[site,axis]},(site,axis,observed)
            print(site,axis,len(square),observed,flush=True)
    print('square Haar denominator',96*8**4)
