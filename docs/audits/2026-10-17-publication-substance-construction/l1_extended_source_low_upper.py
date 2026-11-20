"""Selected low/upper insertions with the low frame fixed by the actual tree."""
from itertools import combinations_with_replacement,product
from l1_direct_b_haar import add,bilinear,gamma,scale,wedge
from l1_equal_time_int_contract import sparse_int
from l1_extended_overlap_upper_block import L,frame_pair,pair
from l1_extended_source_separated import shared
from l1_extended_source_upper import join

def low_source(removed):
    low=removed^2
    T=[add(bilinear(g,low,removed),scale(bilinear(g,removed,low),-1)) for g in gamma]
    # T=4T_phys. Put fixed G33 over 8*4^2 as for the Haar-two source.
    return scale(add(*(wedge(t,t) for t in T)),8)

def blocks(removed,shared_link):
    retained=removed^1
    low=low_source(removed)
    if shared_link:
        P=shared(retained)
        Q=pair(retained,1)
        A=sparse_int(low)
    else:
        source_axis2=pair(removed,0)
        A=sparse_int(wedge(low,add(*(source_axis2[a][a] for a in range(4)))))
    for a,b in combinations_with_replacement(range(6),2):
        if shared_link:
            terms=[]
            for (g,h),(j,k) in product(L,repeat=2):
                weight=dict(L[g,h]).get(a,0)*dict(L[j,k]).get(b,0)
                if weight:
                    terms.append(scale(wedge(P[g,j],Q[h][k]),weight))
            B=sparse_int(add(*terms))
        else:
            B=frame_pair(retained,a,b)
        yield (a,b),join(A,B) if removed==2 else join(B,A)

def low_upper_complements(removed,shared_link):
    from l1_reduced_wedge_reference import wedge_sign
    maps=dict(blocks(removed,shared_link))
    reference=maps[0,0]
    assert len(reference)==504
    assert all(tensor==(reference if a==b else {}) for (a,b),tensor in maps.items())
    out={}
    for (upper,phase),value in reference.items():
        assert not phase
        lower=0xffffffff^upper
        assert not shared_link or value%12==0
        out[lower]=wedge_sign(lower,upper)*(value//12 if shared_link else value)
    return out

if __name__ == "__main__":
    for shared_link, site in product((False, True), (2, 3)):
        complements = low_upper_complements(site, shared_link)
        assert len(complements) == 504
        print(f"Shared link {shared_link}, site {site}: 504 signed complements")
