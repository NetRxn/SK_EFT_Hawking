"""Upper separated-source replacement, with shared-link exact Haar-four."""
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement,product
from l1_direct_b_haar import add,bilinear,diag,gamma,scale,wedge
from l1_equal_time_int_contract import sparse_int
from l1_extended_overlap_upper_block import L,block,pair
from l1_normalization_disjoint_sector import adj,quat
from l1_normalization_opposed_fourth import nodes
from l1_extended_source_upper import join

def shared(site):
    other=site^1
    out={(g,j):{} for g,j in product(range(4),repeat=2)}
    for left,right,weight in nodes():
        U=diag(quat(left),quat(right))
        Ud=diag(quat(adj(left)),quat(adj(right)))
        T=[add(bilinear(g*Ud,site,other),scale(bilinear(U*g,other,site),-1)) for g in gamma]
        G=add(*(wedge(t,t) for t in T))
        for g,j in out:
            out[g,j]=add(out[g,j],scale(wedge(G,wedge(T[g],T[j])),weight))
    return out

def combined(removed):
    retained=removed^1
    P=shared(retained)
    Q=pair(retained,1)
    source=add(*(pair(removed,1)[a][a] for a in range(4)))
    for a,b in combinations_with_replacement(range(6),2):
        parts=[]
        for (g,h),(j,k) in product(L,repeat=2):
            weight=dict(L[g,h]).get(a,0)*dict(L[j,k]).get(b,0)
            if weight:
                parts.append(scale(wedge(P[g,j],Q[h][k]),weight))
        retained_poly=sparse_int(add(*parts))
        raw=join(sparse_int(source),retained_poly) if removed==2 else join(retained_poly,sparse_int(source))
        yield (a,b),raw

def degree_census():
    upper = range(8, 16)

    def vertex_degree(site):
        return Counter({site: 2, site ^ 4: 1, site ^ 8: 1})

    def source_degree(site, axis):
        return Counter({site: 2, site ^ (1 << axis): 2})

    matches = []
    for u, v in combinations_with_replacement(upper, 2):
        removed = vertex_degree(u) + vertex_degree(v)
        for x, y in combinations_with_replacement(upper, 2):
            for a, b in product((2, 3), repeat=2):
                if source_degree(x, a) + source_degree(y, b) == removed:
                    matches.append((u, v, x, y, a, b))
    assert len(matches) == 24
    assert sum(x != y for _, _, x, y, _, _ in matches) == 8
    return matches


if __name__ == "__main__":
    degree_census()
    baseline = block(0, 0, 0, 0)
    for removed in (2, 3):
        for (a, b), raw in combined(removed):
            if a != b:
                assert not raw
                continue
            assert raw.keys() == baseline.keys()
            assert {Fraction(v, baseline[k]) for k, v in raw.items()} == {24, 36}
        print(f"Site {removed}: same diagonal support, raw ratios 24 and 36")
