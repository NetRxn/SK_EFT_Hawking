"""Upper separated-source replacement, with shared-link exact Haar-four."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement,product
from l1_direct_b_haar import add,bilinear,diag,gamma,scale,wedge
from l1_equal_time_int_contract import sparse_int
from l1_extended_overlap_upper_block import L,block,pair
from l1_normalization_disjoint_sector import adj,quat
from l1_normalization_opposed_fourth import nodes
from l1_extended_source_upper import join
from l1_reduced_wedge_reference import wedge_sign

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

def twice_signed_lower_complements():
    """Return the signed complement coefficients with a common extra factor 2."""
    _, tensor = next(combined(2))
    result = {}
    for (mask, phase), raw in tensor.items():
        assert phase == 0
        value, remainder = divmod(raw, 12)
        assert not remainder
        complement = ((1 << 32) - 1) ^ mask
        result[complement] = value * wedge_sign(complement, mask)
    return result


def degree_census():
    def vertex_degree(site, plane_axis):
        return Counter({site: 2, site ^ (1 << (3 - plane_axis)): 1, site ^ 8: 1})

    def source_degree(site, axis):
        return Counter({site: 2, site ^ (1 << axis): 2})

    def link_parity(site, plane_axis):
        frame_axis = 3 - plane_axis
        anchor = site if site >= 8 else site & ~(1 << frame_axis)
        return {
            (site, 0), (site ^ (1 << plane_axis), 0),
            (site, plane_axis), (site ^ 1, plane_axis),
            (anchor, frame_axis), (site, 3),
        }

    vertices = [(x, a) for x in range(8) for a in (1, 2)]
    vertices += [(x, 1) for x in range(8, 16) for _ in range(2)]
    removals = sorted(set(combinations(vertices, 2)))
    degrees = {}
    for x, y in combinations_with_replacement(range(16), 2):
        for a, b in product((2, 3), repeat=2):
            key = tuple(sorted((source_degree(x, a) + source_degree(y, b)).items()))
            degrees.setdefault(key, []).append((x, y, a, b))

    candidates = []
    for u, v in removals:
        key = tuple(sorted((vertex_degree(*u) + vertex_degree(*v)).items()))
        for placement in degrees.get(key, ()):
            candidates.append((u, v, placement))
    assert len(removals) == 284 and len(candidates) == 104
    # The original word has even degree on each link, and each source adds two.
    matches = [row for row in candidates if link_parity(*row[0]) == link_parity(*row[1])]
    assert all(u == v and u[0] >= 8 for u, v, _ in matches)
    assert Counter((x >= 8, x == y) for _, _, (x, y, _, _) in matches) == {
        (True, True): 16, (True, False): 8, (False, False): 16,
    }
    print("104 degree-compatible placements, 40 also pass Haar parity")
    return matches


if __name__ == "__main__":
    degree_census()
    baseline = block(0, 0, 0, 0)
    shared_diagonal = None
    for removed in (2, 3):
        for (a, b), raw in combined(removed):
            if a != b:
                assert not raw
                continue
            if shared_diagonal is None:
                shared_diagonal = raw
            assert raw == shared_diagonal
            assert raw.keys() == baseline.keys()
            assert Counter(Fraction(v, baseline[k]) for k, v in raw.items()) == {24: 72, 36: 144}
        print(f"Site {removed}: same diagonal support, raw ratios 24 and 36")
