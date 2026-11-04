"""Exact right boundary after integrating U4 and two curvature-only links."""

from collections import Counter
from functools import cache
from itertools import product
from time import perf_counter
from l1_extended_overlap_u6 import build_right,Q,S
from l1_normalization_uniform_mixed_edge import moment,mul,qadj,unit

@cache
def factor(a,b):
    # G=(0,0,2) gives U4†. H=(4,0,2) gives J† K U4.
    # I=(5,0,2) gives K† V† J W, V=U(1,0), W=U(5,0).
    # Both J=(4,2) and K=(5,2) project independently at degree 2.
    out=Counter()
    for e,f in product(S,repeat=2):
        if e%4==0:continue
        m=moment(a,b,e,f)
        if not m:continue
        g=3*(e//4)+(e%4)-1
        c=f//4
        for j,k,v,w in product(Q,repeat=4):
            h=mul(mul(qadj(unit(j)),unit(k)),unit(f%4))
            i=mul(mul(qadj(unit(k)),qadj(unit(v))),mul(unit(j),unit(w)))
            if not any(h[1:]) or not any(i[1:]):continue
            for u,y in product(range(3),repeat=2):
                z=h[u+1]*i[y+1]
                if z:out[4*c+v,4*c+w,36*g+6*(3*c+u)+3*c+y]-=m*z
    return tuple((k,v) for k,v in out.items() if v)

def projected_slots():
    """Yield one sparse boundary tensor per ordered U6 slot."""
    for slot, rows in build_right().items():
        boundary = Counter()
        for (ports, curvature), coefficient in rows.items():
            *linear_ports, a, b = ports
            for (j, k, added_curvature), weight in factor(a, b):
                key = (tuple(linear_ports) + (j, k), 216 * curvature + added_curvature)
                boundary[key] += coefficient * weight
        yield slot, {key: value for key, value in boundary.items() if value}


if __name__ == "__main__":
    start = perf_counter()
    counts = [len(boundary) for _, boundary in projected_slots()]
    assert len(counts) == 64
    assert sum(counts) == 2_737_152
    assert max(counts) == 54_432
    print(f"{len(counts)} slots, {sum(counts):,} entries, peak {max(counts):,}")
    print(f"Elapsed {perf_counter() - start:.2f} s")
