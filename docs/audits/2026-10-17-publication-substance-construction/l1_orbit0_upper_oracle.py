"""Independent complete local channel for all-protected orbit 0 at 8c5c823e3."""

from collections import Counter, defaultdict
from functools import cache
from itertools import product
from math import factorial, prod
from sympy import I, diag, zeros
from l1_protected_edge_oracle import G, P, basis, pair, sphere, wedge
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_two_face_tree import upper_tensor


@cache
def coordinate_rows(n, probe):
    rows = []
    for coords in product(range(16), repeat=n):
        powers = Counter(coords)
        if probe is None:
            if any(powers[i] for i in (9, 10, 11, 13, 14, 15)):
                continue
            starts = (0, 4)
        else:
            powers.update(8 + i for i in probe)
            starts = (0, 4, 8, 12)
        if any(powers[s + i] % 2 for s in starts for i in range(4)):
            continue
        # The common unprobed edge uses doubled coordinates and 96 cubature
        # per independent anchor. Protected exclusive edges use 192 per anchor.
        scale = 96**2 * 2**n if probe == () else 192**2
        weight = scale * prod(
            sphere(tuple(powers[s + i] for i in range(4))) for s in starts
        )
        assert weight.denominator == 1
        if weight:
            rows.append((coords, int(weight)))
    return rows


def merge(out, terms, w):
    for m, (r, i) in terms.items():
        out[m][0] += w * r
        out[m][1] += w * i


def sparse(out):
    return {m: tuple(v) for m, v in out.items() if any(v)}


@cache
def frame(labels, probe, site):
    n = len(labels)
    out = defaultdict(lambda: [0, 0])
    for coords, w in coordinate_rows(n, probe):
        p = pair(*labels[:2], *coords[:2])
        if n == 4:
            p = wedge(p, pair(*labels[2:], *coords[2:]))
        merge(out, p, w)
    return {(m & 255) | ((m >> 8) << (8 * site)): v for m, v in sparse(out).items()}


@cache
def trace(a, b):
    g5 = diag(1, 1, -1, -1)
    return tuple(
        int((-I * block * G[a] * G[b] * g5).trace())
        for block in [*(diag(p, zeros(2)) for p in P), *(diag(zeros(2), p) for p in P)]
    )


def peeled():
    weights = Counter()
    for a, b, c, d in product(range(4), repeat=4):
        w = 12 * sum(x * y for x, y in zip(trace(a, c), trace(b, d), strict=True))
        if w:
            weights[tuple(sorted((a, b))), tuple(sorted((c, d)))] += w
    return tuple((a, b, w) for (a, b), w in weights.items() if w)


def actual(probe):
    out = defaultdict(lambda: [0, 0])
    weights = peeled()
    for a, u, w in weights:
        for b, v, t in weights:
            first = frame(u, probe, 1)
            common = frame(tuple(sorted(a + b)), (), 2)
            last = frame(v, None, 3)
            if first and common and last:
                row = {
                    m: z
                    for m, z in wedge(wedge(first, common), last).items()
                    if m & 255 == 255
                }
                merge(out, row, w * t)
    return sparse(out), len(weights)


def global_map(raw, sites):
    return {
        sum(((m >> (8 * (i + 1))) & 255) << (8 * x) for i, x in enumerate(sites)): z
        for m, z in raw.items()
    }


if __name__ == "__main__":
    face = (12, 1, 3)
    live = ((4, 1),)
    fixed = dict.fromkeys(((12, 1), (12, 3), (14, 3)), ((1, 0, 0, 0), (1, 0, 0, 0)))
    sites = (4, 7, 14)
    assert tuple(6 ^ (1 << a) for a in (1, 0, 3)) == sites
    # Here P is U_(4,1)^†, so each spatial-vector leg has a minus sign.
    components = (0, 0)
    probe = tuple(4 * (q // 3) + q % 3 + 1 for q in components)
    terms = face_tensor(face, live, fixed, components)
    assert terms == {(PAIRS.index(probe),): 1}
    result, n = actual(probe)
    expected = {}
    for m, c in upper_tensor(False, (1, 3), probe, False, None).items():
        if c:
            z = c.const()
            expected[m] = (int(z.x), int(z.y))
    assert result == expected
    assert all(
        tuple(((m >> (8 * i)) & 255).bit_count() for i in range(4)) == (8, 2, 4, 2)
        for m in result
    )
    mapped = global_map(result, sites)
    assert len(mapped) == len(result) and result
    divisor = (192**4 * 4**4) * (96**2 * 8**4) * 48**2 * factorial(2) ** 2
    print(
        "components",
        components,
        "probe",
        probe,
        "weights",
        n,
        "signed full map",
        len(result),
        "positive/negative",
        tuple(sum(s * v > 0 for z in result.values() for v in z) for s in (1, -1)),
        "global sites",
        sites,
        "divisor",
        divisor,
        flush=True,
    )
