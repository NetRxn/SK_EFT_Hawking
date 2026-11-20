"""Exact factor assembly for the predeclared odd-curvature offset word."""

from collections import Counter
from functools import cache
from itertools import combinations, product
from time import monotonic

from l1_extended_anchor_census import anchor_multiplicity
from l1_extended_offset_pair_census import AXES, SITES, source_endpoints
from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY
from l1_extended_mixed_curvature_core import face_vector
from l1_extended_mixed_frame_moment import SCALE, moment, anchored
from l1_extended_offset_witness import coframe, center_weights, gaussian
from l1_extended_two_mixed_centers import remap
from l1_normalization_opposed_fourth import L
from l1_normalization_uniform_mixed_edge import unit

SOURCES = ((0, 2), (1, 2))
FRAME_PLANES = {x: ((0, 1),) * 2 for x in SITES if x}
FRAME_PLANES.update({x: ((0, 1), (0, 3)) for x in (1, 3, 9, 11)})
FRAME_PLANES.update(
    {
        5: ((1, 3),) * 2,
        **{x: ((0, 3),) * 2 for x in (7, 8, 10)},
        **{x: ((1, 2),) * 2 for x in (12, 14)},
    }
)
TREE = {(1, 1), (1, 2), (1, 3), (3, 2), (9, 2), (11, 2), (13, 1)}


def endpoint(edge):
    x, axis = edge
    return x ^ (1 << axis)


def undirected(edge):
    return min(edge[0], endpoint(edge)), edge[1]


def geometry():
    slots = Counter()
    faces = {}
    for site, planes in FRAME_PLANES.items():
        for plane, multiplicity in Counter(planes).items():
            first, second = (a for a in AXES if a not in plane)
            face = site, first, second
            faces[face] = (
                multiplicity,
                {
                    (site, first),
                    (site ^ (1 << first), second),
                    (site ^ (1 << second), first),
                    (site, second),
                },
            )
            for axis in plane:
                slots[undirected((site, axis))] += multiplicity
    word = [face for face, (n, _) in faces.items() for _ in range(n)]
    degrees, anchors = anchor_multiplicity(word, 16, 4)
    endpoints = source_endpoints(1, 2, 2)
    assert len(word) == 30 and Counter(Counter(word).values()) == {2: 11, 1: 8}
    assert anchors == 2**37
    assert all(degrees[x] + 2 * endpoints[x] == 8 for x in SITES)
    assert len(slots) == 23 and Counter(slots.values()) == {2: 16, 4: 7}
    protected = {(y, a) for x, a in slots for y in (x, x ^ (1 << a))} | set(SOURCES)
    peeled = 0
    while True:
        counts = Counter(e for _, edges in faces.values() for e in edges)
        private = next(
            (
                f
                for f, (_, edges) in faces.items()
                if any(counts[e] == 1 and e not in protected for e in edges)
            ),
            None,
        )
        if private is None:
            break
        multiplicity, _ = faces.pop(private)
        assert multiplicity == 2
        peeled += 1
    assert peeled == 11 and len(faces) == 8
    assert all(n == 1 for n, _ in faces.values())
    incidence = Counter(e for _, edges in faces.values() for e in edges)
    assert len(incidence) == 20 and TREE <= incidence.keys()
    assert (1, 2) in TREE and (0, 2) not in incidence
    vertices = {x for e in incidence for x in (e[0], endpoint(e))}
    reached = {min(vertices)}
    for _ in TREE:
        for edge in TREE:
            x, y = edge[0], endpoint(edge)
            if x in reached or y in reached:
                reached.update((x, y))
    assert len(TREE) == len(vertices) - 1 and reached == vertices
    live = incidence.keys() - TREE
    assert len(live) == 13 and all(incidence[e] == 1 for e in live)
    assert {(9, 1), (11, 1)} <= live
    assert all(slots[undirected(e)] in (2, 4) for e in live)
    return slots, faces, live


SLOTS, FACES, LIVE = geometry()
DIVISOR = SCALE ** (2 * len(SLOTS) + 2) * 4**64 * 48**11 * 2**11


def gkey(site, axis):
    return "gamma", site, axis


def qkey(edge):
    return "coordinate", *edge


def face_keys(face):
    _, edges = FACES[face]
    return tuple(sorted(edges & LIVE))


def face_rows(face):
    """Linear closed curvature coefficient for each residual coordinate monomial."""
    _, edges = FACES[face]
    free = face_keys(face)
    out = {}
    for chirality in range(2):
        for coordinates in product(range(4), repeat=len(free)):
            values = dict.fromkeys(edges - set(free), IDENTITY)
            for edge, q in zip(free, coordinates, strict=True):
                values[edge] = (unit(q), unit(q))
            labels = tuple(4 * chirality + q for q in coordinates)
            for component in range(3):
                value = face_vector(face, values, chirality, component)
                if value:
                    out[3 * chirality + component, labels] = value
    assert len(out) == (6 if len(free) == 1 else 24)
    return out


def action_centers():
    for site, planes in sorted(FRAME_PLANES.items()):
        if len(set(planes)) == 1:
            a, b = planes[0]
            yield (
                (gkey(site, a), gkey(site, b)),
                {key: {0: (value, 0)} for key, value in center_weights(None).items()},
                {},
            )
            continue

        axes = tuple(sorted(set().union(*planes)))
        faces = [(site, *(a for a in AXES if a not in plane)) for plane in planes]
        coordinate_keys = tuple(
            sorted(set().union(*(set(face_keys(face)) for face in faces)))
        )
        rows = Counter()
        for ((comp0, values0), s0), ((comp1, values1), s1) in product(
            *(face_rows(face).items() for face in faces)
        ):
            assignment = dict(zip(face_keys(faces[0]), values0, strict=True))
            other = dict(zip(face_keys(faces[1]), values1, strict=True))
            if any(assignment[e] != other[e] for e in assignment.keys() & other.keys()):
                continue
            assignment.update(other)
            probes = tuple(assignment[e] for e in coordinate_keys)
            for first, last in product(L, repeat=2):
                w = dict(L[first]).get(comp0, 0) * dict(L[last]).get(comp1, 0)
                if not w:
                    continue
                gamma = {axis: [] for axis in axes}
                for plane, labels in zip(planes, (first, last), strict=True):
                    for axis, label in zip(plane, labels, strict=True):
                        gamma[axis].append(label)
                rows[tuple(tuple(sorted(gamma[a])) for a in axes) + probes] += (
                    s0 * s1 * w
                )
        # Sorted complements for both singleton planes have positive world epsilon.
        yield (
            tuple(gkey(site, a) for a in axes) + tuple(map(qkey, coordinate_keys)),
            {key: {0: (value, 0)} for key, value in rows.items() if value},
            {},
        )


@cache
def directed(anchor, slots, probe, fixed):
    if not fixed and (len(slots) + len(probe)) % 2:
        return {}
    assert fixed or len(slots) + len(probe) <= 4
    terms = []
    for coordinates in product((0, 4) if fixed else range(8), repeat=len(slots)):
        weight = SCALE if fixed else moment(tuple(sorted(coordinates + probe)))
        if not weight:
            continue
        row = {0: R.one}
        for (center, gamma), q in zip(slots, coordinates, strict=True):
            row = wedge(row, coframe(center, anchor, q, gamma))
        if row:
            terms.append(scale(row, weight))
    return add(*terms)


@cache
def edge_row(slots, probes, fixed):
    rows = []
    for n in range(len(slots) + 1):
        if (
            not fixed[0]
            and (n + len(probes[0])) % 2
            or not fixed[1]
            and (len(slots) - n + len(probes[1])) % 2
        ):
            continue
        for ids in combinations(range(len(slots)), n):
            a = tuple(slots[i] for i in ids)
            b = tuple(slot for i, slot in enumerate(slots) if i not in ids)
            rows.append(
                wedge(
                    directed(0, a, probes[0], fixed[0]),
                    directed(1, b, probes[1], fixed[1]),
                )
            )
    return add(*rows)


def prepare():
    begin = monotonic()
    factors = list(action_centers())
    domains = {}
    for keys, rows, _ in factors:
        for i, key in enumerate(keys):
            assert key not in domains
            domains[key] = tuple(sorted({r[i] for r in rows}))
    print(
        "center factor counts",
        [(len(keys), len(rows)) for keys, rows, _ in factors],
        flush=True,
    )
    odd = edge_row(((0, 0), (1, 0)), ((1,), (1,)), (False, False))
    assert len(odd) == 16 and set(gaussian(odd).values()) == {(-4608, 0)}
    for lo, a in sorted(SLOTS):
        hi = lo ^ (1 << a)
        gsites = tuple(site for site in (lo, hi) if gkey(site, a) in domains)
        gedges = tuple(gkey(site, a) for site in gsites)
        directed_edges = ((lo, a), (hi, a))
        qedges = tuple(qkey(edge) for edge in directed_edges if edge in LIVE)
        keys = gedges + qedges
        fixed = tuple(edge in TREE for edge in directed_edges)
        rows = {}
        for values in product(*(domains[key] for key in keys)):
            assignment = dict(zip(keys, values, strict=True))
            slots = tuple(
                (int(site == hi), g)
                for site, key in zip(gsites, gedges, strict=True)
                for g in assignment[key]
            )
            probes = tuple(
                (assignment[qkey(edge)],) if qkey(edge) in assignment else ()
                for edge in directed_edges
            )
            local = edge_row(slots, probes, fixed)
            if local:
                rows[values] = gaussian(remap(local, (lo, hi)))
        degree = SLOTS[lo, a]
        assert rows
        factors.append((keys, rows, {lo: degree, hi: degree}))
        print(
            "edge factor",
            (lo, a),
            len(rows),
            sum(map(len, rows.values())),
            "seconds",
            round(monotonic() - begin, 3),
            flush=True,
        )
    for site, axis in SOURCES:
        assert undirected((site, axis)) not in SLOTS
        probe = None if (site, axis) in TREE else ()
        end = site ^ (1 << axis)
        row = add(*(anchored(0, (), probe, g) for g in range(4)))
        factors.append(((), {(): gaussian(remap(row, (site, end)))}, {site: 2, end: 2}))
    assert len(factors) == 40
    assert set(Counter(k for keys, _, _ in factors for k in keys).values()) == {2}
    assert {
        site: sum(d.get(site, 0) for _, _, d in factors) for site in SITES
    } == dict.fromkeys(SITES, 8)
    print("assembled", len(factors), "factors", "divisor", DIVISOR, flush=True)
    return factors


if __name__ == "__main__":
    import signal

    signal.alarm(75)
    prepare()
