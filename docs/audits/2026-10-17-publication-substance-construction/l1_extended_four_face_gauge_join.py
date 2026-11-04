"""Exact normalization of the four-face L1 cores in tree gauge."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import factorial

from l1_direct_b_haar import R, add, scale
from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, swap_patterns
from l1_extended_mixed_center_gamma import COMPONENTS, gamma_block
from l1_extended_mixed_curvature_core import PAIRS, PAIR_INDEX, face_tensor
from l1_extended_mixed_frame_moment import SCALE
from l1_extended_opposed_source import summed_fourth
from l1_extended_two_face_gamma_join import pure_table, remote_environment
from l1_normalization_uniform_mixed_edge import unit
from l1_reduced_wedge_reference import wedge_sign

IDENTITY = (unit(0),) * 2
PROBE_CLASSES = (
    ((0, 0), 1), ((0, 1), 3), ((1, 1), 3), ((1, 2), 3),
    ((4, 4), 1), ((4, 5), 3), ((5, 5), 3), ((5, 6), 3),
    ((0, 4), 1), ((0, 5), 3), ((1, 4), 3), ((1, 5), 9),
)


def geometry(pattern, faces, protected):
    mixed = {x for x, _, _ in faces}
    links = {e for edges in faces.values() for e in edges}
    lower = sorted(e for e in links & protected if e[0] in mixed)
    free = links - protected
    tree = free | set(lower[:-1])
    live = lower[-1]
    vertices = {v for x, a in tree for v in (x, x ^ (1 << a))}
    assert len(tree) == 7 and len(vertices) == 8
    reached = {min(vertices)}
    for _ in vertices:
        for x, a in tree:
            y = x ^ (1 << a)
            if x in reached or y in reached:
                reached.update((x, y))
    assert reached == vertices
    pure = defaultdict(list)
    for face, edges in faces.items():
        (x, axis), = edges - tree - {live}
        center = x ^ (1 << axis)
        assert center in EVEN and center not in mixed
        pure[center].append((axis, face, (x, axis)))
    assert sorted(map(len, pure.values())) == [2, 2]
    return mixed, pure, tree, live


def pure_factor(faces, tree, live, probe, items, table):
    rows = []
    for _, face, link in items:
        boundary = {}
        has_live = live in faces[face]
        open_links = (link, live) if has_live else (link,)
        fixed = {edge: IDENTITY for edge in faces[face] & tree}
        for components in COMPONENTS:
            raw = face_tensor(face, open_links, fixed, components)
            row = {key[0]: weight for key, weight in raw.items()
                   if not has_live or key[1] == probe}
            if row:
                boundary[components] = row
        rows.append(boundary)
    factor = {}
    for a, b in product(*rows):
        out = defaultdict(lambda: [0, 0])
        for (i, u), (j, v) in product(rows[0][a].items(), rows[1][b].items()):
            for mask, (re, im) in table.get((i, j), {}).items():
                assert mask & 255 == 255
                value = out[mask >> 8]
                value[0] += u*v*re
                value[1] += u*v*im
        poly = {m: tuple(value) for m, value in out.items() if any(value)}
        if poly:
            factor[a, b] = poly
    return factor


def close_pure(a, b, swapped):
    total_re = total_im = 0
    for mask, (re, im) in a.items():
        target = 65535 ^ mask
        if swapped:
            target = ((target & 255) << 8) | (target >> 8)
        u, v = b.get(target, (0, 0))
        sign = wedge_sign(mask, 65535 ^ mask)
        total_re += sign*(re*u - im*v)
        total_im += sign*(re*v + im*u)
    return total_re, total_im


def mixed_layout(pattern, faces, site, live, probe, common):
    p, q = pattern[EVEN.index(site)]
    axis, = set(p) & set(q)
    a, b = sorted(set(p) ^ set(q))
    ordered = [next(f for f in faces if f[0] == site and exclusive not in f[1:])
               for exclusive in (a, b)]
    probes = tuple(PAIRS[probe] if (site, exclusive) == live else None for exclusive in (a, b))
    return ordered, tuple(site ^ (1 << i) for i in (a, axis, b)), gamma_block(*probes, common)


def mixed_rows(block, sites, channels):
    rows = {}
    for a, b in channels:
        row = {}
        for mask, value in block(a, b).items():
            assert mask & 255 == 255 and value.is_ground
            m = sum(((mask >> (8*i)) & 255) << (8*x) for i, x in enumerate(sites, 1))
            row[m] = int(value.const().x), int(value.const().y)
        rows[a, b] = row
    return rows


def dual_mixed(keep, environment, first, second_sites):
    second_mask = sum(255 << (8*x) for x in second_sites)
    fixed = keep ^ second_mask
    indexed = defaultdict(list)
    for mask, value in environment.items():
        assert value.is_ground
        indexed[mask & fixed].append((mask, int(value.const().x), int(value.const().y)))
    out = {}
    for key, poly in first.items():
        row = defaultdict(lambda: [0, 0])
        for a, (r, i) in poly.items():
            for b, u, j in indexed[fixed ^ (a & fixed)]:
                if a & b:
                    continue
                target = keep ^ (a | b)
                sign = wedge_sign(a, target) * wedge_sign(a | target, b)
                value = row[target]
                value[0] += sign*(r*u - i*j)
                value[1] += sign*(r*j + i*u)
        out[key] = {mask: tuple(value) for mask, value in row.items() if any(value)}
    return out


def dot(a, b):
    re = im = 0
    for mask, (r, i) in a.items():
        u, j = b.get(mask, (0, 0))
        re += r*u - i*j
        im += r*j + i*u
    return re, im


def coefficient(pattern, faces, protected, probe, table, common, reuse):
    mixed, pure, tree, live = geometry(pattern, faces, protected)
    pure_items = [sorted(items) for _, items in sorted(pure.items())]
    pure_sites = [tuple(x ^ (1 << a) for a, _, _ in items)
                  for x, items in zip(sorted(pure), pure_items, strict=True)]
    assert set(pure_sites[0]) == set(pure_sites[1])
    factors = []
    for i, items in enumerate(pure_items):
        if any(live in faces[face] for _, face, _ in items):
            factors.append(pure_factor(faces, tree, live, probe, items, table))
        else:
            if i not in reuse:
                reuse[i] = pure_factor(faces, tree, live, probe, items, table)
            factors.append(reuse[i])
    order = [f for items in pure_items for _, f, _ in items]
    layouts = [mixed_layout(pattern, faces, x, live, probe, common) for x in sorted(mixed)]
    slot = [tuple(order.index(f) for f in layout[0]) for layout in layouts]
    supports = [tuple({key[i] for key in factor} for i in range(2)) for factor in factors]
    channels = (*supports[0], *supports[1])
    if "dual" not in reuse:
        keep, environment = remote_environment(pattern, mixed | pure.keys())
        pure_mask = sum(255 << (8*x) for x in pure_sites[0])
        assert not any(mask & pure_mask for mask in environment)
        assert live[0] == max(mixed)
        first = mixed_rows(layouts[0][2], layouts[0][1], product(COMPONENTS, repeat=2))
        reuse["dual"] = dual_mixed(keep ^ pure_mask, environment, first, layouts[1][1])
    second = mixed_rows(layouts[1][2], layouts[1][1], product(*(channels[i] for i in slot[1])))
    dual = reuse["dual"]
    re = im = 0
    mixed_cache = {}
    for a, b in product(*factors):
        u, v = close_pure(factors[0][a], factors[1][b], pure_sites[0] != pure_sites[1])
        if not (u or v):
            continue
        keys = tuple(tuple((a + b)[i] for i in indices) for indices in slot)
        if keys not in mixed_cache:
            mixed_cache[keys] = dot(dual[keys[0]], second[keys[1]])
        r, j = mixed_cache[keys]
        re += u*r - v*j
        im += u*j + v*r
    assert not im
    divisor = (48 * SCALE**4 * 4**8 * factorial(4))**2
    divisor *= (SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2)**2
    for x, pairs in zip(EVEN, pattern, strict=True):
        if x not in mixed and x not in pure:
            divisor *= 96**4 * 8**8
            for pair in set(pairs):
                divisor *= 48 * factorial(2 * pairs.count(pair))
    return Fraction(re, divisor), tuple(map(len, factors))


def main():
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--probe", type=int, choices=range(len(PAIRS)))
    mode.add_argument("--probe-classes", action="store_true")
    parser.add_argument("--orbit", type=int, choices=range(3))
    args = parser.parse_args()
    common = summed_fourth(1)
    table = pure_table()
    total = Fraction()
    probes = [(i, 1) for i in (range(len(PAIRS)) if args.probe is None else (args.probe,))]
    if args.probe_classes:
        probes = [(PAIR_INDEX[pair], weight) for pair, weight in PROBE_CLASSES]
        assert sum(weight for _, weight in probes) == len(PAIRS)
    representatives = ((p, n, f, pr) for p, n in orbits(swap_patterns())
                       for f, pr in (curvature_boundary(p),) if len(f) == 4)
    for i, (pattern, multiplicity, faces, protected) in enumerate(representatives):
        if args.orbit is not None and i != args.orbit:
            continue
        reuse = {}
        for probe, weight in probes:
            value, rows = coefficient(pattern, faces, protected, probe, table, common, reuse)
            print("orbit", i, "probe", PAIRS[probe], "class weight", weight, "pure rows", rows,
                  "coefficient", value, flush=True)
            total += 2 * multiplicity * weight * value
    if args.probe is None and args.orbit is None:
        print("four-face normalization, both checkerboards", total)


if __name__ == "__main__":
    main()
