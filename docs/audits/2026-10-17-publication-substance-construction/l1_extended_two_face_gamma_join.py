"""Exact two-face contraction at specified protected coordinate-pair probes."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial

from l1_direct_b_haar import R, add, scale
from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, source_variants, summed_source_tensor, swap_patterns
from l1_extended_mixed_center_gamma import COMPONENTS, gamma_block, gamma_tensor
from l1_extended_mixed_curvature_core import PAIRS, PAIR_INDEX, face_tensor, face_vector
from l1_normalization_uniform_mixed_edge import unit
from l1_extended_mixed_frame_join import join_factors, remote_center
from l1_extended_mixed_frame_moment import SCALE
from l1_extended_opposed_source import summed_fourth
from l1_extended_overlap_strip import HAAR
from l1_extended_protected_center import protected_center, summed_protected_source
from l1_extended_two_mixed_centers import contract, contract_boundary, remap
from l1_reduced_wedge_reference import wedge_sign


@cache
def slice_rows(face, links, probes, free):
    rows = {}
    orientations = [(p,) if p[0] == p[1] else (p, p[::-1]) for p in probes]
    for components in COMPONENTS:
        (ca, ia), (cb, ib) = (divmod(label, 3) for label in components)
        row = Counter()
        for choices in product(*orientations):
            if any(a // 4 != ca or b // 4 != cb for a, b in choices):
                continue
            left = {edge: (unit(a % 4),) * 2 for edge, (a, _) in zip(links, choices)}
            right = {edge: (unit(b % 4),) * 2 for edge, (_, b) in zip(links, choices)}
            for u, v in product(range(4), repeat=2):
                left[free], right[free] = (unit(u),) * 2, (unit(v),) * 2
                weight = face_vector(face, left, ca, ia) * face_vector(face, right, cb, ib)
                if weight:
                    key = tuple(sorted((4*ca + u, 4*cb + v)))
                    row[PAIR_INDEX[key]] += weight
        row = {i: value for i, value in row.items() if value}
        if row:
            rows[components] = row
    return rows


def curvature_join(first, last):
    result = {}
    for a, b in product(first, last):
        value = sum(u * weight * last[b].get(j, 0)
                    for i, u in first[a].items() for j, weight in HAAR[PAIRS[i]])
        if value:
            result[a, b] = value
    return result


def coefficient(pattern, faces, protected, probes, common, *,
                remote_source=False, protected_source=False):
    free, = {e for edges in faces.values() for e in edges} - protected
    site, = {f[0] for f in faces}
    first, last = pattern[EVEN.index(site)]
    axis, = set(first) & set(last)
    a, b = sorted(set(first) ^ set(last))
    ordered = []
    for exclusive in (a, b):
        # The residual face that uses this frame direction is the one
        # whose curvature plane excludes it.
        face, = [f for f in faces if exclusive not in f[1:]]
        links = tuple(sorted(faces[face] - {free}))
        ordered.append(slice_rows(face, links, tuple(probes[e] for e in links), free))
    channels = curvature_join(*ordered)
    core = add(*(scale(gamma_tensor(probes[site, a], probes[site, b], c, d, common), weight)
                 for (c, d), weight in channels.items()))
    terms = {site: remap(core, (site, site ^ (1 << a), site ^ (1 << axis), site ^ (1 << b)))}
    divisor = 48 * SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2

    coupled = {site}
    changes = {}
    for x, pairs in zip(EVEN, pattern, strict=True):
        if x == site:
            continue
        p, q = pairs
        protected_axes = [i for i in sorted(set(p) | set(q)) if (x ^ (1 << i), i) in probes]
        if protected_axes:
            coupled.add(x)
            assert p == q and tuple(protected_axes) == p
            local_probes = tuple(probes[x ^ (1 << i), i] for i in p)
            local = protected_center(local_probes)
            if protected_source:
                changes[x] = remap(summed_protected_source(local_probes),
                                   (x, *(x ^ (1 << i) for i in p)))
            axes = p
            divisor *= 48 * SCALE**4 * 4**8 * factorial(4)
        else:
            local, axes = remote_center(pairs)
            divisor *= 96**4 * 8**8
            for pair in set(pairs):
                divisor *= 48 * factorial(2 * pairs.count(pair))
        terms[x] = remap(local, (x, *(x ^ (1 << i) for i in axes)))
    if not core:
        return len(channels), 0, Fraction(0)
    if protected_source:
        assert not remote_source and len(changes) == 2
        raw = -24 * sum((contract({**terms, x: local}) for x, local in changes.items()), R.zero)
        assert raw.is_ground and not raw.const().y
        return len(channels), len(core), Fraction(int(raw.const().x), divisor)
    if remote_source:
        raw = sum((weight * contract(replaced)
                   for replaced, weight in remote_source_replacements(pattern, terms, coupled)), R.zero)
    else:
        raw = contract(terms)
    keep, environment = remote_environment(pattern, coupled, source=remote_source)
    boundary = contract_boundary({x: terms[x] for x in coupled}, keep)
    closed = R.zero
    for mask, value in boundary.items():
        opposite = keep ^ mask
        if opposite in environment:
            closed += value * environment[opposite] * wedge_sign(mask, opposite)
    assert raw == closed
    assert raw.is_ground and not raw.const().y
    return len(channels), len(core), Fraction(int(raw.const().x), divisor)


def pure_links(face, edges, protected):
    local, = (e for e in edges & protected if e[0] == face[0])
    pure = tuple(sorted((edges & protected) - {local}, key=lambda e: e[1]))
    assert len(pure) == 2
    site, = {x ^ (1 << axis) for x, axis in pure}
    return pure, local, site


@cache
def pure_table(source=False):
    table = {}
    tensor = summed_protected_source if source else protected_center
    for i, j in product(range(len(PAIRS)), repeat=2):
        poly = tensor((PAIRS[i], PAIRS[j]))
        if poly:
            assert all(value.is_ground for value in poly.values())
            table[i, j] = {m: (int(v.const().x), int(v.const().y)) for m, v in poly.items()}
    return table


def fuse_face(face, pure, local, free, table):
    out = {}
    for components in COMPONENTS:
        boundary = defaultdict(dict)
        for (a, b, probe, live), weight in face_tensor(
                face, (*pure, local, free), {}, components).items():
            if (a, b) not in table:
                continue
            row = boundary[probe, live]
            for mask, (re, im) in table[a, b].items():
                old_re, old_im = row.get(mask, (0, 0))
                row[mask] = old_re + weight*re, old_im + weight*im
        for key, row in boundary.items():
            reduced = {m: value for m, value in row.items() if any(value)}
            if reduced:
                out[components, *key] = reduced
    return out


def check_fusion(face, pure, local, free, table, pair):
    index = PAIR_INDEX[pair]
    if (index, index) not in table:
        return
    row = table[index, index]
    fused = fuse_face(face, pure, local, free, {(index, index): row})
    reference = slice_rows(face, (*pure, local), (pair,) * 3, free)
    expected = {(components, index, live): {m: (weight*r, weight*i)
                                           for m, (r, i) in row.items()}
                for components, values in reference.items() for live, weight in values.items()}
    assert {key: poly for key, poly in fused.items() if key[1] == index} == expected


def remote_environment(pattern, coupled, *, source=False):
    terms = {}
    open_sites = {x ^ (1 << a) for x in coupled
                  for pair in pattern[EVEN.index(x)] for a in pair}
    keep = sum(255 << (8*x) for x in open_sites)
    for x, pairs in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            local, axes = remote_center(pairs)
            terms[x] = remap(local, (x, *(x ^ (1 << i) for i in axes)))
    if not source:
        return keep, contract_boundary(terms, keep)

    return keep, add(*(scale(contract_boundary(replaced, keep), weight)
                       for replaced, weight in remote_source_replacements(pattern, terms, coupled)))


def remote_source_replacements(pattern, terms, coupled):
    for x in terms.keys() - coupled:
        directions, variants = source_variants(*pattern[EVEN.index(x)])
        sites = (x, *(x ^ (1 << axis) for axis in directions))
        for local, adjustment, _ in variants:
            replaced = dict(terms)
            replaced[x] = remap(summed_source_tensor(local), sites)
            yield replaced, -2 * adjustment


def fuse_all():
    table = pure_table()
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2:
            continue
        free, = {e for edges in faces.values() for e in edges} - protected
        mixed, = {face[0] for face in faces}
        coupled = {mixed}
        for face, edges in sorted(faces.items()):
            pure, local, site = pure_links(face, edges, protected)
            coupled.add(site)
            assert len(set(pattern[EVEN.index(site)])) == 1
            for pair in ((0, 0), (0, 4)):
                check_fusion(face, pure, local, free, table, pair)
            fused = fuse_face(face, pure, local, free, table)
            print("orbit", multiplicity, "face", face, "fused rows", len(fused),
                  "exterior entries", sum(map(len, fused.values())), flush=True)
        assert len(coupled) == 3
        keep, environment = remote_environment(pattern, coupled)
        print("orbit", multiplicity, "open passive sites", keep.bit_count() // 8,
              "remote environment entries", len(environment), flush=True)


def open_face(fused, site, axes, free, side, probe=None):
    # The local tensor has already saturated the pure center.
    a, b = (site ^ (1 << axis) for axis in axes)
    rows = {}
    for (components, local, live), poly in fused.items():
        if probe is not None and probe != local:
            continue
        rows[live, components, local] = {
            (((mask >> 8) & 255) << (8*a)) | (((mask >> 16) & 255) << (8*b)): value
            for mask, value in poly.items()
        }
    return (free, (side, "components"), (side, "probe")), rows


def build_fused(pattern, faces, protected, table, source_table=None):
    free, = {e for edges in faces.values() for e in edges} - protected
    site, = {f[0] for f in faces}
    first, last = pattern[EVEN.index(site)]
    axis, = set(first) & set(last)
    a, b = sorted(set(first) ^ set(last))
    factors = []
    changed = []
    coupled = {site}
    for side, exclusive in enumerate((a, b)):
        face, = [f for f in faces if exclusive not in f[1:]]
        pure, local, center = pure_links(face, faces[face], protected)
        assert local == (site, (b, a)[side])
        p, q = pattern[EVEN.index(center)]
        assert p == q
        coupled.add(center)
        factors.append(open_face(fuse_face(face, pure, local, free, table),
                                 center, p, free, side))
        if source_table is not None:
            changed.append(open_face(fuse_face(face, pure, local, free, source_table),
                                     center, p, free, side))
    return site, (a, axis, b), coupled, factors, changed


def restrict_probes(factors, first, second=None):
    return [(axes, {key: value for key, value in rows.items()
                    if selected is None or key[2] == selected})
            for (axes, rows), selected in zip(factors, (first, second), strict=True)]


def sum_fused(pattern, faces, protected, table, common, probe=None, other_probe=None, *, remote_source=False):
    site, directions, coupled, factors, _ = build_fused(pattern, faces, protected, table)
    boundary = remote_environment(pattern, coupled, source=True) if remote_source else None
    return close_fused(pattern, site, directions, coupled,
                       restrict_probes(factors, probe, other_probe), common, boundary=boundary)


def close_fused(pattern, site, directions, coupled, factors, common, *, boundary=None, changed=None):
    keep, environment = remote_environment(pattern, coupled) if boundary is None else boundary
    sites = tuple(site ^ (1 << axis) for axis in directions)
    if changed is None:
        axes, joined = join_factors(*factors)
    else:
        # Insert one source pair, never both, at the two pure centers.
        axes, joined = join_factors(changed[0], factors[1])
        other_axes, other = join_factors(factors[0], changed[1])
        assert axes == other_axes
        for key, row in other.items():
            out = joined.setdefault(key, {})
            for mask, (re, im) in row.items():
                r, i = out.get(mask, (0, 0))
                out[mask] = r + re, i + im
    assert axes == ((0, "components"), (0, "probe"), (1, "components"), (1, "probe"))

    @cache
    def dual(mask):
        weights = {}
        for other, value in environment.items():
            if not mask & other:
                required = keep ^ (mask | other)
                sign = wedge_sign(mask, required) * wedge_sign(mask | required, other)
                weights[required] = value * sign
        return weights

    total = R.zero
    groups = defaultdict(list)
    for first, p, last, q in joined:
        groups[p, q].append((first, last))
    for (p, q), channels in groups.items():
        # Each face's live base link lies in its curvature plane, so
        # it probes the other face's exclusive frame axis.
        block = gamma_block(PAIRS[q], PAIRS[p], common)
        for first, last in channels:
            pure = joined[first, p, last, q]
            if not any(dual(mask) for mask in pure):
                continue
            local = block(first, last)
            mixed = {sum(((mask >> (8*i)) & 255) << (8*x)
                         for i, x in enumerate(sites, 1)): value for mask, value in local.items()}
            for mask, (re, im) in pure.items():
                subtotal = sum((coefficient * mixed.get(target, R.zero)
                                for target, coefficient in dual(mask).items()), R.zero)
                total += R.ground_new(R.domain.dtype(re, im)) * subtotal
    divisor = 48 * SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2
    divisor *= (48 * SCALE**4 * 4**8 * factorial(4))**2
    for x, pairs in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            divisor *= 96**4 * 8**8
            for pair in set(pairs):
                divisor *= 48 * factorial(2 * pairs.count(pair))
    assert total.is_ground and not total.const().y
    # Opposite shear signs, two source orders, and 4! / 2! at the replaced center.
    weight = -24 if changed is not None else 1
    return Fraction(weight * int(total.const().x), divisor), len(joined)


PROBE_CLASSES = (((0, 0), 4), ((0, 1), 6), ((4, 4), 4), ((4, 5), 6), ((0, 4), 16))


def canonical_inputs(pattern, site, directions, coupled, factors, *, boundary=None):
    passive = tuple(site ^ (1 << axis) for axis in directions)
    keep, environment = remote_environment(pattern, coupled) if boundary is None else boundary
    remaining, = set(x for x in range(16) if keep & (255 << (8*x))) - set(passive)
    ordered = (*passive, remaining)

    def canonical(mask):
        return sum(((mask >> (8*x)) & 255) << (8*i) for i, x in enumerate(ordered))

    return (
        [{key: {canonical(mask): value for mask, value in poly.items()}
          for key, poly in rows.items()} for _, rows in factors],
        {canonical(mask): value for mask, value in environment.items()},
        tuple(sorted(tuple(sorted(Counter(pairs).values()))
                     for x, pairs in zip(EVEN, pattern, strict=True) if x not in coupled)),
    )


def check_protected_source(pattern, faces, protected, common, index, table, source):
    key = index, index
    pair = PAIRS[index]
    probes = dict.fromkeys({e for row in faces.values() for e in row} & protected, pair)
    _, _, direct = coefficient(pattern, faces, protected, probes, common, protected_source=True)
    site, directions, coupled, factors, changed = build_fused(
        pattern, faces, protected, {key: table[key]}, {key: source[key]})
    fused, _ = close_fused(pattern, site, directions, coupled, restrict_probes(factors, index, index),
                           common, changed=restrict_probes(changed, index, index))
    assert fused == direct
    return direct


def replay_fused(probe, orbit, by_class=False, *, remote_source=False, protected_source=False):
    common = summed_fourth(1)
    table = pure_table()
    source = pure_table(True) if protected_source else None
    total = Fraction()
    completed = 0
    probes = [(i, 1) for i in (range(len(PAIRS)) if probe is None else (probe,))]
    if by_class:
        probes = [(PAIR_INDEX[pair], count) for pair, count in PROBE_CLASSES]
        assert sum(weight for _, weight in probes) == len(PAIRS)
    previous = []
    representatives = ((pattern, n, faces, protected)
                       for pattern, n in orbits(swap_patterns())
                       for faces, protected in (curvature_boundary(pattern),)
                       if len(faces) == 2)
    for representative, (pattern, multiplicity, faces, protected) in enumerate(representatives):
        if orbit is not None and orbit != representative:
            continue
        for pair in ((0, 0), (0, 4)):
            index = PAIR_INDEX[pair]
            limited = {(index, index): table[index, index]}
            value, _ = sum_fused(pattern, faces, protected, limited, common, index, index)
            expected = {
                (0, 0): Fraction(277641541909346923828125, 37778931862957161709568),
                (0, 4): Fraction(243274383544921875, 75557863725914323419136),
            }
            assert value == expected[pair]
            if remote_source:
                fixed_probes = dict.fromkeys({e for row in faces.values() for e in row} & protected, pair)
                _, _, direct = coefficient(pattern, faces, protected, fixed_probes, common, remote_source=True)
                fused, _ = sum_fused(pattern, faces, protected, limited, common, index, index,
                                     remote_source=True)
                assert direct == fused
                print("remote source control", representative, pair, direct, flush=True)
            if protected_source:
                value = check_protected_source(pattern, faces, protected, common, index, table, source)
                print("protected source control", representative, pair, value, flush=True)
        site, directions, coupled, factors, changed = build_fused(pattern, faces, protected, table, source)
        boundary = remote_environment(pattern, coupled, source=True) if remote_source else None
        inputs = canonical_inputs(pattern, site, directions, coupled, factors, boundary=boundary)
        if protected_source:
            inputs = (inputs, canonical_inputs(pattern, site, directions, coupled, changed))
        prior = next((old for old_inputs, old in previous if old_inputs == inputs), None)
        if prior is not None:
            print("orbit", representative, "reuses identical canonical input", flush=True)
            subtotal = prior
        else:
            subtotal = Fraction()
            for index, count in probes:
                value, rows = close_fused(pattern, site, directions, coupled,
                                          restrict_probes(factors, index), common, boundary=boundary,
                                          changed=restrict_probes(changed, index) if protected_source else None)
                print("orbit", representative, "multiplicity", multiplicity,
                      "first probe", PAIRS[index], "class weight", count,
                      "candidate rows" if protected_source else "rows", rows,
                      "coefficient", value, flush=True)
                subtotal += count * value
            previous.append((inputs, subtotal))
        total += 2 * multiplicity * subtotal / (6 if remote_source or protected_source else 1)
        completed += 1
    assert completed == (3 if orbit is None else 1)
    if probe is None:
        label = "two-face remote source subtotal" if remote_source else "two-face normalization"
        if protected_source:
            label = "two-face protected source subtotal"
        if orbit is not None:
            label = "selected orbit " + label
        print(label, "both checkerboards", total, flush=True)


def check_crossed_probes():
    common = summed_fourth(1)
    for pattern, _ in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2:
            continue
        site, = {f[0] for f in faces}
        first, last = pattern[EVEN.index(site)]
        a, b = sorted(set(first) ^ set(last))
        ordered = [next(f for f in faces if axis not in f[1:]) for axis in (a, b)]
        pure_probe = PAIR_INDEX[0, 0]
        table = {(pure_probe, pure_probe): protected_center(((0, 0), (0, 0)))}
        table = {key: {m: (int(v.const().x), int(v.const().y)) for m, v in poly.items()}
                 for key, poly in table.items()}
        for left, right in (((0, 0), (0, 4)), ((0, 0), (1, 1)), ((0, 1), (1, 1))):
            probes = dict.fromkeys(set.union(*faces.values()) & protected, (0, 0))
            for f, pair in zip(ordered, (left, right), strict=True):
                _, local, _ = pure_links(f, faces[f], protected)
                probes[local] = pair
            _, _, direct = coefficient(pattern, faces, protected, probes, common)
            fused, _ = sum_fused(pattern, faces, protected, table, common,
                                 PAIR_INDEX[left], PAIR_INDEX[right])
            assert fused == direct, (left, right, fused, direct)
            print("unequal probe check", left, right, direct, flush=True)
        return
    raise AssertionError("expected a two-face control orbit")


def main():
    common = summed_fourth(1)
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2:
            continue
        links = {e for edges in faces.values() for e in edges} & protected
        assert len(links) == 6
        for (x, _, _), edges in faces.items():
            frame_links = edges & links
            local = {edge for edge in frame_links if edge[0] == x}
            assert len(local) == 1
            pure_sites = {y ^ (1 << axis) for y, axis in frame_links - local}
            pure_site, = pure_sites
            assert len(frame_links - local) == 2 and pure_site in EVEN
            a, b = pattern[EVEN.index(pure_site)]
            assert a == b
        for pair in ((0, 0), (0, 4)):
            probes = dict.fromkeys(links, pair)
            print("orbit", multiplicity, "probe", pair,
                  "channels, core entries, coefficient", coefficient(
                      pattern, faces, protected, probes, common), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--crossed-control", action="store_true")
    mode.add_argument("--fuse-pure-centers", action="store_true")
    mode.add_argument("--first-probe", type=int, choices=range(len(PAIRS)))
    mode.add_argument("--all-probes", action="store_true")
    mode.add_argument("--probe-classes", action="store_true")
    mode.add_argument("--remote-source", action="store_true")
    mode.add_argument("--protected-source", action="store_true")
    parser.add_argument("--orbit", type=int, choices=range(3))
    args = parser.parse_args()
    if args.all_probes or args.probe_classes or args.remote_source or args.protected_source or args.first_probe is not None:
        replay_fused(args.first_probe, args.orbit, args.probe_classes or args.remote_source or args.protected_source,
                     remote_source=args.remote_source, protected_source=args.protected_source)
    elif args.crossed_control:
        check_crossed_probes()
    elif args.fuse_pure_centers:
        fuse_all()
    else:
        main()
