"""Attach protected frame tensors on fixed gamma slices of the curvature cores."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial, prod

from l1_direct_b_haar import R, wedge
from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, swap_patterns
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE, frame_edge
from l1_extended_opposed import curvature, staged_center
from l1_extended_opposed_source import summed_fourth
from l1_extended_overlap_strip import HAAR
from l1_extended_two_mixed_centers import contract, mixed_center, remap, second_sum
from l1_normalization_opposed_fourth import L


def attached_face(face, protected, free, frames, components):
    raw = Counter()
    for (a, u), (b, v) in product(components, repeat=2):
        for key, weight in face_tensor(face, (*protected, *free), {}, (a, b)).items():
            raw[key] += u * v * weight

    @cache
    def combined(left, middle):
        return wedge(frames[protected[0]][left], frames[protected[1]][middle])

    out = defaultdict(lambda: defaultdict(lambda: R.zero))
    for (a, b, *tail), weight in raw.items():
        if not weight:
            continue
        term = combined(a, b)
        if len(protected) == 3:
            c, *tail = tail
            term = wedge(term, frames[protected[2]][c])
        if term:
            live = tuple(tail)
            row = out[live]
            for mask, value in term.items():
                row[mask] += value * weight
    reduced = {i: {mask: value for mask, value in poly.items() if value}
               for i, poly in out.items()}
    return {i: poly for i, poly in reduced.items() if poly}


def complement_mask(left, right):
    first = next(iter(next(iter(left.values()))))
    second = next(iter(next(iter(right.values()))))
    return sum(255 << shift for shift in range(0, 128, 8)
               if ((first >> shift) & 255).bit_count()
               + ((second >> shift) & 255).bit_count() == 8)


def preceding_parity(mask):
    # Exclusive prefix parity of the right factor at every generator.
    for shift in (1, 2, 4, 8, 16, 32, 64):
        mask ^= mask << shift
    return mask << 1


def wedge_accumulate(out, left, index, full, weight):
    for a, (r, i) in left.items():
        for b, parity, (s, j) in index[full ^ (a & full)]:
            if not a & b:
                signed = -weight if (a & parity).bit_count() % 2 else weight
                old_r, old_i = out.get(a | b, (0, 0))
                out[a | b] = old_r + signed*(r*s - i*j), old_i + signed*(r*j + i*s)


def join_factors(first, second, *, match_labels=False):
    axes, left = first
    other, right = second
    common = tuple(e for e in axes if e in other)
    ai, bi = (tuple(axis.index(e) for e in common) for axis in (axes, other))
    la, ra = (tuple(i for i, e in enumerate(axis) if e not in common)
              for axis in (axes, other))
    output = defaultdict(dict)
    if not left or not right:
        return tuple(axes[i] for i in la) + tuple(other[i] for i in ra), {}
    full = complement_mask(left, right)
    lookup = defaultdict(list)
    for q, poly in right.items():
        index = defaultdict(list)
        for mask, coefficient in poly.items():
            index[mask & full].append((mask, preceding_parity(mask), coefficient))
        lookup[tuple(q[i] for i in bi)].append((q, index))
    for p, poly in left.items():
        choices = (((p[i], 1),) if match_labels else HAAR[PAIRS[p[i]]] for i in ai)
        for moments in product(*choices):
            indices = tuple(index for index, _ in moments)
            weight = prod(w for _, w in moments)
            for q, value in lookup[indices]:
                dest = tuple(p[i] for i in la) + tuple(q[i] for i in ra)
                wedge_accumulate(output[dest], poly, value, full, weight)
    open_links = tuple(axes[i] for i in la) + tuple(other[i] for i in ra)
    reduced = {k: {m: v for m, v in row.items() if any(v)} for k, row in output.items()}
    return open_links, {k: v for k, v in reduced.items() if v}


def close_shared(factors):
    if len(factors) == 4:
        # Join the two faces based at each center first. These pairs
        # close the degree-eight frame endpoints before the final join.
        factors = [join_factors(*factors[:2]), join_factors(*factors[2:])]
    axes, result = join_factors(*factors)
    assert not axes
    return result.get((), {})


@cache
def frame_table(labels, anchor):
    return tuple(frame_edge(labels, anchor, probe) for probe in PAIRS)


def protected_frames(pattern, faces, protected):
    result = {}
    for edge in {e for edges in faces.values() for e in edges} & protected:
        x, axis = edge
        y = x ^ (1 << axis)
        center, passive = (x, y) if x in EVEN else (y, x)
        degree = 2 * sum(axis in pair for pair in pattern[EVEN.index(center)])
        result[edge] = tuple(remap(poly, (center, passive))
                             for poly in frame_table((axis,) * degree, int(x != center)))
    return result


def translated_factors(factors, shift):
    translated = []
    for edges, rows in factors:
        coordinates = tuple((x ^ shift, axis) for x, axis in edges)
        order = sorted(range(len(coordinates)), key=coordinates.__getitem__)
        polynomials = {
            tuple(key[i] for i in order): {sum(((mask >> (8*x)) & 255) << (8*(x ^ shift)) for x in range(16)): value
                  for mask, value in poly.items()}
            for key, poly in rows.items()
        }
        translated.append((tuple(coordinates[i] for i in order), polynomials))
    return translated


@cache
def unprobed_frame(axis, degree):
    moments = second_sum(0) if degree == 2 else summed_fourth(0)
    return moments[(axis,) * degree]


@cache
def remote_tensor(mixed):
    common = summed_fourth(1)
    if mixed:
        return mixed_center(common)
    normal, _ = staged_center(summed_fourth(0), common)
    return normal


def remote_center(pairs):
    first, second = pairs
    if first == second:
        return remote_tensor(False), first
    axis, = set(first) & set(second)
    a, b = sorted(set(first) ^ set(second))
    return remote_tensor(True), (a, axis, b)


def saturate_slice(pattern, faces, attached, result, free_count, shift, *, sum_remote=False):
    core = {mask: R.ground_new(R.domain.dtype(re, im))
            for mask, (re, im) in result.items()}
    terms = {-1: remap(core, tuple(x ^ shift for x in range(16)))}
    used = set()
    divisor = 48**free_count
    weight = 1
    summed = 0
    for x, pairs in zip(EVEN, pattern, strict=True):
        axes = sorted(set().union(*map(set, pairs)))
        incident = {(site, axis) for axis in axes for site in (x, x ^ (1 << axis))}
        if sum_remote and not incident & attached.keys() and not any(f[0] == x for f in faces):
            poly, directions = remote_center(pairs)
            terms[x] = remap(poly, (x, *(x ^ (1 << axis) for axis in directions)))
            divisor *= 96**4 * 8**8
            for pair in set(pairs):
                divisor *= 48 * factorial(2 * pairs.count(pair))
            summed += 1
            continue
        for a, b in set(pairs):
            n = 2 * pairs.count((a, b))
            k, l = (axis for axis in range(4) if axis not in (a, b))
            if (x, k, l) not in faces:
                weight *= curvature(((a, b),) * n)
                divisor *= 48
            divisor *= factorial(n)
        for axis in axes:
            y = x ^ (1 << axis)
            degree = 2 * sum(axis in pair for pair in pairs)
            used_links = attached.keys() & {(x, axis), (y, axis)}
            if used_links:
                assert len(used_links) == 1
                used.update(used_links)
                divisor *= SCALE**2 * 4**degree
            else:
                terms[x, axis] = remap(unprobed_frame(axis, degree), (x, y))
                divisor *= 96**(degree // 2) * 8**degree
    assert used == attached.keys()
    # Stable integer keys keep the contraction tie-break homogeneous.
    factors = tuple(terms.values())
    raw = contract(dict(enumerate(factors)))
    assert raw == contract(dict(enumerate(factors[::-1])))
    assert raw.is_ground and not raw.const().y
    return Fraction(weight * int(raw.const().x), divisor), summed


def translated_inputs(faces, frames, shift):
    sites = tuple(x ^ shift for x in range(16))
    geometry = {(sites[x], k, l): {(sites[y], a) for y, a in edges}
                 for (x, k, l), edges in faces.items()}
    tables = {(sites[x], axis): tuple(remap(poly, sites) for poly in rows)
              for (x, axis), rows in frames.items()}
    return geometry, tables


def build_boundaries(faces, protected, free, frames, single_component):
    boundaries = []
    for face, edges in sorted(faces.items()):
        a, b = (axis for axis in range(4) if axis not in face[1:])
        components = L[a, b][:1] if single_component else L[a, b]
        links = tuple(sorted(set(edges) & protected))
        open_links = tuple(sorted(set(edges) & free))
        row = attached_face(face, links, open_links, frames, components)
        assert row == attached_face(face, links[::-1], open_links, frames, components)
        assert all(value.is_ground for poly in row.values() for value in poly.values())
        integer = {key: {mask: (int(value.const().x), int(value.const().y))
                         for mask, value in poly.items()} for key, poly in row.items()}
        boundaries.append((open_links, integer))
    return boundaries


def main(face_count, single_component):
    previous = None
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != face_count:
            continue
        free = {e for edges in faces.values() for e in edges} - protected
        frames = protected_frames(pattern, faces, protected)
        shift = min(x for x, _, _ in faces) if face_count == 4 else 0
        inputs = translated_inputs(faces, frames, shift) if face_count == 4 else None
        if face_count == 4 and previous is not None:
            expected_inputs, sizes, result = previous
            assert inputs == expected_inputs
        else:
            boundaries = build_boundaries(faces, protected, free, frames, single_component)
            sizes = [sum(map(len, row.values())) for _, row in boundaries]
            print("faces", face_count, "orbit", multiplicity, "input boundary entries",
                  sizes, flush=True)
            if face_count == 4:
                boundaries = translated_factors(boundaries, shift)
            result = close_shared(boundaries)
            assert result == close_shared(boundaries[::-1])
            if face_count == 4:
                previous = inputs, sizes, result
        print("faces", face_count, "orbit", multiplicity, "face boundary sizes",
              sizes, "joined exterior entries", len(result), flush=True)
        coefficient, _ = saturate_slice(pattern, faces, frames, result, len(free), shift)
        print("saturated fixed-label coefficient", coefficient, flush=True)
        coefficient, summed = saturate_slice(
            pattern, faces, frames, result, len(free), shift, sum_remote=True)
        print("remote gamma sum at", summed, "centers", coefficient, flush=True)



if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--faces", type=int, choices=(2, 4), default=2)
    parser.add_argument("--single-component", action="store_true",
                        help="replay the original one-component control")
    args = parser.parse_args()
    main(args.faces, args.single_component)
