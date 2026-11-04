"""Attach protected frame tensors on fixed gamma slices of the curvature cores."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from itertools import product
from math import prod

from l1_direct_b_haar import add, scale, wedge
from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, swap_patterns
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import frame_edge
from l1_extended_overlap_strip import HAAR
from l1_extended_two_mixed_centers import remap
from l1_normalization_opposed_fourth import L
from l1_reduced_wedge_reference import wedge_sign


def attached_face(face, protected, free, frames, labels):
    raw = face_tensor(face, (*protected, *free), {}, labels)

    @cache
    def combined(left, middle):
        return wedge(frames[protected[0]][left], frames[protected[1]][middle])

    out = defaultdict(dict)
    for (a, b, *tail), weight in raw.items():
        term = combined(a, b)
        if len(protected) == 3:
            c, *tail = tail
            term = wedge(term, frames[protected[2]][c])
        if term:
            live = tuple(tail)
            out[live] = add(out[live], scale(term, weight))
    return {i: poly for i, poly in out.items() if poly}


def wedge_accumulate(out, left, right, weight):
    first, second = next(iter(left)), next(iter(right))
    full = sum(255 << shift for shift in range(0, 128, 8)
               if ((first >> shift) & 255).bit_count()
               + ((second >> shift) & 255).bit_count() == 8)
    index = defaultdict(list)
    for mask, coefficient in right.items():
        index[mask & full].append((mask, coefficient))
    for a, (r, i) in left.items():
        for b, (s, j) in index[full ^ (a & full)]:
            if not a & b:
                signed = weight * wedge_sign(a, b)
                old_r, old_i = out.get(a | b, (0, 0))
                out[a | b] = old_r + signed*(r*s - i*j), old_i + signed*(r*j + i*s)


def join_factors(first, second):
    axes, left = first
    other, right = second
    common = tuple(e for e in axes if e in other)
    ai, bi = (tuple(axis.index(e) for e in common) for axis in (axes, other))
    la, ra = (tuple(i for i, e in enumerate(axis) if e not in common)
              for axis in (axes, other))
    output = defaultdict(dict)
    lookup = defaultdict(list)
    for q, poly in right.items():
        lookup[tuple(q[i] for i in bi)].append((q, poly))
    for p, poly in left.items():
        for moments in product(*(HAAR[PAIRS[p[i]]] for i in ai)):
            indices, weights = zip(*moments, strict=True)
            for q, value in lookup[indices]:
                dest = tuple(p[i] for i in la) + tuple(q[i] for i in ra)
                wedge_accumulate(output[dest], poly, value, prod(weights))
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


def main(face_count):
    previous = None
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != face_count:
            continue
        free = {e for edges in faces.values() for e in edges} - protected
        frames = protected_frames(pattern, faces, protected)
        boundaries = []
        for face, edges in sorted(faces.items()):
            a, b = (axis for axis in range(4) if axis not in face[1:])
            label, _ = L[a, b][0]
            links = tuple(sorted(set(edges) & protected))
            open_links = tuple(sorted(set(edges) & free))
            row = attached_face(face, links, open_links, frames, (label, label))
            assert row == attached_face(face, links[::-1], open_links, frames, (label, label))
            assert all(value.is_ground for poly in row.values() for value in poly.values())
            integer = {key: {mask: (int(value.const().x), int(value.const().y))
                             for mask, value in poly.items()} for key, poly in row.items()}
            boundaries.append((open_links, integer))
        print("faces", len(faces), "orbit", multiplicity, "input boundary entries",
              [sum(map(len, row.values())) for _, row in boundaries], flush=True)
        if face_count == 4:
            # These cores differ only by translations, checked on the
            # complete attached input before reusing the first closure.
            shift = min(x for x, _, _ in faces)
            normalized = translated_factors(boundaries, shift)
            if previous is None:
                result = close_shared(normalized)
                assert result == close_shared(normalized[::-1])
                previous = normalized, result
            else:
                assert normalized == previous[0]
                result = previous[1]
        else:
            result = close_shared(boundaries)
            assert result == close_shared(boundaries[::-1])
        print("faces", len(faces), "orbit", multiplicity, "face boundary sizes",
              [sum(map(len, row.values())) for _, row in boundaries],
              "joined exterior entries", len(result), flush=True)



if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--faces", type=int, choices=(2, 4), default=2)
    main(parser.parse_args().faces)
