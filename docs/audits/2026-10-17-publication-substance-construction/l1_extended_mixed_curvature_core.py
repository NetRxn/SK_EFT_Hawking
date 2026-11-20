"""Conditional Haar contraction of the two- and four-face mixed cores."""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod

from l1_direct_a_haar import adj, mul
from l1_extended_mixed_center_census import curvature_boundary, orbits, swap_patterns
from l1_extended_overlap_strip import HAAR, PAIRS
from l1_normalization_opposed_fourth import nodes
from l1_normalization_uniform_mixed_edge import unit

PAIR_INDEX = {pair: i for i, pair in enumerate(PAIRS)}


def face_vector(face, coordinates, chirality, component):
    x, k, l = face
    a, b, c, d = (coordinates[e][chirality] for e in
                  ((x, k), (x ^ (1 << k), l), (x ^ (1 << l), k), (x, l)))
    return mul(mul(adj(d), adj(c)), mul(b, a))[1 + component]


def face_tensor(face, free, fixed, labels):
    entries = []
    for label in labels:
        chirality, component = divmod(label, 3)
        row = {}
        for js in product(range(4), repeat=len(free)):
            coordinates = dict(fixed)
            for edge, j in zip(free, js, strict=True):
                coordinates[edge] = (unit(j), unit(j))
            value = face_vector(face, coordinates, chirality, component)
            if value:
                row[tuple(4 * chirality + j for j in js)] = value
        entries.append(row)
    out = Counter()
    for a, u in entries[0].items():
        for b, v in entries[1].items():
            key = tuple(PAIR_INDEX[tuple(sorted(pair))] for pair in zip(a, b, strict=True))
            out[key] += u * v
    return {k: v for k, v in out.items() if v}


def integrate(factors, free):
    pending = set(free)
    while pending:
        edge = min(pending)
        (axes, a), (other, b) = [f for f in factors if edge in f[0]]
        factors = [f for f in factors if edge not in f[0]]
        shared = tuple(e for e in axes if e in other)
        pending.difference_update(shared)
        ai = tuple(axes.index(e) for e in shared)
        bi = tuple(other.index(e) for e in shared)
        left = tuple(i for i, e in enumerate(axes) if e not in shared)
        right = tuple(i for i, e in enumerate(other) if e not in shared)
        result = Counter()
        by_index = {}
        for key, value in b.items():
            by_index.setdefault(tuple(key[i] for i in bi), []).append((key, value))
        for key, value in a.items():
            for moments in product(*(HAAR[PAIRS[key[i]]] for i in ai)):
                indices, weights = zip(*moments, strict=True)
                for q, v in by_index.get(indices, ()):
                    merged = tuple(key[i] for i in left) + tuple(q[i] for i in right)
                    result[merged] += value * v * prod(weights)
        output_axes = tuple(axes[i] for i in left) + tuple(other[i] for i in right)
        factors.append((output_axes, {k: v for k, v in result.items() if v}))
    assert len(factors) == 1 and not factors[0][0]
    return Fraction(factors[0][1].get((), 0), 48**len(free))


def conditional(faces, protected, fixed, labels):
    free = sorted({e for edges in faces.values() for e in edges} - protected)
    factors = []
    for face, edges in faces.items():
        local = tuple(e for e in free if e in edges)
        factors.append((local, face_tensor(face, local, fixed, labels[face])))
    return integrate(factors, free)


def two_face_cubature(faces, protected, fixed, labels):
    edge, = {e for edges in faces.values() for e in edges} - protected
    total = 0
    for a, b, weight in nodes():
        coordinates = dict(fixed)
        coordinates[edge] = a, b
        for face in faces:
            for label in labels[face]:
                weight *= face_vector(face, coordinates, *divmod(label, 3))
        total += weight
    return Fraction(total, 96 * 2**4)


def cycle_cubature(faces, protected, fixed, labels):
    free = {e for edges in faces.values() for e in edges} - protected
    unseen = dict(faces)
    incoming = min(free)
    rules = tuple(nodes())
    matrices = []
    while unseen:
        face = next(f for f, edges in unseen.items() if incoming in edges)
        outgoing, = (set(unseen.pop(face)) & free) - {incoming}
        matrix = []
        for a, b, weight in rules:
            row = {}
            for j, (c, d, _) in enumerate(rules):
                coordinates = dict(fixed)
                coordinates[incoming], coordinates[outgoing] = (a, b), (c, d)
                value = weight * prod(face_vector(face, coordinates, *divmod(label, 3))
                                      for label in labels[face])
                if value:
                    row[j] = value
            matrix.append(row)
        matrices.append(matrix)
        incoming = outgoing
    assert incoming == min(free)
    total = 0
    for i in range(len(rules)):
        values = {i: 1}
        for matrix in matrices:
            next_values = Counter()
            for j, coefficient in values.items():
                for k, value in matrix[j].items():
                    next_values[k] += coefficient * value
            values = next_values
        total += values[i]
    return Fraction(total, (96 * 2**4)**len(free))


def main():
    count = Counter()
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if not faces:
            continue
        protected = {e for edges in faces.values() for e in edges} & protected
        free_degree = Counter(e for edges in faces.values() for e in edges if e not in protected)
        assert set(free_degree.values()) == {2}
        assert len(free_degree) == (1 if len(faces) == 2 else 4)
        count[len(faces)] += 1
        fixed = {e: (unit((e[0] + e[1]) % 4), unit((e[0] - e[1]) % 4)) for e in protected}
        for pair in ((0, 0), (0, 3), (2, 5)):
            labels = dict.fromkeys(faces, pair)
            value = conditional(faces, protected, fixed, labels)
            cubature = two_face_cubature if len(faces) == 2 else cycle_cubature
            assert value == cubature(faces, protected, fixed, labels)
            print("faces", len(faces), "orbit", multiplicity, "labels", pair,
                  "conditional slice", value)
    assert count == {2: 3, 4: 3}


if __name__ == "__main__":
    main()
