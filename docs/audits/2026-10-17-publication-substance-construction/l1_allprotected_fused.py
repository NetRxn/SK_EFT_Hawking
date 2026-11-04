"""Opt-in component replay for the all-protected two-face family."""
from argparse import ArgumentParser
from fractions import Fraction
from functools import cache
from itertools import product

from l1_direct_b_haar import add, scale
from l1_extended_four_face_gauge_join import mixed_rows
from l1_extended_mixed_center_census import (
    EVEN, curvature_boundary, orbits, words_with_mixed_count,
)
from l1_extended_mixed_frame_join import remote_center
from l1_extended_two_face_gamma_join import remote_source_replacements
from l1_extended_two_face_tree import coefficient, disjoint_base, upper_links
from l1_extended_two_mixed_centers import contract_boundary, remap
from l1_reduced_wedge_reference import wedge_sign

ZERO = (0, 0)
UNIT = (1, 0)
CONTROLS = {
    0: (
        Fraction(1460729721830618365576171875, 590295810358705651712),
        Fraction(-36888186278621288225390625, 4611686018427387904),
        Fraction(-1039919139505603564453125, 288230376151711744),
    ),
    2: (
        Fraction(528111682107330805576171875, 590295810358705651712),
        Fraction(-13303693999582087250390625, 4611686018427387904),
        Fraction(-374240228781168017578125, 288230376151711744),
    ),
    8: (
        Fraction(330053836700073321826171875, 1180591620717411303424),
        Fraction(-8234693198583117711328125, 9223372036854775808),
        Fraction(-233919342720723779296875, 576460752303423488),
    ),
}


def site_mask(sites):
    return sum(255 << (8 * site) for site in sites)


def byte(mask, site):
    return (mask >> (8 * site)) & 255


def footprint(row):
    return site_mask(site for site in range(16) if any(byte(mask, site) for mask in row))


def component_layout(incidence, open_sites):
    pending = set(incidence)
    groups = {}
    while pending:
        first = min(pending)
        group = {first}
        touched = set(incidence[first])
        while neighbors := {x for x in pending - group if incidence[x] & touched}:
            group.update(neighbors)
            touched.update(*(incidence[x] for x in neighbors))
        pending.difference_update(group)
        groups[tuple(sorted(group))] = site_mask(touched & open_sites)
    return groups


def geometry(pattern, faces, protected):
    base, = {face[0] for face in faces}
    p, q = pattern[EVEN.index(base)]
    if set(p) & set(q):
        return None
    uppers = []
    for face in ((base, *q), (base, *p)):
        center, edges = upper_links(face, faces[face], protected)
        a, b = pattern[EVEN.index(center)]
        if a == b:
            return None
        first, last = sorted(set(a) ^ set(b))
        common, = set(a) & set(b)
        axes = first, common, last
        if tuple(axes.index(axis) for _, axis in edges) != (0, 2):
            return None
        uppers.append((center, tuple(center ^ (1 << axis) for axis in axes)))
    coupled = {base, *(center for center, _ in uppers)}
    open_sites = set().union(*(set(sites) for _, sites in uppers))
    exclusive_sites = {site for _, sites in uppers for site in (sites[0], sites[2])}
    if len(open_sites) != 6 or {base ^ (1 << axis) for axis in p + q} != exclusive_sites:
        return None
    remote = {x: pairs for x, pairs in zip(EVEN, pattern, strict=True) if x not in coupled}
    if not all(a == b for a, b in remote.values()):
        return None
    incidence = {x: {x, *(x ^ (1 << axis) for axis in a)} for x, (a, _) in remote.items()}
    groups = component_layout(incidence, open_sites)
    active = [mask for mask in groups.values() if mask]
    if len(active) != 3 or len(set(active)) != 3:
        return None
    upper_sites = tuple(sites for _, sites in uppers)
    if all(sum(bool(byte(mask, site)) for site in sites) == 1
           for mask in active for sites in upper_sites):
        return coupled, open_sites, remote, incidence, groups, upper_sites, True
    roles = []
    for _, (a, c, b) in uppers:
        choices = [(q, c, w) for q, w in ((a, b), (b, a)) if site_mask((q, c)) in active]
        if len(choices) != 1:
            return None
        roles.append(choices[0])
    if set(active) != {*(site_mask(role[:2]) for role in roles), site_mask(role[2] for role in roles)}:
        return None
    return coupled, open_sites, remote, incidence, groups, tuple(roles), False


def gaussian(row):
    out = {}
    for mask, value in row.items():
        assert value.is_ground
        z = value.const()
        out[mask] = int(z.x), int(z.y)
    return out


def plus(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def signed(pair, sign):
    return sign * pair[0], sign * pair[1]


def dual_mul(a, b):
    n, s = a
    m, t = b
    return mul(n, m), plus(mul(n, t), mul(s, m))


@cache
def local_sign(a, t, b):
    return wedge_sign(a, t) * wedge_sign(a | t, b)


def remote_components(pattern, geometry):
    coupled, open_sites, remote, incidence, groups, _, _ = geometry
    keep = site_mask(open_sites)
    terms = {}
    for x, pairs in remote.items():
        local, axes = remote_center(pairs)
        terms[x] = remap(local, (x, *(x ^ (1 << axis) for axis in axes)))
        assert footprint(terms[x]) == site_mask(incidence[x])
    components = []
    for group, mask in groups.items():
        factors = {x: terms[x] for x in group}
        normal = contract_boundary(factors, keep)
        variants = []
        for replaced, weight in remote_source_replacements(pattern, factors, coupled):
            assert all(not row or footprint(row) == footprint(factors[x])
                       for x, row in replaced.items())
            variants.append(scale(contract_boundary(replaced, keep), weight))
        source = add(*variants)
        for row in (normal, source):
            assert all(not m & ~mask and all(byte(m, x).bit_count() == 4
                       for x in open_sites if byte(mask, x)) for m in row)
        components.append((mask, gaussian(normal), gaussian(source)))
    return components


class FusedJoin:
    def configure(self, pattern, layout):
        self.pattern = pattern
        self.coupled, self.open_sites, _, _, _, self.roles, _ = layout
        self.keep = site_mask(self.open_sites)
        self.scalar = UNIT, ZERO
        active = {}
        for mask, normal, source in remote_components(pattern, layout):
            if mask:
                active[mask] = normal, source
            else:
                assert set(normal) <= {0} and set(source) <= {0}
                self.scalar = dual_mul(self.scalar, (normal.get(0, ZERO), source.get(0, ZERO)))
        assert sum(active) == self.keep
        self.transforms = {}
        self.contractions = {}
        return active

    def __init__(self, pattern, layout):
        active = self.configure(pattern, layout)
        self.own = [active[site_mask(role[:2])] for role in self.roles]
        normal, source = active[site_mask(role[2] for role in self.roles)]
        self.cross = [(m, (normal.get(m, ZERO), source.get(m, ZERO)))
                      for m in sorted(normal.keys() | source.keys())]

    def environment(self, pattern, coupled, *, source=False, only_face=None):
        assert pattern == self.pattern and coupled == self.coupled and only_face is None
        return self.keep, source

    def transform(self, side, upper):
        key = side, id(upper)
        if key in self.transforms:
            retained, rows = self.transforms[key]
            assert retained is upper
            return rows
        own, common, crossing = self.roles[side]
        normal, source = self.own[side]
        by_common = {}
        for m in normal.keys() | source.keys():
            by_common.setdefault(byte(m, common), []).append(
                (byte(m, own), (normal.get(m, ZERO), source.get(m, ZERO)))
            )
        partial = []
        for m, coef in gaussian(upper).items():
            assert not m & ~site_mask(self.roles[side])
            u, v, w = (byte(m, site) for site in self.roles[side])
            assert (u.bit_count(), v.bit_count(), w.bit_count()) == (2, 4, 2)
            for b, weight in by_common.get(255 ^ v, ()):
                if u & b:
                    continue
                a = 255 ^ u ^ b
                sign = local_sign(a, u, b) * local_sign(0, v, 255 ^ v)
                partial.append((a << (8 * own), w, tuple(signed(mul(coef, t), sign) for t in weight)))
        rows = []
        for m, _ in self.cross:
            b = byte(m, crossing)
            row = {}
            for own_mask, w, weight in partial:
                if w & b:
                    continue
                a = 255 ^ w ^ b
                mask = own_mask | (a << (8 * crossing))
                old = row.get(mask, (ZERO, ZERO))
                sign = local_sign(a, w, b)
                row[mask] = tuple(plus(x, signed(y, sign)) for x, y in zip(old, weight, strict=True))
            rows.append({m: v for m, v in row.items() if v != (ZERO, ZERO)})
        self.transforms[key] = upper, rows
        return rows

    def contract(self, key, left, right, base):
        index = key, id(left), id(right)
        if index not in self.contractions:
            total = ZERO, ZERO
            left_rows = self.transform(0, left)
            right_rows = self.transform(1, right)
            for a, b, (_, cross) in zip(left_rows, right_rows, self.cross, strict=True):
                for u, first in a.items():
                    for v, last in b.items():
                        weight = base.get(u | v)
                        if weight is not None:
                            n, s = dual_mul(dual_mul(first, last), cross)
                            total = plus(total[0], mul(weight, n)), plus(total[1], mul(weight, s))
            self.contractions[index] = dual_mul(total, self.scalar)
        return self.contractions[index]

    def close(self, base, base_sites, keep, source, upper_sites, terms):
        assert keep == self.keep and upper_sites == self.open_sites
        totals = [ZERO for _ in terms]
        channels = set().union(*(set(product(left, right)) for left, right in terms))
        for key in sorted(channels):
            x, y = key
            row = None
            for j, (left, right) in enumerate(terms):
                if x in left and y in right:
                    l, r = left[x], right[y]
                    if (key, id(l), id(r)) not in self.contractions and row is None:
                        row = mixed_rows(base, base_sites, (key,))[key]
                    totals[j] = plus(totals[j], self.contract(key, l, r, row)[source])
        assert all(im == 0 for _, im in totals)
        return tuple(re for re, _ in totals)


class AllCrossJoin(FusedJoin):
    """Project the three disjoint remote pairs between opposite uppers."""

    def __init__(self, pattern, layout):
        self.cross = []
        for mask, (normal, source) in self.configure(pattern, layout).items():
            i, = (i for i, site in enumerate(self.roles[0]) if byte(mask, site))
            j, = (j for j, site in enumerate(self.roles[1]) if byte(mask, site))
            u, v = self.roles[0][i], self.roles[1][j]
            rows = [(byte(m, u), byte(m, v), (normal.get(m, ZERO), source.get(m, ZERO)))
                    for m in normal.keys() | source.keys()]
            self.cross.append((i, j, u, v, rows))
        # Common sites require an exact complement, so test those pairs first.
        self.cross.sort(key=lambda row: -((row[0] == 1) + (row[1] == 1)))
        self.options = cache(self.options)

    def options(self, index, left, right):
        i, j, u, v, rows = self.cross[index]
        result = []
        for a, b, weight in rows:
            if a & left or b & right:
                continue
            A, B = 255 ^ left ^ a, 255 ^ right ^ b
            if (i == 1 and A) or (j == 1 and B):
                continue
            sign = local_sign(A, left, a) * local_sign(B, right, b)
            result.append(((A << (8 * u)) | (B << (8 * v)),
                           tuple(signed(w, sign) for w in weight)))
        return result

    def transform(self, side, upper):
        key = side, id(upper)
        if key not in self.transforms:
            sites = self.roles[side]
            footprint = site_mask(sites)
            prepared = []
            for mask, coef in gaussian(upper).items():
                assert not mask & ~footprint
                parts = tuple(byte(mask, site) for site in sites)
                assert tuple(part.bit_count() for part in parts) == (2, 4, 2)
                prepared.append((parts, coef))
            self.transforms[key] = upper, prepared
        stored, prepared = self.transforms[key]
        assert stored is upper
        return prepared

    def contract(self, key, left, right, base):
        index = key, id(left), id(right)
        if index not in self.contractions:
            normal = source = ZERO
            for l, u in self.transform(0, left):
                for r, v in self.transform(1, right):
                    choices = []
                    for k, (i, j, *_) in enumerate(self.cross):
                        rows = self.options(k, l[i], r[j])
                        if not rows:
                            break
                        choices.append(rows)
                    if len(choices) != 3:
                        continue
                    for (a, first), (b, second), (c, third) in product(*choices):
                        weight = base.get(a | b | c)
                        if weight is not None:
                            n, s = dual_mul(dual_mul(first, second), third)
                            coef = mul(mul(u, v), weight)
                            normal, source = plus(normal, mul(coef, n)), plus(source, mul(coef, s))
            self.contractions[index] = dual_mul((normal, source), self.scalar)
        return self.contractions[index]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--orbit", type=int, action="append", required=True)
    args = parser.parse_args()
    seen = 0
    selected = set(args.orbit)
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2 or set.union(*faces.values()) - protected:
            continue
        index = seen
        seen += 1
        if index not in selected:
            continue
        layout = geometry(pattern, faces, protected)
        if layout is None:
            parser.error(f"orbit {index} requires the existing tree contraction")
        fused = (AllCrossJoin if layout[-1] else FusedJoin)(pattern, layout)
        normal, remote, upper = coefficient(
            pattern, faces, protected, disjoint_base, source=True, probe_classes=True,
            environment=fused.environment, close=fused.close,
        )
        result = normal, remote, upper
        if index in CONTROLS:
            assert result == CONTROLS[index], (index, result)
        print(index, multiplicity, *result, flush=True)
        selected.remove(index)
    assert seen == 23
    if selected:
        parser.error(f"unknown orbit indices {sorted(selected)}")


if __name__ == "__main__":
    main()
