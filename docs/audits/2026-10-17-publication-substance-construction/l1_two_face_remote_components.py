"""Opt-in exact component reuse for two-face remote boundary contractions."""
from functools import cache, lru_cache
from itertools import permutations

from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_mixed_center_census import EVEN, source_variants, summed_source_tensor
from l1_extended_mixed_frame_join import remote_center
from l1_extended_two_face_gamma_join import remote_environment
from l1_extended_two_mixed_centers import remap


PLANES = (((0, 1), (0, 1)), ((0, 1), (1, 2)))


def site_mask(sites):
    return sum(255 << (8 * site) for site in sites)


def components(pattern, coupled):
    opened = {x ^ (1 << a) for x in coupled for plane in pattern[EVEN.index(x)] for a in plane}
    pending = {}
    for x, (first, second) in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            assert set(first) & set(second)
            axes, _ = source_variants(first, second)
            pending[x] = (int(first != second), tuple(x ^ (1 << a) for a in axes))
    groups = []
    while pending:
        group = [pending.pop(min(pending))]
        touched = set(group[0][1])
        while neighbors := [x for x, (_, sites) in pending.items() if touched.intersection(sites)]:
            for x in neighbors:
                group.append(pending.pop(x))
                touched.update(group[-1][1])
        groups.append(group)
    return opened, groups


def canonical_component(group, opened):
    # At most five remote centers. Preserve each local slot order and
    # which shared passive sites are kept; center order is immaterial.
    best = None
    for order in permutations(group):
        sites = {}
        signature = tuple((kind, tuple((sites.setdefault(x, len(sites)), x in opened)
                                       for x in passive))
                          for kind, passive in order)
        if best is None or signature < best[0]:
            best = signature, tuple(sites)
    return best


def footprint(row):
    occupied = 0
    for mask in row:
        occupied |= mask
    return site_mask(site for site in range(16) if occupied & (255 << (8 * site)))


@cache
def local_rows(kind):
    normal, _ = remote_center(PLANES[kind])
    _, variants = source_variants(*PLANES[kind])
    replacements = [(summed_source_tensor(local), -2 * weight) for local, weight, _ in variants]
    # Local passive degrees are even, so relabeling whole site bytes
    # does not introduce exterior signs. Check every original variant.
    for row in (normal, *(row for row, _ in replacements)):
        assert not row or footprint(row) == footprint(normal)
        assert all(all(((mask >> shift) & 255).bit_count() % 2 == 0
                       for shift in range(0, 32, 8)) for mask in row)
    return normal, add(*(scale(row, weight) for row, weight in replacements))


def component_rows(signature):
    passive = {site: opened for _, sites in signature for site, opened in sites}
    keep = site_mask(site for site, opened in passive.items() if opened)
    ordinary, replacements = {}, {}
    for x, (kind, sites) in enumerate(signature, len(passive)):
        targets = (x, *(site for site, _ in sites))
        normal, source = local_rows(kind)
        ordinary[x], replacements[x] = remap(normal, targets), remap(source, targets)
    incident = {x: footprint(row) for x, row in ordinary.items()}

    @cache
    def remaining(todo):
        mask = 0
        for x in todo:
            mask |= incident[x]
        return mask

    todo = tuple(ordinary)
    normal, source = {0: R.one}, {}
    while todo:
        x = min(todo, key=lambda x: (-(remaining(todo) ^ remaining(
            tuple(y for y in todo if y != x))).bit_count(), x))
        todo = tuple(y for y in todo if y != x)
        closed = incident[x] & ~remaining(todo) & ~keep
        next_source = add(wedge(source, ordinary[x]), wedge(normal, replacements[x]))
        next_normal = wedge(normal, ordinary[x])
        source = {m ^ closed: v for m, v in next_source.items() if m & closed == closed}
        normal = {m ^ closed: v for m, v in next_normal.items() if m & closed == closed}
    return normal, source


class ComponentRemotes:
    """Reuse up to 32 canonical components and one completed orbit pair per run."""

    def __init__(self):
        self.component_rows = lru_cache(maxsize=32)(component_rows)
        self.previous = None

    def maps(self, pattern, coupled):
        key = pattern, frozenset(coupled)
        if self.previous is not None and self.previous[0] == key:
            return self.previous[1]
        self.previous = None
        opened, groups = components(pattern, coupled)
        if len(groups) == 1:
            keep, normal = remote_environment(pattern, coupled)
            source_keep, source = remote_environment(pattern, coupled, source=True)
            assert keep == source_keep
        else:
            keep = site_mask(opened)
            normal, source = {0: R.one}, {}
            for group in groups:
                signature, sites = canonical_component(group, opened)
                ordinary, replacement = (remap(row, sites) for row in self.component_rows(signature))
                source = add(wedge(source, ordinary), wedge(normal, replacement))
                normal = wedge(normal, ordinary)
        result = keep, normal, source
        self.previous = key, result
        return result

    def environment(self, pattern, coupled, *, source=False, only_face=None):
        assert only_face is None
        keep, normal, replacement = self.maps(pattern, coupled)
        return keep, replacement if source else normal
