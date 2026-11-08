from collections import Counter
from functools import cache
from itertools import permutations, product

from sympy import I, ImmutableMatrix, diag, eye, simplify, sqrt, symbols, zeros

LENGTH = 5
ORIGIN = (0, 0, 0, 0)
DIRECTIONS = range(4)
GAUGE_SITE = (1, 0, 0, 0)
SITES = tuple(product(range(LENGTH), repeat=4))
ORDERS = tuple(permutations(DIRECTIONS))
g1, g2 = symbols("g1 g2")
identity = ImmutableMatrix(eye(4))
pauli = [ImmutableMatrix([[0, 1], [1, 0]]),
         ImmutableMatrix([[0, -I], [I, 0]]), ImmutableMatrix(diag(1, -1))]
gamma = [ImmutableMatrix(zeros(2).row_join(-I * p).col_join((I * p).row_join(zeros(2))))
         for p in pauli]
gamma.append(ImmutableMatrix(zeros(2).row_join(eye(2)).col_join(eye(2).row_join(zeros(2)))))
gamma5 = ImmutableMatrix(diag(1, 1, -1, -1))
y_link = ImmutableMatrix(diag(I * pauli[0], eye(2)))
t = symbols("t", real=True)
phase = (1 + I*t)/(1 - I*t)
rotation = ImmutableMatrix(diag(phase, 1/phase, 1, 1))


def step(site, mu, n=1):
    return tuple((v + n) % LENGTH if j == mu else v for j, v in enumerate(site))


local = ((ORIGIN, 2), (ORIGIN, 3), (step(ORIGIN, 2), 4), (step(ORIGIN, 3), 4))
canonical = tuple(sorted(local))


def inversion_sign(values):
    return (-1) ** sum(a > b for j, a in enumerate(values) for b in values[j + 1:])


def extract_bits(left, right):
    indices = tuple(canonical.index(v) for v in (*left, *right))
    if len(set(indices)) != 4:
        return 0
    mask = 0
    sign = 1
    for index in indices:
        sign *= (-1) ** ((mask >> (index + 1)).bit_count())
        mask |= 1 << index
    return sign


def extract_reverse(left, right):
    # Independently remove target generators in reverse canonical order.
    word = list((*left, *right))
    sign = 1
    for generator in reversed(canonical):
        if generator not in word:
            return 0
        at = word.index(generator)
        sign *= (-1) ** (len(word) - at - 1)
        del word[at]
    return sign


@cache
def gauge(site, transformed):
    return rotation if transformed and site == GAUGE_SITE else identity


@cache
def link(site, mu, transformed, omit_endpoint=False):
    bare = y_link if (site, mu) == (step(ORIGIN, 0), 1) else identity
    end = (identity if omit_endpoint and (site, mu) == (ORIGIN, 0)
           else gauge(step(site, mu), transformed))
    return ImmutableMatrix((end * bare * gauge(site, transformed).H).applyfunc(simplify))


@cache
def frame(site, mu, transformed, omit_endpoint):
    forward, backward = step(site, mu), step(site, mu, -1)
    blocks = ((site, forward, 0, 1), (forward, site, 1, -1),
              (site, backward, 2, -1), (backward, site, 3, 1))
    out = {}
    for bars, psi, j, sign in blocks:
        # The target quotient is applied to each original block after recording it.
        for a in canonical[:2]:
            if a[0] != bars:
                continue
            for b in canonical[2:]:
                if b[0] != psi:
                    continue
                f = link(site, mu, transformed, omit_endpoint)
                back = link(backward, mu, transformed, omit_endpoint)
                values = []
                for gamma_a in gamma:
                    matrices = (gamma_a * f.H, f * gamma_a, gamma_a * back, back.H * gamma_a)
                    mat = gauge(bars, transformed).H * matrices[j] * gauge(psi, transformed)
                    values.append(simplify(sign * mat[a[1], b[1] - 4] / 4))
                out[(a, b)] = out.get((a, b), zeros(4)) + sum(
                    (c * mat for c, mat in zip(values, gamma)), zeros(4))
    return {word: mat for word, mat in out.items() if mat != zeros(4)}


def coefficient(ordering, transformed, extract, poison=None):
    stats = Counter()
    total = 0
    for x in SITES:
        stats["bases"] += 1
        # S4 is a sum of four degree-two T factors. The target extractor is homogeneous degree four.
        stats["g1_degree8_excluded"] += 1
        for k, l, mu, nu in ORDERS:
            stats["world_tuples"] += 1
            left = frame(x, mu, transformed, poison == "omit_endpoint")
            right = frame(x, nu, transformed, poison == "omit_endpoint")
            terms = [(a, b, extract(wa, wb)) for wa, a in left.items() for wb, b in right.items()]
            if not any(sign for _, _, sign in terms):
                continue
            stats["surviving_world_tuples"] += 1
            factors = [link(x, k, transformed, poison == "omit_endpoint"),
                       link(step(x, k), l, transformed, poison == "omit_endpoint"),
                       link(step(x, l), k, transformed, poison == "omit_endpoint").H,
                       link(x, l, transformed, poison == "omit_endpoint").H]
            if ordering == "closed":
                factors.reverse()
            plaquette = identity
            for factor in factors:
                plaquette *= factor
            for a, b, sign in terms:
                if sign:
                    divisor = 1 if poison == "drop_action_quarter" else 4
                    chirality = -gamma5 if poison == "flip_gamma5" else gamma5
                    total += (sign * inversion_sign((k, l, mu, nu))
                              * (plaquette * a * b * chirality).trace() / divisor)
                    stats["nonzero_wedges"] += 1
    assert len(SITES) * len(DIRECTIONS) == 2500
    assert stats["bases"] == stats["g1_degree8_excluded"] == 625
    assert stats["world_tuples"] == 15000
    return simplify(g1 * 0 + g2 * total), stats


def main():
    orientation = inversion_sign(tuple(canonical.index(v) for v in local))
    for ordering in ("literal", "closed"):
        val, stats = coefficient(ordering, True, extract_bits)
        val2, stats2 = coefficient(ordering, True, extract_reverse)
        assert simplify(val-val2) == 0 and stats == stats2
        derivative = simplify(orientation * val.diff(t).subs(t, 0))
        source = (gamma[2])[2, 0] / 4
        remote_site = (3, 3, 3, 3)
        remote_word = ((remote_site, 2), (step(remote_site, 0), 4))
        target = (*local, *remote_word)
        target_orientation = inversion_sign(target)
        sourced = simplify(target_orientation * source * derivative)
        print(ordering, "local coefficient", simplify(orientation*val),
              "local derivative", derivative, "remote T coefficient", source,
              "global six-word orientation", target_orientation, "global sourced coefficient", sourced)
        if ordering == "literal":
            assert sourced == -I*g2/2
        else:
            assert sourced == 0


if __name__ == "__main__":
    main()
