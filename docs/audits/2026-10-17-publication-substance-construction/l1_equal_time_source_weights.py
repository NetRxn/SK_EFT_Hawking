"""Local exact D^2 tensor after one source link is Haar integrated."""
from fractions import Fraction as F
from itertools import combinations_with_replacement

from l1_direct_b_haar import haar_moment, wedge
from l1_transverse_top import G, T, trace, g4


def coeff(poly, powers):
    total = F(0)
    for exp, c in poly.items():
        assert c.y == 0
        full = tuple(a + b for a, b in zip(exp, powers, strict=True))
        total += F(int(c.x), 256) * haar_moment(full[:4]) * haar_moment(full[4:])
    return total


square = wedge(G, G)[T]
cross = wedge(G, trace)[T]
zero = (0,) * 8


def weighted(powers):
    return (coeff(square, powers) - 2 * coeff(cross, powers)
            + g4 * haar_moment(powers[:4]) * haar_moment(powers[4:]))


assert weighted(zero) == 21
second = {}
fourth = {}
for k, out in ((2, second), (4, fourth)):
    for indices in combinations_with_replacement(range(8), k):
        powers = tuple(indices.count(i) for i in range(8))
        out[indices] = weighted(powers)
    print(k, 'nonzero:', sum(v != 0 for v in out.values()), '/', len(out))
print('second diagonal', [second[i, i] for i in range(8)])
assert all(second[i, j] == 0 for i, j in second if i != j)
assert sum(second[i,i] for i in range(4)) == 21
assert sum(second[i,i] for i in range(4,8)) == 21
for (i,j), v in second.items():
    assert sum(fourth[tuple(sorted((i,j,k,k)))] for k in range(4)) == v
    assert sum(fourth[tuple(sorted((i,j,k,k)))] for k in range(4,8)) == v
print('separate chiral sphere contractions PASS')
