from collections import Counter
from fractions import Fraction
from math import factorial, prod

from l1_interacting_support import AXES, forward, same_site_quadratic_support


def links(label):
    site, k, l, left_site, right_site = label
    left_dir, right_dir = (axis for axis in AXES if axis not in (k, l))
    return ((site, k), (forward(site, k), l), (forward(site, l), k),
            (site, l), (left_site, left_dir), (right_site, right_dir))


population = Counter()
local = []
for word in same_site_quadratic_support():
    incidence = Counter(link for label in word for link in links(label))
    degrees = incidence[0, 2], incidence[0, 3]
    population[degrees] += 1
    if degrees == (0, 0):
        local.append(word)
assert population == {(0, 0): 1, (0, 2): 20, (2, 0): 20,
                      (0, 4): 26, (4, 0): 26, (2, 2): 92}
assert local == [tuple((site, 0, 1, site, site)
                      for site in (1, 2, 3) for _ in range(2))]

faces = [links((site, 0, 1, site, site))[:4] for site in (1, 2, 3)]
for subset in range(1, 8):
    counts = Counter(link for i, face in enumerate(faces)
                     if subset & (1 << i) for link in face)
    assert 1 in counts.values(), subset

source_moment = 21  # Prior exact local D² Berezin/Haar reference.
curvature_square = 24  # Prior exact local action-square Berezin reference.
trivial_part = Fraction(3, 2)
exponential_weight = Fraction(1, prod(factorial(n) for n in Counter(local[0]).values()))
value = source_moment * curvature_square**3 * trivial_part**3 * exponential_weight
assert value == 122472
print("source-link incidence:", sorted(population.items()))
print("unique no-touch word:", local[0])
print("all seven nonempty adjoint subsets have an exposed edge")
print("exact factorial-weighted contribution:", value)
