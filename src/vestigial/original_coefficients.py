"""Exact sparse original-coframe/Dirac foundation on the declared finite torus.

Task1 supplies construction and structural certificates, not an integrated partition
function. Quaternion coordinates, sources and anchored links retain their identities.
No Haar/W evaluation or scientific work occurs at import time. Physics definitions
are imported lazily from core.formulas; generic sparse algebra lives here.
"""
from dataclasses import dataclass, field, fields, is_dataclass, replace
from contextvars import ContextVar
from fractions import Fraction
from itertools import product
from math import prod
from functools import lru_cache
import sys


_ACTIVE_COST = ContextVar('original_coefficient_scalar_cost', default=None)


def _check_integer(value):
    cost = _ACTIVE_COST.get()
    bits = abs(value).bit_length()
    if cost is not None and hasattr(cost, 'integer_bit_limit'):
        cost.peak_integer_bits = max(cost.peak_integer_bits, bits)
        if bits > cost.integer_bit_limit:
            raise BudgetExceeded('integer height exceeded: incomplete coefficient control')
    return value


def checked_integer_product(a, b):
    _check_integer(a); _check_integer(b)
    cost = _ACTIVE_COST.get()
    if cost is not None:
        cost.integer_products += 1
    return _check_integer(a * b)


def checked_integer_power(a,n):
    if type(n)is not int or n<0:raise ValueError('nonnegative integer exponent required')
    out=1;_check_integer(a)
    while n:
        if n&1:out=checked_integer_product(out,a)
        n//=2
        if n:a=checked_integer_product(a,a)
    return out


def checked_factorial(n):
    if type(n)is not int or n<0:raise ValueError('nonnegative factorial input required')
    out=1
    for i in range(1,n+1):out=checked_integer_product(out,i)
    return out


def rational_add(a, b):
    a, b = _rational(a), _rational(b)
    if not a:return b
    if not b:return a
    numerator = _check_integer(checked_integer_product(a.numerator,b.denominator) + checked_integer_product(b.numerator,a.denominator))
    return _rational(Fraction(numerator,checked_integer_product(a.denominator,b.denominator)))


def rational_product(a, b, *, bill=True):
    a, b = _rational(a), _rational(b)
    if bill and _ACTIVE_COST.get() is not None:
        _ACTIVE_COST.get().consume()
    if not a or not b:return Fraction()
    return _rational(Fraction(checked_integer_product(a.numerator,b.numerator),checked_integer_product(a.denominator,b.denominator)))


def rational_inverse(a):
    a = _rational(a)
    if not a: raise ValueError('nonzero rational required')
    return _rational(Fraction(a.denominator,a.numerator))


def rational_power(a, n):
    if type(n) is not int or n < 0: raise ValueError('nonnegative exact exponent required')
    out=Fraction(1); a=_rational(a)
    while n:
        if n&1: out=rational_product(out,a)
        n//=2
        if n: a=rational_product(a,a)
    return out


def rational_product_all(values):
    out=Fraction(1)
    for value in values: out=rational_product(out,value)
    return out


def scalar_multiply(a,b):
    if isinstance(a,QComplex) or isinstance(b,QComplex): return QComplex(a)*QComplex(b)
    return rational_product(a,b)


def _freeze_label(value):
    """Copy nested label sequences; reject opaque/mutable key domains."""
    if isinstance(value, (tuple, list)):
        return tuple(_freeze_label(v) for v in value)
    if value is None or type(value) in (int, str, bool) or isinstance(value, Fraction):
        return value
    raise TypeError('labels require immutable scalar or nested sequence data')


def _rational(value):
    if isinstance(value, (int, Fraction)):
        value=Fraction(value)
        _check_integer(value.numerator); _check_integer(value.denominator)
        return value
    raise TypeError('exact integer or Fraction required')


@dataclass(frozen=True, slots=True, init=False)
class QComplex:
    """Normalized exact complex scalar, stored as four integers (rn,rd,in,id)."""
    storage: tuple[int, int, int, int]

    def __init__(self, real=0, imag=0):
        if isinstance(real, QComplex) and imag == 0:
            for v in real.storage: _check_integer(v)
            object.__setattr__(self, 'storage', real.storage)
        else:
            r, i = _rational(real), _rational(imag)
            object.__setattr__(self, 'storage', (r.numerator, r.denominator, i.numerator, i.denominator))

    @property
    def real(self):
        return Fraction(*self.storage[:2])

    @property
    def imag(self):
        return Fraction(*self.storage[2:])

    def __bool__(self):
        return bool(self.storage[0] or self.storage[2])

    def __add__(self, other):
        if not isinstance(other, (QComplex, int, Fraction)):
            return NotImplemented
        other = QComplex(other)
        return QComplex(rational_add(self.real,other.real), rational_add(self.imag,other.imag))

    __radd__ = __add__

    def __neg__(self):
        return QComplex(-self.real, -self.imag)

    def __sub__(self, other):
        return self + -QComplex(other)

    def __mul__(self, other):
        if not isinstance(other, (QComplex, int, Fraction)):
            return NotImplemented
        other = QComplex(other)
        cost=_ACTIVE_COST.get()
        if cost is not None: cost.consume()
        ac=rational_product(self.real,other.real,bill=False)
        bd=rational_product(self.imag,other.imag,bill=False)
        ad=rational_product(self.real,other.imag,bill=False)
        bc=rational_product(self.imag,other.real,bill=False)
        return QComplex(rational_add(ac,-bd),rational_add(ad,bc))

    __rmul__ = __mul__

    def conjugate(self):
        return QComplex(self.real, -self.imag)


# The direct polar section introduces only these two real commuting
# coordinates. An arbitrary source in family 'r' remains complex.
_POLAR_RADIAL_FAMILY = '_original_edge_polar_radius'
_POLAR_RADIAL_INDICES = (('L',), ('R',))


def _is_polar_radial(family, index):
    return family == _POLAR_RADIAL_FAMILY and index in _POLAR_RADIAL_INDICES


@dataclass(frozen=True, slots=True, order=True)
class Symbol:
    """A commuting coordinate with its complete source/link identity."""
    family: str
    index: tuple
    conjugated: bool = False

    def __post_init__(self):
        if type(self.family) is not str or type(self.conjugated) is not bool:
            raise TypeError('symbol family and conjugation flag have invalid types')
        index = _freeze_label(self.index)
        if not isinstance(index, tuple):
            raise TypeError('symbol index must be a sequence')
        object.__setattr__(self, 'index', index)
        if self.family in ('q', 'h') or _is_polar_radial(self.family, index):
            object.__setattr__(self, 'conjugated', False)

    def conjugate(self):
        # Only the declared quaternion and auxiliary coordinates are real.
        if self.family in ('q', 'h') or _is_polar_radial(self.family, self.index):
            return self
        return replace(self, conjugated=not self.conjugated)


@dataclass(slots=True)
class ScalarCost:
    """Counts individual complex scalar product-accumulations, not ring products."""
    limit: int
    products: int = 0
    integer_products: int = 0
    _token: object = field(default=None, init=False, repr=False)

    def __enter__(self):
        if self._token is not None:
            raise ValueError('cost scope is already active')
        self._token = _ACTIVE_COST.set(self)
        return self

    def __exit__(self, exc_type, exc, traceback):
        _ACTIVE_COST.reset(self._token)
        self._token = None

    def consume(self):
        if self.products >= self.limit:
            raise ValueError('scalar product budget exceeded; no complete result')
        self.products += 1


def _collect(terms):
    out = {}
    for key, value in terms:
        out[key] = out.get(key, QComplex()) + value
    return tuple(sorted((k, v) for k, v in out.items() if v))


@dataclass(frozen=True, slots=True)
class Polynomial:
    """Finite exact polynomial; key is a sorted tuple of repeated real symbols.

    Each entry contains ONE QComplex scalar coefficient. Multiplication expands
    and optionally counts each scalar product. No sphere relation is assumed.
    """
    terms: tuple = ()

    def __post_init__(self):
        object.__setattr__(self, 'terms', _collect((tuple(sorted(k)), QComplex(v)) for k, v in self.terms))

    @classmethod
    def scalar(cls, value):
        return cls((((), QComplex(value)),)) if QComplex(value) else cls()

    @classmethod
    def variable(cls, symbol):
        return cls((((symbol,), QComplex(1)),))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Polynomial) else Polynomial.scalar(value)

    def __bool__(self):
        return bool(self.terms)

    def __add__(self, other):
        other = self.coerce(other)
        return Polynomial(self.terms + other.terms)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial(tuple((k, -v) for k, v in self.terms))

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def multiply(self, other, cost=None):
        other = self.coerce(other)
        active=_ACTIVE_COST.get(); token=None
        if cost is not None and cost is not active: token=_ACTIVE_COST.set(cost)
        try:
            out = {}
            for a, av in self.terms:
                for b, bv in other.terms:
                    key = tuple(sorted(a + b))
                    out[key] = out.get(key, QComplex()) + av * bv
            return Polynomial(tuple(out.items()))
        finally:
            if token is not None: _ACTIVE_COST.reset(token)

    def __mul__(self, other):
        return self.multiply(other)

    __rmul__ = __mul__

    def conjugate(self):
        return Polynomial(tuple((tuple(s.conjugate() for s in k), v.conjugate()) for k, v in self.terms))

    def evaluate(self, values):
        out = QComplex()
        for key, coefficient in self.terms:
            for symbol in key:
                value = QComplex(values[replace(symbol, conjugated=False)])
                if symbol.conjugated:
                    value = value.conjugate()
                coefficient *= value
            out += coefficient
        return out


def permutation_sign(values):
    if len(set(values)) != len(values):
        return 0
    return (-1) ** sum(a > b for i, a in enumerate(values) for b in values[i + 1:])


def epsilon(values):
    return permutation_sign(values) if sorted(values) == list(range(4)) else 0


def identity_matrix(n):
    return tuple(tuple(Polynomial.scalar(int(i == j)) for j in range(n)) for i in range(n))


def exact_matrix(value, shape=None):
    """Validate the entire rectangle and freeze exact polynomial entries.

    () denotes the unique represented 0x0 matrix. Nonempty zero-width rows
    are rejected: nested tuples cannot retain their missing transpose dimension.
    An optional shape is checked before arithmetic (Spin4 consumers use 4x4).
    """
    try:
        rows = tuple(tuple(row) for row in value)
    except TypeError as exc:
        raise ValueError('matrix must be a rectangular sequence of rows') from exc
    width = len(rows[0]) if rows else 0
    if rows and (width == 0 or any(len(row) != width for row in rows)):
        raise ValueError('matrix must be rectangular with nonzero row width')
    if shape is not None and (len(rows), width) != shape:
        raise ValueError(f'matrix must have exact shape {shape[0]}x{shape[1]}')
    return tuple(tuple(Polynomial.coerce(v) for v in row) for row in rows)


def matrix_add(a, b):
    a, b = exact_matrix(a), exact_matrix(b)
    if len(a) != len(b) or (a and len(a[0]) != len(b[0])):
        raise ValueError('matrix shapes differ')
    return tuple(tuple(x + y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def matrix_scale(a, scalar):
    return tuple(tuple(v * scalar for v in row) for row in exact_matrix(a))


def matrix_multiply(a, b, cost=None):
    a, b = exact_matrix(a), exact_matrix(b)
    if not a or not b:
        if not a and not b:
            return ()
        raise ValueError('matrix product shapes differ')
    if len(a[0]) != len(b):
        raise ValueError('matrix product shapes differ')
    return tuple(tuple(sum((a[i][k].multiply(b[k][j], cost) for k in range(len(b))), Polynomial())
                       for j in range(len(b[0]))) for i in range(len(a)))


def matrix_dagger(a):
    a = exact_matrix(a)
    if not a:
        return ()
    return tuple(tuple(a[j][i].conjugate() for j in range(len(a))) for i in range(len(a[0])))


@dataclass(frozen=True, slots=True)
class OriginalRegulator:
    """Frozen original four-dimensional carrier; both directed L2 anchors survive."""
    extents: tuple = (2, 2, 2, 2)
    boundary_signs: tuple = (1, 1, 1, 1)
    convention: str = 'source_C'
    word: str = 'closed'
    temporal_axis: int | None = None

    def __post_init__(self):
        object.__setattr__(self, 'extents', tuple(self.extents))
        object.__setattr__(self, 'boundary_signs', tuple(self.boundary_signs))
        if len(self.extents) != 4 or any(type(n) is not int or n < 1 for n in self.extents):
            raise ValueError('four positive integer extents required')
        if len(self.boundary_signs) != 4 or any(type(s) is not int or s not in (-1, 1) for s in self.boundary_signs):
            raise ValueError('four paired real boundary signs required')
        if self.convention not in ('source_C', 'metric_M') or self.word not in ('printed', 'closed'):
            raise ValueError('explicit convention and word label required')
        if self.temporal_axis is None:
            object.__setattr__(self, 'temporal_axis', 3 if self.convention == 'source_C' else 0)
        if type(self.temporal_axis) is not int or self.temporal_axis not in range(4):
            raise ValueError('temporal axis must be an explicit integer in 0..3')

    @property
    def sites(self):
        return tuple(product(*(range(n) for n in self.extents)))

    @property
    def volume(self):
        return prod(self.extents)

    @property
    def gamma(self):
        from src.core.formulas import original_gamma
        return tuple(original_gamma(a, self.convention) for a in range(4))

    @property
    def gamma5(self):
        from src.core.formulas import original_gamma5
        return original_gamma5()

    @property
    def reflection_matrix(self):
        # This is cut metadata only; it supplies no physical adjoint or kernel map.
        return self.gamma[self.temporal_axis]

    @property
    def auxiliary_degree_bound(self):
        return 4 * self.volume

    @property
    def link_order(self):
        return tuple((x, mu) for x in self.sites for mu in range(4))

    @property
    def generator_order(self):
        local = (('bar', 0), ('bar', 1), ('psi', 0), ('psi', 1),
                 ('bar', 2), ('bar', 3), ('psi', 2), ('psi', 3))
        return tuple((x, kind, i) for x in self.sites for kind, i in local)

    def site_number(self, x):
        self.validate_site(x)
        n = 0
        for v, length in zip(x, self.extents):
            n = n * length + v
        return n

    def validate_site(self, x):
        if len(x) != 4 or any(type(v) is not int or not 0 <= v < n for v, n in zip(x, self.extents)):
            raise ValueError('site outside regulator')

    def step(self, x, mu, direction=1):
        self.validate_site(x)
        if mu not in range(4) or direction not in (-1, 1):
            raise ValueError('unit axis step required')
        raw = x[mu] + direction
        y = tuple(raw % self.extents[mu] if j == mu else v for j, v in enumerate(x))
        return y, self.boundary_signs[mu] if raw < 0 or raw >= self.extents[mu] else 1

    def reflect_site(self, x):
        self.validate_site(x)
        t = self.temporal_axis
        return tuple((1 - v) % self.extents[t] if j == t else v for j, v in enumerate(x))

    def reflected_anchor(self, anchor):
        x, mu = anchor
        y = self.reflect_site(x)
        if mu == self.temporal_axis:
            y = self.step(y, mu, -1)[0]
        return (y, mu), mu == self.temporal_axis


@dataclass(frozen=True, slots=True)
class ConventionTransport:
    """Entrywise M/C dictionary. Order is preserved within either word label."""
    source: str
    target: str

    def __post_init__(self):
        if self.source not in ('source_C', 'metric_M') or self.target not in ('source_C', 'metric_M'):
            raise ValueError('unknown convention')

    def axis(self, a):
        if a not in range(4):
            raise ValueError('invalid axis')
        if self.source == self.target:
            return a
        return (3, 0, 1, 2)[a] if self.source == 'metric_M' else (1, 2, 3, 0)[a]

    def site(self, x):
        out = [0] * 4
        for a, v in enumerate(x):
            out[self.axis(a)] = v
        return tuple(out)

    def anchor(self, anchor):
        x, mu = anchor
        return self.site(x), self.axis(mu)

    def composite(self, alpha):
        x, mu, a = alpha
        return self.site(x), self.axis(mu), self.axis(a)

    linear_label = composite
    auxiliary_label = composite
    phase_label = site

    def metric_pair(self, pair):
        return tuple(sorted(self.axis(i) for i in pair))

    def frame_pair(self, pair):
        return tuple(self.axis(i) for i in pair)

    def regulator(self, reg):
        if reg.convention != self.source:
            raise ValueError('transport source mismatch')
        return OriginalRegulator(self.site(reg.extents), self.site(reg.boundary_signs), self.target, reg.word, self.axis(reg.temporal_axis))

    def couplings(self, g1, g2):
        return g1, g2 if self.source == self.target else -g2

    def spinor(self, i):
        return i

    def chirality(self, label):
        return label

    def sigma2(self, v):
        return v

    def reflect_site(self, reg, x):
        return self.site(reg.reflect_site(x))

    def temporal_reflection_anchor(self, reg, anchor):
        reflected, dagger = reg.reflected_anchor(anchor)
        return self.anchor(reflected), dagger

    def berezin_sign(self, reg):
        # Site relabeling exchanges blocks of degree eight; spinor order is fixed.
        return permutation_sign(tuple(self.regulator(reg).site_number(self.site(x)) for x in reg.sites)) ** 8


@dataclass(frozen=True, slots=True)
class BlockIncrement:
    alpha: tuple
    bar_site: tuple
    psi_site: tuple
    anchor: tuple
    weight: Fraction
    matrix: tuple

    def __post_init__(self):
        for name in ('alpha', 'bar_site', 'psi_site', 'anchor'):
            object.__setattr__(self, name, _freeze_label(getattr(self, name)))
        object.__setattr__(self, 'weight', _rational(self.weight))
        object.__setattr__(self, 'matrix', exact_matrix(self.matrix, shape=(4, 4)))


@dataclass(frozen=True, slots=True)
class ActionFactor:
    t_degree: int
    components: tuple
    coefficient: Polynomial
    anchors: tuple = ()

    def __post_init__(self):
        object.__setattr__(self, 'components', _freeze_label(self.components))
        object.__setattr__(self, 'anchors', _freeze_label(self.anchors))
        object.__setattr__(self, 'coefficient', Polynomial.coerce(self.coefficient))


@dataclass(frozen=True, slots=True)
class GeneratorLinkSupport:
    """Complete structural generator/anchor labels before coefficient cancellation."""
    generators: tuple
    anchors: tuple
    sites: tuple

    def __post_init__(self):
        for name in ('generators', 'anchors', 'sites'):
            object.__setattr__(self, name, _freeze_label(getattr(self, name)))


def factor_support(reg, factor):
    """Support union of the original coframe blocks and ordered curvature path.

    This is an envelope; zero specialized coefficients do not delete incidence.
    In particular it does not make two occurrences of a shared link independent.
    """
    sites, anchors = set(), set(factor.anchors)
    for x, mu, a in factor.components:
        reg.validate_site(x)
        forward, backward = reg.step(x, mu)[0], reg.step(x, mu, -1)[0]
        sites.update((x, forward, backward))
        anchors.update(((x, mu), (backward, mu)))
    return GeneratorLinkSupport(tuple(g for g in reg.generator_order if g[0] in sites),
                                tuple(sorted(anchors)), tuple(sorted(sites)))


def legacy_quaternion_to_c(coordinates):
    """Old minus-i coordinates -> canonical plus-i, a Haar sphere isometry."""
    if len(coordinates) != 4:
        raise ValueError('four quaternion coordinates required')
    return (coordinates[0], *(-v for v in coordinates[1:]))


@dataclass(frozen=True, slots=True)
class SparseMatrix:
    size: int
    entries: tuple

    def __post_init__(self):
        if type(self.size) is not int or self.size < 0:
            raise ValueError('matrix size must be a nonnegative integer')
        out = {}
        for entry in self.entries:
            if len(entry) != 2:
                raise ValueError('matrix entry must contain coordinate and coefficient')
            key, value = entry
            key = tuple(key)
            if len(key) != 2 or any(type(i) is not int or not 0 <= i < self.size for i in key):
                raise ValueError('matrix coordinates must be in-range integer indices')
            out[key] = out.get(key, Polynomial()) + Polynomial.coerce(value)
        object.__setattr__(self, 'entries', tuple(sorted((k, v) for k, v in out.items() if v)))

    def at(self, i, j):
        if any(type(k) is not int or not 0 <= k < self.size for k in (i, j)):
            raise ValueError('matrix access requires in-range integer indices')
        return dict(self.entries).get((i, j), Polynomial())

    def to_exterior(self, reg):
        if self.size != 4 * reg.volume:
            raise ValueError('matrix/regulator size mismatch')
        positions = {g: i for i, g in enumerate(reg.generator_order)}
        out = ExteriorPolynomial()
        for (i, j), value in self.entries:
            a = positions[(reg.sites[i // 4], 'bar', i % 4)]
            b = positions[(reg.sites[j // 4], 'psi', j % 4)]
            out += ExteriorPolynomial.generator(a) * ExteriorPolynomial.generator(b) * value
        return out


def assemble_coframe(reg, increments):
    out = {}
    for b in increments:
        rb, cb = 4 * reg.site_number(b.bar_site), 4 * reg.site_number(b.psi_site)
        for i, row in enumerate(b.matrix):
            for j, v in enumerate(row):
                if v:
                    key = rb + i, cb + j
                    out[key] = out.get(key, Polynomial()) + v * b.weight
    return SparseMatrix(4 * reg.volume, tuple(sorted((k, v) for k, v in out.items() if v)))


def assemble_dirac(reg, h_plus_J=None, links=None):
    """Add all original blocks, retaining their shared h/J/link polynomials."""
    from src.core.formulas import original_coframe_blocks
    out = {}
    for x in reg.sites:
        for mu in range(4):
            for a in range(4):
                alpha = x, mu, a
                weight = (Polynomial.variable(Symbol('h', alpha)) + Polynomial.variable(Symbol('J', alpha))
                          if h_plus_J is None else Polynomial.coerce(h_plus_J.get(alpha, 0)))
                for key, value in assemble_coframe(reg, original_coframe_blocks(reg, alpha, links)).entries:
                    out[key] = out.get(key, Polynomial()) + weight * value
    return SparseMatrix(4 * reg.volume, tuple(sorted((k, v) for k, v in out.items() if v)))


@dataclass(frozen=True, slots=True)
class ExteriorPolynomial:
    """Bitmask exterior algebra over exact coefficient polynomials."""
    terms: tuple = ()

    def __post_init__(self):
        out = {}
        for key, value in self.terms:
            if type(key) is not int or key < 0:
                raise ValueError('nonnegative generator mask required')
            out[key] = out.get(key, Polynomial()) + value
        object.__setattr__(self, 'terms', tuple(sorted((k, v) for k, v in out.items() if v)))

    @classmethod
    def generator(cls, i):
        return cls(((1 << i, Polynomial.scalar(1)),))

    def __neg__(self):
        return ExteriorPolynomial(tuple((k, -v) for k, v in self.terms))

    def __add__(self, other):
        return ExteriorPolynomial(self.terms + other.terms)

    def __mul__(self, other):
        if not isinstance(other, ExteriorPolynomial):
            return ExteriorPolynomial(tuple((k, v * other) for k, v in self.terms))
        out = []
        for a, av in self.terms:
            for b, bv in other.terms:
                if a & b:
                    continue
                swaps = sum((b & ((1 << i) - 1)).bit_count() for i in range(a.bit_length()) if a & (1 << i))
                out.append((a | b, av * bv * (-1) ** swaps))
        return ExteriorPolynomial(tuple(out))


@dataclass(frozen=True, slots=True)
class LocalDegreeCertificate:
    center: tuple
    center_mask: int
    minimum_center_generators: int
    degree_bound: int
    checked_monomials: int
    production_authorized: bool = False

    def __post_init__(self):
        object.__setattr__(self, 'center', _freeze_label(self.center))

    def vanishes_above(self, degree):
        """Whether the tested power is strictly beyond the last allowed degree."""
        return degree > self.degree_bound


def local_degree_certificate(reg, center, coframes):
    reg.validate_site(center)
    mask = sum(1 << i for i, g in enumerate(reg.generator_order) if g[0] == center)
    minimum, checked = 8, 0
    for frame in coframes:
        for word, coefficient in frame.terms:
            if word.bit_length() > 8 * reg.volume or word.bit_count() != 2:
                raise ValueError('coframe must be homogeneous bilinear on regulator')
            n = (word & mask).bit_count()
            if n == 0:
                raise ValueError('noncentered frame has no center generator')
            minimum = min(minimum, n)
            checked += 1
    if not checked:
        raise ValueError('nonempty centered support required')
    return LocalDegreeCertificate(center, mask, minimum, min(4 * reg.volume, 8 // minimum), checked)


@dataclass(frozen=True, slots=True)
class StructuralCertificate:
    components: int
    block_increments: int
    scalar_slot_writes: int
    coframe_slots: int
    coordinate_terms: int
    dirac_slots: int
    dirac_row_populations: tuple
    independent_su2_factors: int

    def __post_init__(self):
        object.__setattr__(self, 'dirac_row_populations', tuple(self.dirac_row_populations))


def structural_certificate(reg):
    from src.core.formulas import original_coframe_blocks
    components = increments = writes = slots = terms = 0
    union = set()
    for x in reg.sites:
        for mu in range(4):
            for a in range(4):
                blocks = original_coframe_blocks(reg, (x, mu, a))
                components += 1
                increments += len(blocks)
                writes += sum(bool(v) for b in blocks for row in b.matrix for v in row)
                matrix = assemble_coframe(reg, blocks)
                slots += len(matrix.entries)
                terms += sum(len(v.terms) for _, v in matrix.entries)
                union.update(k for k, _ in matrix.entries)
    return StructuralCertificate(components, increments, writes, slots, terms, len(union),
                                 tuple(sum(i == row for i, _ in union) for row in range(4 * reg.volume)), 8 * reg.volume)


@dataclass(frozen=True, slots=True)
class DeterminantSupport:
    row_order: tuple
    column_order: tuple
    row_sign: int
    column_sign: int
    block_sizes: tuple
    layer_populations: tuple
    total_reachable_masks: int
    transitions_per_block: int
    transitions_all_blocks: int

    def __post_init__(self):
        for name in ('row_order', 'column_order', 'block_sizes', 'layer_populations'):
            object.__setattr__(self, name, tuple(getattr(self, name)))


def determinant_support(reg):
    """Signed four-block permutation and unsigned row-subset reachability.

    No determinant coefficient, Haar factorization or nonzero claim is made.
    A periodic torus is bipartite only when each extent is even.
    """
    if any(n % 2 for n in reg.extents):
        raise ValueError('periodic bipartite partition requires all even extents')
    groups = {}
    for parity, chirality in product(range(2), range(2)):
        groups[parity, chirality] = tuple(4 * reg.site_number(x) + i for x in reg.sites
                                        if sum(x) % 2 == parity for i in range(2 * chirality, 2 * chirality + 2))
    row_groups = ((0, 0), (1, 1), (0, 1), (1, 0))
    col_groups = ((1, 1), (0, 0), (1, 0), (0, 1))
    rows = sum((groups[g] for g in row_groups), ())
    cols = sum((groups[g] for g in col_groups), ())
    populations, edge_counts = [], []
    for rg, cg in zip(row_groups, col_groups):
        states, layers, transitions = {0}, [1], 0
        for row in groups[rg]:
            x = reg.sites[row // 4]
            neighbors = {reg.step(x, mu, direction)[0] for mu in range(4) for direction in (-1, 1)}
            choices = tuple(j for j, col in enumerate(groups[cg]) if reg.sites[col // 4] in neighbors)
            nxt = set()
            for mask in states:
                for j in choices:
                    if not mask & (1 << j):
                        transitions += 1
                        nxt.add(mask | (1 << j))
            states = nxt
            layers.append(len(states))
        populations.append(tuple(layers))
        edge_counts.append(transitions)
    if len(set(populations)) != 1:
        raise ValueError('directed block reachability differs; retain separate certificates')
    return DeterminantSupport(rows, cols, permutation_sign(rows), permutation_sign(cols),
                              tuple(len(groups[g]) for g in row_groups), populations[0], sum(populations[0]),
                              edge_counts[0], sum(edge_counts))


def recursive_size_bytes(value):
    """Unique live Python payload bytes, including nested dataclass slots/integers.

    Measures the supplied object graph, not RSS, allocator slack or future maps.
    Callers must additionally account for simultaneous inputs/outputs and resize.
    """
    seen = set()
    def visit(obj):
        if id(obj) in seen:
            return 0
        seen.add(id(obj))
        size = sys.getsizeof(obj)
        if isinstance(obj, dict):
            return size + sum(visit(k) + visit(v) for k, v in obj.items())
        if isinstance(obj, (tuple, list, set, frozenset)):
            return size + sum(visit(v) for v in obj)
        if is_dataclass(obj) and not isinstance(obj, type):
            return size + sum(visit(getattr(obj, f.name)) for f in fields(obj))
        return size
    return visit(value)


# Exact finite coefficient algebra; shared scalar primitives above enforce cost and height contracts.
def polynomial_derivative(poly, symbol):
    terms=[]
    for key,value in Polynomial.coerce(poly).terms:
        n=key.count(symbol)
        if n:
            rest=list(key); rest.remove(symbol)
            terms.append((tuple(rest),value*n))
    return Polynomial(tuple(terms))


def polynomial_substitute(poly, values):
    out=Polynomial()
    for key,value in Polynomial.coerce(poly).terms:
        term=Polynomial.scalar(value)
        for s in key:
            term*=values.get(s,Polynomial.variable(s))
        out+=term
    return out


def raw_derivative(poly, symbols):
    for s in symbols:
        poly=polynomial_derivative(poly,s)
    return poly


@dataclass(frozen=True, slots=True)
class RawJet:
    """Undivided C2 derivatives; every repeated product has both cross terms."""
    labels: tuple
    entries: tuple

    def __post_init__(self):
        labels=_freeze_label(self.labels)
        if len(set(labels))!=len(labels):
            raise ValueError('jet labels must be distinct')
        out={}
        for key,value in self.entries:
            if not isinstance(value,(int,Fraction,QComplex,Polynomial,ExteriorPolynomial)):
                raise TypeError('raw jet requires immutable exact scalar/polynomial values')
            if isinstance(value,(int,Fraction)):value=_rational(value)
            key=tuple(sorted(key))
            if len(key)>2 or any(type(i)is not int or not 0<=i<len(labels) for i in key):
                raise ValueError('invalid raw C2 derivative index')
            if key in out:
                raise ValueError('duplicate raw derivative entry')
            out[key]=value
        if () not in out:
            raise ValueError('raw jet requires its value')
        object.__setattr__(self,'labels',labels)
        object.__setattr__(self,'entries',tuple(sorted(out.items())))

    @classmethod
    def constant(cls,value,labels=(0,1)):
        return cls(tuple(labels),(((),value),))

    @classmethod
    def from_slots(cls,slots):
        if len(slots)!=6:
            raise ValueError('two-label raw C2 has six scalar slots')
        return cls((0,1),tuple(zip(((),(0,),(1,),(0,0),(0,1),(1,1)),slots)))

    def indices(self):
        from itertools import combinations_with_replacement
        return ((),)+tuple((i,) for i in range(len(self.labels)))+tuple(combinations_with_replacement(range(len(self.labels)),2))

    def at(self,index=()):
        index=tuple(index)
        if len(index)>2 or any(type(i)is not int or not 0<=i<len(self.labels) for i in index):
            raise ValueError('derivative request outside declared raw C2 jet')
        value=dict(self.entries)[()]
        entries=dict(self.entries); key=tuple(sorted(index))
        if key in entries:return entries[key]
        if isinstance(value,(int,Fraction)):return Fraction()
        return type(value)()

    def slots(self):
        return tuple(self.at(k) for k in self.indices())

    def _coerce(self,other):
        if not isinstance(other,RawJet):
            return RawJet.constant(other,self.labels)
        if other.labels!=self.labels:
            raise ValueError('raw jet label mismatch')
        return other

    def __add__(self,other):
        other=self._coerce(other)
        return RawJet(self.labels,tuple((k,rational_add(self.at(k),other.at(k)) if isinstance(self.at(k),(int,Fraction)) and isinstance(other.at(k),(int,Fraction)) else self.at(k)+other.at(k)) for k in self.indices()))

    __radd__=__add__

    def __neg__(self):
        return RawJet(self.labels,tuple((k,-v) for k,v in self.entries))

    def __sub__(self,other):
        return self+-self._coerce(other)

    def __mul__(self,other):
        other=self._coerce(other)
        out=[]
        for k in self.indices():
            base=self.at(())
            value=Fraction() if isinstance(base,(int,Fraction)) else type(base)()
            # Positions, rather than a set of labels, preserve repeated factors.
            for choose in range(1<<len(k)):
                a=tuple(v for i,v in enumerate(k) if choose>>i&1)
                b=tuple(v for i,v in enumerate(k) if not choose>>i&1)
                av,bv=self.at(a),other.at(b)
                term=scalar_multiply(av,bv) if isinstance(av,(int,Fraction,QComplex)) and isinstance(bv,(int,Fraction,QComplex)) else av*bv
                value=rational_add(value,term) if isinstance(value,(int,Fraction)) and isinstance(term,(int,Fraction)) else value+term
            out.append((k,value))
        return RawJet(self.labels,tuple(out))

    __rmul__=__mul__


def exponential_jet(action, exp_value):
    out=[((),exp_value)]
    for k in action.indices()[1:]:
        value=action.at(k)
        if len(k)==2:
            a,b=action.at((k[0],)),action.at((k[1],))
            cross=scalar_multiply(a,b) if isinstance(a,(int,Fraction,QComplex)) and isinstance(b,(int,Fraction,QComplex)) else a*b
            value=rational_add(value,cross) if isinstance(value,(int,Fraction)) and isinstance(cross,(int,Fraction)) else value+cross
        v=scalar_multiply(value,exp_value) if isinstance(value,(int,Fraction,QComplex)) and isinstance(exp_value,(int,Fraction,QComplex)) else value*exp_value
        out.append((k,v))
    return RawJet(action.labels,tuple(out))


def insertion_action_measure_jet(insertion, action, measure, exp_value):
    return insertion*exponential_jet(action,exp_value)*measure


def determinant_polynomial(matrix):
    """Row/subset polynomial DP. Empty minor=1, no inverse at singular inputs."""
    if not isinstance(matrix,SparseMatrix):
        rows=exact_matrix(matrix)
        if rows and len(rows)!=len(rows[0]): raise ValueError('square matrix required')
        matrix=SparseMatrix(len(rows),tuple(((i,j),v) for i,row in enumerate(rows) for j,v in enumerate(row)))
    entries=dict(matrix.entries); states={0:Polynomial.scalar(1)}
    for i in range(matrix.size):
        nxt={}
        for mask,prev in states.items():
            for j in range(matrix.size):
                entry=entries.get((i,j))
                if mask>>j&1 or entry is None: continue
                sign=(-1)**((mask>>(j+1)).bit_count())
                key=mask|1<<j
                nxt[key]=nxt.get(key,Polynomial())+prev*entry*sign
        states=nxt
        cost=_ACTIVE_COST.get()
        if isinstance(cost,ExactBudget): cost.check_storage((entries,states,nxt))
    return states.get((1<<matrix.size)-1,Polynomial())


def determinant_jet(matrix, increments, accelerations=None):
    increments=tuple(increments); n=matrix.size
    if any(a.size!=n for a in increments): raise ValueError('matrix increment size mismatch')
    accelerations={} if accelerations is None else accelerations
    for k,v in accelerations.items():
        if len(k)!=2 or v.size!=n: raise ValueError('invalid matrix acceleration')
    labels=tuple(range(len(increments))); base=dict(matrix.entries)
    inc=tuple(dict(a.entries) for a in increments)
    acc={tuple(sorted(k)):dict(a.entries) for k,a in accelerations.items()}
    entries={}
    keys=set(base).union(*(set(a) for a in inc),*(set(a) for a in acc.values()))
    for coord in keys:
        entries[coord]=RawJet(labels,(((),base.get(coord,Polynomial())),)+tuple(((i,),v.get(coord,Polynomial())) for i,v in enumerate(inc))+tuple((k,v.get(coord,Polynomial())) for k,v in acc.items()))
    states={0:RawJet.constant(Polynomial.scalar(1),labels)}
    for i in range(n):
        nxt={}
        for mask,prev in states.items():
            for j in range(n):
                if mask>>j&1 or (i,j) not in entries: continue
                key=mask|1<<j
                term=prev*entries[i,j]*((-1)**((mask>>(j+1)).bit_count()))
                nxt[key]=nxt.get(key,RawJet.constant(Polynomial(),labels))+term
        states=nxt
        cost=_ACTIVE_COST.get()
        if isinstance(cost,ExactBudget): cost.check_storage((entries,states,nxt))
    return states.get((1<<n)-1,RawJet.constant(Polynomial(),labels))


def complementary_insertion(matrix,bars,psis):
    """Sorted bars followed by sorted psis in the canonical all-bar/all-psi top."""
    bars,psis=tuple(bars),tuple(psis); n=matrix.size
    if len(bars)!=len(psis) or bars!=tuple(sorted(set(bars))) or psis!=tuple(sorted(set(psis))) or any(i not in range(n) for i in bars+psis):
        raise ValueError('sorted distinct equal-cardinality deletion sets required')
    r=tuple(i for i in range(n) if i not in bars); c=tuple(i for i in range(n) if i not in psis)
    minor=SparseMatrix(len(r),tuple(((i,j),matrix.at(a,b)) for i,a in enumerate(r) for j,b in enumerate(c)))
    k=len(bars)
    # Canonical Berezin convention integral exp(bar M psi)=det M.
    return determinant_polynomial(minor)*((-1)**(k*(k-1)//2+sum(bars)+sum(psis)))


def haar_polynomial(poly):
    from src.core.formulas import original_quaternion_haar_moment
    out=[]
    for key,value in Polynomial.coerce(poly).terms:
        groups={}; rest=[]
        for s in key:
            if s.family!='q': rest.append(s); continue
            if len(s.index)!=4 or type(s.index[-1])is not int or s.index[-1] not in range(4):
                raise ValueError('quaternion requires site/anchor/chirality/coordinate identity')
            group=groups.setdefault(s.index[:-1],[0]*4); group[s.index[-1]]+=1
        moment=rational_product_all(original_quaternion_haar_moment(tuple(v)) for v in groups.values())
        if moment: out.append((tuple(rest),value*moment))
    return Polynomial(tuple(out))


def hermite_gaussian_contraction(eta,beta,variance):
    """Independent finite Hermite expansion integrated using Gaussian moments."""
    from src.core.formulas import original_scaled_hermite, original_gaussian_moment
    if len(eta)!=len(beta): raise ValueError('moment dimension mismatch')
    variance=_rational(variance)
    if variance<=0: raise ValueError('positive variance required')
    value=Fraction(1)
    for a,b in zip(eta,beta):
        moment=Fraction()
        for degree,c in original_scaled_hermite(a,variance):moment=rational_add(moment,rational_product(c,original_gaussian_moment((degree+b,),variance)))
        value=rational_product(value,rational_product(moment,rational_inverse(rational_power(variance,a))))
    return value


@dataclass(frozen=True,slots=True)
class GradedTerm:
    t_degree:int
    coupling_powers:tuple
    source_powers:tuple
    contact_labels:tuple
    support:GeneratorLinkSupport
    multiplicity:Fraction
    coefficient:QComplex=QComplex(1)
    exterior_mask:int|None=None
    monomial:tuple=()

    def __post_init__(self):
        if not isinstance(self.support,GeneratorLinkSupport): raise TypeError('typed immutable generator/link support required')
        object.__setattr__(self,'monomial',_freeze_exact_metadata(self.monomial))
        if self.monomial!=tuple(sorted(self.monomial)) or any(not isinstance(v,Symbol) for v in self.monomial): raise TypeError('exact monomial symbols required')
        if self.exterior_mask is not None and (type(self.exterior_mask)is not int or self.exterior_mask<0 or self.exterior_mask.bit_count()!=2*self.t_degree): raise ValueError('grading exterior mask must match homogeneous degree')
        for name in ('coupling_powers','source_powers','contact_labels'):
            object.__setattr__(self,name,_freeze_label(getattr(self,name)))
        if type(self.t_degree)is not int or self.t_degree<0 or len(self.coupling_powers)!=2 or len(self.source_powers)!=2 or any(type(k)is not int or k<0 for k in self.coupling_powers+self.source_powers):
            raise ValueError('homogeneous nonnegative family grading required')
        object.__setattr__(self,'multiplicity',_rational(self.multiplicity))
        object.__setattr__(self,'coefficient',QComplex(self.coefficient))
        for symbol in self.monomial:
            if symbol.family=='q':
                if len(symbol.index)!=4 or symbol.index[2] not in ('L','R') or type(symbol.index[3])is not int or symbol.index[3] not in range(4):raise ValueError('grading needs exact original quaternion anchor identity')
                if (symbol.index[0],symbol.index[1]) not in self.support.anchors:raise ValueError('grading support cannot omit actual quaternion anchor')
        cp=tuple(sum(s.family==g for s in self.monomial) for g in ('g1','g2'))
        sp=tuple(sum(s.family==g for s in self.monomial) for g in ('J','H'))
        if any(cp) and cp!=self.coupling_powers:raise ValueError('coupling grading contradicts formal monomial')
        if any(sp) and sp!=self.source_powers:raise ValueError('source grading contradicts formal monomial')

    def saturates(self,volume,inserted_degree=0):
        # t_degree ALREADY includes action/source/contact degrees of this summand.
        return self.t_degree+inserted_degree==4*volume


@dataclass(frozen=True,slots=True)
class SourceFamilyGrading:
    entries:tuple
    def __post_init__(self):
        entries=tuple((tuple(k),tuple(v)) for k,v in self.entries)
        if any(len(k)>2 or k!=tuple(sorted(k)) or any(type(i)is not int or i<0 for i in k) for k,v in entries): raise ValueError('grading requires canonical C2 derivative indices')
        if len(set(k for k,v in entries))!=len(entries) or any(not isinstance(t,GradedTerm) for k,v in entries for t in v):
            raise ValueError('unique derivative indices and exact graded terms required')
        object.__setattr__(self,'entries',entries)


@dataclass(frozen=True,slots=True)
class SourceJet:
    labels:tuple
    grading:SourceFamilyGrading
    action:RawJet
    insertion:RawJet
    measure:RawJet
    order:int=2
    insertion_id:str='unit'
    def __post_init__(self):
        object.__setattr__(self,'labels',_freeze_label(self.labels))
        if self.order not in (0,1,2) or any(v.labels!=self.labels for v in (self.action,self.insertion,self.measure)):
            raise ValueError('source families must share explicit raw jet labels')
        if not isinstance(self.insertion_id,str) or not self.insertion_id: raise ValueError('explicit insertion identity required')
        if not isinstance(self.grading,SourceFamilyGrading): raise TypeError('typed immutable source grading required')
        required=set(self.action.indices()) if self.order==2 else {()}|({(i,) for i in range(len(self.labels))} if self.order else set())
        if set(k for k,_ in self.grading.entries)!=required:
            raise ValueError('every derivative summand requires family grading')
        for jet in (self.action,self.insertion,self.measure):
            if any(len(k)>self.order and (bool(v.terms) if isinstance(v,(Polynomial,ExteriorPolynomial)) else bool(v)) for k,v in jet.entries): raise ValueError('nonzero contact outside declared grading scope')
        # Reconstruct each raw component from the graded pre-collection pieces.
        # Numeric H and current identities survive even when summands cancel.
        for k,terms in self.grading.entries:
            grouped={'action':[], 'insertion':[], 'measure':[]}
            for term in terms:
                if len(term.contact_labels)!=1: raise ValueError('grading needs one typed component role')
                role=term.contact_labels[0]
                kind=role if role in ('insertion','measure') else 'action'
                if kind=='action' and role not in ('action','literal_T','literal_metric','current_action','current_literal_T','current_literal_metric'): raise ValueError('unknown grading component role')
                coefficient=Polynomial(((term.monomial,term.coefficient*term.multiplicity),))
                if kind=='measure':
                    if term.exterior_mask is not None or term.t_degree: raise ValueError('measure grading must be scalar')
                    grouped[kind].extend(coefficient.terms)
                else:
                    if term.exterior_mask is None: raise ValueError('grading must bind each exterior monomial')
                    grouped[kind].append((term.exterior_mask,coefficient))
            expected={'action':ExteriorPolynomial(tuple(grouped['action'])), 'insertion':ExteriorPolynomial(tuple(grouped['insertion'])), 'measure':Polynomial(tuple(grouped['measure']))}
            if any(expected[name]!=getattr(self,name).at(k) for name in expected): raise ValueError('grading does not reconstruct actual action/insertion/measure')
            # The original finite exponential uses the positive even exterior
            # ideal in EVERY raw action slot; insertion/measure bodies are valid.
            # Inspect the collected action, so exact cancelled bodies stay valid.
            if any(mask == 0 or mask.bit_count() % 2 for mask, _ in self.action.at(k).terms):
                raise ValueError('action jets require positive even exterior degree and zero scalar body for nilpotent contraction')



def literal_source_supported(total_degree,k_T,k_Q,inserted_degree=0):
    return k_T+2*k_Q+inserted_degree<=total_degree and (k_T+inserted_degree)%2==0


@dataclass(frozen=True,slots=True)
class Unknown:
    reason:str


@dataclass(frozen=True,slots=True)
class NonzeroZCertificate:
    value:QComplex
    def __post_init__(self):
        v=QComplex(self.value)
        if not v: raise ValueError('nonzero exact Z required')
        object.__setattr__(self,'value',v)


def _scalar_value(value):
    if isinstance(value,Polynomial):
        if any(k for k,v in value.terms): raise ValueError('exact evaluated scalar required')
        return dict(value.terms).get((),QComplex())
    return QComplex(value)


def scalar_inverse(value):
    z=_scalar_value(value)
    d=rational_add(rational_product(z.real,z.real),rational_product(z.imag,z.imag))
    if not d: raise ValueError('nonzero scalar required')
    inv=rational_inverse(d)
    return QComplex(rational_product(z.real,inv),rational_product(-z.imag,inv))


def normalize_jet(numerator,denominator,certificate):
    if isinstance(denominator,Unknown): raise ValueError('UNKNOWN denominator cannot normalize')
    z=_scalar_value(denominator.at(()))
    if not isinstance(certificate,NonzeroZCertificate) or certificate.value!=z:
        raise ValueError('matching nonzero Z certificate required')
    inv=scalar_inverse(z); entries=[((),inv)]
    for k in denominator.indices()[1:]:
        d=_scalar_value(denominator.at(k))
        v=-d*inv*inv
        if len(k)==2:
            v+=2*_scalar_value(denominator.at((k[0],)))*_scalar_value(denominator.at((k[1],)))*inv*inv*inv
        entries.append((k,v))
    n=RawJet(numerator.labels,tuple((k,_scalar_value(v)) for k,v in numerator.entries))
    return n*RawJet(denominator.labels,tuple(entries))


def legendre_local(hessian,subspace):
    """Invert only the explicitly declared source subspace, exact rank refusal."""
    subspace=tuple(subspace)
    if not subspace or len(set(subspace))!=len(subspace): raise ValueError('explicit nonempty Hessian subspace required')
    rows=tuple(tuple(QComplex(x) for x in r) for r in hessian)
    if any(len(r)!=len(rows) for r in rows) or any(i not in range(len(rows)) for i in subspace): raise ValueError('invalid Hessian shape/subspace')
    n=len(subspace); a=[[rows[i][j] for j in subspace]+[QComplex(int(k==l)) for l in range(n)] for k,i in enumerate(subspace)]
    for j in range(n):
        pivot=next((k for k in range(j,n) if a[k][j]),None)
        if pivot is None: raise ValueError('degenerate restricted Hessian')
        a[j],a[pivot]=a[pivot],a[j]
        v=scalar_inverse(a[j][j]); a[j]=[x*v for x in a[j]]
        for k in range(n):
            if k!=j:
                v=a[k][j]; a[k]=[x-v*y for x,y in zip(a[k],a[j])]
    return tuple(tuple(r[n:]) for r in a)


class BudgetExceeded(ValueError):
    """An incomplete contraction, never a complete zero or partially accepted map."""


@dataclass(slots=True,init=False)
class ExactBudget(ScalarCost):
    storage_limit:int=512*1024**2
    peak_payload_bytes:int=0
    peak_scalar_records:int=0
    integer_bit_limit:int=1024
    fixed_reserve_bytes:int=128*1024**2
    peak_integer_bits:int=0

    def __init__(self,limit,storage_limit=512*1024**2,integer_bit_limit=1024):
        self.limit=limit; self.products=0; self.integer_products=0; self._token=None
        self.peak_integer_bits=0
        self.storage_limit=storage_limit; self.integer_bit_limit=integer_bit_limit
        self.peak_payload_bytes=0; self.peak_scalar_records=0
        self.fixed_reserve_bytes=128*1024**2

    def consume(self):
        if self.products>=self.limit:
            raise BudgetExceeded('scalar budget exceeded: incomplete coefficient control')
        self.products+=1

    def check_storage(self,*objects,additional_records=0):
        # Unique live objects PLUS worst-case table resizing/container slack.
        payload=recursive_size_bytes(objects)
        modeled=payload*2+additional_records*1536+self.fixed_reserve_bytes
        self.peak_payload_bytes=max(self.peak_payload_bytes,modeled)
        if modeled>self.storage_limit: raise BudgetExceeded('storage budget exceeded: incomplete coefficient control')
        seen=set()
        def visit(x):
            if id(x) in seen:return 0
            seen.add(id(x))
            if isinstance(x,(QComplex,Fraction)):
                values=x.storage if isinstance(x,QComplex) else (x.numerator,x.denominator)
                width=max(abs(v).bit_length() for v in values)
                self.peak_integer_bits=max(self.peak_integer_bits,width)
                if width>self.integer_bit_limit: raise BudgetExceeded('integer height exceeded: incomplete coefficient control')
                return 1
            if isinstance(x,dict):return sum(visit(k)+visit(v) for k,v in x.items())
            if isinstance(x,(tuple,list,set,frozenset)):return sum(visit(v) for v in x)
            if is_dataclass(x):return sum(visit(getattr(x,f.name)) for f in fields(x))
            return 0
        self.peak_scalar_records=max(self.peak_scalar_records,visit(objects)+additional_records)
        return modeled


def require_original_n16_budget(budget):
    """Check the shared exact resource contract before any N16 allocation."""
    if not isinstance(budget, ExactBudget) or _ACTIVE_COST.get() is not budget:
        raise ValueError('original N16 edge/core requires an active explicit ExactBudget')
    for name, maximum in (
        ('limit', 70_000_000), ('storage_limit', 2 * 1024**3), ('integer_bit_limit', 1024),
    ):
        value = getattr(budget, name)
        if type(value) is not int or not 0 < value <= maximum:
            raise ValueError(f'{name} must be a positive exact integer at most {maximum}')
    if type(budget.fixed_reserve_bytes) is not int or budget.fixed_reserve_bytes != 128 * 1024**2:
        raise ValueError('invalid original N16 budget accounting state: fixed_reserve_bytes')
    for name in ('products', 'integer_products', 'peak_payload_bytes',
                 'peak_scalar_records', 'peak_integer_bits'):
        value = getattr(budget, name)
        if type(value) is not int or value < 0:
            raise ValueError(f'invalid original N16 budget accounting state: {name}')
    if budget.products > budget.limit:
        raise ValueError('invalid original N16 budget accounting state: products')


def polynomial_degree_truncate(poly,symbols,bound):
    symbols=frozenset(symbols)
    return Polynomial(tuple((k,v) for k,v in poly.terms if sum(s in symbols for s in k)<=bound))


def hermite_weight(source,coordinates,sigma2,degree_bound=64):
    """Literal finite exp(S(X)) exp(-v X²/2), then scaled-Hermite conversion.

    Generic exact implementation, no local8 optimization or hidden ring pricing.
    All arithmetic executes under the active scalar budget, including conversion.
    """
    from math import factorial
    from src.core.formulas import original_scaled_hermite
    coordinates=tuple(coordinates); variance=_rational(sigma2)
    if variance<=0 or type(degree_bound)is not int or degree_bound<0:
        raise ValueError('positive variance and explicit global degree bound required')
    source=Polynomial.coerce(source)
    if any(not any(s in coordinates for s in k) for k,v in source.terms):
        raise ValueError('source must have zero X-constant coefficient')
    x=tuple(Polynomial.variable(s) for s in coordinates)
    exponent=source-sum((a*a*variance*Fraction(1,2) for a in x),Polynomial())
    power=Polynomial.scalar(1); truncated=power
    for n in range(1,degree_bound+1):
        power=polynomial_degree_truncate(power*exponent,coordinates,degree_bound)
        if not power:break
        truncated+=power*Fraction(1,checked_factorial(n))
    result=Polynomial()
    for key,coefficient in truncated.terms:
        eta=tuple(key.count(s) for s in coordinates)
        rest=tuple(s for s in key if s not in coordinates)
        term=Polynomial(((rest,coefficient),))
        for coordinate,degree in zip(coordinates,eta):
            h=Symbol('h',coordinate.index)
            term*=Polynomial(tuple(((h,)*d,QComplex(rational_product(c,rational_inverse(rational_power(variance,degree))))) for d,c in original_scaled_hermite(degree,variance)))
        result+=term
    return result


def _validate_source_roster(roster):
    if len(set(roster))!=len(roster):raise ValueError('source roster must have unique monomials')
    for key in roster:
        if not isinstance(key,tuple) or any(not isinstance(s,Symbol) or s.family not in ('J','H') for s in key) or key!=tuple(sorted(key)):
            raise ValueError('source roster requires canonical J/H monomials')


@dataclass(frozen=True,slots=True)
class SupportCertificate:
    """Exact declared domain and complete requested roster, not a nonzero claim."""
    scope:str
    source_multiindices:tuple
    grading:SourceFamilyGrading
    complete:bool
    generator_order:tuple
    link_order:tuple

    def __post_init__(self):
        if not isinstance(self.grading,SourceFamilyGrading): raise TypeError('typed immutable source grading required')
        for name in ('source_multiindices','generator_order','link_order'):
            object.__setattr__(self,name,_freeze_exact_metadata(getattr(self,name)))
        _validate_source_roster(self.source_multiindices)
        if not isinstance(self.scope,str) or not self.scope or type(self.complete)is not bool:
            raise ValueError('explicit support scope and completeness required')


@dataclass(frozen=True,slots=True)
class CoefficientRequest:
    coupling_powers:tuple|None
    source_multiindices:tuple
    insertion_id:str
    complete_support_certificate:SupportCertificate

    def __post_init__(self):
        if self.coupling_powers is not None:
            object.__setattr__(self,'coupling_powers',_freeze_exact_metadata(self.coupling_powers))
            if any(len(k)!=2 or any(type(i)is not int or i<0 for i in k) for k in self.coupling_powers):
                raise ValueError('nonnegative exact coupling roster required')
        object.__setattr__(self,'source_multiindices',_freeze_exact_metadata(self.source_multiindices))
        _validate_source_roster(self.source_multiindices)
        if not isinstance(self.complete_support_certificate,SupportCertificate): raise TypeError('typed immutable support certificate required')
        if not isinstance(self.insertion_id,str) or not self.insertion_id:
            raise ValueError('explicit insertion identity required')


@dataclass(frozen=True,slots=True)
class UnnormalizedResult:
    Z:object
    N:tuple
    support:SupportCertificate
    cost:tuple
    convention:OriginalRegulator


def contract_original(reg,factors,request,budget,denominator=None):
    """Exact direct finite exterior contraction. No partial return on refusal.

    factors are the FULL exponent summands and insertion/measure SourceJet.
    Requesting a selected coefficient never certifies unrequested full Z.
    """
    if not isinstance(request,CoefficientRequest) or not request.complete_support_certificate.complete:
        raise ValueError('complete source/support roster required')
    certificate=request.complete_support_certificate
    if certificate.generator_order!=reg.generator_order or certificate.link_order!=reg.link_order:
        raise ValueError('support certificate must bind the exact original carrier/anchors')
    source=factors
    if not isinstance(source,SourceJet):raise TypeError('complete action/insertion/measure SourceJet required')
    if request.insertion_id!=source.insertion_id:raise ValueError('support insertion identity must bind actual source')
    if certificate.source_multiindices!=request.source_multiindices:
        raise ValueError('support source roster must match request exactly; empty means all sources')
    if certificate.grading!=source.grading:
        raise ValueError('support grading must bind actual source/action/insertion/measure')
    for _,terms in source.grading.entries:
        for term in terms:
            if term.exterior_mask is not None:
                if term.exterior_mask >> len(reg.generator_order): raise ValueError('grading outside original carrier')
                actual=tuple(v for i,v in enumerate(reg.generator_order) if term.exterior_mask>>i&1)
                if term.support.generators!=actual: raise ValueError('grading generator support mismatch')
            if any(a not in reg.link_order for a in term.support.anchors): raise ValueError('grading anchor support mismatch')
            if term.support.sites!=tuple(sorted(set(g[0] for g in term.support.generators))): raise ValueError('grading site support mismatch')

    with budget:
        zero=ExteriorPolynomial(); one=ExteriorPolynomial(((0,Polynomial.scalar(1)),))
        power=RawJet.constant(one,source.labels); exp=power
        from math import factorial
        for k in range(1,4*reg.volume+1):
            power=power*source.action
            exp+=power*Fraction(1,checked_factorial(k))
            budget.check_storage((source,power,exp))
        raw=source.insertion*exp*source.measure
        top=(1<<(8*reg.volume))-1
        def integrate(v):
            if isinstance(v,ExteriorPolynomial):return haar_polynomial(dict(v.terms).get(top,Polynomial()))
            raise ValueError('insertion/action pullback must retain exterior carrier')
        entries=[]
        for k in raw.indices():
            if len(k)>source.order:continue
            value=integrate(raw.at(k))
            value=extract_requested_coefficients(value,request)
            entries.append((k,value))
        z=Unknown('complete denominator not separately computed') if denominator is None else denominator
        return UnnormalizedResult(z,tuple(entries),request.complete_support_certificate,(('products',budget.products),('peak_payload_bytes',budget.peak_payload_bytes)),reg)


def extract_requested_coefficients(poly,request):
    """Roster extraction keeps explicit zero slots; unknown support is refused."""
    entries=[]
    for key,value in poly.terms:
        sources=tuple(s for s in key if s.family in ('J','H'))
        if request.source_multiindices and sources not in request.source_multiindices:continue
        if request.coupling_powers is not None:
            powers=tuple(sum(s.family==g for s in key) for g in ('g1','g2'))
            if powers not in request.coupling_powers:continue
        entries.append((key,value))
    return Polynomial(tuple(entries))


def exterior_phase_derivative(poly,reg,charges):
    """Exact local U(1) generator on every original bar/psi; shared sites kept."""
    out=[]
    for mask,value in poly.terms:
        charge=Fraction()
        for i,(x,kind,_) in enumerate(reg.generator_order):
            if mask>>i&1:
                q=_rational(charges[x])
                # A generator's fixed sign changes no width or product unit.
                charge=rational_add(charge,q if kind=='psi' else -q)
        out.append((mask,value*QComplex(0,charge)))
    return ExteriorPolynomial(tuple(out))


def apply_linear_map_jet(jet,operation):
    return RawJet(jet.labels,tuple((k,operation(v)) for k,v in jet.entries))


def source_polynomial_jets(poly,variables):
    """Full first/second raw derivative polynomials at arbitrary supplied source."""
    from itertools import combinations_with_replacement
    variables=tuple(variables)
    return (tuple(polynomial_derivative(poly,s) for s in variables),
            tuple(raw_derivative(poly,(variables[i],variables[j])) for i,j in combinations_with_replacement(range(len(variables)),2)))


def multiindices(labels,degree):
    from itertools import combinations_with_replacement
    return tuple(combinations_with_replacement(range(labels),degree))


def monomial_factorial(key):
    from math import factorial
    out=1
    for k in set(key):out=checked_integer_product(out,checked_factorial(key.count(k)))
    return out


def direction_center_even(key):
    return all(sum(i//4==mu for i in key)%2==0 for mu in range(4))


@lru_cache(maxsize=256)
def _quaternion_group_moment(powers):
    from src.core.formulas import original_quaternion_haar_moment
    return rational_product_all(original_quaternion_haar_moment(p) for p in powers)


def quaternion_key_moment(key):
    groups={}
    for s in key:
        if s.family!='q' or len(s.index)!=4 or type(s.index[-1])is not int or s.index[-1] not in range(4):raise ValueError('pure original quaternion key required')
        group=groups.setdefault(s.index[:-1],[0]*4)
        group[s.index[-1]]+=1
    if any(k%2 for powers in groups.values() for k in powers):return Fraction()
    # Exchange equal normalized independent-factor kernels only after grouping
    # by the full site/anchor/chirality identity. A repeated anchor is ONE group.
    return _rational(_quaternion_group_moment(tuple(sorted(tuple(sorted(v)) for v in groups.values()))))


def integrated_polynomial_product(a,b,sign=1):
    """Complete shared-link Haar contraction, bucketed by exact moment.

    Every surviving coefficient pair multiplies once; equal rational moments
    share ONE final scaling after exact signed accumulation. No source, link or
    coefficient is independently averaged or omitted.
    """
    buckets={}
    for ka,va in a.terms:
        for kb,vb in b.terms:
            moment=quaternion_key_moment(ka+kb)
            if moment:
                term=va*vb
                if sign==-1:term=-term
                elif sign!=1:term=term*sign
                buckets[moment]=buckets.get(moment,QComplex())+term
    result=QComplex()
    for moment,total in buckets.items(): result+=total*moment
    return result


def integrated_exterior_complements(a,b,top=255):
    """Full oriented top pairing, shared fermion carrier; no independent-site lie."""
    result=QComplex(); right=dict(b.terms)
    for ka,va in a.terms:
        kb=top^ka
        if ka&~top or kb not in right:continue
        swaps=sum((kb&((1<<i)-1)).bit_count() for i in range(ka.bit_length()) if ka>>i&1)
        result+=integrated_polynomial_product(va,right[kb],(-1)**swaps)
    return result


def direct_one_site_tensor(coframes,budget):
    """136 complete exterior pairs -> all 3876 quartics; 3136 center certificates."""
    reserve_scalar_records(budget,400_000,coframes)
    pairs={key:coframes[key[0]]*coframes[key[1]] for key in multiindices(16,2)}
    budget.check_storage((coframes,pairs),additional_records=20_000)
    tensor={}
    for key in multiindices(16,4):
        if direction_center_even(key):
            tensor[key]=integrated_exterior_complements(pairs[key[:2]],pairs[key[2:]])*Fraction(1,monomial_factorial(key))
        else:tensor[key]=QComplex()
    budget.check_storage((pairs,tensor),additional_records=20_000)
    return tensor


def determinant_one_site_tensor(matrices,budget):
    """Two actual signed 2x2 determinants, independently of exterior pair route."""
    reserve_scalar_records(budget,55_000,matrices)
    pairs=[]
    for rows,cols in (((0,1),(2,3)),((2,3),(0,1))):
        table={}
        a,b=rows; c,d=cols
        for key in multiindices(16,2):
            i,j=key
            value=matrices[i].at(a,c)*matrices[j].at(b,d)-matrices[i].at(a,d)*matrices[j].at(b,c)
            if i!=j:value+=matrices[j].at(a,c)*matrices[i].at(b,d)-matrices[j].at(a,d)*matrices[i].at(b,c)
            table[key]=value
        pairs.append(table)
    budget.check_storage((matrices,pairs),additional_records=20_000)
    tensor={}
    for key in multiindices(16,4):
        value=QComplex()
        if direction_center_even(key):
            # All distinct multiset splits, not six copies on repeated labels.
            for left in sorted(set(tuple(key[i] for i in chosen) for chosen in __import__('itertools').combinations(range(4),2))):
                remaining=list(key)
                for i in left:remaining.remove(i)
                value+=integrated_polynomial_product(pairs[0][left],pairs[1][tuple(remaining)])
        tensor[key]=value
    return tensor


@dataclass(frozen=True,slots=True)
class FactoredWeightTerm:
    """One RAW P4 summand; quaternion factors stay shared and unexpanded."""
    eta:tuple
    scalar:Fraction
    curvature:tuple=()
    coupling:tuple=()
    frame_directions:tuple=()
    origin:str='constant'

    def __post_init__(self):
        for name in ('eta','curvature','coupling','frame_directions'):
            object.__setattr__(self,name,_freeze_exact_metadata(getattr(self,name)))
        object.__setattr__(self,'scalar',_rational(self.scalar))
        if any(type(i)is not int or i not in range(16) for i in self.eta):
            raise ValueError('W exponent labels require original16 components')
        if any(type(i)is not int or i not in range(4) for i in self.frame_directions):
            raise ValueError('W frame directions require original four axes')


def one_site_weight_terms(action_quadratic,action_quartic,variance):
    """Complete 4029 raw P/Hermite summands, compensation retained."""
    quadratic=[FactoredWeightTerm(k,Fraction(1),(k,),('g2',),tuple(i//4 for i in k),'action2') for k in sorted(action_quadratic)]
    quadratic.extend(FactoredWeightTerm((i,i),rational_product(-variance,Fraction(1,2)),(),(),(),'compensation') for i in range(16))
    terms=[FactoredWeightTerm((),Fraction(1))]+quadratic
    for i,a in enumerate(quadratic):
        for j in range(i,len(quadratic)):
            b=quadratic[j]
            terms.append(FactoredWeightTerm(tuple(sorted(a.eta+b.eta)),rational_product(rational_product(a.scalar,b.scalar),(Fraction(1,2) if i==j else 1)),a.curvature+b.curvature,a.coupling+b.coupling,a.frame_directions+b.frame_directions,'quadratic_square'))
    terms.extend(FactoredWeightTerm(k,c,(),('g1',),tuple(i//4 for i in k),'action4') for k,c in action_quartic)
    return tuple(terms)


def gaussian_compatible_queries(term):
    """Complete raw 23504-query schedule per word/variance, including zeros."""
    eta=term.eta
    if len(eta)==4:
        yield eta,()
    elif len(eta)==2:
        for source in multiindices(16,2):yield eta,source
        for i in range(16):yield tuple(sorted(eta+(i,i))),()
    elif not eta:
        for source in multiindices(16,4):yield (),source
        for i in range(16):
            for source in multiindices(16,2):yield (i,i),source
        for a,b in multiindices(16,2):yield tuple(sorted((a,a,b,b))),()
    else:raise ValueError('P4 term must have even degree at most four')


def count_hermite_contraction(eta,beta,variance):
    """Sparse version of the independently checked polynomial moment kernel."""
    from math import factorial
    result=Fraction(1)
    for i in set(eta+beta):
        a,b=eta.count(i),beta.count(i)
        if b<a or (b-a)%2:return Fraction()
        t=(b-a)//2
        denominator=checked_integer_product(checked_integer_power(2,t),checked_factorial(t))
        factor=_rational(Fraction(checked_factorial(b),denominator))
        result=rational_product(result,rational_product(rational_power(variance,t),factor))
    return result


def shifted_monomial_binomial(total,beta):
    out=1
    for i in set(total):
        n,k=total.count(i),beta.count(i)
        if k>n:return 0
        k=min(k,n-k);coefficient=1
        for j in range(1,k+1):coefficient=checked_integer_product(coefficient,n-k+j)//j
        out=checked_integer_product(out,coefficient)
    return out


def frame_product_jet(directions,frames):
    value=RawJet.constant(Polynomial.scalar(1))
    for mu in directions:value=value*frames[mu]
    return value


def literal_metric_source_polynomial(z,linear_sources,metric_sources):
    """exp(H sum_A dJ_muA dJ_nuA)Z; independent offdiagonal H occurs ONCE."""
    out=z; current=z
    from itertools import combinations_with_replacement
    pairs=tuple(combinations_with_replacement(range(4),2))
    for n in range(1,3):
        nxt=Polynomial()
        for h,(mu,nu) in zip(metric_sources,pairs):
            lap=sum((raw_derivative(current,(linear_sources[4*mu+a],linear_sources[4*nu+a])) for a in range(4)),Polynomial())
            nxt+=lap*Polynomial.variable(h)
        current=nxt*Fraction(1,n)
        out+=current
    return out


def logarithmic_response(partition,certificate):
    """Connected first/second logZ derivatives; value requires a local log branch."""
    if isinstance(partition,Unknown):raise ValueError('UNKNOWN denominator cannot define logZ')
    z=_scalar_value(partition.at(()))
    if not isinstance(certificate,NonzeroZCertificate) or certificate.value!=z:
        raise ValueError('matching nonzero Z certificate required for logZ')
    inv=scalar_inverse(z); out=[]
    for k in partition.indices()[1:]:
        v=_scalar_value(partition.at(k))*inv
        if len(k)==2:v-=_scalar_value(partition.at((k[0],)))*_scalar_value(partition.at((k[1],)))*inv*inv
        out.append((k,v))
    return Unknown('logZ value requires an explicit local branch'),tuple(out)


def scalar_product(*values):
    """Count each expanded exact scalar coefficient product (including zeros)."""
    out=QComplex(1)
    for value in values:
        out*=value
    return out


def reserve_scalar_records(budget,records,*live):
    """Reserve future packed scalar payload BEFORE allocating a bounded map."""
    if type(records)is not int or records<0:raise ValueError('nonnegative scalar record reservation required')
    return budget.check_storage(live,additional_records=records)


def reserve_original_n16_records(budget, records, *live):
    """Check actual retained state plus the next bounded N16 allocation."""
    reserve_scalar_records(budget, records, *live)
    if budget.peak_scalar_records > 120_000:
        raise BudgetExceeded('original N16 record limit exceeded')


@dataclass(frozen=True, slots=True)
class DirectPolarEdge:
    """Complete six-by-six literal and dual-basis tables of one direct edge."""

    labels: tuple
    local_pairing: tuple
    radial_moments: tuple
    cubic_x_tests: tuple
    cubic_mixed_tests: tuple
    cubic_x: tuple
    cubic_mixed: tuple
    fourth_top: QComplex
    attempted_wedge_pairs: int


def _pack_radial_edge_coframe(coframe):
    out = {}
    for mask, polynomial in coframe.terms:
        for key, value in polynomial.terms:
            if len(key) != 1 or not _is_polar_radial(key[0].family, key[0].index):
                raise ValueError('one real radial symbol per polar coframe term required')
            chi = key[0].index
            if mask.bit_count() != 2 or (mask & 255).bit_count() != 1 or mask >= 1 << 16:
                raise ValueError('polar coframe must use one generator from each endpoint')
            # Packed 16-bit exterior mask and two 4-bit radial exponents.
            out[(mask << 8) | (16 if chi == ('L',) else 1)] = value
    return out


def _reserve_edge_records(budget, additional_records, *live_maps, retained=()):
    # Count occupied coefficient slots separately from the unique Python
    # scalar objects counted by ExactBudget.check_storage.
    unique_maps = {id(table): table for table in live_maps}
    occupied = sum(len(table) for table in unique_maps.values()) + additional_records
    if occupied > 55_000:
        raise BudgetExceeded('direct edge record limit exceeded: incomplete coefficient control')
    reserve_original_n16_records(budget, additional_records, *unique_maps.values(), *retained)
    budget.peak_scalar_records = max(budget.peak_scalar_records, occupied)


def _edge_wedge_negative(left, right):
    swaps = 0
    while left:
        low_bit = left & -left
        swaps += (right & (low_bit - 1)).bit_count()
        left ^= low_bit
    return swaps % 2


def _edge_wedge_accumulate(out, left, right, *, max_records):
    """Coalesce signed products immediately inside a previously reserved map."""
    for left_key, av in left.items():
        a = left_key >> 8
        for right_key, bv in right.items():
            b = right_key >> 8
            if a & b:
                continue
            # The callers join homogeneous layers of total radial degree at
            # most eight. Neither exponent can carry into its neighbor.
            key = ((a | b) << 8) | ((left_key & 255) + (right_key & 255))
            term = av * bv
            if _edge_wedge_negative(a, b):
                term = -term
            prior = out.get(key)
            if prior is not None:
                term = prior + term
            if term:
                if prior is None and len(out) >= max_records:
                    raise BudgetExceeded('reserved edge map record limit exceeded')
                out[key] = term
            elif prior is not None:
                del out[key]


def _edge_invariant_basis():
    """Literal n, b, p two-forms and their six-form dual roster at each end."""
    labels = tuple((chi, kind) for chi in ('L', 'R') for kind in ('n', 'b', 'p'))

    def forms(site_offset):
        g = ExteriorPolynomial.generator
        out, tops = [], []
        for start in (site_offset, site_offset + 4):
            b1, b2, p1, p2 = (g(start + j) for j in range(4))
            out.extend((b1 * p1 + b2 * p2, b1 * b2, p1 * p2))
            tops.append(b1 * b2 * p1 * p2)
        return out, tops

    def scalar_terms(form):
        return {mask: _scalar_value(poly) for mask, poly in form.terms}

    x, x_tops = forms(0)
    y, _ = forms(8)
    beta = tuple(x_tops[1 - i // 3] * form for i, form in enumerate(x))
    pairing = tuple(tuple(scalar_terms(a * b).get(255, QComplex()) for b in x)
                    for a in beta)
    tests = tuple(tuple(scalar_terms(a * b) for b in y) for a in x)
    return labels, pairing, tests


def _radial_edge_top_integral(layer, test, degree, moments):
    """Contract all oriented complements, then average the even radial powers."""
    top = (1 << 16) - 1
    radial = {}
    for test_mask, test_scalar in test.items():
        complement = top ^ test_mask
        negative = _edge_wedge_negative(complement, test_mask)
        for l in range(degree + 1):
            key = l, degree - l
            coefficient = layer.get((complement << 8) | (l << 4) | key[1])
            if coefficient is not None:
                term = coefficient * test_scalar
                radial[key] = radial.get(key, QComplex()) + (-term if negative else term)
    total = QComplex()
    for (l, r), value in radial.items():
        if value:
            if l % 2 or r % 2:
                raise ValueError('nonvanishing odd radial power in invariant edge test')
            total += value * moments[l // 2] * moments[r // 2]
    return total


@dataclass(frozen=True, slots=True)
class AuxiliaryPolarEdge:
    """Complete local auxiliary edge evidence in literal and dual bases."""

    labels: tuple
    local_pairing: tuple
    radial_moments: tuple
    cubic_x_tests: tuple
    cubic_mixed_tests: tuple
    cubic_x: tuple
    cubic_mixed: tuple
    fourth_top: QComplex
    minor_counts: tuple
    empty_test_counts: tuple


_AUXILIARY_POLAR_EXP_BITS = 40
_AUXILIARY_POLAR_EXP_MASK = (1 << _AUXILIARY_POLAR_EXP_BITS) - 1
_AUXILIARY_POLAR_FIXED_RECORDS = 4096


def _auxiliary_polar_powers(key):
    return tuple((key >> (4 * index)) & 15 for index in range(10))


def _auxiliary_polar_rows(reg, *, mixed):
    """Sparse h/k coefficient rows for the original two-endpoint blocks."""
    rows = [dict() for _ in range(8)]
    for a, gamma in enumerate(reg.gamma):
        h = 1 << (4 * a)
        k = 1 << (4 * (4 + a))
        for i, row in enumerate(gamma):
            for j, value in enumerate(row):
                if not value:
                    continue
                d_i = 1 << (4 * (8 + i // 2))
                d_j = 1 << (4 * (8 + j // 2))
                q = _scalar_value(value) * Fraction(1, 4)
                xy = ((h + d_j, q),)
                yx = ((h + d_i, -q),)
                if mixed:
                    xy += ((k + d_i, q),)
                    yx += ((k + d_j, -q),)
                rows[i].setdefault(4 + j, []).extend(xy)
                rows[4 + i].setdefault(j, []).extend(yx)
    if any(sum(map(len, row.values())) > 16 for row in rows):
        raise ValueError('original auxiliary row exceeded the reviewed monomial bound')
    return tuple(tuple((col, tuple(terms)) for col, terms in sorted(row.items()))
                 for row in rows)


def _auxiliary_polar_minor_roster(rows, x_label, y_label):
    """Derive ordered insertion signs and prove missing perfect matchings."""
    def insertions(label, offset):
        chirality, kind = divmod(label, 3)
        first = offset + 2 * chirality
        pair = first, first + 1
        if kind == 0:
            return tuple(((i,), (i,)) for i in pair)
        return ((pair, ()),) if kind == 1 else (((), pair),)

    def can_match(bars, psis):
        removed = sum(1 << j for j in psis)
        reachable = {removed}
        for i, row in enumerate(rows):
            if i in bars:
                continue
            reachable = {mask | (1 << j) for mask in reachable for j, _ in row
                         if not mask & (1 << j)}
            if not reachable:
                return False
        return (1 << len(rows)) - 1 in reachable

    roster = []
    for xb, xp in insertions(x_label, 0):
        for yb, yp in insertions(y_label, 4):
            bars, psis = xb + yb, xp + yp
            if len(bars) != len(psis) or not can_match(bars, psis):
                continue
            # Move x psis past y bars, then use the ordinary signed
            # complementary determinant in the original orientation.
            swaps = len(xp) * len(yb) + len(bars) * (len(bars) - 1) // 2
            sign = (-1) ** (swaps + sum(bars) + sum(psis))
            roster.append((bars, psis, sign))
    return tuple(roster)


def _auxiliary_polar_minor_rows(rows, bars, psis):
    kept_cols = {j: new for new, j in enumerate(j for j in range(8) if j not in psis)}
    return tuple(tuple((kept_cols[j], terms) for j, terms in row if j in kept_cols)
                 for i, row in enumerate(rows) if i not in bars)


def _auxiliary_polar_determinant(rows, auxiliary_count, budget, *, _retained=()):
    """Row-subset recurrence with both adjacent scalar maps reserved.

    Row entries have one auxiliary and one radial factor per monomial.
    Four-bit fields therefore add without carry at order at most eight.
    Returns the terminal packed exponents, with the known column mask.
    """
    from math import comb

    n = len(rows)
    shift = _AUXILIARY_POLAR_EXP_BITS

    def reserve(states, additional):
        prospective = len(states) + additional + _AUXILIARY_POLAR_FIXED_RECORDS
        if prospective > 120_000:
            raise BudgetExceeded('auxiliary edge record limit exceeded: incomplete coefficient control')
        reserve_original_n16_records(
            budget, additional + _AUXILIARY_POLAR_FIXED_RECORDS, states, rows, *_retained,
        )
        budget.peak_scalar_records = max(budget.peak_scalar_records, prospective)

    reserve({}, 1)
    states = {0: QComplex(1)}
    for degree, row in enumerate(rows, 1):
        next_limit = comb(n, degree) * comb(degree + auxiliary_count - 1,
                                            auxiliary_count - 1) * (degree + 1)
        reserve(states, next_limit)
        nxt = {}
        for packed, value in states.items():
            mask = packed >> shift
            powers = packed & _AUXILIARY_POLAR_EXP_MASK
            for column, terms in row:
                bit = 1 << column
                if mask & bit:
                    continue
                negative = (mask >> (column + 1)).bit_count() % 2
                next_mask = (mask | bit) << shift
                for exponent, coefficient in terms:
                    product = value * coefficient
                    if negative:
                        product = -product
                    key = next_mask | (powers + exponent)
                    prior = nxt.get(key)
                    if prior is not None:
                        product = prior + product
                    if product:
                        if prior is None and len(nxt) >= next_limit:
                            raise BudgetExceeded('auxiliary determinant layer exceeded its reservation')
                        nxt[key] = product
                    elif prior is not None:
                        del nxt[key]
        states = nxt
        if not states:
            return {}
    # The final row-subset mask is fixed. Reserve enough capacity for the
    # terminal exponent-only copy before making it.
    reserve(states, len(states))
    return {key & _AUXILIARY_POLAR_EXP_MASK: value for key, value in states.items()}


def _auxiliary_polar_project(terms, degrees, sign, radial, moments):
    from src.core.formulas import original_gaussian_moment

    for key, value in terms.items():
        powers = _auxiliary_polar_powers(key)
        h, k = powers[:4], powers[4:8]
        if (sum(h), sum(k)) != degrees or any(power % 2 for power in h + k):
            continue
        if (h, k) not in moments:
            moments[h, k] = original_gaussian_moment(h + k, 1)
        radial_key = powers[8:]
        term = value * moments[h, k]
        radial[radial_key] = radial.get(radial_key, QComplex()) + (-term if sign < 0 else term)


def _auxiliary_polar_average(radial, moments, factorial_scale):
    total = QComplex()
    for (left, right), value in radial.items():
        if not value:
            continue
        if left % 2 or right % 2:
            raise ValueError('nonvanishing odd radial power in invariant auxiliary edge test')
        total += value * moments[left // 2] * moments[right // 2]
    return total * factorial_scale


def _auxiliary_polar_radial_moments():
    from math import comb
    from src.core.formulas import original_quaternion_haar_moment

    moments = []
    for k in range(5):
        total = Fraction()
        for j in range(k + 1):
            coefficient = checked_integer_product(comb(k, j), checked_integer_product(
                checked_integer_power(2, k - j), checked_integer_power(-2, j),
            ))
            term = rational_product(coefficient, original_quaternion_haar_moment((j, 0, 0, 0)))
            total = rational_add(total, term)
        moments.append(total)
    return tuple(moments)


def _auxiliary_polar_cubic(rows, degrees, moments, budget, *, _retained=()):
    results, minor_count, empty_count = [], 0, 0
    gaussian = {}
    scale = checked_integer_power(2, 3)
    for degree in degrees:
        scale = checked_integer_product(scale, checked_factorial(degree // 2))
    for x_label in range(6):
        result_row = []
        for y_label in range(6):
            roster = _auxiliary_polar_minor_roster(rows, x_label, y_label)
            empty_count += int(not roster)
            radial = {}
            for bars, psis, sign in roster:
                minor_count += 1
                live = (*_retained, rows, moments, results, result_row, roster, radial, gaussian)
                reserve_original_n16_records(budget, _AUXILIARY_POLAR_FIXED_RECORDS, *live)
                minor = _auxiliary_polar_minor_rows(rows, bars, psis)
                terms = _auxiliary_polar_determinant(
                    minor, 8 if degrees[1] else 4, budget, _retained=live,
                )
                reserve_original_n16_records(budget, _AUXILIARY_POLAR_FIXED_RECORDS, terms, *live)
                _auxiliary_polar_project(terms, degrees, sign, radial, gaussian)
                del terms, minor, live
            result_row.append(_auxiliary_polar_average(radial, moments, scale))
        results.append(tuple(result_row))
    if (minor_count, empty_count) != (12, 30):
        raise ValueError('original auxiliary edge support or ordinary minor roster changed')
    return tuple(results), minor_count, empty_count


def _auxiliary_polar_basis():
    # In each chirality n∧n = −2 Θ and b∧p = p∧b = Θ in the
    # local bar-bar-psi-psi orientation. Mixed chirality pairings vanish.
    labels = tuple((chi, kind) for chi in ('L', 'R') for kind in ('n', 'b', 'p'))
    local = ((-2, 0, 0), (0, 0, 1), (0, 1, 0))
    pairing = tuple(tuple(QComplex(local[i % 3][j % 3] if i // 3 == j // 3 else 0)
                          for j in range(6)) for i in range(6))
    return labels, pairing


def _auxiliary_polar_dual(literal, pairing):
    inverse = legendre_local(pairing, tuple(range(6)))
    return tuple(tuple(sum((inverse[a][c] * literal[a][b] * inverse[b][d]
                            for a in range(6) for b in range(6)
                            if inverse[a][c] and literal[a][b] and inverse[b][d]),
                           QComplex()) for d in range(6)) for c in range(6))


def _freeze_exact_metadata(value):
    """Freeze source/weight rosters, retaining the existing immutable Symbol."""
    if isinstance(value,Symbol):return value
    if isinstance(value,(tuple,list)):
        return tuple(_freeze_exact_metadata(v) for v in value)
    return _freeze_label(value)
