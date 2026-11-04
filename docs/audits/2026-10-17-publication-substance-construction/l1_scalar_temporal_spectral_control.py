"""Finite transfer-spectrum control for the periodic free scalar shear probe."""

from fractions import Fraction
from itertools import product
from math import asinh, cos, exp, isclose, pi, sin, sinh, sqrt


def exact_two_slice():
    """Return the connected covariances and local bare contact per spatial site."""
    connected = [Fraction(), Fraction()]
    contact = Fraction()
    for p1, p2, p3 in product((0, 4), repeat=3):
        mass_squared = 1 + p1 + p2 + p3
        for t in range(2):
            propagator = (Fraction(1, mass_squared)
                          + Fraction((-1)**t, mass_squared + 4)) / 2
            connected[t] += Fraction((p3 - p2)**2, 4) * propagator**2
        for p0 in (0, 4):
            contact += Fraction(1, 4) - Fraction(p2 + p3, 2 * (mass_squared + p0))
    return tuple(value / 8 for value in connected), contact / 16


def transfer_energy(mass_squared, time_spacing):
    return 2 * asinh(time_spacing * sqrt(mass_squared) / 2) / time_spacing


def shear_terms(gap, weight, beta, tau):
    """Static and dynamical terms for a single squared propagator."""
    thermal_factor = 0 if beta is None else exp(-gap * beta / 2)
    backward = 0 if beta is None else exp(-gap * (beta - tau))
    factor = weight / (1 - thermal_factor)**2
    return 2 * thermal_factor * factor, (exp(-gap * tau) + backward) * factor


def check_transfer(slices):
    """Compare transfer formulas to direct lattice Fourier sums."""
    spacing = 0.7
    beta = slices * spacing
    for p1, p2, p3 in product((0, 4), repeat=3):
        mass_squared = 1 + p1 + p2 + p3
        denominators = [mass_squared + (2 * sin(pi * n / slices) / spacing)**2
                        for n in range(slices)]
        energy = transfer_energy(mass_squared, spacing)
        gap = 2 * energy
        amplitude = spacing / (2 * sinh(spacing * energy))
        shear_factor = (p3 - p2)**2 / 4
        weight = shear_factor * amplitude**2
        finite_time_sum = 0
        for t in range(slices):
            tau = t * spacing
            propagator = sum(complex_exp(t * n / slices) / denominator
                             for n, denominator in enumerate(denominators)) / beta
            assert abs(propagator.imag) < 1e-13
            static, dynamic = shear_terms(gap, weight, beta, tau)
            assert isclose(static + dynamic, shear_factor * propagator.real**2,
                           rel_tol=1e-11, abs_tol=1e-15)
            finite_time_sum += spacing * (static + dynamic)

        # Discrete Parseval identifies the zero-frequency connected sum.
        parseval = shear_factor * sum(1 / d**2 for d in denominators) / beta
        assert isclose(finite_time_sum, parseval, rel_tol=1e-11, abs_tol=1e-15)
        static, dynamic = shear_terms(gap, weight, None, spacing)
        assert static == 0 and dynamic == weight * exp(-gap * spacing)
        # Only nonzero weights contribute spectral lines.
        assert (weight > 0) == (p2 != p3)
        if weight:
            assert gap >= 2 * transfer_energy(5, spacing)


def complex_exp(turns):
    angle = 2 * pi * turns
    return complex(cos(angle), sin(angle))


def main():
    connected, contact = exact_two_slice()
    assert connected == (Fraction(11306, 342225), Fraction(776, 342225))
    assert sum(connected) == Fraction(12082, 342225)
    assert contact == Fraction(587, 13260)
    for slices in (2, 3, 7, 16):
        check_transfer(slices)
    print("2^4 per-site connected shear:", *connected)
    print("Per-site affine contact at coincident time:", contact)
    print("Transfer, finite-time sum, zero-temperature and absent-line controls passed")


if __name__ == "__main__":
    main()
