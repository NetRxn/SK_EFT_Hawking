"""Finite transfer-spectrum control for the periodic free scalar shear probe."""

from fractions import Fraction
from itertools import product
from math import asinh, cos, exp, isclose, pi, sin, sinh, sqrt


def exact_two_slice(staggered=False):
    """Return the connected covariances and local bare contact per spatial site."""
    connected = [Fraction(), Fraction()]
    contact = Fraction()
    for p1, p2, p3 in product((0, 4), repeat=3):
        mass_squared = 1 + p1 + p2 + p3
        for t in range(2):
            shifted_mass = mass_squared + (4 - 2 * p1 if staggered else 0)
            propagator = two_slice_propagator(mass_squared, t)
            shifted = two_slice_propagator(shifted_mass, t)
            connected[t] += Fraction((p3 - p2)**2, 4) * propagator * shifted
        for p0 in (0, 4):
            contact += Fraction(1, 4) - Fraction(p2 + p3, 2 * (mass_squared + p0))
    return tuple(value / 8 for value in connected), contact / 16


def two_slice_propagator(mass_squared, time):
    return (Fraction(1, mass_squared) + Fraction((-1)**time, mass_squared + 4)) / 2


def scalar_real_space_projection(staggered):
    """Project the Wick kernel over the eight spatial displacements."""
    propagator = [
        sum(Fraction((-1)**((p & r).bit_count()), 1 + 4 * p.bit_count())
            for p in range(16)) / 16
        for r in range(16)
    ]
    connected = [Fraction(), Fraction()]
    for r in range(16):
        def gradient_pair(i, j):
            return (propagator[r ^ i ^ j] - propagator[r ^ i]
                    - propagator[r ^ j] + propagator[r])

        kernel = (gradient_pair(4, 4)**2 + gradient_pair(8, 8)**2
                  - gradient_pair(4, 8)**2 - gradient_pair(8, 4)**2) / 4
        spatial_character = (-1)**((r >> 1) & 1) if staggered else 1
        connected[r & 1] += spatial_character * kernel
    return tuple(connected)


def check_staggered_controls():
    uniform, contact = exact_two_slice()
    staggered, staggered_contact = exact_two_slice(staggered=True)
    assert uniform == scalar_real_space_projection(False)
    assert staggered == scalar_real_space_projection(True)
    assert staggered == (Fraction(154, 5265), Fraction(8, 5265))
    assert staggered_contact == contact == Fraction(587, 13260)

    # Separate geometry regulator 2×2×1×1, closed ordering at g₂=1.
    # Same-site transfer at 04e107a2c and diagonal replay at 9d4012c47
    # with corrected receipt validation e41960619. Closed normalization
    # and conventions are in L1_RETARDED_SPECTRAL_INTERFACE.md.
    normalization = Fraction(1252309350145403, 2123366400)
    equal_time = Fraction(10179913, 32) / normalization
    half_period = Fraction(1171, 1024) / normalization
    assert half_period == Fraction(2428185600, 1252309350145403)

    inverse_secants = []
    for subtraction in (0, (equal_time - half_period) / 2):
        zero = equal_time - subtraction + half_period
        nyquist = equal_time - subtraction - half_period
        assert zero > nyquist > 0
        assert nyquist - zero == -2 * half_period
        # At unit temporal spacing the squared Nyquist momentum is 4.
        inverse_secants.append((1 / nyquist - 1 / zero) / 4)
    assert 0 < inverse_secants[0] < inverse_secants[1]
    print("2^4 staggered scalar connected shear:", *staggered)
    print("2×2×1×1 geometry: equal direct contrasts and distinct inverse secants")


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
    check_staggered_controls()
    print("2^4 per-site connected shear:", *connected)
    print("Per-site affine contact at coincident time:", contact)
    print("Transfer, finite-time sum, zero-temperature and absent-line controls passed")


if __name__ == "__main__":
    main()
