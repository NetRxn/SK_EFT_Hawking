"""Tests for fracton hydrodynamics Layer 2 (Phase 4, Item 2B).

Validates:
1. Fracton symmetry classification and multipole counting
2. Transport coefficient structure (Glorioso-Huang-Lucas)
3. SK axiom verification (normalization, positivity, KMS)
4. Dispersion relation: quadratic sound omega ~ k^2
5. Information retention: standard vs fracton hydro
6. Hilbert space fragmentation bounds
7. Gauge information assessment
8. Higher-multipole generalizations and upper critical dimensions
9. Cross-consistency between SK-EFT and information modules
"""

import pytest
import numpy as np
from math import comb, log2

from src.fracton.sk_eft import (
    ConservationType,
    MultipoleCharge,
    FractonSymmetry,
    FractonTransportCoefficients,
    FractonSKAction,
    FractonDispersionRelation,
    FractonSKAxiomCheck,
    classify_symmetry,
    compute_transport_coefficients,
    fracton_dispersion,
    verify_sk_axioms,
    upper_critical_dimension,
)
from src.fracton.information_retention import (
    StandardHydroInfo,
    FractonHydroInfo,
    FragmentationData,
    InformationComparison,
    GaugeInformationAssessment,
    GaugeInfoMechanism,
    GaugeCoarsegrainingResult,
    standard_hydro_charges,
    fracton_hydro_charges,
    information_ratio,
    hilbert_space_fragmentation,
    gauge_information_assessment,
    gauge_coarsegraining_example,
    compare_information_retention,
)


# ═══════════════════════════════════════════════════════════════════
# Multipole charges
# ═══════════════════════════════════════════════════════════════════

class TestMultipoleCharge:
    """Test multipole charge counting and classification."""

    def test_charge_is_order_zero(self):
        mc = MultipoleCharge(order=0, spatial_dim=3)
        assert mc.conservation_type == ConservationType.CHARGE
        assert mc.n_components == 1

    def test_dipole_is_order_one(self):
        mc = MultipoleCharge(order=1, spatial_dim=3)
        assert mc.conservation_type == ConservationType.DIPOLE
        assert mc.n_components == 3

    def test_quadrupole_is_order_two(self):
        mc = MultipoleCharge(order=2, spatial_dim=3)
        assert mc.conservation_type == ConservationType.QUADRUPOLE
        # Symmetric 2-tensor in 3D: C(4,2) = 6
        assert mc.n_components == 6

    def test_higher_multipole(self):
        mc = MultipoleCharge(order=5, spatial_dim=3)
        assert mc.conservation_type == ConservationType.MULTIPOLE

    def test_components_formula(self):
        """C(n + d - 1, n) components for rank-n symmetric tensor in d dims."""
        for d in [1, 2, 3, 4]:
            for n in range(6):
                mc = MultipoleCharge(order=n, spatial_dim=d)
                assert mc.n_components == comb(n + d - 1, n)

    def test_1d_components_always_one(self):
        """In 1D, every multipole has exactly 1 component."""
        for n in range(10):
            mc = MultipoleCharge(order=n, spatial_dim=1)
            assert mc.n_components == 1

    def test_negative_order_raises(self):
        with pytest.raises(ValueError, match="Multipole order"):
            MultipoleCharge(order=-1, spatial_dim=3)

    def test_zero_dim_raises(self):
        with pytest.raises(ValueError, match="Spatial dimension"):
            MultipoleCharge(order=0, spatial_dim=0)

    def test_label_format(self):
        mc = MultipoleCharge(order=1, spatial_dim=3)
        assert "dipole" in mc.label
        assert "3" in mc.label


# ═══════════════════════════════════════════════════════════════════
# Fracton symmetry
# ═══════════════════════════════════════════════════════════════════

class TestFractonSymmetry:
    """Test fracton symmetry classification."""

    def test_minimal_fracton_dipole(self):
        """Minimal fracton: charge + dipole conservation."""
        sym = classify_symmetry(max_multipole=1, spatial_dim=3)
        assert sym.charge_conservation
        assert sym.dipole_conservation
        assert sym.max_multipole_order == 1

    def test_charge_only(self):
        """Standard charge conservation only (not fracton)."""
        sym = classify_symmetry(max_multipole=0, spatial_dim=3)
        assert sym.charge_conservation
        assert not sym.dipole_conservation

    def test_total_multipole_charges_formula(self):
        """Total multipole charges = C(N + d, d)."""
        for d in [1, 2, 3]:
            for N in range(6):
                sym = classify_symmetry(max_multipole=N, spatial_dim=d)
                expected = comb(N + d, d)
                assert sym.total_multipole_charges == expected

    def test_3d_dipole_charges(self):
        """In 3D with dipole: C(1+3, 3) = 4 multipole charges."""
        sym = classify_symmetry(max_multipole=1, spatial_dim=3)
        assert sym.total_multipole_charges == 4  # 1 charge + 3 dipole

    def test_3d_quadrupole_charges(self):
        """In 3D with quadrupole: C(2+3, 3) = 10 multipole charges."""
        sym = classify_symmetry(max_multipole=2, spatial_dim=3)
        assert sym.total_multipole_charges == 10  # 1 + 3 + 6

    def test_total_with_momentum_energy(self):
        """Total conserved charges include momentum and energy."""
        sym = classify_symmetry(max_multipole=1, spatial_dim=3)
        # 4 multipole + 3 momentum + 1 energy = 8
        assert sym.total_conserved_charges == 8

    def test_dp_commutator_with_dipole_and_momentum(self):
        """[D, P] = iQ is active when both dipole and momentum are conserved."""
        sym = classify_symmetry(max_multipole=1, spatial_dim=3)
        assert sym.dp_commutator_nontrivial

    def test_dp_commutator_without_dipole(self):
        sym = classify_symmetry(max_multipole=0, spatial_dim=3)
        assert not sym.dp_commutator_nontrivial

    def test_dipole_requires_charge(self):
        """Dipole conservation requires charge conservation."""
        with pytest.raises(ValueError, match="charge conservation"):
            FractonSymmetry(
                charge_conservation=False,
                dipole_conservation=True,
                max_multipole_order=1,
            )

    def test_multipole_order_consistency(self):
        """max_multipole_order >= 1 implies dipole_conservation."""
        with pytest.raises(ValueError, match="dipole_conservation"):
            FractonSymmetry(
                charge_conservation=True,
                dipole_conservation=False,
                max_multipole_order=2,
            )

    def test_conserved_multipoles_list(self):
        sym = classify_symmetry(max_multipole=3, spatial_dim=2)
        multipoles = sym.conserved_multipoles
        assert len(multipoles) == 4
        assert multipoles[0].order == 0
        assert multipoles[3].order == 3


# ═══════════════════════════════════════════════════════════════════
# Transport coefficients
# ═══════════════════════════════════════════════════════════════════

class TestFractonTransportCoefficients:
    """Test Glorioso-Huang-Lucas transport coefficient structure."""

    def test_coefficient_counts(self):
        """4 dissipative + 2 Hall + 4 thermodynamic = 10 total."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym, temperature=1.0)
        assert coeffs.n_dissipative == 4
        assert coeffs.n_hall == 2
        assert coeffs.n_thermodynamic == 4
        assert coeffs.n_total == 10

    def test_positivity_constraint(self):
        """Dissipative coefficients must be >= 0."""
        sym = classify_symmetry(max_multipole=1)
        with pytest.raises(ValueError, match="s1"):
            FractonTransportCoefficients(
                s1=-1.0, s2=1.0, t1=1.0, t2=1.0,
                d1=0.0, d2=0.0, b=1.0,
                a1=1.0, a2=0.0, a3=0.0,
                symmetry=sym,
            )

    def test_hall_coefficients_sign_unconstrained(self):
        """Hall-like coefficients can be negative."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym, d1=-2.0, d2=-3.0)
        assert coeffs.d1 == -2.0
        assert coeffs.d2 == -3.0

    def test_inverse_temperature_positive(self):
        """Inverse temperature b = 1/T must be positive."""
        sym = classify_symmetry(max_multipole=1)
        with pytest.raises(ValueError, match="inverse temperature"):
            FractonTransportCoefficients(
                s1=1.0, s2=1.0, t1=1.0, t2=1.0,
                d1=0.0, d2=0.0, b=-1.0,
                a1=1.0, a2=0.0, a3=0.0,
                symmetry=sym,
            )

    def test_total_dissipation(self):
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(
            sym, s1=1.0, s2=2.0, t1=3.0, t2=4.0
        )
        assert coeffs.total_dissipation == 10.0

    def test_standard_hydro_comparison(self):
        """Standard first-order NS has 3 transport coefficients (eta, zeta, kappa).

        Fracton SK-EFT has 6 transport coefficients (4 dissipative + 2 Hall)
        at leading dissipative order: twice as many as standard hydro.
        """
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym)
        standard_transport = 3  # eta, zeta, kappa in standard 1st-order NS
        fracton_transport = coeffs.n_dissipative + coeffs.n_hall
        assert fracton_transport == 6
        assert fracton_transport == 2 * standard_transport


# ═══════════════════════════════════════════════════════════════════
# SK action
# ═══════════════════════════════════════════════════════════════════

class TestFractonSKAction:
    """Test the fracton SK effective action structure."""

    def test_field_content(self):
        """SK-EFT has doubled fields: X^i, phi_i, phi each in r and a."""
        sym = classify_symmetry(max_multipole=1, spatial_dim=3)
        coeffs = compute_transport_coefficients(sym)
        action = FractonSKAction(coefficients=coeffs)
        assert action.n_dynamical_fields == 2 * (3 + 3 + 1)  # 14

    def test_field_content_2d(self):
        sym = classify_symmetry(max_multipole=1, spatial_dim=2)
        coeffs = compute_transport_coefficients(sym)
        action = FractonSKAction(coefficients=coeffs)
        assert action.n_dynamical_fields == 2 * (2 + 2 + 1)  # 10

    def test_noise_lagrangian_positivity(self):
        """Noise Lagrangian is imaginary with correct sign (Im S >= 0)."""
        sym = classify_symmetry(max_multipole=1, spatial_dim=3)
        coeffs = compute_transport_coefficients(sym, s1=1.0, s2=1.0, t1=1.0, t2=1.0)
        action = FractonSKAction(coefficients=coeffs)

        E_a = np.array([1.0, 0.5, 0.3])
        DU_a = np.array([0.2, 0.1, 0.4])
        L_noise = action.lagrangian_noise(E_a, DU_a)
        # -i * beta * (positive terms) should give negative imaginary part
        # which means Im(S) = integral Im(L) >= 0 when L has factor -i
        assert np.imag(L_noise) < 0  # -i * positive = negative imaginary

    def test_symmetry_accessible(self):
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym)
        action = FractonSKAction(coefficients=coeffs)
        assert action.symmetry == sym


# ═══════════════════════════════════════════════════════════════════
# SK axioms
# ═══════════════════════════════════════════════════════════════════

class TestSKAxioms:
    """Test SK axiom verification for fracton SK-EFT."""

    def test_valid_coefficients_satisfy_all(self):
        """Valid positive coefficients satisfy all three SK axioms."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym)
        check = verify_sk_axioms(coeffs)
        assert check.normalization_satisfied
        assert check.positivity_satisfied
        assert check.kms_satisfied
        assert check.all_satisfied

    def test_normalization_always_true(self):
        """Normalization is structural: always holds by SK-EFT construction."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym)
        check = verify_sk_axioms(coeffs)
        assert check.normalization_satisfied

    def test_kms_always_true(self):
        """KMS is structural: L^(1) is derived from L^(2) by construction."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym)
        check = verify_sk_axioms(coeffs)
        assert check.kms_satisfied

    def test_zero_dissipation_still_valid(self):
        """Zero dissipation (all s, t = 0) still satisfies positivity."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(
            sym, s1=0.0, s2=0.0, t1=0.0, t2=0.0
        )
        check = verify_sk_axioms(coeffs)
        assert check.all_satisfied


# ═══════════════════════════════════════════════════════════════════
# Dispersion relation
# ═══════════════════════════════════════════════════════════════════

class TestFractonDispersion:
    """Test fracton dispersion relation: quadratic sound."""

    def test_quadratic_dispersion(self):
        """Fracton sound is quadratic: omega ~ k^2, not linear omega ~ k."""
        disp = FractonDispersionRelation(c2=1.0, gamma4=0.1, multipole_order=1)
        assert disp.dispersion_power == 2
        assert disp.damping_power == 4

    def test_dipole_dispersion_power(self):
        """Dipole conservation (n=1): omega ~ k^2."""
        disp = FractonDispersionRelation(c2=1.0, gamma4=0.1, multipole_order=1)
        assert disp.dispersion_power == 2

    def test_quadrupole_dispersion_power(self):
        """Quadrupole conservation (n=2): omega ~ k^3."""
        disp = FractonDispersionRelation(c2=1.0, gamma4=0.1, multipole_order=2)
        assert disp.dispersion_power == 3
        assert disp.damping_power == 6

    def test_general_dispersion_power(self):
        """n-pole conservation: omega ~ k^{n+1}."""
        for n in range(5):
            disp = FractonDispersionRelation(c2=1.0, gamma4=0.1, multipole_order=n)
            assert disp.dispersion_power == n + 1

    def test_omega_scaling(self):
        """omega(k) should scale as k^{n+1} for small k."""
        disp = FractonDispersionRelation(c2=1.0, gamma4=0.0, multipole_order=1)
        k1, k2 = 0.1, 0.2
        omega1 = abs(disp.omega(k1))
        omega2 = abs(disp.omega(k2))
        # omega ~ k^2 means omega(2k)/omega(k) = 4
        ratio = omega2 / omega1
        expected = (k2 / k1) ** 2
        assert abs(ratio - expected) < 1e-10

    def test_subdiffusive_damping(self):
        """Imaginary part of omega should scale as k^4 for dipole."""
        disp = FractonDispersionRelation(c2=0.0, gamma4=1.0, multipole_order=1)
        k = 0.5
        omega = disp.omega(k)
        assert np.real(omega) == 0.0
        assert np.imag(omega) < 0  # damping
        assert abs(np.imag(omega) - (-k**4)) < 1e-10

    def test_relaxation_timescale_scaling(self):
        """Relaxation time ~ lambda^{2(n+1)}: anomalously slow."""
        disp = FractonDispersionRelation(c2=1.0, gamma4=1.0, multipole_order=1)
        tau1 = disp.relaxation_timescale(1.0)
        tau2 = disp.relaxation_timescale(2.0)
        # For n=1: tau ~ lambda^4
        expected_ratio = (2.0 / 1.0) ** 4
        actual_ratio = tau2 / tau1
        assert abs(actual_ratio - expected_ratio) < 1e-6

    def test_from_transport_coefficients(self):
        """fracton_dispersion() correctly derives dispersion from coefficients."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym, s1=2.0, t1=3.0, a1=4.0)
        disp = fracton_dispersion(coeffs, charge_density=1.0)
        assert disp.c2 > 0
        assert disp.gamma4 > 0
        assert disp.multipole_order == 1

    def test_omega_array_input(self):
        """omega() should accept numpy arrays."""
        disp = FractonDispersionRelation(c2=1.0, gamma4=0.1, multipole_order=1)
        k_arr = np.linspace(0.1, 1.0, 10)
        omega_arr = disp.omega(k_arr)
        assert omega_arr.shape == (10,)


# ═══════════════════════════════════════════════════════════════════
# Upper critical dimension
# ═══════════════════════════════════════════════════════════════════

class TestUpperCriticalDimension:
    """Test upper critical dimension formula (Guo-Glorioso-Lucas)."""

    def test_standard_diffusion(self):
        """n=0 (standard charge conservation): d_c = 2."""
        assert upper_critical_dimension(0) == 2

    def test_dipole(self):
        """n=1 (dipole conservation, odd): d_c = 2*1 = 2."""
        assert upper_critical_dimension(1) == 2

    def test_quadrupole(self):
        """n=2 (quadrupole conservation, even): d_c = 2*(1+2) = 6."""
        assert upper_critical_dimension(2) == 6

    def test_octupole(self):
        """n=3 (odd): d_c = 2*3 = 6."""
        assert upper_critical_dimension(3) == 6

    def test_hexadecapole(self):
        """n=4 (even): d_c = 2*(1+4) = 10."""
        assert upper_critical_dimension(4) == 10

    def test_d_c_grows_unbounded(self):
        """d_c -> infinity as n -> infinity."""
        dims = [upper_critical_dimension(n) for n in range(20)]
        # Should be non-decreasing
        for i in range(1, len(dims)):
            assert dims[i] >= dims[i - 1]
        # Should grow without bound
        assert dims[-1] >= 18

    def test_negative_order_raises(self):
        with pytest.raises(ValueError, match="Multipole order"):
            upper_critical_dimension(-1)


# ═══════════════════════════════════════════════════════════════════
# Standard hydrodynamics info
# ═══════════════════════════════════════════════════════════════════

class TestStandardHydroInfo:
    """Test standard NS hydro information content."""

    def test_1d_charges(self):
        """1D: energy + momentum + particle = 3 charges."""
        info = standard_hydro_charges(1)
        assert info.conserved_charges == 3

    def test_2d_charges(self):
        """2D: 1 + 2 + 1 = 4 charges."""
        info = standard_hydro_charges(2)
        assert info.conserved_charges == 4

    def test_3d_charges(self):
        """3D: 1 + 3 + 1 = 5 charges."""
        info = standard_hydro_charges(3)
        assert info.conserved_charges == 5

    def test_general_d_plus_2(self):
        """d + 2 charges for d spatial dimensions."""
        for d in range(1, 10):
            info = standard_hydro_charges(d)
            assert info.conserved_charges == d + 2

    def test_info_bits(self):
        info = standard_hydro_charges(3)
        assert info.info_bits == 5.0

    def test_macroscopic_parameters(self):
        info = standard_hydro_charges(3)
        params = info.macroscopic_parameters
        assert len(params) == 5  # T, u_1, u_2, u_3, mu

    def test_zero_dim_raises(self):
        with pytest.raises(ValueError, match="Spatial dimension"):
            StandardHydroInfo(spatial_dim=0)


# ═══════════════════════════════════════════════════════════════════
# Fracton hydrodynamics info
# ═══════════════════════════════════════════════════════════════════

class TestFractonHydroInfo:
    """Test fracton hydro information content."""

    def test_exact_multipole_charges_formula(self):
        """C(N + d, d) exact multipole charges."""
        for d in [1, 2, 3]:
            for N in range(6):
                info = FractonHydroInfo(
                    spatial_dim=d, max_multipole_order=N
                )
                assert info.exact_multipole_charges == comb(N + d, d)

    def test_3d_dipole_charges(self):
        """3D dipole: C(4, 3) = 4."""
        info = FractonHydroInfo(spatial_dim=3, max_multipole_order=1)
        assert info.exact_multipole_charges == 4

    def test_3d_quadrupole_charges(self):
        """3D quadrupole: C(5, 3) = 10."""
        info = FractonHydroInfo(spatial_dim=3, max_multipole_order=2)
        assert info.exact_multipole_charges == 10

    def test_total_charges_with_momentum_energy(self):
        """Total = multipole + momentum + energy."""
        info = FractonHydroInfo(spatial_dim=3, max_multipole_order=1)
        # 4 multipole + 3 momentum + 1 energy = 8
        assert info.conserved_charges == 8

    def test_harmonic_moments_2d(self):
        """Harmonic moments exist in 2D with dipole conservation."""
        info = fracton_hydro_charges(d=2, max_multipole=1)
        assert info.has_harmonic_moments

    def test_no_harmonic_moments_3d(self):
        """Harmonic moments are a 2D feature."""
        info = fracton_hydro_charges(d=3, max_multipole=1)
        assert not info.has_harmonic_moments

    def test_fragmentation_data_attached(self):
        """Fragmentation data should be attached when system_size given."""
        info = fracton_hydro_charges(d=1, max_multipole=1, system_size=20)
        assert info.fragmentation is not None
        assert info.fragmentation.preserved_bits > 0


# ═══════════════════════════════════════════════════════════════════
# Hilbert space fragmentation
# ═══════════════════════════════════════════════════════════════════

class TestHilbertSpaceFragmentation:
    """Test Hilbert space fragmentation bounds (Sala et al.)."""

    def test_1d_frozen_states_scaling(self):
        """1D spin-1 frozen states: ~(4/3)^L."""
        for L in [10, 20, 30]:
            frag = hilbert_space_fragmentation(system_size=L, spatial_dim=1)
            expected = round((4.0 / 3.0) ** L)
            assert frag.n_frozen_states == expected

    def test_1d_preserved_bits(self):
        """Preserved bits: L * log2(4/3) ~ 0.415 * L."""
        L = 100
        frag = hilbert_space_fragmentation(system_size=L, spatial_dim=1)
        expected = L * log2(4.0 / 3.0)
        assert abs(frag.preserved_bits - expected) < 1e-10

    def test_strong_fragmentation(self):
        """Strong fragmentation: largest sector fraction -> 0."""
        frag = hilbert_space_fragmentation(system_size=50, spatial_dim=1)
        assert frag.is_strongly_fragmented
        assert frag.largest_sector_fraction < 1e-5

    def test_3d_xcube_bits(self):
        """X-Cube (3D): 6L - 3 logical qubits."""
        L = 10
        frag = hilbert_space_fragmentation(system_size=L, spatial_dim=3)
        assert frag.preserved_bits == 6 * L - 3

    def test_bits_grow_with_size(self):
        """Preserved bits should grow with system size."""
        bits_small = hilbert_space_fragmentation(
            system_size=10, spatial_dim=1
        ).preserved_bits
        bits_large = hilbert_space_fragmentation(
            system_size=100, spatial_dim=1
        ).preserved_bits
        assert bits_large > bits_small

    def test_invalid_system_size(self):
        with pytest.raises(ValueError, match="System size"):
            hilbert_space_fragmentation(system_size=0)


# ═══════════════════════════════════════════════════════════════════
# Information comparison
# ═══════════════════════════════════════════════════════════════════

class TestInformationComparison:
    """Test standard vs fracton information retention comparison."""

    def test_fracton_always_more(self):
        """Fracton hydro always preserves >= standard hydro information."""
        for d in [1, 2, 3]:
            for N in [1, 2, 5]:
                comp = information_ratio(d=d, max_multipole=N)
                assert comp.retention_ratio >= 1.0

    def test_charge_ratio_grows_with_multipole(self):
        """More conserved multipoles -> higher charge ratio."""
        ratios = []
        for N in [1, 2, 5, 10]:
            comp = information_ratio(d=3, max_multipole=N)
            ratios.append(comp.exact_charge_ratio)
        # Monotonically increasing
        for i in range(1, len(ratios)):
            assert ratios[i] > ratios[i - 1]

    def test_fragmentation_dominates_at_large_L(self):
        """At large system size, fragmentation dominates multipole charges."""
        comp = information_ratio(d=1, max_multipole=1, system_size=1000)
        assert comp.fragmentation_factor > float(
            comp.fracton.conserved_charges
        )

    def test_3d_dipole_exact_charge_ratio(self):
        """3D dipole: fracton has 8 charges vs standard 5."""
        comp = information_ratio(d=3, max_multipole=1)
        assert comp.fracton.conserved_charges == 8
        assert comp.standard.conserved_charges == 5
        assert comp.exact_charge_ratio == 8 / 5

    def test_compare_table_output(self):
        """compare_information_retention produces structured table."""
        results = compare_information_retention(
            spatial_dims=[1, 3],
            multipole_orders=[0, 1, 5],
            system_size=50,
        )
        assert len(results) == 6  # 2 dims * 3 orders
        for r in results:
            assert "spatial_dim" in r
            assert "retention_ratio" in r
            assert r["retention_ratio"] >= 1.0


# ═══════════════════════════════════════════════════════════════════
# Gauge information assessment
# ═══════════════════════════════════════════════════════════════════

class TestGaugeInformationAssessment:
    """Test the gauge information assessment for fracton hydro."""

    def test_partial_gauge_information(self):
        """Fracton hydro carries gauge info PARTIALLY."""
        assessment = gauge_information_assessment()
        assert assessment.carries_gauge_info == "partially"

    def test_no_conventional_transport(self):
        """Conventional gauge transport is blocked (gauge erasure theorem)."""
        assessment = gauge_information_assessment()
        assert not assessment.conventional_transport

    def test_fragmentation_encoding(self):
        """Fragmentation CAN encode gauge information."""
        assessment = gauge_information_assessment()
        assert assessment.fragmentation_encoding

    def test_gksw_evasion(self):
        """Subsystem symmetries evade the GKSW commutativity argument."""
        assessment = gauge_information_assessment()
        assert assessment.gksw_evasion

    def test_finite_temperature_not_proven(self):
        """Survival at finite temperature is NOT yet proven."""
        assessment = gauge_information_assessment()
        assert not assessment.finite_temperature_proven

    def test_confidence_medium(self):
        """Confidence is medium: lattice evidence but no finite-T proof."""
        assessment = gauge_information_assessment()
        assert assessment.confidence_level == "medium"

    def test_mechanisms_present(self):
        """Multiple mechanisms contribute."""
        assessment = gauge_information_assessment()
        assert GaugeInfoMechanism.FRAGMENTATION_PATTERNS in assessment.mechanisms
        assert GaugeInfoMechanism.SUBSYSTEM_SYMMETRY in assessment.mechanisms
        assert GaugeInfoMechanism.POSITION_DEPENDENT_DEGENERACY in assessment.mechanisms

    def test_overall_assessment_nonempty(self):
        assessment = gauge_information_assessment()
        assert len(assessment.overall_assessment) > 100


# ═══════════════════════════════════════════════════════════════════
# Cross-consistency
# ═══════════════════════════════════════════════════════════════════

class TestCrossConsistency:
    """Test consistency between SK-EFT and information modules."""

    def test_symmetry_charge_count_consistency(self):
        """FractonSymmetry.total_multipole_charges == FractonHydroInfo.exact_multipole_charges."""
        for d in [1, 2, 3]:
            for N in range(5):
                sym = classify_symmetry(max_multipole=N, spatial_dim=d)
                info = FractonHydroInfo(spatial_dim=d, max_multipole_order=N)
                assert sym.total_multipole_charges == info.exact_multipole_charges

    def test_standard_vs_charge_only_fracton(self):
        """Charge-only fracton (N=0) should have same multipole charges as standard."""
        for d in [1, 2, 3]:
            std = standard_hydro_charges(d)
            frac = fracton_hydro_charges(d=d, max_multipole=0)
            # Multipole charges only (1 for charge)
            # Standard has d+2, fracton with N=0 has 1 multipole + d momentum + 1 energy = d+2
            assert frac.conserved_charges == std.conserved_charges

    def test_transport_vs_standard_ratio(self):
        """Fracton has 2x transport coefficients vs standard NS at leading order."""
        sym = classify_symmetry(max_multipole=1)
        coeffs = compute_transport_coefficients(sym)
        # Standard NS: 3 (eta, zeta, kappa)
        # Fracton: 4 dissipative + 2 Hall = 6
        assert (coeffs.n_dissipative + coeffs.n_hall) == 6

    def test_dispersion_vs_standard_comparison(self):
        """Fracton omega ~ k^2 vs standard omega ~ k^1."""
        # Fracton (n=1)
        disp_frac = FractonDispersionRelation(
            c2=1.0, gamma4=0.1, multipole_order=1
        )
        assert disp_frac.dispersion_power == 2

        # Standard (n=0)
        disp_std = FractonDispersionRelation(
            c2=1.0, gamma4=0.1, multipole_order=0
        )
        assert disp_std.dispersion_power == 1

    def test_module_imports(self):
        """All public names importable from the package."""
        from src.fracton import (
            FractonSymmetry,
            FractonTransportCoefficients,
            FractonSKAction,
            StandardHydroInfo,
            FractonHydroInfo,
            InformationComparison,
            GaugeInformationAssessment,
        )


# ═══════════════════════════════════════════════════════════════════
# Z_3 gauge coarse-graining example
# ═══════════════════════════════════════════════════════════════════

class TestGaugeCoarsegrainingExample:
    """Test the Z_3 gauge coarse-graining example for fracton information retention."""

    def test_default_parameters(self):
        """Default call (L=8, block=2, Z_3) should produce valid result."""
        result = gauge_coarsegraining_example()
        assert result.lattice_size == 8
        assert result.block_size == 2
        assert result.group_order == 3

    def test_total_configs(self):
        """Total configurations = q^L."""
        result = gauge_coarsegraining_example(lattice_size=4, group_order=3)
        assert result.n_total_configs == 3 ** 4

    def test_gauge_invariant_count(self):
        """Number of gauge-invariant states equals group order for 1D periodic."""
        for q in [2, 3, 5]:
            result = gauge_coarsegraining_example(lattice_size=4, group_order=q)
            assert result.n_gauge_invariant == q

    def test_one_wilson_loop(self):
        """1D periodic chain has exactly 1 independent Wilson loop."""
        result = gauge_coarsegraining_example()
        assert result.n_wilson_loops == 1

    def test_fracton_fidelity_geq_standard(self):
        """Fracton CG preserves at least as much info as standard CG."""
        result = gauge_coarsegraining_example()
        assert result.fracton_fidelity >= result.standard_fidelity

    def test_fidelity_ratio_geq_one(self):
        """Fidelity ratio (fracton/standard) >= 1."""
        result = gauge_coarsegraining_example()
        assert result.fidelity_ratio >= 1.0

    def test_fracton_more_cg_states_than_standard(self):
        """Fracton CG produces at least as many distinguishable states as standard."""
        result = gauge_coarsegraining_example()
        assert result.n_fracton_cg_states >= result.n_standard_cg_states

    def test_standard_fidelity_positive(self):
        """Standard CG fidelity is positive (retains some information)."""
        result = gauge_coarsegraining_example()
        assert result.standard_fidelity > 0.0

    def test_fracton_fidelity_positive(self):
        """Fracton CG fidelity is positive."""
        result = gauge_coarsegraining_example()
        assert result.fracton_fidelity > 0.0

    def test_fidelity_leq_one(self):
        """Both fidelities should be at most 1 (can't recover more than exists)."""
        result = gauge_coarsegraining_example()
        assert result.standard_fidelity <= 1.0
        assert result.fracton_fidelity <= 1.0

    def test_n_blocks_computed(self):
        """Number of blocks = L / block_size."""
        result = gauge_coarsegraining_example(lattice_size=8, block_size=4)
        assert result.n_blocks == 2

    def test_z2_gauge_group(self):
        """Z_2 gauge group works correctly."""
        result = gauge_coarsegraining_example(lattice_size=4, group_order=2)
        assert result.group_order == 2
        assert result.n_gauge_invariant == 2
        assert result.n_total_configs == 2 ** 4

    def test_larger_block_less_fidelity(self):
        """Larger blocks should not increase standard CG fidelity."""
        result_small = gauge_coarsegraining_example(lattice_size=8, block_size=2)
        result_large = gauge_coarsegraining_example(lattice_size=8, block_size=4)
        # With fewer blocks (larger block_size), standard CG has fewer bins
        assert result_large.n_standard_cg_states <= result_small.n_standard_cg_states

    def test_info_bits_positive(self):
        """Info retained bits should be positive."""
        result = gauge_coarsegraining_example()
        assert result.standard_info_retained_bits > 0
        assert result.fracton_info_retained_bits > 0

    def test_total_gauge_invariant_bits(self):
        """Total gauge-invariant bits for Z_3 = log2(3)."""
        result = gauge_coarsegraining_example(lattice_size=4, group_order=3)
        expected = log2(3)
        assert abs(result.total_gauge_invariant_bits - expected) < 1e-10

    def test_invalid_lattice_size(self):
        """lattice_size < 2 should raise ValueError."""
        with pytest.raises(ValueError, match="lattice_size"):
            gauge_coarsegraining_example(lattice_size=1)

    def test_invalid_block_size(self):
        """block_size < 1 should raise ValueError."""
        with pytest.raises(ValueError, match="block_size"):
            gauge_coarsegraining_example(block_size=0)

    def test_invalid_group_order(self):
        """group_order < 2 should raise ValueError."""
        with pytest.raises(ValueError, match="group_order"):
            gauge_coarsegraining_example(group_order=1)

    def test_non_divisible_raises(self):
        """lattice_size not divisible by block_size should raise ValueError."""
        with pytest.raises(ValueError, match="divisible"):
            gauge_coarsegraining_example(lattice_size=7, block_size=2)

    def test_block_size_one_maximal_fidelity(self):
        """block_size=1 means no coarse-graining: both CG types should be maximal."""
        result = gauge_coarsegraining_example(lattice_size=4, block_size=1, group_order=2)
        # With block_size=1, each link is its own block
        # Standard CG keeps individual link sums (= the links themselves)
        # Fracton CG keeps (charge, dipole) = (link_value, 0) per block
        # Both should be equivalent to keeping all link values
        assert result.n_standard_cg_states == result.n_fracton_cg_states

    def test_concrete_z3_fidelity_ratio(self):
        """Z_3 with L=8, block=2: fracton fidelity ratio should be > 1."""
        result = gauge_coarsegraining_example(lattice_size=8, block_size=2, group_order=3)
        assert result.fidelity_ratio > 1.0

    def test_fracton_info_bits_geq_standard(self):
        """Fracton retained bits >= standard retained bits."""
        result = gauge_coarsegraining_example()
        assert result.fracton_info_retained_bits >= result.standard_info_retained_bits
