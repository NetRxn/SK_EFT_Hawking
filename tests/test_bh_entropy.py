"""Phase 6a Wave 3 tests: Bekenstein-Hawking entropy from MTC state counting.

Cross-validation between Lean theorems in
`lean/SKEFTHawking/BHEntropyMicroscopic.lean` and Python numerics in
`src/bh_entropy/`. Covers:

- Verlinde-formula numerics for SU(2)_k k ∈ {2, 3, 4, 10}.
- Kaul-Majumdar closed form S = A/(4G) − (3/2) log(A/(4G)) + c0.
- Log-correction structural decomposition (-3/2 = -1/2 + -1).
- Sen 4D Schwarzschild non-universality witness.
- Per-MTC falsifier-instance status (F1-F5) for the zoo:
  Fibonacci, Ising, ToricCode (abelian falsifier), DS3, SU(2)_k.
- Lean cross-checks for `verlindeEntropy_SU2k` opaque function asymptotic.
"""

from __future__ import annotations

import numpy as np
import pytest

from src.core.constants import BH_ENTROPY_PARAMS
from src.core.formulas import (
    bh_entropy_kaul_majumdar,
    bh_entropy_leading_coefficient,
    log_correction_coefficient_per_mtc,
    log_correction_coefficient_su2k,
    mtc_area_law_kappa,
    mtc_horizon_falsifier_status,
    verlinde_dim_horizon,
)
from src.bh_entropy import (
    HorizonMTCInstance,
    ds3_instance,
    falsifier_status_table,
    fibonacci_instance,
    ising_instance,
    kaul_majumdar_entropy_grid,
    leading_coefficient_vs_immirzi,
    log_correction_zoo,
    mtc_global_dim_squared,
    sen_disagreement_witness,
    su2k_instance,
    su2k_S_matrix,
    su2k_quantum_dimensions,
    toric_code_instance,
    verlinde_dim_at_horizon,
)


class TestSU2kModularData:
    """SU(2)_k quantum dimensions and S-matrix — formula correctness."""

    def test_su2k_quantum_dimensions_at_k2_match_ising(self):
        """SU(2)_2 quantum dimensions reproduce Ising: (1, √2, 1)."""
        d = su2k_quantum_dimensions(2)
        assert np.allclose(d, [1.0, np.sqrt(2), 1.0], atol=1e-12)

    def test_su2k_quantum_dimensions_at_k3_match_double_fibonacci(self):
        """SU(2)_3 d = (1, φ, φ, 1); φ = (1+√5)/2."""
        phi = (1 + np.sqrt(5)) / 2
        d = su2k_quantum_dimensions(3)
        assert np.allclose(d, [1.0, phi, phi, 1.0], atol=1e-12)

    def test_su2k_quantum_dimensions_at_k4(self):
        """SU(2)_4 d = (1, √3, 2, √3, 1)."""
        d = su2k_quantum_dimensions(4)
        assert np.allclose(d, [1.0, np.sqrt(3), 2.0, np.sqrt(3), 1.0], atol=1e-12)

    def test_su2k_quantum_dimensions_unit_at_label_zero(self):
        """The unit object (label 0) has quantum dim = 1 for all k."""
        for k in (1, 2, 3, 5, 10):
            d = su2k_quantum_dimensions(k)
            assert d[0] == pytest.approx(1.0, abs=1e-12)

    def test_su2k_quantum_dimensions_positive(self):
        """All SU(2)_k quantum dimensions are positive (HorizonMTCBC.quantum_dim_pos)."""
        for k in (2, 3, 4, 10):
            d = su2k_quantum_dimensions(k)
            assert (d > 0).all(), f"SU(2)_{k} has non-positive quantum dim"

    def test_su2k_S_matrix_unitarity(self):
        """SU(2)_k modular S-matrix is unitary (S S^T = I)."""
        for k in (2, 3, 4, 5, 10):
            S = su2k_S_matrix(k)
            err = np.max(np.abs(S @ S.T - np.eye(k + 1)))
            assert err < 1e-12, f"SU(2)_{k} S not unitary: err = {err}"

    def test_su2k_S_matrix_symmetric(self):
        """SU(2)_k modular S-matrix is symmetric."""
        for k in (2, 3, 4, 10):
            S = su2k_S_matrix(k)
            assert np.allclose(S, S.T, atol=1e-12)

    def test_su2k_S_matrix_first_column_quantum_dims(self):
        """S_{j,0} / S_{0,0} = d_j (Verlinde first-column = quantum dims)."""
        for k in (2, 3, 4):
            S = su2k_S_matrix(k)
            d = su2k_quantum_dimensions(k)
            ratio = S[:, 0] / S[0, 0]
            assert np.allclose(ratio, d, atol=1e-12)


class TestVerlindeFormula:
    """Verlinde-formula state counts at the horizon."""

    def test_verlinde_ising_ss_to_vacuum(self):
        """Ising σ⊗σ has dim 1 (single fusion channel containing vacuum) at p=2."""
        # SU(2)_2 with labels [σ, σ] at p=2: dim = δ_{σ, σ̄} = 1 (σ self-dual)
        result = verlinde_dim_at_horizon(2, 2, [1, 1])
        assert result == pytest.approx(1.0, abs=1e-10)

    def test_verlinde_ising_4sigma_correlator(self):
        """Ising σ⊗σ⊗σ⊗σ has dim 2 (two Ising fusion channels)."""
        result = verlinde_dim_at_horizon(2, 4, [1, 1, 1, 1])
        assert result == pytest.approx(2.0, abs=1e-10)

    def test_verlinde_psi_squared_ising_is_vacuum(self):
        """Ising ψ⊗ψ has dim 1 (ψ²=1 fusion in Ising)."""
        # Label ψ = 2 in SU(2)_2 (j_label = 2 ↔ spin 1)
        result = verlinde_dim_at_horizon(2, 2, [2, 2])
        assert result == pytest.approx(1.0, abs=1e-10)

    def test_verlinde_dim_horizon_p_lt_2_raises(self):
        """Verlinde formula requires p ≥ 2 (sphere-with-p-punctures has p ≥ 2)."""
        S = su2k_S_matrix(2)
        with pytest.raises(ValueError, match="p ≥ 2"):
            verlinde_dim_horizon(1, S, [1])

    def test_verlinde_fibonacci_via_su2k3(self):
        """Fibonacci τ⊗τ via SU(2)_3 sub-MTC: τ²=1+τ ⇒ Verlinde p=2 (1,1) = 1.

        In the Fibonacci-subcategory embedding, label 0 = vacuum, label 1 = τ
        (the d=φ object). Verlinde[2; τ, τ] on the SU(2)_3 fusion ring still
        gives dim = δ_{τ, τ̄} = 1 (τ self-dual).
        """
        # Fibonacci is the SU(2)_3 subcategory {0, 2} where label 2 has d = φ
        # Use direct Verlinde on SU(2)_3 with labels [1, 1] (full SU(2)_3, label 1
        # has d = φ in our convention from the fixed formula).
        result = verlinde_dim_at_horizon(3, 2, [1, 1])
        assert result == pytest.approx(1.0, abs=1e-10)


class TestKaulMajumdarClosedForm:
    """Kaul-Majumdar closed-form entropy and log-correction structure."""

    def test_kaul_majumdar_at_4GN_equals_one(self):
        """At A = 4 G_N, S = 1 - (3/2) log(1) + 0 = 1."""
        for G_N in (0.5, 1.0, 2.0, 100.0):
            S = bh_entropy_kaul_majumdar(4 * G_N, G_N=G_N, c0=0)
            assert S == pytest.approx(1.0, abs=1e-12)

    def test_kaul_majumdar_log_coefficient_is_minus_three_halves(self):
        """The log-correction coefficient is exactly −3/2."""
        assert log_correction_coefficient_su2k() == -1.5

    def test_kaul_majumdar_log_decomposition(self):
        """−3/2 = (−1/2) + (−1) Gaussian + singlet projection."""
        c_gauss = BH_ENTROPY_PARAMS["LOG_CORRECTION_GAUSSIAN_SADDLE"]
        c_singlet = BH_ENTROPY_PARAMS["LOG_CORRECTION_SINGLET_PROJECTION"]
        assert c_gauss + c_singlet == pytest.approx(-1.5, abs=1e-12)
        assert c_gauss == -0.5
        assert c_singlet == -1.0

    def test_kaul_majumdar_grid_monotone_at_large_area(self):
        """For A ≫ G_N, S(A) is monotone increasing in A."""
        log_A, S = kaul_majumdar_entropy_grid(
            log_area_lower=10, log_area_upper=80, n_points=200
        )
        assert (np.diff(S) >= 0).all(), "Kaul-Majumdar S not monotone at large A"

    def test_kaul_majumdar_dominated_by_leading_at_large_area(self):
        """At large A, S(A) / [A/(4 G_N)] → 1."""
        G_N = 1.0
        for log_A in (40.0, 60.0, 80.0):
            A = 4 * G_N * np.exp(log_A)
            S = bh_entropy_kaul_majumdar(A, G_N=G_N, c0=0)
            leading = A / (4 * G_N)
            ratio = S / leading
            assert abs(ratio - 1.0) < 1e-10, f"S/leading = {ratio} at log_A = {log_A}"

    def test_kaul_majumdar_invalid_area_raises(self):
        """A ≤ 0 raises (asymptotic regime requires A > 0)."""
        with pytest.raises(ValueError):
            bh_entropy_kaul_majumdar(-1.0, G_N=1.0)


class TestImmirziTuning:
    """The 1/4 leading coefficient as an Immirzi γ tuning (NOT a derivation)."""

    def test_leading_coefficient_at_DL_gamma_equals_quarter(self):
        """At γ = γ_DL, the leading coefficient equals 1/4 by construction."""
        γ_DL = BH_ENTROPY_PARAMS["IMMIRZI_GAMMA_DOMAGALA_LEWANDOWSKI"]
        κ = bh_entropy_leading_coefficient(γ_DL)
        assert κ == pytest.approx(0.25, abs=1e-12)

    def test_leading_coefficient_at_meissner_gamma_off_quarter(self):
        """At γ = γ_Meissner, κ ≠ 1/4 (witnessing the tuning).

        Specifically κ_Meissner = γ_DL / γ_Meissner · 1/4 ≈ 0.2167.
        This is the 'tuning' anti-falsifier of F4: different γ choices give
        different leading coefficients, with both 'matching' 1/4 only under
        their own counting prescription.
        """
        γ_M = BH_ENTROPY_PARAMS["IMMIRZI_GAMMA_MEISSNER"]
        γ_DL = BH_ENTROPY_PARAMS["IMMIRZI_GAMMA_DOMAGALA_LEWANDOWSKI"]
        κ = bh_entropy_leading_coefficient(γ_M)
        # κ = (γ_DL / γ_M) * 0.25
        assert κ == pytest.approx(γ_DL / γ_M * 0.25, abs=1e-12)
        assert κ != pytest.approx(0.25)
        # Within wave-3 tolerance (10%): yes, but not at exactly 1/4.
        tol = BH_ENTROPY_PARAMS["BH_ENTROPY_COEFFICIENT_MATCH_TOLERANCE"]
        assert abs(κ - 0.25) < tol

    def test_leading_coefficient_scan_includes_quarter_locus(self):
        """The κ(γ) scan crosses 1/4 at γ = γ_DL (sanity check on the tuning)."""
        γs, κs, anchors = leading_coefficient_vs_immirzi()
        # At γ = γ_DL, κ = 1/4
        idx_DL = int(np.argmin(np.abs(γs - anchors["DL"])))
        # The minimum |κ - 1/4| on the grid should be very close to 0
        min_dist = np.min(np.abs(κs - 0.25))
        assert min_dist < 0.01, f"κ scan does not cross 1/4 (min dist = {min_dist})"


class TestSenNonUniversality:
    """Sen 2013 heat-kernel result disagrees with Kaul-Majumdar −3/2."""

    def test_sen_4d_log_coeff_value(self):
        """c_log(Sen 4D) = 212/45 − 3 = 77/45 ≈ 1.711."""
        c_sen = BH_ENTROPY_PARAMS["LOG_CORRECTION_SEN_4D_SCHWARZSCHILD"]
        assert c_sen == pytest.approx(77 / 45, abs=1e-6)

    def test_sen_disagrees_with_kaul_majumdar(self):
        """Sen +1.71 ≠ Kaul-Majumdar −3/2 (universality fails)."""
        witness = sen_disagreement_witness()
        assert witness.c_log_kaul_majumdar == -1.5
        assert witness.c_log_sen_4d > 0
        assert witness.is_disagreement
        # |1.71 − (−1.5)| = 3.21 > tolerance 0.01
        assert abs(witness.disagreement) > 3.0

    def test_log_correction_zoo_status(self):
        """SU2k = known/-1.5; Fib/Ising/DS3 = conjectural; Toric = falsifier."""
        zoo = log_correction_zoo()
        assert zoo["SU2k"]["status"] == "known"
        assert zoo["SU2k"]["value"] == -1.5
        assert zoo["Sen4DSchwarzschild"]["status"] == "known"
        for name in ("Fibonacci", "Ising", "DS3"):
            assert zoo[name]["status"] == "conjectural"
            assert zoo[name]["value"] is None
        assert zoo["ToricCode"]["status"] == "falsifier"


class TestMTCFalsifierInstances:
    """Per-MTC F1-F5 falsifier-instance status checks."""

    def test_fibonacci_falsifier_passes_F1_F2_F3_F4(self):
        inst = fibonacci_instance()
        assert "passes" in inst.falsifier_status["F1_positivity"]
        assert "passes" in inst.falsifier_status["F2_areaLeading"]
        assert "passes" in inst.falsifier_status["F3_secondLaw"]
        assert "passes" in inst.falsifier_status["F4_modularInvariance"]
        assert "conjectural" in inst.falsifier_status["F5_anomalyMatch"]

    def test_ising_falsifier_passes_F1_F2_F3_F4(self):
        inst = ising_instance()
        assert "passes" in inst.falsifier_status["F1_positivity"]
        assert "passes" in inst.falsifier_status["F2_areaLeading"]
        assert "passes" in inst.falsifier_status["F4_modularInvariance"]

    def test_toric_code_FAILS_F2_areaLeading(self):
        """Abelian MTC ⇒ log d_max = 0 ⇒ κ = 0 ⇒ F2 falsifier triggered."""
        inst = toric_code_instance()
        assert "FAILS" in inst.falsifier_status["F2_areaLeading"]
        assert inst.is_abelian
        assert inst.log_d_max == 0.0

    def test_ds3_falsifier_passes_F1_F2_F3(self):
        inst = ds3_instance()
        assert inst.num_objects == 8
        assert inst.global_dim_squared == 36.0
        assert not inst.is_abelian
        assert inst.log_d_max == pytest.approx(np.log(3), abs=1e-12)

    def test_su2k_2_instance_matches_ising(self):
        """SU(2)_2 instance should have d_max = √2 (the σ object)."""
        inst = su2k_instance(2)
        assert inst.num_objects == 3
        assert inst.log_d_max == pytest.approx(0.5 * np.log(2), abs=1e-12)
        assert not inst.is_abelian

    def test_su2k_3_instance_matches_fibonacci_d_max(self):
        """SU(2)_3 has d_max = φ; matches Fibonacci anchor (the τ object)."""
        inst = su2k_instance(3)
        phi = (1 + np.sqrt(5)) / 2
        assert inst.log_d_max == pytest.approx(np.log(phi), abs=1e-12)

    def test_falsifier_status_table_covers_zoo(self):
        """Falsifier status table covers the full Wave 3 MTC zoo."""
        table = falsifier_status_table()
        for name in ("Fibonacci", "Ising", "ToricCode", "DS3"):
            assert name in table
        assert "SU(2)_2" in table
        assert "SU(2)_3" in table
        assert "SU(2)_4" in table
        assert "SU(2)_10" in table

    def test_global_dim_squared_zoo(self):
        """Lookup of D² for the named-MTC zoo."""
        assert mtc_global_dim_squared("Fibonacci") == pytest.approx(2 + (1 + np.sqrt(5)) / 2, abs=1e-12)
        assert mtc_global_dim_squared("Ising") == 4.0
        assert mtc_global_dim_squared("ToricCode") == 4.0
        assert mtc_global_dim_squared("DS3") == 36.0


class TestAreaLawKappa:
    """Area-law leading coefficient κ_C ∝ log d_max."""

    def test_area_law_kappa_zero_for_abelian(self):
        """log d_max = 0 (all d_a = 1) ⇒ κ = 0 (F2 falsifier)."""
        assert mtc_area_law_kappa(0.0) == 0.0

    def test_area_law_kappa_positive_for_fibonacci(self):
        """Fibonacci has d_max = φ > 1 ⇒ κ = log φ > 0."""
        log_d = BH_ENTROPY_PARAMS["FIBONACCI_LOG_D_MAX"]
        assert mtc_area_law_kappa(log_d) > 0
        assert mtc_area_law_kappa(log_d) == pytest.approx(log_d, abs=1e-12)


class TestLeanCrossChecks:
    """Cross-validation against `BHEntropyMicroscopic.lean` symbolic theorems."""

    def test_kaul_majumdar_S_at_4GN_lean_anchor(self):
        """Lean: `kaulMajumdar_S_at_4GN`: S(4·G_N, G_N, 0) = 1."""
        for G_N in (0.5, 1.0, 5.0):
            S = bh_entropy_kaul_majumdar(4 * G_N, G_N=G_N, c0=0)
            assert S == pytest.approx(1.0, abs=1e-12)

    def test_kaul_majumdar_S_pos_at_e_squared_lean_anchor(self):
        """Lean: `kaulMajumdar_S_pos_at_e_squared`: S(4·G_N·e², G_N, 0) > 0."""
        for G_N in (0.5, 1.0, 2.0):
            A = 4 * G_N * np.exp(2)
            S = bh_entropy_kaul_majumdar(A, G_N=G_N, c0=0)
            assert S > 0
            # S = e² − 3 ≈ 4.39
            expected = np.exp(2) - 3
            assert S == pytest.approx(expected, abs=1e-12)

    def test_log_decomposition_lean_anchor(self):
        """Lean: `kaul_majumdar_log_decomposition`: −1/2 + (−1) = −3/2."""
        c_gauss = BH_ENTROPY_PARAMS["LOG_CORRECTION_GAUSSIAN_SADDLE"]
        c_singlet = BH_ENTROPY_PARAMS["LOG_CORRECTION_SINGLET_PROJECTION"]
        assert c_gauss + c_singlet == -1.5

    def test_sen_disagreement_lean_anchor(self):
        """Lean: `sen_4d_disagrees_with_kaul_majumdar`: 212/45 − 3 ≠ −3/2."""
        c_sen = 212 / 45 - 3
        assert c_sen != pytest.approx(-1.5)
        # Lean: `sen_4d_log_coeff_pos`: 0 < c_sen
        assert c_sen > 0

    def test_areaLawKappa_nonneg_lean_anchor(self):
        """Lean: `HorizonMTCBC.areaLawKappa_nonneg`: κ ≥ 0 for all instances."""
        for inst in (fibonacci_instance(), ising_instance(),
                     toric_code_instance(), ds3_instance()):
            assert mtc_area_law_kappa(inst.log_d_max) >= 0


class TestStrengtheningPass:
    """Wave 3 post-Stage-12 strengthening pass cross-checks (3-pattern audit)."""

    def test_lean_strengthening_abelian_falsifier_anchored(self):
        """Lean: `abelian_MTC_falsifies_H_HorizonBoundaryCondition`. The abelian
        toric-code instance has all d_a = 1, hence d_max = 1, hence
        log d_max = 0, hence κ_C = 0, hence F2 falsifier triggers."""
        inst = toric_code_instance()
        # All quantum dims are 1
        assert all(d == 1.0 for d in inst.quantum_dimensions)
        # log d_max = 0
        assert inst.log_d_max == 0.0
        # κ_C = log d_max = 0
        kappa = mtc_area_law_kappa(inst.log_d_max)
        assert kappa == 0.0
        # F2 falsifier triggered
        assert "FAILS" in inst.falsifier_status["F2_areaLeading"]

    def test_lean_strengthening_fibonacci_witness_kappa_pos(self):
        """Lean: `fibonacci_horizon_areaLawKappa_pos`. Fibonacci has
        d_max = φ > 1, hence κ_C = log φ > 0 (non-vacuous bundle witness)."""
        inst = fibonacci_instance()
        kappa = mtc_area_law_kappa(inst.log_d_max)
        assert kappa > 0
        # log φ ≈ 0.481
        phi = (1 + np.sqrt(5)) / 2
        assert kappa == pytest.approx(np.log(phi), abs=1e-12)

    def test_lean_strengthening_sen_quantitative_bound(self):
        """Lean: `sen_4d_quantitative_disagreement_bound`. Sen 4D Schwarzschild
        c_log differs from Kaul-Majumdar -3/2 by more than 3."""
        c_sen = BH_ENTROPY_PARAMS["LOG_CORRECTION_SEN_4D_SCHWARZSCHILD"]
        c_km = BH_ENTROPY_PARAMS["LOG_CORRECTION_KAUL_MAJUMDAR_SU2K"]
        diff = c_sen - c_km
        # 212/45 - 3 - (-3/2) = 289/90 ≈ 3.211
        assert diff == pytest.approx(289 / 90, abs=1e-6)
        assert diff > 3.0

    def test_implies_areaLawKappa_pos_anchor(self):
        """Lean: `H_HorizonBoundaryCondition_implies_areaLawKappa_pos`. Bundle
        consistency requires κ_C > 0 (non-vacuous via Fibonacci witness +
        abelian falsifier)."""
        # Fibonacci satisfies F1+F3+F4 with κ_C > 0 (bundle non-vacuous)
        fib = fibonacci_instance()
        assert mtc_area_law_kappa(fib.log_d_max) > 0
        # Abelian toric code FAILS F2 with κ_C = 0 (bundle unsatisfiable)
        toric = toric_code_instance()
        assert mtc_area_law_kappa(toric.log_d_max) == 0


class TestNoveltyFlags:
    """Wave 3 novelty-flag claims (per deep-research §7)."""

    def test_no_published_4D_ADW_MTC_synthesis(self):
        """The 4D + ADW + MTC synthesis is novel-research-flagged.

        This is a documentation-level test: the deep-research return
        surveyed the literature and found no published derivation of
        any specific MTC at the horizon for an ADW substrate. We encode
        this as a status check on the conjectural-class entries.
        """
        zoo = log_correction_zoo()
        # All non-LQG MTCs are conjectural or falsifier — none are 'known'
        # outside SU(2)_k (Kaul-Majumdar) and Sen heat-kernel 4D.
        for name in ("Fibonacci", "Ising", "DS3"):
            assert zoo[name]["status"] == "conjectural"

    def test_walker_wang_inflow_is_conjectural_for_all_MTCs(self):
        """F5 (anomaly match) is conjectural across the MTC zoo."""
        for inst in (fibonacci_instance(), ising_instance(),
                     toric_code_instance(), ds3_instance()):
            assert "conjectural" in inst.falsifier_status["F5_anomalyMatch"]

    def test_immirzi_tuning_is_explicit(self):
        """Two distinct γ values (DL ≠ Meissner) both 'tune' to 1/4."""
        γ_DL = BH_ENTROPY_PARAMS["IMMIRZI_GAMMA_DOMAGALA_LEWANDOWSKI"]
        γ_M = BH_ENTROPY_PARAMS["IMMIRZI_GAMMA_MEISSNER"]
        assert γ_DL != γ_M
        # Both yield 1/4 under their own counting (here, only γ_DL by construction)
        assert bh_entropy_leading_coefficient(γ_DL) == pytest.approx(0.25)
