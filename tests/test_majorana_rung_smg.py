"""Phase 5z Wave 4 tests: Symmetric-Mass-Generation route to Majorana rung.

Mirrors the Lean module `MajoranaRungSMG.lean` against its Python formula
equivalents in `src/core/formulas.py` (`smg_gap_substrate`,
`m_r_smg_from_gap`). Deep-research-anchored band per
Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate Phase Diagram.md §2
(verdict 2026-04-27): NJL-scaling-derived seesaw-restricted band
c_SMG ∈ [10⁻¹⁰, 10⁻⁴] with Λ_UV = M_Pl substrate anchor.
SMG bypasses the Wave 2 BCS L-symmetry obstruction
(`MajoranaRung.lepton_number_symmetry_obstructs_BCS_form`).
"""

from __future__ import annotations

import math

import pytest

from src.core.constants import MAJORANA_PARAMS
from src.core.formulas import (
    smg_gap_substrate,
    m_r_smg_from_gap,
    seesaw_neutrino_mass,
    seesaw_m_r_from_observed,
)


class TestSMGGapSubstrate:
    """Λ_SMG = c_SMG · Λ_UV — NJL-derived seesaw-restricted band scaling."""

    def test_fiducial_evaluation(self):
        """At c_SMG = 1e-7 (mid-band) and Λ_UV = 1e19 GeV (M_Pl), Λ_SMG = 1e12 GeV."""
        result = smg_gap_substrate(1.0e19, c_smg=1.0e-7)
        assert math.isclose(result, 1.0e12)

    def test_band_lower_at_seesaw_lower(self):
        """At seesaw-restricted band lower (c=1e-10) and Λ_UV = M_Pl, Λ_SMG = 1e9."""
        result = smg_gap_substrate(1.0e19, c_smg=1.0e-10)
        assert math.isclose(result, 1.0e9)

    def test_band_upper_at_seesaw_upper(self):
        """At seesaw-restricted band upper (c=1e-4) and Λ_UV = M_Pl, Λ_SMG = 1e15."""
        result = smg_gap_substrate(1.0e19, c_smg=1.0e-4)
        assert math.isclose(result, 1.0e15)

    def test_default_c_smg_is_fiducial(self):
        """Default c_SMG = 1e-7 matches MAJORANA_PARAMS['C_SMG_FIDUCIAL']."""
        assert MAJORANA_PARAMS['C_SMG_FIDUCIAL'] == 1.0e-7
        result_default = smg_gap_substrate(1.0e19)
        result_explicit = smg_gap_substrate(1.0e19, c_smg=1.0e-7)
        assert result_default == result_explicit

    def test_lambda_uv_must_be_positive(self):
        with pytest.raises(ValueError, match="Λ_UV"):
            smg_gap_substrate(0.0, c_smg=1.0e-7)
        with pytest.raises(ValueError, match="Λ_UV"):
            smg_gap_substrate(-1.0, c_smg=1.0e-7)

    def test_c_smg_must_be_in_unit_interval(self):
        with pytest.raises(ValueError, match="c_SMG"):
            smg_gap_substrate(1.0e19, c_smg=0.0)
        with pytest.raises(ValueError, match="c_SMG"):
            smg_gap_substrate(1.0e19, c_smg=-0.1)
        with pytest.raises(ValueError, match="c_SMG"):
            smg_gap_substrate(1.0e19, c_smg=1.5)

    def test_seesaw_band_consistency_round_trip(self):
        """For every c_SMG ∈ [1e-10, 1e-4] and Λ_UV = M_Pl, Λ_SMG sits in
        the seesaw band [1e9, 1e15]. Mirrors Lean theorem
        `smg_window_predicts_Λ_SMG_in_seesaw_band`."""
        c_lo = MAJORANA_PARAMS['C_SMG_SEESAW_LOWER']
        c_hi = MAJORANA_PARAMS['C_SMG_SEESAW_UPPER']
        c_mid = MAJORANA_PARAMS['C_SMG_FIDUCIAL']
        uv_planck = MAJORANA_PARAMS['LAMBDA_UV_SMG_FIDUCIAL_GEV']
        for c in [c_lo, c_mid, c_hi]:
            lam_smg = smg_gap_substrate(uv_planck, c)
            assert 1.0e9 <= lam_smg <= 1.0e15, (
                f"c={c}, Λ_UV={uv_planck} produces Λ_SMG={lam_smg} outside seesaw band"
            )


class TestMRFromSMGGap:
    """M_R_i = c_i · Λ_SMG — SMG-route Majorana mass per generation."""

    def test_saturated_at_unity(self):
        """At c_i = 1 (saturated), M_R = Λ_SMG."""
        assert m_r_smg_from_gap(5.0e11, c_i=1.0) == 5.0e11

    def test_suppressed_below_unity(self):
        """At c_i = 0.5, M_R = 0.5 · Λ_SMG."""
        assert m_r_smg_from_gap(5.0e11, c_i=0.5) == 2.5e11

    def test_default_is_saturated(self):
        """Default c_i = 1.0 returns Λ_SMG."""
        result_default = m_r_smg_from_gap(5.0e11)
        result_explicit = m_r_smg_from_gap(5.0e11, c_i=1.0)
        assert result_default == result_explicit

    def test_lambda_smg_must_be_positive(self):
        with pytest.raises(ValueError, match="Λ_SMG"):
            m_r_smg_from_gap(0.0)
        with pytest.raises(ValueError, match="Λ_SMG"):
            m_r_smg_from_gap(-1.0e10)

    def test_c_i_must_be_in_unit_interval(self):
        with pytest.raises(ValueError, match="c_i"):
            m_r_smg_from_gap(1.0e12, c_i=0.0)
        with pytest.raises(ValueError, match="c_i"):
            m_r_smg_from_gap(1.0e12, c_i=1.5)


class TestSMGBypassesBCSObstruction:
    """Structural: SMG holds at substrates where BCS cannot."""

    def test_smg_witness_no_lnv_input(self):
        """The SMG formula has no LNV parameter — caller cannot supply one.
        Mirrors Lean theorem `smg_route_witness_no_LNV`: existence with no LNV."""
        # Compute Λ_SMG and M_R without any G_LV input
        lam_smg = smg_gap_substrate(1.0e12, c_smg=0.5)
        mr = m_r_smg_from_gap(lam_smg, c_i=1.0)
        assert mr > 0
        # The function signature does not accept G_LV — the bypass is structural

    def test_smg_disjoint_regimes_quantitative(self):
        """At a substrate scale where the BCS exponential gives M_R = 0
        (G_LV-conserving regime in the strong form), SMG can still produce
        a positive M_R. Mirrors Lean theorem
        `smg_route_disjoint_from_L_conserving_BCS`."""
        # In the BCS form at G_LV = 0, M_R cannot satisfy the strong hypothesis
        # (the H_LeptonNumberViolated conjunct fails). In the SMG form, M_R is
        # given directly by Λ_SMG · c_i, no LNV input.
        lam_smg = smg_gap_substrate(1.0e12, c_smg=0.5)
        mr_smg = m_r_smg_from_gap(lam_smg, c_i=1.0)
        assert mr_smg == 5.0e11
        # The non-existence of a BCS-form M_R at G_LV = 0 is the Lean-side
        # content; here we just confirm SMG produces a positive value.


class TestQuantitativeAnchor:
    """The seesaw-restricted band × Planck-UV → seesaw band map."""

    def test_seesaw_band_endpoints_exact(self):
        """At Λ_UV = M_Pl, the 2 endpoint c_SMG values hit the seesaw band
        exactly. Mirrors Lean `smg_window_predicts_Λ_SMG_in_seesaw_band`."""
        # Lower endpoint: c_lower × Λ_UV = 1e-10 · 1e19 = 1e9 (seesaw lower)
        assert smg_gap_substrate(1.0e19, c_smg=1.0e-10) == pytest.approx(1.0e9, rel=1e-12)
        # Upper endpoint: c_upper × Λ_UV = 1e-4 · 1e19 = 1e15 (seesaw upper)
        assert smg_gap_substrate(1.0e19, c_smg=1.0e-4) == pytest.approx(1.0e15, rel=1e-12)
        # Mid-band: 1e-7 · 1e19 = 1e12 (central seesaw)
        assert smg_gap_substrate(1.0e19, c_smg=1.0e-7) == pytest.approx(1.0e12, rel=1e-12)

    def test_seesaw_consistency_via_yukawa(self):
        """At Λ_SMG in the seesaw band and saturated c_i = 1, the Type-I
        seesaw m_ν = y² v² / M_R reproduces the NuFit-6.0 m_ν band for some
        natural Yukawa. Cross-check: BCS-route and SMG-route share the same
        seesaw target, only the bridge mechanism differs."""
        v_ew = 246.22  # GeV
        m_nu_target = 0.0501e-9  # 50.1 meV in GeV
        # Scan the seesaw-restricted band at Λ_UV = M_Pl
        for c_smg in [1.0e-10, 1.0e-7, 1.0e-4]:
            lam_smg = smg_gap_substrate(1.0e19, c_smg=c_smg)
            mr = m_r_smg_from_gap(lam_smg, c_i=1.0)
            # Solve for y via the seesaw inverse
            y_required = math.sqrt(m_nu_target * mr) / v_ew
            # y_required must be positive and bounded; with M_R up to 1e15 GeV,
            # y_required ≤ √(0.05e-9 · 1e15) / 246 ≈ 0.91 — natural.
            assert 0 < y_required < 10, (
                f"At c={c_smg}: y_required={y_required}"
            )

    def test_below_band_falsifier(self):
        """If Λ_SMG drops below 1e9 GeV at Λ_UV = M_Pl, the c_SMG must be
        below the seesaw-restricted lower bound. Mirrors Lean theorem
        `Λ_SMG_below_seesaw_at_Planck_UV_falsifies_NJL_band`."""
        # At Λ_UV = M_Pl = 1e19, Λ_SMG < 1e9 forces c_SMG < 1e-10
        lam_smg_target = 0.5e9  # below seesaw lower
        c_required = lam_smg_target / 1.0e19
        assert c_required < 1.0e-10, (
            f"Λ_UV=M_Pl: c_SMG={c_required} should be < 1e-10 to give Λ_SMG < 1e9"
        )


class TestProvenance:
    """Provenance / constants integrity checks."""

    def test_smg_constants_present_in_majorana_params(self):
        """All Wave 4 SMG constants populated (deep-research-anchored)."""
        for key in (
            'C_SMG_BROAD_LOWER',
            'C_SMG_BROAD_UPPER',
            'C_SMG_SEESAW_LOWER',
            'C_SMG_SEESAW_UPPER',
            'C_SMG_FIDUCIAL',
            'LAMBDA_UV_SMG_FIDUCIAL_GEV',
        ):
            assert key in MAJORANA_PARAMS, f"missing {key}"

    def test_seesaw_band_endpoints_consistent_with_band(self):
        c_lo = MAJORANA_PARAMS['C_SMG_SEESAW_LOWER']
        c_hi = MAJORANA_PARAMS['C_SMG_SEESAW_UPPER']
        c_mid = MAJORANA_PARAMS['C_SMG_FIDUCIAL']
        assert 0 < c_lo < c_mid < c_hi <= 1
        assert c_mid == 1.0e-7
        # Geometric mid-band check: √(c_lo · c_hi) = c_mid
        assert math.isclose(math.sqrt(c_lo * c_hi), c_mid, rel_tol=1e-9)

    def test_broad_band_contains_seesaw_band(self):
        """Broad NJL envelope [10⁻¹², 10⁻³] contains seesaw-restricted [10⁻¹⁰, 10⁻⁴]."""
        broad_lo = MAJORANA_PARAMS['C_SMG_BROAD_LOWER']
        broad_hi = MAJORANA_PARAMS['C_SMG_BROAD_UPPER']
        seesaw_lo = MAJORANA_PARAMS['C_SMG_SEESAW_LOWER']
        seesaw_hi = MAJORANA_PARAMS['C_SMG_SEESAW_UPPER']
        assert broad_lo <= seesaw_lo
        assert seesaw_hi <= broad_hi

    def test_planck_anchor_consistent_with_seesaw_band(self):
        """At Λ_UV = M_Pl, the seesaw-restricted band hits the seesaw mass band exactly."""
        c_lo = MAJORANA_PARAMS['C_SMG_SEESAW_LOWER']
        c_hi = MAJORANA_PARAMS['C_SMG_SEESAW_UPPER']
        uv_planck = MAJORANA_PARAMS['LAMBDA_UV_SMG_FIDUCIAL_GEV']
        # Lower: 1e-10 · 1e19 = 1e9 (seesaw M_R lower)
        assert math.isclose(c_lo * uv_planck, 1.0e9)
        # Upper: 1e-4 · 1e19 = 1e15 (seesaw M_R upper)
        assert math.isclose(c_hi * uv_planck, 1.0e15)
