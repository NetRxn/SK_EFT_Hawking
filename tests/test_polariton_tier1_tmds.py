"""
Regression tests for Wave 6v.4 — Penn TMD polariton scope demarcation.

These tests pin the parameter values used in the Lean theorem
`SKEFTHawking.PolaritonTier1.polariton_tier1_fails_tmds` to the
Python `POLARITON_PLATFORMS['Penn_TMD_MoSe2']` registry entry,
and verify the post-processing tags it `intractable` / `tier1_valid=False`.

Source: Wang, Kim, Zhen, He, PRL 136, 146901 (2026); arXiv:2411.16635.
"""

import math
import pytest

from src.core.constants import POLARITON_PLATFORMS, FALQUE_STEEP_HORIZON_KAPPA
from src.core.provenance import PARAMETER_PROVENANCE
from src.core.citations import CITATION_REGISTRY


PENN = "Penn_TMD_MoSe2"
BIBKEY = "WangKimBZHe2026PennTMDPolariton"


# ─── Platform registration ─────────────────────────────────────────────


def test_penn_tmd_registered_in_polariton_platforms():
    assert PENN in POLARITON_PLATFORMS, (
        "Penn_TMD_MoSe2 must be registered in POLARITON_PLATFORMS "
        "(Wave 6v.4 substrate)."
    )


def test_penn_tmd_source_of_truth_parameters():
    """Source-of-truth parameters from Wang et al. 2026 (LLM-verified)."""
    p = POLARITON_PLATFORMS[PENN]
    # Each value here is the literal LLM-extracted value from arXiv:2411.16635.
    assert p["g_meV"] == pytest.approx(16.8)
    assert p["gamma_LP_meV"] == pytest.approx(1.8)
    assert p["gamma_UP_meV"] == pytest.approx(2.3)
    assert p["gamma_cav_meV"] == pytest.approx(1.9)
    assert p["Q_factor"] == 914
    assert p["switching_energy_fJ"] == pytest.approx(4.0)


# ─── Derived quantities ────────────────────────────────────────────────


def test_penn_tmd_gamma_pol_matches_hbar_conversion():
    """Γ_LP = γ_LP / ℏ from γ_LP=1.8 meV → ≈ 2.7347×10¹² s⁻¹."""
    p = POLARITON_PLATFORMS[PENN]
    # SI 2019 exact values for ℏ and the elementary charge.
    HBAR = 1.054571817e-34
    e = 1.602176634e-19
    expected = 1.8e-3 * e / HBAR  # ≈ 2.7347e12
    assert p["Gamma_pol"] == pytest.approx(expected, rel=1e-12)
    assert 2.73e12 < p["Gamma_pol"] < 2.74e12


def test_penn_tmd_validity_ratio_at_steep_falque_kappa():
    """
    With κ at the Falque steep-horizon maximum (the most generous polariton-
    family surface gravity), Γ_LP / κ ≈ 24.86 — still >> 0.1.
    """
    p = POLARITON_PLATFORMS[PENN]
    ratio_steep = p["Gamma_pol"] / FALQUE_STEEP_HORIZON_KAPPA
    assert 24.0 < ratio_steep < 25.5, f"ratio_steep = {ratio_steep}"
    # And `>= 0.1` is the load-bearing inequality in the Lean theorem.
    assert ratio_steep >= 0.1


def test_penn_tmd_validity_ratio_at_smooth_falque_kappa():
    """At Falque smooth-horizon κ = 7×10¹⁰ s⁻¹ the ratio is ≈ 39.07."""
    p = POLARITON_PLATFORMS[PENN]
    ratio_smooth = p["Gamma_pol"] / 7.0e10
    assert 38.5 < ratio_smooth < 39.5, f"ratio_smooth = {ratio_smooth}"


# ─── Tier-1 classification ─────────────────────────────────────────────


def test_penn_tmd_tier1_classifier_outputs_intractable():
    """
    With Penn's own platform κ = 7e10 (Falque smooth baseline), the
    POLARITON_PLATFORMS post-processing must tag the platform as
    `intractable` and `tier1_valid=False` — the desired scope-demarcation
    signal.
    """
    p = POLARITON_PLATFORMS[PENN]
    assert p["tier1_regime"] == "intractable"
    assert p["tier1_valid"] is False
    # Also verify the boundary: ratio >> 1
    assert p["Gamma_pol_over_kappa"] > 1.0


# ─── Provenance + citation registry ────────────────────────────────────


@pytest.mark.parametrize(
    "key",
    [
        f"{PENN}.g_meV",
        f"{PENN}.gamma_LP_meV",
        f"{PENN}.gamma_UP_meV",
        f"{PENN}.gamma_cav_meV",
        f"{PENN}.Q_factor",
        f"{PENN}.switching_energy_fJ",
        f"{PENN}.tau_cav",
        f"{PENN}.Gamma_pol",
    ],
)
def test_penn_tmd_provenance_entry_llm_verified(key):
    entry = PARAMETER_PROVENANCE.get(key)
    assert entry is not None, f"Missing PARAMETER_PROVENANCE entry for {key}."
    assert entry["llm_verified_date"] is not None, (
        f"Provenance entry for {key} must be LLM-verified."
    )


def test_penn_tmd_bibkey_present_in_citation_registry():
    bib = CITATION_REGISTRY.get(BIBKEY)
    assert bib is not None, (
        f"Bibkey {BIBKEY} must be in CITATION_REGISTRY (Wave 6v.4 source)."
    )
    assert bib["arxiv"] == "2411.16635"
    assert bib["doi"] == "10.1103/gc15-qsvf"
    assert bib["year"] == 2026


def test_penn_tmd_primary_source_cache_file_exists():
    """Pipeline Invariant #11 — every external bibitem has a primary-source cache."""
    import os

    bib = CITATION_REGISTRY[BIBKEY]
    workspace_root = os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    )
    path = os.path.join(workspace_root, bib["primary_source_path"])
    assert os.path.exists(path), (
        f"Primary source cache file missing at {path}. "
        "Run: curl -sL -o <path> https://arxiv.org/pdf/2411.16635"
    )
    assert os.path.getsize(path) > 100_000, (
        f"Primary source file too small at {path} (<100KB); likely truncated download."
    )
