"""
Regression tests for Wave 6v.2 — Shor ECC-256 T-gate count bound.

These tests pin the Python mirror of the Lean encoding
`googleShorECC256TGateBound` to the headline numerical values
630M (config1200) and 490M (config1450), and verify the bibkey
+ primary-source cache invariants for `BabbushGidneyEtAl2026ECC256Shor`
+ `BravyiKitaev2005MagicState`.

Companion Lean theorems in
`lean/SKEFTHawking/FaultTolerance/ShorTGateCount.lean`:
- `shor_ecc256_tgate_count_le`
- `googleShorECC256TGateBound_config1200_eq`
- `googleShorECC256TGateBound_config1450_eq`
- `shor_ecc256_falls_within_megagate_envelope_at_1G`
- `config1450_T_strictly_less_than_config1200`
- `wave_6v_2_substantive_closure`
"""

import os
import pytest

from src.core.citations import CITATION_REGISTRY


GOOGLE_BIBKEY = "BabbushGidneyEtAl2026ECC256Shor"
BK_BIBKEY = "BravyiKitaev2005MagicState"


# ─── Citation registry ─────────────────────────────────────────────────


def test_google_bibkey_present():
    bib = CITATION_REGISTRY.get(GOOGLE_BIBKEY)
    assert bib is not None, f"Bibkey {GOOGLE_BIBKEY} must be in CITATION_REGISTRY."
    assert bib["arxiv"] == "2603.28846"
    assert bib["year"] == 2026


def test_bk_bibkey_present():
    bib = CITATION_REGISTRY.get(BK_BIBKEY)
    assert bib is not None, f"Bibkey {BK_BIBKEY} must be in CITATION_REGISTRY."
    assert bib["doi"] == "10.1103/PhysRevA.71.022316"
    assert bib["year"] == 2005


@pytest.mark.parametrize("bibkey", [GOOGLE_BIBKEY, BK_BIBKEY])
def test_primary_source_cache_file_exists(bibkey):
    """Pipeline Invariant #11."""
    bib = CITATION_REGISTRY[bibkey]
    workspace_root = os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    )
    path = os.path.join(workspace_root, bib["primary_source_path"])
    assert os.path.exists(path), (
        f"Primary source cache file missing at {path}."
    )
    assert os.path.getsize(path) > 100_000, (
        f"Primary source file too small at {path} (<100KB)."
    )


# ─── Substrate arithmetic sanity (Python mirror of Lean) ──────────────


def bravyi_kitaev_toffoli_t(n_toffoli: int) -> int:
    """Python mirror of Lean `bravyiKitaevToffoliT n := 7 * n`."""
    return 7 * n_toffoli


GOOGLE_ECC256_TOFFOLI = {"config1200": 90_000_000, "config1450": 70_000_000}


def google_shor_ecc256_tgate_bound(config: str) -> int:
    return bravyi_kitaev_toffoli_t(GOOGLE_ECC256_TOFFOLI[config])


def test_bravyi_kitaev_toffoli_t_seven_factor():
    for n in [0, 1, 7, 100, 1_000_000, 90_000_000]:
        assert bravyi_kitaev_toffoli_t(n) == 7 * n


def test_google_shor_ecc256_tgate_bound_config1200():
    """config1200: 7 × 90M = 630M T-gates (matches Lean theorem
    `googleShorECC256TGateBound_config1200_eq`)."""
    assert google_shor_ecc256_tgate_bound("config1200") == 630_000_000


def test_google_shor_ecc256_tgate_bound_config1450():
    """config1450: 7 × 70M = 490M T-gates."""
    assert google_shor_ecc256_tgate_bound("config1450") == 490_000_000


def test_config1450_t_strictly_less_than_config1200():
    """Substantive qubit-T trade-off (matches Lean
    `config1450_T_strictly_less_than_config1200`)."""
    assert google_shor_ecc256_tgate_bound("config1450") < google_shor_ecc256_tgate_bound("config1200")
    # Concrete savings: 140M T-gates by spending +250 qubits.
    diff = google_shor_ecc256_tgate_bound("config1200") - google_shor_ecc256_tgate_bound("config1450")
    assert diff == 140_000_000


def test_both_configs_fit_inside_1G_envelope():
    """Both Google configurations fit in the natural 1-G T-gate
    FT-QC envelope with concrete headroom (matches Lean
    `shor_ecc256_falls_within_megagate_envelope_at_1G`)."""
    one_g = 1_000_000_000
    assert google_shor_ecc256_tgate_bound("config1200") < one_g
    assert google_shor_ecc256_tgate_bound("config1450") < one_g
    # Concrete headroom: 370M / 510M.
    assert one_g - google_shor_ecc256_tgate_bound("config1200") == 370_000_000
    assert one_g - google_shor_ecc256_tgate_bound("config1450") == 510_000_000
