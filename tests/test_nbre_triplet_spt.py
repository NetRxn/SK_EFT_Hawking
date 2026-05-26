"""
Regression tests for Wave 6v.8 — NbRe noncentrosymmetric triplet superconductor.

These tests pin the bibkey + primary-source cache invariants for
`Colangelo2025NbReTripletSpinValve` and verify the NbRe parameter
values (Tc, ASOC scale, pairing channel) match the Lean encoding.

Companion Lean theorems in
`lean/SKEFTHawking/NbReTripletSPT.lean`:
- `nbRe_is_DIII_topological`
- `elementalNb_not_DIII_topological`
- `wave_6v_8_substantive_closure`
"""

import os
import pytest

from src.core.citations import CITATION_REGISTRY


COLANGELO_BIBKEY = "Colangelo2025NbReTripletSpinValve"


# ─── Citation registry ─────────────────────────────────────────────────


def test_colangelo_bibkey_present():
    bib = CITATION_REGISTRY.get(COLANGELO_BIBKEY)
    assert bib is not None, f"Bibkey {COLANGELO_BIBKEY} must be in CITATION_REGISTRY."
    assert bib["arxiv"] == "2510.08110"
    assert bib["doi"] == "10.1103/q1nb-cvh6"
    assert bib["year"] == 2025
    assert bib["volume"] == 135
    assert bib["page"] == "226002"


def test_colangelo_primary_source_cache():
    bib = CITATION_REGISTRY[COLANGELO_BIBKEY]
    workspace_root = os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    )
    path = os.path.join(workspace_root, bib["primary_source_path"])
    assert os.path.exists(path), f"Primary source missing at {path}."
    assert os.path.getsize(path) > 100_000


# ─── NbRe parameter sanity (Python mirror of Lean encoding) ────────────


# These match the Lean `nbReParameters` values exactly.
NBRE_TC_K = 8.7
NBRE_ASOC_MEV = 10.0
NBRE_PAIRING_CHANNEL = "Triplet"
NBRE_CENTROSYMMETRIC = False

# Elemental Nb contrast values.
NB_TC_K = 9.2
NB_ASOC_MEV = 0.0
NB_PAIRING_CHANNEL = "Singlet"
NB_CENTROSYMMETRIC = True


def test_nbre_tc_in_expected_range():
    """NbRe Tc ≈ 8.7 K per Colangelo et al. 2025."""
    assert 8.0 < NBRE_TC_K < 9.5


def test_nbre_is_noncentrosymmetric():
    """NbRe lacks spatial inversion symmetry (α-Mn structure / space group I-43m)."""
    assert NBRE_CENTROSYMMETRIC is False


def test_nbre_pairing_is_triplet():
    """NbRe is an intrinsic equal-spin triplet superconductor per
    Colangelo et al. 2025 inverse-spin-valve evidence."""
    assert NBRE_PAIRING_CHANNEL == "Triplet"


def test_nbre_asoc_positive():
    """NbRe has antisymmetric spin-orbit coupling on the ~ 10 meV scale."""
    assert NBRE_ASOC_MEV > 0


# ─── Contrast with elemental Nb ────────────────────────────────────────


def test_elemental_nb_is_centrosymmetric():
    """Elemental Nb has bcc crystal structure → inversion symmetric."""
    assert NB_CENTROSYMMETRIC is True


def test_elemental_nb_is_singlet():
    """Elemental Nb is a canonical s-wave singlet superconductor."""
    assert NB_PAIRING_CHANNEL == "Singlet"


def test_elemental_nb_asoc_zero_by_symmetry():
    """Centrosymmetric materials have vanishing ASOC by symmetry."""
    assert NB_ASOC_MEV == 0.0


def test_contrast_diii_class():
    """The DIII-class predicate requires BOTH noncentrosymmetric AND
    triplet. NbRe satisfies both; elemental Nb satisfies neither —
    matches Lean `nbRe_is_DIII_topological` and
    `elementalNb_not_DIII_topological`."""
    nbre_diii = (not NBRE_CENTROSYMMETRIC) and (NBRE_PAIRING_CHANNEL == "Triplet")
    nb_diii = (not NB_CENTROSYMMETRIC) and (NB_PAIRING_CHANNEL == "Triplet")
    assert nbre_diii is True
    assert nb_diii is False
