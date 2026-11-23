"""Adopted MIR scalar arithmetic and estimated-length comparisons.

Legacy names and return keys are preserved. A true comparison is not
verification of a physical CHHK model, its state or validity window.
The stored impurity momentum-relaxation lengths are fit estimates; their
identification with collective sqrt(tau*D) remains a physical obligation.
Canonical formulas live in src.core.formulas.
"""

from __future__ import annotations

from src.core.formulas import (
    graphene_mir_constant,
    graphene_mir_constant_mpmath,
)


# ──────────────────────────────────────────────────────────────────────
# Graphene experimental anchors
# ──────────────────────────────────────────────────────────────────────

#: Graphene lattice spacing a = 0.246 nm (= √3 · 0.142 nm = √3 · a_CC).
#:
#: Source: Castro Neto, Guinea, Peres, Novoselov, Geim, "The electronic
#: properties of graphene," Rev. Mod. Phys. 81, 109 (2009), §I.B.1
#: (Tight-Binding Hamiltonian) — the standard graphene lattice constant.
#: Cached primary source at
#: `Lit-Search/Phase-1-and-Background/primary-sources/CastroNeto2009RMPGraphene.pdf`.
GRAPHENE_LATTICE_SPACING_M: float = 0.246e-9

#: Stored S1 impurity momentum-relaxation fit estimate at 60 K.
#: Crossno arXiv:1509.04713v1 p.4 reports S1/S2/S3 estimates of
#: 1.5/0.6/0.034 micrometres. No identification with sqrt(tau*D) is made.
CROSSNO_GRAPHENE_MEAN_FREE_PATH_M: float = 1.5e-6

#: Stored S3/S2/S1 fitted-length range, not a measurement uncertainty.
#: Arithmetic ordering against a scalar does not verify CHHK applicability.
CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M: tuple[float, float, float] = (
    0.034e-6,  # S3
    0.6e-6,    # S2
    1.5e-6,    # S1
)


# Adopted d=2 scalar and supplied-ratio comparisons; legacy API names retained.

def graphene_mir_bound_constant() -> float:
    """Return the adopted d=2 scalar, about 0.075628928.

    The normalized Lean inequality 1/2 <= 1 and this scalar have distinct
    roles. Their numerical ordering proves no material identification.
    """
    return graphene_mir_constant()


def graphene_mir_constraint(ell_m: float, a_m: float = GRAPHENE_LATTICE_SPACING_M) -> bool:
    """Compare the supplied positive ratio ell_m/a_m with the adopted scalar.

    This boolean tests arithmetic only. Treat ell_m as a collective length
    for a physical bound only after independently establishing that
    identification and the applicable CHHK premises. No uniqueness follows.
    Raises ValueError for nonpositive ell_m or a_m.
    """
    if ell_m <= 0:
        raise ValueError(f"mean free path must be positive, got {ell_m}")
    if a_m <= 0:
        raise ValueError(f"lattice spacing must be positive, got {a_m}")
    return ell_m / a_m >= graphene_mir_bound_constant()


def crossno_graphene_satisfies_chhk_bound() -> dict:
    """Return scalar ratios and margins for the stored fitted-length inputs.

    Crossno arXiv:1509.04713v1 p.4 estimates impurity momentum-relaxation
    lengths S1=1.5, S2=0.6, S3=0.034 micrometres at 60 K. These are not
    direct measurements of the CHHK collective length. The same text
    distinguishes S3 from the more hydrodynamic S1/S2 samples.
    At a=0.246 nm, S1/S2/S3 ratios are about 6098/2439/138 and margins
    against the adopted scalar are about 8.1e4/3.2e4/1.8e3.
    All legacy keys retain their values and arithmetic meanings:
    ell_over_a_representative/per_sample are supplied-length ratios;
    mir_bound is the adopted scalar; margin_representative/per_sample
    divide those ratios by it; satisfies_bound_all_samples is only their
    all-samples scalar comparison, not physical applicability verification.
    """
    s3_ell, s2_ell, s1_ell = CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M
    a = GRAPHENE_LATTICE_SPACING_M
    mir_bound = graphene_mir_bound_constant()

    per_sample = {
        "S3": s3_ell / a,
        "S2": s2_ell / a,
        "S1": s1_ell / a,
    }
    margins = {k: v / mir_bound for k, v in per_sample.items()}

    return {
        "ell_over_a_representative": s1_ell / a,
        "ell_over_a_per_sample": per_sample,
        "mir_bound": mir_bound,
        "margin_representative": (s1_ell / a) / mir_bound,
        "margin_per_sample": margins,
        "satisfies_bound_all_samples": all(v >= mir_bound for v in per_sample.values()),
    }


def graphene_mir_constant_high_precision(dps: int = 30) -> str:
    """Return an mpmath decimal string for the adopted scalar.

    dps sets arithmetic precision. Exportability or precision does not
    establish a material bound, physical uncertainty or a Lean theorem.
    """
    import mpmath
    return mpmath.nstr(graphene_mir_constant_mpmath(dps), dps)
