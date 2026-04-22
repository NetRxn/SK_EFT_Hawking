"""
Phase 5x Wave 2: ℤ₁₆ Hidden Sector DM Candidate Classification

Computational companion to ``lean/SKEFTHawking/HiddenSectorClassification.lean``.
Enumerates minimal SM-singlet Weyl hidden-sector configurations that cancel the
Standard Model's ℤ₁₆ anomaly when right-handed neutrinos are absent, and maps
each viable configuration to known dark-matter candidate types.

Physics reference
-----------------
The three-generation Standard Model without ν_R has ℤ₁₆ anomaly index
3 × 15 = 45 ≡ 13 ≡ -3 mod 16 (formalized in
``Z16AnomalyComputation.three_gen_is_neg3``). To close the anomaly a
compensating SM-singlet hidden sector must contribute (N : ZMod 16) = 3
(formalized in ``HiddenSectorClassification.hidden_sector_anomaly_value``).

The particle-sector enumeration below gives the candidate counts (N) and
maps them to the Wang / Wan-Wang / García-Etxebarria taxonomy of
dark-sector types. The TQFT candidate T-0 (K-gauge, zero particle
content) is not enumerable here — it requires TQFT formalism deferred
to Phase 6.

Lean anchors
------------
- HiddenSectorClassification.anomaly_index_weyl_singlet (T1)
- HiddenSectorClassification.hidden_sector_anomaly_value (T2)
- HiddenSectorClassification.minimal_singlet_count (T3)
- HiddenSectorClassification.all_singlet_solutions_bounded (T10)
- HiddenSectorClassification.z4x_singlet_constraint (T11)
- HiddenSectorClassification.generation_independent_z16 (T12)
"""

from __future__ import annotations

from dataclasses import dataclass

#: ℤ₁₆ anomaly index of the three-generation SM without ν_R.
#:
#: 3 generations × 15 Weyl/gen = 45 ≡ 13 ≡ -3 mod 16. Matches
#: ``three_gen_is_neg3`` in Z16AnomalyComputation.lean.
SM_3GEN_NO_NUR_ANOMALY = 13

#: ℤ₁₆ index a compensating SM-singlet hidden sector must carry.
#:
#: Solves (13 + N) ≡ 0 mod 16; i.e. N ≡ 3 mod 16. Matches the RHS of
#: ``hidden_sector_anomaly_value`` in HiddenSectorClassification.lean.
HIDDEN_SECTOR_REQUIRED_INDEX = 3


def singlet_anomaly_index(n_weyl: int) -> int:
    """ℤ₁₆ anomaly index contributed by ``n_weyl`` SM-singlet Weyl fermions.

    Each Weyl fermion contributes +1 to the ℤ₁₆ index (per
    ``weyl_anomaly_unit`` in Z16AnomalyComputation.lean). The index is
    taken mod 16.

    Lean: ``HiddenSectorClassification.anomaly_index_weyl_singlet``.

    Parameters
    ----------
    n_weyl : int
        Number of SM-singlet Weyl fermions in the hidden sector. Must be
        non-negative.

    Returns
    -------
    int
        The ℤ₁₆ index in the range [0, 15].
    """
    if n_weyl < 0:
        raise ValueError(f"n_weyl must be non-negative, got {n_weyl}")
    return n_weyl % 16


def enumerate_bounded_solutions(max_n: int = 32) -> list[int]:
    """Enumerate SM-singlet Weyl counts N ≤ ``max_n`` with (N mod 16) = 3.

    For ``max_n = 32`` this returns ``[3, 19]`` — matching the Lean
    theorem ``all_singlet_solutions_bounded`` which proves the same
    equality as a Finset identity.

    Parameters
    ----------
    max_n : int, default 32
        Upper bound on N (inclusive of 0 through ``max_n``).

    Returns
    -------
    list[int]
        Sorted list of N ∈ [0, max_n] satisfying the ℤ₁₆ constraint.
    """
    return [
        n
        for n in range(max_n + 1)
        if singlet_anomaly_index(n) == HIDDEN_SECTOR_REQUIRED_INDEX
    ]


@dataclass(frozen=True)
class DMCandidate:
    """Metadata for a hidden-sector DM candidate.

    Attributes
    ----------
    tag : str
        Wang / Wan-Wang taxonomy tag (S-0, S-1, C-1, T-0, etc.).
    n_weyl : int
        Number of Weyl fermions in the particle sector. Zero for the
        TQFT candidate T-0.
    dm_types : tuple[str, ...]
        Observational DM channels this candidate can populate.
    detection_notes : str
        One-line summary of the leading experimental constraint or
        detection channel.
    singlet_cancellation : bool
        True iff the candidate's ℤ₁₆ anomaly cancellation follows from
        the pure SM-singlet rule ``N mod 16 == 3`` (Lean T2/T3/T10).
        False for mixed-charge candidates (C-1) whose cancellation
        requires ℤ₁₆ ⊕ ℤ₄ charge algebra, and for TQFT candidates (T-0)
        whose cancellation is topological.
    """

    tag: str
    n_weyl: int
    dm_types: tuple[str, ...]
    detection_notes: str
    singlet_cancellation: bool


#: Hidden-sector ↔ DM-type matching matrix.
#:
#: Derived from the deep-research document
#: ``Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter
#: Candidate Constraints.md`` §1.4. Only enumerable particle candidates
#: (S-0, S-1, C-1) are populated here; T-0 (TQFT, zero particles) is
#: included as a descriptor but carries ``n_weyl = 0`` since it has no
#: perturbative particle content.
DM_CANDIDATE_MATRIX: dict[str, DMCandidate] = {
    "S-0": DMCandidate(
        tag="S-0",
        n_weyl=3,
        dm_types=("sterile-neutrino",),
        detection_notes=(
            "Warm DM at 1-50 keV; X-ray constraint sin²(2θ) < 1e-10 at ~7 keV"
        ),
        singlet_cancellation=True,
    ),
    "S-1": DMCandidate(
        tag="S-1",
        n_weyl=19,
        dm_types=("dark-QCD-SU(N)-D-19-quarks",),
        detection_notes="Confinement scale free; dark hadrons as composite DM",
        singlet_cancellation=True,
    ),
    "C-1": DMCandidate(
        tag="C-1",
        n_weyl=8,
        dm_types=("dark-QCD-8-flavor",),
        detection_notes=(
            "7 q=-2, 1 q=6 mixed-charge; cancels via Z16⊕Z4 charge algebra "
            "(N mod 16 = 8 ≠ 3); compatible with 8-flavor dark SU(3); "
            "Wan-Wang arXiv:2512.25038 Table IV"
        ),
        singlet_cancellation=False,
    ),
    "T-0": DMCandidate(
        tag="T-0",
        n_weyl=0,
        dm_types=("topological",),
        detection_notes=(
            "K-gauge TQFT (K=ℤ₂ or ℤ₄) carrying anomaly index +3; zero particle "
            "content; invisible to LZ/XENONnT/DARWIN; physically preferred "
            "when ν_R is absent"
        ),
        singlet_cancellation=False,
    ),
}


def match_n_weyl_to_candidates(n_weyl: int) -> list[DMCandidate]:
    """Return DM candidates whose particle count matches ``n_weyl``.

    The T-0 topological candidate (``n_weyl = 0``) is returned only when
    ``n_weyl == 0``; otherwise only the matching particle candidates are
    returned.

    Parameters
    ----------
    n_weyl : int
        Hidden-sector Weyl count to look up.

    Returns
    -------
    list[DMCandidate]
        Zero or more matching candidates, ordered by tag.
    """
    return [c for c in DM_CANDIDATE_MATRIX.values() if c.n_weyl == n_weyl]


def verify_anomaly_cancellation(n_weyl: int) -> bool:
    """Check whether a hidden sector of ``n_weyl`` SM-singlet Weyl fermions
    cancels the 3-generation SM ℤ₁₆ anomaly.

    Equivalently: verifies that
    ``(SM_3GEN_NO_NUR_ANOMALY + n_weyl) mod 16 == 0``.

    Lean: ``HiddenSectorClassification.hidden_sector_anomaly_value``.

    Parameters
    ----------
    n_weyl : int

    Returns
    -------
    bool
    """
    return (SM_3GEN_NO_NUR_ANOMALY + n_weyl) % 16 == 0


def z4x_cubic_anomaly(x_charges: list[int]) -> int:
    """Perturbative U(1)_X³ anomaly sum ∑ X³ for a hidden fermion sector.

    The ℤ₁₆ constraint alone does NOT imply cancellation of this sum —
    see ``HiddenSectorClassification.z4x_singlet_constraint`` (T11),
    which exhibits a hidden sector satisfying ℤ₁₆ with ∑ X³ ≠ 0.

    Parameters
    ----------
    x_charges : list[int]
        The U(1)_X charges of the hidden-sector Weyl fermions.

    Returns
    -------
    int
        The sum ∑ X_i³. For a single-representation sector, this equals
        ``n * q**3`` where ``n = len(x_charges)`` and ``q`` is the common
        charge.
    """
    return sum(x**3 for x in x_charges)
