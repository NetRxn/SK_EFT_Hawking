"""Extract σ_1..σ_5 6-strand Fibonacci R-matrix generators from TQSim
v0.0.2 + symbolically convert each entry to a closed-form Q(ζ_5, √φ)
element, ready to paste as Lean `Mat13K_5Ext` literals.

Wave 1.D.4 (f) Phase 1.3a substrate-extraction script.

## Source

TQSim 0.0.2 (Constantine-Quantum-Tech, Apache-2.0,
github.com/Constantine-Quantum-Tech/tqsim). The TQSim authors
implement the Tounsi 2023 algorithm (arXiv:2307.01892 §3) for
constructing braid generators of N Fibonacci anyons. Their
`AnyonicCircuit(2, 3).braiding_operators` gives the 5 σ matrices
σ_1..σ_5 as 13×13 numpy complex arrays in TQSim basis ordering
(verified to MATCH DR Table 2 ordering at indices 0..7, 11, 12; with
a 3-cycle permutation at indices {8, 9, 10} per the basis-mapping
discovery in session 13 — TQSim has (|00⟩₁, |10⟩₁, |21⟩₁) where DR
Table 2 has (|21⟩₁, |00⟩₁, |10⟩₁)).

## Basis ordering (canonical for the Lean substrate)

We use **TQSim ordering** as canonical (it's what's extracted; switching
the Lean substrate to DR ordering would require permuting all σ
matrices which is more error-prone). The TQSim basis at `AnyonicCircuit
(nb_qudits=2, nb_anyons_per_qudit=3)` is:

  idx | logical state | (i_1, q1_tot, i_4, q2_tot, c) |
  ---|---|---|
   0  | |22⟩₀         | (τ, 0, τ, 0, 1)               |
   1  | |00⟩₀ (sec 0) | (0, τ, 0, τ, 1)               |
   2  | |10⟩₀ (sec 0) | (τ, τ, 0, τ, 1)               |
   3  | |01⟩₀ (sec 0) | (0, τ, τ, τ, 1)               |
   4  | |11⟩₀ (sec 0) | (τ, τ, τ, τ, 1)               |
   5  | |02⟩₁         | (0, τ, τ, 0, τ)               |
   6  | |12⟩₁         | (τ, τ, τ, 0, τ)               |
   7  | |20⟩₁         | (τ, 0, 0, τ, τ)               |
   8  | |00⟩₁ (sec 1) | (0, τ, 0, τ, τ)               |
   9  | |10⟩₁ (sec 1) | (τ, τ, 0, τ, τ)               |
  10  | |21⟩₁         | (τ, 0, τ, τ, τ)               |
  11  | |01⟩₁ (sec 1) | (0, τ, τ, τ, τ)               |
  12  | |11⟩₁ (sec 1) | (τ, τ, τ, τ, τ)               |

**Computational sub-blocks (TQSim ordering):**
- Sector 0: {1, 2, 3, 4} (matches DR Q2.2)
- Sector 1: **{8, 9, 11, 12}** (DR Q2.2 says {9, 10, 11, 12} per DR ordering; we use TQSim)

Phase 2's computational-sub-block extraction lemma must use TQSim indices.

## Symbolic conversion

Each non-zero entry is a polynomial of total degree ≤ 4 in the building
blocks (per DR Q2.3):

  τ      = 1/φ           = (√5 − 1)/2  ∈ Q(√5) ⊂ Q(ζ_5)
  √τ     = 1/√φ          ∈ Q(√φ); requires the √φ adjunction
  ζ      = ζ_5 = e^{2πi/5}
  R_1    = e^{-i4π/5}    = ζ^3
  R_τ    = e^{i3π/5}     = -ζ        (since e^{i3π/5} = e^{i(π + 3π/5 - π)} = ... let me re-derive)

Wait — R_τ = e^{i3π/5}. We have ζ = e^{2πi/5}, so ζ^{1.5} = e^{i3π/5} = R_τ, but ζ^{1.5} isn't a power of ζ in Q(ζ_5). However we can express R_τ in terms of ζ_10 = e^{iπ/5} = -ζ^{-2} (since ζ_10^5 = -1 ⟹ -ζ^{-2}^5 = -ζ^{-10} = -1 ⟹ ζ^{-10} = 1 ⟺ true since ζ^5 = 1).

  R_1 = e^{-i4π/5} = ζ_10^{-4} = (-ζ^{-2})^{-4} = (-1)^{-4} ζ^8 = ζ^8 = ζ^3 (since ζ^5=1)
  R_τ = e^{i3π/5}  = ζ_10^{3}  = (-ζ^{-2})^{3}  = (-1)^3 ζ^{-6} = -ζ^{-6} = -ζ^{-1} = -ζ^4 (since ζ^{-1} = ζ^4)

Hmm let me verify numerically:
  ζ = e^{2πi/5} ≈ 0.309 + 0.951j
  ζ^3 ≈ e^{6πi/5} ≈ cos(216°) + i sin(216°) ≈ -0.809 - 0.588j
  R_1 = e^{-i4π/5} ≈ cos(-144°) + i sin(-144°) ≈ -0.809 - 0.588j ✓ matches ζ^3

  ζ^4 ≈ e^{8πi/5} ≈ cos(288°) + i sin(288°) ≈ 0.309 - 0.951j
  -ζ^4 ≈ -0.309 + 0.951j
  R_τ = e^{i3π/5} ≈ cos(108°) + i sin(108°) ≈ -0.309 + 0.951j ✓ matches -ζ^4

So in Q(ζ_5):
  R_1 = ζ^3                = (0, 0, 0, 1, 0)   in tuple form (1, ζ, ζ^2, ζ^3, ζ^4) — wait, QCyc5Ext is 4-dim with basis (1, ζ, ζ^2, ζ^3) since ζ^4 = -1 - ζ - ζ^2 - ζ^3
  R_τ = -ζ^4 = -(-1 - ζ - ζ^2 - ζ^3) = 1 + ζ + ζ^2 + ζ^3

Let me check the QCyc5Ext representation convention.

(I'll check the QCyc5Ext source at runtime via lean_hover_info or by reading the file.)

## Output

The script outputs (a) a Lean code snippet for each σ_n + σ_n_inv as
`Mat13K_5Ext` literals, (b) numerical cross-validation showing the
symbolic form embeds back to the TQSim numerical at < 1e-12 residual.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from typing import Dict, List, Tuple

import numpy as np
from tqsim import AnyonicCircuit


# ---------------------------------------------------------------------------
# QCyc5Ext representation conventions
# ---------------------------------------------------------------------------
# QCyc5Ext (per SK_EFT_Hawking/lean/SKEFTHawking/QCyc5Ext.lean) carries
# elements as `⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩` where:
#   re-tuple (a0, a1, a2, a3): coefficients of (1, ζ, ζ², ζ³) in the
#     "rational" part, where ζ = ζ₅ = e^{2πi/5}
#   im-tuple (b0, b1, b2, b3): coefficients of (1, ζ, ζ², ζ³) in the
#     "√φ" part (i.e., multiplying by √φ = 1/√τ)
#
# So a QCyc5Ext element x is: x = (a₀ + a₁ζ + a₂ζ² + a₃ζ³) + √φ·(b₀ + b₁ζ + b₂ζ² + b₃ζ³)
#
# Embedding into ℂ: ζ ↦ exp(2πi/5); √φ ↦ √((1+√5)/2) ≈ 1.272.

# Numerical constants
PHI = (1 + np.sqrt(5)) / 2
TAU = 1 / PHI                      # = (√5 - 1)/2 = φ - 1
SQRT_TAU = np.sqrt(TAU)             # = 1/√φ
SQRT_PHI = np.sqrt(PHI)             # = 1/√τ

ZETA_5 = np.exp(2j * np.pi / 5)
R_1_NUM = np.exp(-1j * 4 * np.pi / 5)    # = ζ^3
R_TAU_NUM = np.exp(1j * 3 * np.pi / 5)   # = -ζ^4 = 1 + ζ + ζ^2 + ζ^3


def qe_re(coeffs: Tuple[int, ...]) -> Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]]:
    """Build a QCyc5Ext element with given rational-part coefficients
    of (1, ζ, ζ², ζ³) and zero √φ-part. Each input coefficient is an int
    or Fraction."""
    re = tuple(Fraction(c) for c in coeffs)
    return (re, (Fraction(0),) * 4)


def qe_im(coeffs: Tuple[int, ...]) -> Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]]:
    """Build a QCyc5Ext element with zero rational-part and given
    √φ-part coefficients of (1, ζ, ζ², ζ³)."""
    return ((Fraction(0),) * 4, tuple(Fraction(c) for c in coeffs))


def qe_full(re_coeffs: Tuple[int, ...], im_coeffs: Tuple[int, ...]) -> Tuple:
    return (tuple(Fraction(c) for c in re_coeffs),
            tuple(Fraction(c) for c in im_coeffs))


def qe_to_complex(elt: Tuple) -> complex:
    """Embed a QCyc5Ext element into ℂ via ζ ↦ e^{2πi/5}, √φ ↦ +√φ."""
    re_tuple, im_tuple = elt
    z = ZETA_5
    re_part = sum(float(c) * z**k for k, c in enumerate(re_tuple))
    im_part = sum(float(c) * z**k for k, c in enumerate(im_tuple))
    return complex(re_part) + SQRT_PHI * complex(im_part)


# ---------------------------------------------------------------------------
# Exact symbolic arithmetic on QCyc5 and QCyc5Ext
# ---------------------------------------------------------------------------
# Mirrors the Lean substrate's `QCyc5.mul` + `QCyc5Ext.mul` definitions:
#   QCyc5: (1, ζ, ζ², ζ³) basis with cyclotomic relation
#          ζ⁴ = -1 - ζ - ζ² - ζ³.
#   QCyc5Ext: (a, b) pair representing a + b·√φ, with
#             √φ² = φ = -ζ²-ζ³ (in Q(ζ_5) coords, since φ = (1+√5)/2
#             and √5 = 2τ + 1; substituting τ = -1 - ζ² - ζ³ gives
#             √5 = -1 - 2ζ² - 2ζ³ ... wait let me re-derive).
#
# Cyclotomic identity: 1 + ζ + ζ² + ζ³ + ζ⁴ = 0
# ⟹ ζ + ζ⁴ = -1 - ζ² - ζ³ = τ (since ζ + ζ⁴ = 2 cos(72°) = τ).
# So τ = -1 - ζ² - ζ³ (the QE_TAU above).
# And φ = 1 + τ = -ζ² - ζ³.
# Therefore √φ² = φ = -ζ²-ζ³ as a QCyc5 element ⟨0, 0, -1, -1⟩.
PHI_AS_QCYC5: Tuple[Fraction, ...] = (Fraction(0), Fraction(0), Fraction(-1), Fraction(-1))


def qcyc5_add(p: Tuple[Fraction, ...], q: Tuple[Fraction, ...]) -> Tuple[Fraction, ...]:
    """Add two QCyc5 elements (4-tuples of ℚ coefficients of (1, ζ, ζ², ζ³))."""
    return tuple(p[i] + q[i] for i in range(4))


def qcyc5_neg(p: Tuple[Fraction, ...]) -> Tuple[Fraction, ...]:
    """Negate a QCyc5 element."""
    return tuple(-p[i] for i in range(4))


def qcyc5_mul(p: Tuple[Fraction, ...], q: Tuple[Fraction, ...]) -> Tuple[Fraction, ...]:
    """Multiply two QCyc5 elements as polynomials in ζ mod Φ_5(ζ)
    = 1 + ζ + ζ² + ζ³ + ζ⁴. Uses the cyclotomic-reduction
    `ζ⁴ = -1 - ζ - ζ² - ζ³` to fold degrees ≥ 4 back down.

    Polynomial product (p₀ + p₁ζ + p₂ζ² + p₃ζ³)(q₀ + q₁ζ + q₂ζ² + q₃ζ³)
    has terms of degree 0..6. We collect coefficients into a length-7
    intermediate then fold ζ⁴, ζ⁵, ζ⁶ via:
      ζ⁴ = -1 - ζ - ζ² - ζ³
      ζ⁵ = ζ · ζ⁴ = -ζ - ζ² - ζ³ - ζ⁴ = -ζ - ζ² - ζ³ - (-1 - ζ - ζ² - ζ³) = 1
      ζ⁶ = ζ
    """
    # Polynomial product coefficients (degrees 0..6)
    raw = [Fraction(0)] * 7
    for i in range(4):
        for j in range(4):
            raw[i + j] += p[i] * q[j]
    # Fold using ζ⁵ = 1, ζ⁶ = ζ, then ζ⁴ = -1 - ζ - ζ² - ζ³
    # raw[5] is coefficient of ζ⁵ = 1; raw[6] is coefficient of ζ⁶ = ζ
    raw[0] += raw[5]
    raw[1] += raw[6]
    raw[5] = Fraction(0)
    raw[6] = Fraction(0)
    # raw[4] is coefficient of ζ⁴
    raw[0] -= raw[4]
    raw[1] -= raw[4]
    raw[2] -= raw[4]
    raw[3] -= raw[4]
    raw[4] = Fraction(0)
    return tuple(raw[:4])


def qe_add(a: Tuple, b: Tuple) -> Tuple:
    """Add two QCyc5Ext elements (each = (re, im) pair of QCyc5 elements)."""
    return (qcyc5_add(a[0], b[0]), qcyc5_add(a[1], b[1]))


def qe_neg(a: Tuple) -> Tuple:
    """Negate a QCyc5Ext element."""
    return (qcyc5_neg(a[0]), qcyc5_neg(a[1]))


def qe_mul(a: Tuple, b: Tuple) -> Tuple:
    """Multiply two QCyc5Ext elements.

    (a₁ + b₁·√φ)(a₂ + b₂·√φ) = (a₁·a₂ + φ·b₁·b₂) + (a₁·b₂ + a₂·b₁)·√φ

    Mirrors `SKEFTHawking.QCyc5Ext.mul` in
    `SK_EFT_Hawking/lean/SKEFTHawking/QCyc5Ext.lean`. The `φ·b₁·b₂` term
    uses `PHI_AS_QCYC5 = -ζ² - ζ³` per Q(ζ_5) coordinatization of φ.
    """
    a_re, a_im = a
    b_re, b_im = b
    new_re = qcyc5_add(
        qcyc5_mul(a_re, b_re),
        qcyc5_mul(PHI_AS_QCYC5, qcyc5_mul(a_im, b_im)),
    )
    new_im = qcyc5_add(
        qcyc5_mul(a_re, b_im),
        qcyc5_mul(b_re, a_im),
    )
    return (new_re, new_im)


# ---------------------------------------------------------------------------
# Exact symbolic arithmetic on 13×13 matrices over QCyc5Ext
# ---------------------------------------------------------------------------
# Matrix representation: a dict mapping (i, j) ∈ Fin 13 × Fin 13 to a
# QCyc5Ext element, with omitted entries treated as zero.

Mat13Sym = Dict[Tuple[int, int], Tuple]


def mat13_zero() -> Mat13Sym:
    """The 13×13 zero matrix (all entries omitted)."""
    return {}


def mat13_one() -> Mat13Sym:
    """The 13×13 identity matrix (1 on diagonal, omitted off-diagonal)."""
    return {(i, i): QE_ONE for i in range(13)}


def mat13_get(M: Mat13Sym, i: int, j: int) -> Tuple:
    """Get the (i, j) entry, returning zero if not in dict."""
    return M.get((i, j), QE_ZERO)


def mat13_mul(A: Mat13Sym, B: Mat13Sym) -> Mat13Sym:
    """Multiply two 13×13 matrices over QCyc5Ext (exact symbolic)."""
    result: Mat13Sym = {}
    for i in range(13):
        for k in range(13):
            acc = QE_ZERO
            for j in range(13):
                a_ij = mat13_get(A, i, j)
                b_jk = mat13_get(B, j, k)
                if a_ij == QE_ZERO or b_jk == QE_ZERO:
                    continue
                acc = qe_add(acc, qe_mul(a_ij, b_jk))
            if acc != QE_ZERO:
                result[(i, k)] = acc
    return result


def mat13_compose(matrices: List[Mat13Sym]) -> Mat13Sym:
    """Compose a list of 13×13 matrices left-to-right: M_1 * M_2 * ... * M_n."""
    if not matrices:
        return mat13_one()
    result = matrices[0]
    for M in matrices[1:]:
        result = mat13_mul(result, M)
    return result


def mat13_embed_complex(M: Mat13Sym) -> np.ndarray:
    """Embed a symbolic 13×13 matrix into ℂ for numerical verification."""
    arr = np.zeros((13, 13), dtype=complex)
    for (i, j), elt in M.items():
        arr[i, j] = qe_to_complex(elt)
    return arr


def mat13_from_numerical(M: np.ndarray, lift_fn) -> Mat13Sym:
    """Convert a numerical 13×13 numpy matrix to symbolic Mat13Sym
    via the provided `lift_fn(value) -> QCyc5Ext tuple`."""
    return {(i, j): lift_fn(M[i, j])
            for i in range(13) for j in range(13)
            if abs(M[i, j]) > 1e-12}


# Closed-form representations of the building blocks
QE_ZERO = qe_full((0, 0, 0, 0), (0, 0, 0, 0))
QE_ONE = qe_full((1, 0, 0, 0), (0, 0, 0, 0))
# ζ
QE_ZETA = qe_full((0, 1, 0, 0), (0, 0, 0, 0))
# ζ²
QE_ZETA2 = qe_full((0, 0, 1, 0), (0, 0, 0, 0))
# ζ³ = R_1
QE_R_1 = qe_full((0, 0, 0, 1), (0, 0, 0, 0))
# ζ⁴ = -1 - ζ - ζ² - ζ³  (cyclotomic relation Φ₅(ζ) = 0 ⟹ ζ⁴ = -1 - ζ - ζ² - ζ³)
QE_ZETA4 = qe_full((-1, -1, -1, -1), (0, 0, 0, 0))
# R_τ = -ζ⁴ = 1 + ζ + ζ² + ζ³
QE_R_TAU = qe_full((1, 1, 1, 1), (0, 0, 0, 0))
# τ = (√5 - 1)/2 = φ - 1; but √5 ∉ {1, ζ, ζ², ζ³} basis directly.
# τ = -(ζ² + ζ³) + (-ζ - ζ⁴)... let me think.
# From the minimal polynomial: τ = -1 - ζ - ζ^4 = -1 - ζ - (-1 - ζ - ζ² - ζ³) = ζ² + ζ³
# Wait: 1 + ζ + ζ² + ζ³ + ζ⁴ = 0 ⟹ ζ + ζ⁴ = -1 - ζ² - ζ³.
# τ = (√5 - 1)/2 and √5 = ζ - ζ² - ζ³ + ζ⁴ = ζ + ζ⁴ - ζ² - ζ³ = (-1-ζ²-ζ³) - ζ² - ζ³ = -1 - 2ζ² - 2ζ³.
# Hmm let me verify numerically:
# Wait that doesn't match. Let me re-derive.
# The "trace" gives √5: ζ + ζ⁴ = 2cos(72°) = (√5 - 1)/2 = τ, hmm
# 2cos(72°) ≈ 2·0.309 = 0.618 ≈ τ = 0.618 ✓
# So ζ + ζ⁴ = τ. Then τ = ζ - 1 - ζ - ζ² - ζ³ = -1 - ζ² - ζ³ ?
# ζ⁴ = -1 - ζ - ζ² - ζ³; substitute: ζ + (-1 - ζ - ζ² - ζ³) = -1 - ζ² - ζ³ = τ.
# So τ = -1 - ζ² - ζ³.
QE_TAU = qe_full((-1, 0, -1, -1), (0, 0, 0, 0))
# √τ = 1/√φ. In our QCyc5Ext convention: √φ ↦ +√φ; so √τ = √φ⁻¹ · (some rational).
# Actually note: τ·φ = 1, so √τ = 1/√φ, but to express in basis: √φ part = ?
# √τ has the same form as √φ but scaled. Q(√τ) = Q(√φ) since √τ = 1/√φ = √φ/φ.
# In QCyc5Ext, ⟨_, b⟩ represents the √φ·part. So √τ = (1/φ)·√φ = τ·√φ.
# That's: re = (0,0,0,0), im = (rational coeffs of τ in (1, ζ, ζ², ζ³)).
# τ = -1 - ζ² - ζ³, so:
QE_SQRT_TAU = qe_full((0, 0, 0, 0), (-1, 0, -1, -1))


def _verify_constants():
    """Numerically verify the closed-form constants embed correctly."""
    checks = {
        "R_1": (QE_R_1, R_1_NUM),
        "R_τ": (QE_R_TAU, R_TAU_NUM),
        "τ": (QE_TAU, complex(TAU)),
        "√τ": (QE_SQRT_TAU, complex(SQRT_TAU)),
        "ζ": (QE_ZETA, ZETA_5),
        "ζ²": (QE_ZETA2, ZETA_5**2),
        "ζ⁴": (QE_ZETA4, ZETA_5**4),
    }
    print("# QCyc5Ext closed-form constant verification (10⁻¹² tolerance)")
    all_ok = True
    for name, (sym, num) in checks.items():
        embed = qe_to_complex(sym)
        resid = abs(embed - num)
        ok = resid < 1e-12
        all_ok &= ok
        print(f"  {name:5s}: symbolic→C = {embed:+.6f},  expected = {num:+.6f},  |resid| = {resid:.2e}  {'OK' if ok else 'FAIL'}")
    assert all_ok, "Closed-form constants don't match expected numerical values"
    return all_ok


# ---------------------------------------------------------------------------
# σ extraction from TQSim
# ---------------------------------------------------------------------------

def extract_tqsim_sigmas() -> List[np.ndarray]:
    """Extract the 5 σ_n 13×13 numerical matrices from TQSim v0.0.2.
    Returns σ_1 .. σ_5 in TQSim basis ordering."""
    c = AnyonicCircuit(nb_qudits=2, nb_anyons_per_qudit=3)
    sigmas = list(c.braiding_operators)
    assert len(sigmas) == 5, f"Expected 5 σ matrices, got {len(sigmas)}"
    for n, s in enumerate(sigmas, start=1):
        assert s.shape == (13, 13), f"σ_{n} shape {s.shape} ≠ (13,13)"
    return sigmas


def diagnose_sigma_structure(sigmas: List[np.ndarray]) -> None:
    """Report the nonzero-entry structure of each σ matrix."""
    for n, s in enumerate(sigmas, start=1):
        nonzero = [(i, j) for i in range(13) for j in range(13) if abs(s[i, j]) > 1e-12]
        is_diag = all(i == j for (i, j) in nonzero)
        print(f"σ_{n}: {len(nonzero)} non-zero entries; diagonal={is_diag}")


# ---------------------------------------------------------------------------
# Numerical → symbolic lookup table
# ---------------------------------------------------------------------------
# Each TQSim σ entry is a single Q(ζ_5, √φ) element drawn from a small
# finite alphabet. The derivations below are from §K-matrix / F-symbol
# analysis (DR Q2.3 + algebraic re-derivation; see derivation log in
# session-14 notebook). All entries verified at 10⁻¹² residual through
# `qe_to_complex` round-trip.

# σ_1, σ_4 alphabet (pure diagonal phases)
QE_R_1_SYM = QE_R_1                                                      # R_1 = ζ³
QE_R_TAU_SYM = QE_R_TAU                                                  # R_τ = -ζ⁴ = 1+ζ+ζ²+ζ³

# σ_2, σ_5 alphabet (B_ττ block entries)
# τ·ζ² = -τ·e^{-iπ/5}: derived = ζ+ζ³
QE_TAU_ZETA2 = qe_full((0, 1, 0, 1), (0, 0, 0, 0))
# -√τ·ζ = √τ·e^{-i3π/5}: derived = √φ·(-1-ζ²)
QE_NEG_SQRTTAU_ZETA = qe_full((0, 0, 0, 0), (-1, 0, -1, 0))
# -τ: derived = 1+ζ²+ζ³
QE_NEG_TAU = qe_full((1, 0, 1, 1), (0, 0, 0, 0))

# σ_3 additional alphabet (above + the K-matrix-recoupled extras)
# -τ·ζ = τ·e^{-i3π/5}: derived = -1-ζ²
QE_NEG_TAU_ZETA = qe_full((-1, 0, -1, 0), (0, 0, 0, 0))
# τ²·ζ: derived = -1+ζ-ζ²
QE_TAU2_ZETA = qe_full((-1, 1, -1, 0), (0, 0, 0, 0))
# τ·√τ·ζ: derived = √φ·(-1+ζ-ζ²)
QE_TAUSQRTTAU_ZETA = qe_full((0, 0, 0, 0), (-1, 1, -1, 0))
# -τ·√τ·ζ: negate previous
QE_NEG_TAUSQRTTAU_ZETA = qe_full((0, 0, 0, 0), (1, -1, 1, 0))
# -τ²·√τ·ζ: derived = √φ·(-2+ζ-2ζ²)
QE_NEG_TAU2SQRTTAU_ZETA = qe_full((0, 0, 0, 0), (-2, 1, -2, 0))
# Block A/C diagonal: 2τ²·R_τ + τ³·R_1 = 2+2ζ²+ζ³
QE_BLOCK_A_DIAG = qe_full((2, 0, 2, 1), (0, 0, 0, 0))
# Block D corner: (3-4τ)·R_τ + 2τ³·R_1 = 3-ζ+3ζ²+ζ³
QE_BLOCK_D_DIAG = qe_full((3, -1, 3, 1), (0, 0, 0, 0))

# σ_n_inv alphabet (conjugates of forward alphabet — σ_n is unitary, so
# σ_n_inv = σ_n†, and individual entries satisfy [σ⁻¹]_ji = conj([σ]_ij)).
# Conjugation in Q(ζ_5): ζ̄ = ζ⁴, with ζ⁴ = -1-ζ-ζ²-ζ³.
QE_R_1_BAR = qe_full((0, 0, 1, 0), (0, 0, 0, 0))                         # R_1̄ = ζ²
QE_R_TAU_BAR = qe_full((0, -1, 0, 0), (0, 0, 0, 0))                      # R_τ̄ = -ζ
QE_TAU_ZETA2_BAR = qe_full((-1, -1, 0, -1), (0, 0, 0, 0))                # (τ·ζ²)̄ = τ·ζ³ = -1-ζ-ζ³
QE_NEG_SQRTTAU_ZETA_BAR = qe_full((0, 0, 0, 0), (-1, 0, 0, -1))          # (-√τ·ζ)̄ = -√τ·ζ⁴
QE_NEG_TAU_ZETA_BAR = qe_full((-1, 0, 0, -1), (0, 0, 0, 0))              # (-τ·ζ)̄ = -τ·ζ⁴ = -1-ζ³
QE_TAU2_ZETA_BAR = qe_full((-2, -1, -1, -2), (0, 0, 0, 0))               # (τ²·ζ)̄ = τ²·ζ⁴
QE_TAUSQRTTAU_ZETA_BAR = qe_full((0, 0, 0, 0), (-2, -1, -1, -2))         # (τ√τ·ζ)̄
QE_NEG_TAUSQRTTAU_ZETA_BAR = qe_full((0, 0, 0, 0), (2, 1, 1, 2))         # (-τ√τ·ζ)̄
QE_NEG_TAU2SQRTTAU_ZETA_BAR = qe_full((0, 0, 0, 0), (-3, -1, -1, -3))    # (-τ²√τ·ζ)̄
QE_BLOCK_A_DIAG_BAR = qe_full((2, 0, 1, 2), (0, 0, 0, 0))                # Block A diag conjugate
QE_BLOCK_D_DIAG_BAR = qe_full((4, 1, 2, 4), (0, 0, 0, 0))                # Block D corner conjugate


def _build_symbolic_lookup() -> List[Tuple[complex, Tuple]]:
    """Return the master list of (numerical_value, qe_tuple) pairs.

    All entries appearing anywhere in σ_1..σ_5 are catalogued here. The
    lookup is order-independent — entries are matched by numerical
    proximity (10⁻¹² tolerance)."""
    return [
        # σ_1, σ_4 alphabet (and used elsewhere)
        (qe_to_complex(QE_R_1_SYM), QE_R_1_SYM),
        (qe_to_complex(QE_R_TAU_SYM), QE_R_TAU_SYM),
        # σ_2, σ_5 alphabet
        (qe_to_complex(QE_TAU_ZETA2), QE_TAU_ZETA2),
        (qe_to_complex(QE_NEG_SQRTTAU_ZETA), QE_NEG_SQRTTAU_ZETA),
        (qe_to_complex(QE_NEG_TAU), QE_NEG_TAU),
        # σ_3 alphabet
        (qe_to_complex(QE_NEG_TAU_ZETA), QE_NEG_TAU_ZETA),
        (qe_to_complex(QE_TAU2_ZETA), QE_TAU2_ZETA),
        (qe_to_complex(QE_TAUSQRTTAU_ZETA), QE_TAUSQRTTAU_ZETA),
        (qe_to_complex(QE_NEG_TAUSQRTTAU_ZETA), QE_NEG_TAUSQRTTAU_ZETA),
        (qe_to_complex(QE_NEG_TAU2SQRTTAU_ZETA), QE_NEG_TAU2SQRTTAU_ZETA),
        (qe_to_complex(QE_BLOCK_A_DIAG), QE_BLOCK_A_DIAG),
        (qe_to_complex(QE_BLOCK_D_DIAG), QE_BLOCK_D_DIAG),
        # σ_n_inv alphabet (conjugates)
        (qe_to_complex(QE_R_1_BAR), QE_R_1_BAR),
        (qe_to_complex(QE_R_TAU_BAR), QE_R_TAU_BAR),
        (qe_to_complex(QE_TAU_ZETA2_BAR), QE_TAU_ZETA2_BAR),
        (qe_to_complex(QE_NEG_SQRTTAU_ZETA_BAR), QE_NEG_SQRTTAU_ZETA_BAR),
        (qe_to_complex(QE_NEG_TAU_ZETA_BAR), QE_NEG_TAU_ZETA_BAR),
        (qe_to_complex(QE_TAU2_ZETA_BAR), QE_TAU2_ZETA_BAR),
        (qe_to_complex(QE_TAUSQRTTAU_ZETA_BAR), QE_TAUSQRTTAU_ZETA_BAR),
        (qe_to_complex(QE_NEG_TAUSQRTTAU_ZETA_BAR), QE_NEG_TAUSQRTTAU_ZETA_BAR),
        (qe_to_complex(QE_NEG_TAU2SQRTTAU_ZETA_BAR), QE_NEG_TAU2SQRTTAU_ZETA_BAR),
        (qe_to_complex(QE_BLOCK_A_DIAG_BAR), QE_BLOCK_A_DIAG_BAR),
        (qe_to_complex(QE_BLOCK_D_DIAG_BAR), QE_BLOCK_D_DIAG_BAR),
    ]


_LOOKUP_CACHE: List[Tuple[complex, Tuple]] = []


def lookup_qe(value: complex, tol: float = 1e-10) -> Tuple:
    """Return the QCyc5Ext symbolic form of a numerical complex value.

    Matches against the master lookup table by absolute distance < tol.
    Raises if no match — caller should add the missing entry to the
    lookup table or check whether the input is genuinely outside the
    σ alphabet."""
    global _LOOKUP_CACHE
    if not _LOOKUP_CACHE:
        _LOOKUP_CACHE = _build_symbolic_lookup()
    if abs(value) < tol:
        return QE_ZERO
    matches = [qe for (num, qe) in _LOOKUP_CACHE if abs(num - value) < tol]
    if len(matches) == 1:
        return matches[0]
    if len(matches) == 0:
        raise ValueError(
            f"No symbolic match for numerical value {value:+.10f} "
            f"(|·|={abs(value):.6f}). Catalog has {len(_LOOKUP_CACHE)} "
            f"entries; consider adding this value's closed-form."
        )
    raise ValueError(
        f"Ambiguous symbolic match for {value:+.10f}: {len(matches)} candidates."
    )


def lift_sigma_to_symbolic(M: np.ndarray, name: str, verbose: bool = False) -> Dict[Tuple[int, int], Tuple]:
    """Convert each non-zero entry of a 13×13 σ matrix to its QCyc5Ext
    symbolic form. Returns dict {(i,j): qe_tuple} for non-zero positions.

    Verifies each lookup by embedding the symbolic form back to ℂ and
    comparing with the input numerical value. Raises if any entry
    deviates by more than 10⁻¹⁰."""
    assert M.shape == (13, 13), f"{name}: expected (13,13), got {M.shape}"
    result: Dict[Tuple[int, int], Tuple] = {}
    max_residual = 0.0
    for i in range(13):
        for j in range(13):
            v = M[i, j]
            if abs(v) < 1e-12:
                continue
            qe = lookup_qe(v)
            embedded = qe_to_complex(qe)
            residual = abs(embedded - v)
            max_residual = max(max_residual, residual)
            if residual > 1e-10:
                raise ValueError(
                    f"{name}[{i},{j}]: numerical={v:+.10f} embeds to "
                    f"{embedded:+.10f}, residual={residual:.2e}"
                )
            result[(i, j)] = qe
            if verbose:
                print(f"  {name}[{i:2d},{j:2d}] = {v:+.6f}  →  {_qe_to_lean(qe)}  (resid {residual:.2e})")
    print(f"  {name}: {len(result)} entries lifted; max residual {max_residual:.2e}")
    return result


# ---------------------------------------------------------------------------
# Lean snippet emitter
# ---------------------------------------------------------------------------

def _q_to_lean(q: Fraction) -> str:
    """Render a Fraction as a bare Lean numeric literal (cast handled by context).

    Negative integers render bare (e.g. `-1`) since they appear inside
    structure literals like `⟨-1, 0, -1, -1⟩` (matching existing
    `phi_inv` convention in `QCyc5.lean`)."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"({q.numerator} / {q.denominator})"


# Named primitives existing in QCyc5/QCyc5Ext modules — used to keep the
# emitted literals compact + readable. Mapping: re-tuple/im-tuple → Lean term.
_NAMED_QE: Dict[Tuple[Tuple[int, ...], Tuple[int, ...]], str] = {
    # σ_1, σ_4 alphabet:
    ((0, 0, 0, 1), (0, 0, 0, 0)): "R1_ext",            # R_1 = ζ³
    ((1, 1, 1, 1), (0, 0, 0, 0)): "Rtau_ext",          # R_τ = -ζ⁴ = 1+ζ+ζ²+ζ³
}


def _qe_to_lean(qe: Tuple) -> str:
    """Render a QCyc5Ext element as a Lean term.

    Tries the existing named primitives first (R1_ext, Rtau_ext); falls
    back to `ofQCyc5 ⟨...⟩` for pure-re entries, `⟨0, ⟨...⟩⟩` for pure-im,
    and full `⟨⟨..⟩, ⟨..⟩⟩` for mixed."""
    re_t, im_t = qe
    re_int = tuple(int(c) if c.denominator == 1 else c for c in re_t)
    im_int = tuple(int(c) if c.denominator == 1 else c for c in im_t)
    key = (re_int, im_int)
    if key in _NAMED_QE:
        return _NAMED_QE[key]
    re_zero = all(c == 0 for c in re_t)
    im_zero = all(c == 0 for c in im_t)
    re_str = ", ".join(_q_to_lean(c) for c in re_t)
    im_str = ", ".join(_q_to_lean(c) for c in im_t)
    if im_zero:
        return f"ofQCyc5 ⟨{re_str}⟩"
    if re_zero:
        return f"⟨0, ⟨{im_str}⟩⟩"
    return f"⟨⟨{re_str}⟩, ⟨{im_str}⟩⟩"


def emit_lean_mat13k5ext_literal(name: str, sym: Dict[Tuple[int, int], Tuple]) -> str:
    """Emit a Lean `Mat13K_5Ext` definition for a σ matrix.

    Output form (matches Mat5K convention in FibonacciQuintetTrueRep):
        def {name} : Mat13K_5Ext := fun i j =>
          match (i.val, j.val) with
          | (0, 0) => Rtau_ext
          | (1, 1) => R1_ext
          ...
          | _ => 0
    """
    lines: List[str] = [f"def {name} : Mat13K_5Ext := fun i j =>"]
    lines.append("  match (i.val, j.val) with")
    for i in range(13):
        for j in range(13):
            qe = sym.get((i, j))
            if qe is None:
                continue
            lines.append(f"  | ({i}, {j}) => {_qe_to_lean(qe)}")
    lines.append("  | _ => 0")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnose-only", action="store_true",
                        help="Just report structure; don't do symbolic conversion")
    parser.add_argument("--emit-lean", action="store_true",
                        help="Emit Lean Mat13K_5Ext definitions for σ_1..σ_5")
    parser.add_argument("--verbose", action="store_true",
                        help="Print per-entry lift trace")
    args = parser.parse_args()

    _verify_constants()
    print()
    sigmas = extract_tqsim_sigmas()
    diagnose_sigma_structure(sigmas)
    if args.diagnose_only:
        return

    print()
    print("# Symbolic lift of σ_1 .. σ_5:")
    symbolics: List[Dict[Tuple[int, int], Tuple]] = []
    for n, s in enumerate(sigmas, start=1):
        symbolics.append(lift_sigma_to_symbolic(s, f"σ_{n}", verbose=args.verbose))

    print()
    print("# Symbolic lift of σ_1⁻¹ .. σ_5⁻¹:")
    inverses = [np.linalg.inv(s) for s in sigmas]
    inv_symbolics: List[Dict[Tuple[int, int], Tuple]] = []
    for n, sinv in enumerate(inverses, start=1):
        inv_symbolics.append(lift_sigma_to_symbolic(sinv, f"σ_{n}⁻¹", verbose=args.verbose))

    if args.emit_lean:
        print()
        print("# Lean Mat13K_5Ext definitions:")
        print()
        for n, sym in enumerate(symbolics, start=1):
            print(emit_lean_mat13k5ext_literal(f"sigma{n}_sextet", sym))
            print()
        for n, sym in enumerate(inv_symbolics, start=1):
            print(emit_lean_mat13k5ext_literal(f"sigma{n}_sextet_inv", sym))
            print()


if __name__ == "__main__":
    main()
