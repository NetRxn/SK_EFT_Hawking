"""Validate the Phase 6x Item G phase bridge BEFORE formalizing.

KMM gateMatrixes embed (via toComplexMat) to U(2) matrices (det ωᵏ); the SK headline's
ρ_CliffT lands in SU(2). The bridge: toComplexMat(gateMatrix g) = gatePhase(g)·ρ_CliffT(gateWord g),
where gateWord : CliffordTGate → FreeGroup⟨H,T⟩ (of0=H_SU, of1=T_SU) and gatePhase(g)∈U(1).

Checks:
  (1) For each gate g, the proposed gateWord g + gatePhase g satisfy
      toComplexMat(gateMatrix g) = gatePhase(g) · ρ_CliffT(gateWord g)  (matrix identity).
  (2) For random KMM words gs (incl. the ω gate), the accumulated phase ∏gatePhase factors
      out and ρ_CliffT(concat gateWords) = (∏gatePhase)⁻¹ · toComplexMat(interp gs).
  (3) When interp gs is det-1 (SU(2)), ∏gatePhase = ±1 (the residual sign), and
      -I = ρ_CliffT(H·H) so the sign is correctable by appending HH.
"""
from __future__ import annotations
import numpy as np

w = np.exp(1j * np.pi / 4)          # ω = e^{iπ/4}
I2 = np.eye(2, dtype=complex)
isqrt2 = 1 / np.sqrt(2)

# KMM gateMatrix → ℂ (U(2), the toComplexMat images)
GM = {
    'H': isqrt2 * np.array([[1, 1], [1, -1]], dtype=complex),
    'S': np.array([[1, 0], [0, 1j]], dtype=complex),
    'T': np.array([[1, 0], [0, w]], dtype=complex),
    'X': np.array([[0, 1], [1, 0]], dtype=complex),
    'Y': np.array([[0, -1j], [1j, 0]], dtype=complex),
    'Z': np.array([[1, 0], [0, -1]], dtype=complex),
    'id': I2.copy(),
    'omega': w * I2,
}

# SU(2) generators ρ_CliffT(of 0)=H_SU, ρ_CliffT(of 1)=T_SU
H_SU = (1j * isqrt2) * np.array([[1, 1], [1, -1]], dtype=complex)
T_SU = np.array([[np.exp(-1j * np.pi / 8), 0], [0, np.exp(1j * np.pi / 8)]], dtype=complex)

def rho(word):
    """ρ_CliffT of an H/T word (list of 'H'/'T'), left-to-right product."""
    M = I2.copy()
    for g in word:
        M = M @ (H_SU if g == 'H' else T_SU)
    return M

# proposed gateWord (over H_SU,T_SU) — S=T², Z=T⁴, X=H Z H, Y=S X S† ... validated numerically
GATEWORD = {
    'H': ['H'],
    'T': ['T'],
    'S': ['T', 'T'],
    'Z': ['T', 'T', 'T', 'T'],
    'X': ['H', 'T', 'T', 'T', 'T', 'H'],
    'Y': ['T', 'T', 'H', 'T', 'T', 'T', 'T', 'H', 'T', 'T', 'T', 'T', 'T', 'T'],  # to be solved below
    'id': [],
    'omega': [],
}

def closest_phase(A, B):
    """φ minimizing ‖A - φB‖ over U(1); returns (φ, residual)."""
    # φ = <B,A>/|<B,A>| (Frobenius); for A=φB exactly, φ = (A/B entrywise)[nonzero]
    num = np.vdot(B, A)
    if abs(num) < 1e-12:
        return None, 1.0
    phi = num / abs(num)
    return phi, np.linalg.norm(A - phi * B)

# ── solve Y's word by brute force over short H/T words (Y = phase · ρ(word)) ──
def solve_word(target, maxlen=8):
    from itertools import product
    for n in range(maxlen + 1):
        for word in product('HT', repeat=n):
            phi, res = closest_phase(target, rho(list(word)))
            if res < 1e-9:
                return list(word), phi
    return None, None

print("=== (1) per-gate bridge: toComplexMat(gateMatrix g) = gatePhase · ρ_CliffT(gateWord g) ===")
gatePhase = {}
for g, M in GM.items():
    word = GATEWORD[g]
    phi, res = closest_phase(M, rho(word))
    if res is None or res > 1e-9:
        # try to solve
        sword, sphi = solve_word(M)
        print(f"  {g:6s}: proposed word FAILED (res={res}); SOLVED word={sword} phase={sphi}")
        if sword is not None:
            GATEWORD[g] = sword; gatePhase[g] = sphi
    else:
        gatePhase[g] = phi
        # express phase as power of e^{iπ/8} (16th root)
        k16 = round(np.angle(phi) / (np.pi / 8)) % 16
        print(f"  {g:6s}: word={''.join(word) or '∅':10s} phase=e^{{iπ·{k16}/8}}  (res={res:.1e})")

print("\n=== (2)+(3) random KMM words: ∏gatePhase factors out; det-1 ⟹ ∏phase=±1 ===")
import random
GATES = list(GM.keys())
rng = random.Random(0)
bad = 0; signs = {1: 0, -1: 0, 'other': 0}
for trial in range(2000):
    gs = [rng.choice(GATES) for _ in range(rng.randint(0, 10))]
    M = I2.copy()
    for g in gs:
        M = M @ GM[g]
    word = []
    phaseprod = 1 + 0j
    for g in gs:
        word += GATEWORD[g]; phaseprod *= gatePhase[g]
    # check toComplexMat(interp gs) = phaseprod · ρ_CliffT(word)
    if np.linalg.norm(M - phaseprod * rho(word)) > 1e-7:
        bad += 1
    # det-1 case
    if abs(np.linalg.det(M) - 1) < 1e-7:
        if abs(phaseprod - 1) < 1e-7: signs[1] += 1
        elif abs(phaseprod + 1) < 1e-7: signs[-1] += 1
        else: signs['other'] += 1

print(f"  word-level bridge failures (M ≠ ∏phase·ρ(word)) : {bad}/2000")
print(f"  det-1 words: ∏phase=+1: {signs[1]}, =-1: {signs[-1]}, other: {signs['other']}")
# -I correctable by HH?
print(f"  ρ_CliffT(H·H) = -I ? {np.linalg.norm(rho(['H','H']) + I2) < 1e-9}")
print("\nVERDICT:", "SAFE — per-gate + word bridge hold; det-1 ⟹ ±1 sign (HH-correctable)"
      if bad == 0 and signs['other'] == 0 else "NEEDS REWORK")
