"""Compute EXACT rational Frobenius² distance for the L=46 T-gate braid against ζ_40^k · T_NC target.

This mimics the Lean computation exactly:
  - QCyc40 = Q[x]/Φ_40(x) where Φ_40(x) = x^16 - x^12 + x^8 - x^4 + 1
  - QCyc40Ext = QCyc40[w]/(w² - φ)
  - Mat2K_40_Ext = Fin 2 × Fin 2 → QCyc40Ext
  - frobNormSq_ext(M, N) = sum_{i,j} (M_ij - N_ij)² (NO conjugation!)
"""
from __future__ import annotations
from fractions import Fraction


def qcyc40_zero(): return [Fraction(0)] * 16
def qcyc40_one():
    z = [Fraction(0)] * 16; z[0] = Fraction(1); return z
def qcyc40_neg(a): return [-x for x in a]
def qcyc40_add(a, b): return [a[i] + b[i] for i in range(16)]
def qcyc40_sub(a, b): return [a[i] - b[i] for i in range(16)]


def qcyc40_mul(a, b):
    """Multiplication in Q[x]/Φ_40(x) where Φ_40 = x^16 - x^12 + x^8 - x^4 + 1.
    Mirrors PolyQuotQ.mulReduce 16 in Lean.
    """
    # Polynomial multiply
    r = [Fraction(0)] * 32
    for i in range(16):
        if a[i] == 0:
            continue
        for j in range(16):
            r[i+j] += a[i] * b[j]
    # Reduce: x^k for k >= 16 → x^{k-16} · (x^12 - x^8 + x^4 - 1)
    # = x^{k-4} - x^{k-8} + x^{k-12} - x^{k-16}
    for k in range(31, 15, -1):
        c = r[k]
        if c == 0:
            continue
        r[k - 4] += c
        r[k - 8] -= c
        r[k - 12] += c
        r[k - 16] -= c
        r[k] = Fraction(0)
    return r[:16]


# Verify ζ_40^20 = -1 in this implementation
def test_qcyc40():
    zeta = qcyc40_zero(); zeta[1] = Fraction(1)
    z20 = qcyc40_one()
    for _ in range(20):
        z20 = qcyc40_mul(z20, zeta)
    expected = qcyc40_neg(qcyc40_one())
    assert z20 == expected, f"ζ^20 != -1: {z20}"
test_qcyc40()


# φ = (1+√5)/2. We need φ in QCyc40 basis. Let's look up the existing Lean definition.
# Per QCyc40.lean, phi is defined as some specific 16-tuple. Let me reconstruct from
# the math: ζ_5 = ζ_40^8. √5 = ζ_5 + ζ_5^{-1} - ζ_5^2 - ζ_5^{-2} (via Gauss sum)
# Actually: √5 = ζ_5 - ζ_5^2 - ζ_5^3 + ζ_5^4 (the Legendre Gauss sum)
# Let me verify numerically:
import math
omega = math.cos(2*math.pi/5) + 1j*math.sin(2*math.pi/5)
sum_test = omega - omega**2 - omega**3 + omega**4
# This should equal √5
# Re(sum) = cos(2π/5) - cos(4π/5) - cos(6π/5) + cos(8π/5) = cos(72°) - cos(144°) - cos(216°) + cos(288°)
# = 0.309 - (-0.809) - (-0.809) + 0.309 = 0.309+0.809+0.809+0.309 = 2.236 = √5. OK!
# Im should be 0 by symmetry. ✓
# So √5 = ζ_5 - ζ_5² - ζ_5³ + ζ_5^4 = ζ_40^8 - ζ_40^16 + ζ_40^24 + ζ_40^32 - wait redo: ζ_5^k = ζ_40^(8k).
# √5 = ζ_40^8 - ζ_40^16 - ζ_40^24 + ζ_40^32
# Reduce ζ_40^16 = ζ_40^12 - ζ_40^8 + ζ_40^4 - 1
# Reduce ζ_40^24 = -ζ_40^4 (since ζ_40^20 = -1)
# Reduce ζ_40^32 = -ζ_40^12 (since ζ_40^20 = -1)
# So √5 = ζ_40^8 - (ζ_40^12 - ζ_40^8 + ζ_40^4 - 1) - (-ζ_40^4) + (-ζ_40^12)
#       = ζ_40^8 - ζ_40^12 + ζ_40^8 - ζ_40^4 + 1 + ζ_40^4 - ζ_40^12
#       = 2·ζ_40^8 - 2·ζ_40^12 + 1
# Coefficients: c_0=1, c_8=2, c_12=-2, others 0
sqrt5_qcyc40 = qcyc40_zero()
sqrt5_qcyc40[0] = Fraction(1)
sqrt5_qcyc40[8] = Fraction(2)
sqrt5_qcyc40[12] = Fraction(-2)
# Verify (sqrt5)² = 5
sqrt5_sq = qcyc40_mul(sqrt5_qcyc40, sqrt5_qcyc40)
five = qcyc40_zero(); five[0] = Fraction(5)
assert sqrt5_sq == five, f"(√5)² != 5: {sqrt5_sq}"
print(f"  √5 verified: {sqrt5_qcyc40}")

# φ = (1+√5)/2 = 1/2 + √5/2
phi_qcyc40 = [Fraction(c) / Fraction(2) for c in sqrt5_qcyc40]
phi_qcyc40[0] += Fraction(1, 2)
# φ² = φ + 1 sanity
phi_sq = qcyc40_mul(phi_qcyc40, phi_qcyc40)
phi_plus_one = list(phi_qcyc40)
phi_plus_one[0] += Fraction(1)
assert phi_sq == phi_plus_one, f"φ² != φ+1: {phi_sq} vs {phi_plus_one}"
print(f"  φ verified")

# φ^-1 = (√5 - 1)/2. Sanity: φ · φ^-1 = 1.
phi_inv = [Fraction(c) / Fraction(2) for c in sqrt5_qcyc40]
phi_inv[0] -= Fraction(1, 2)
phi_times_phi_inv = qcyc40_mul(phi_qcyc40, phi_inv)
assert phi_times_phi_inv == qcyc40_one(), f"φ·φ⁻¹ != 1: {phi_times_phi_inv}"
print(f"  φ⁻¹ verified")


# QCyc40Ext = pair (re, im) representing re + im·w where w² = φ
# (a + bw)(c + dw) = (ac + bd·φ) + (ad + bc)·w
def ext_zero(): return (qcyc40_zero(), qcyc40_zero())
def ext_one(): return (qcyc40_one(), qcyc40_zero())
def ext_neg(x): return (qcyc40_neg(x[0]), qcyc40_neg(x[1]))
def ext_add(x, y): return (qcyc40_add(x[0], y[0]), qcyc40_add(x[1], y[1]))
def ext_sub(x, y): return (qcyc40_sub(x[0], y[0]), qcyc40_sub(x[1], y[1]))
def ext_mul(x, y):
    a, b = x; c, d = y
    re = qcyc40_add(qcyc40_mul(a, c), qcyc40_mul(qcyc40_mul(b, d), phi_qcyc40))
    im = qcyc40_add(qcyc40_mul(a, d), qcyc40_mul(b, c))
    return (re, im)
def ext_of_qcyc40(x): return (x, qcyc40_zero())


# Build σ₁, σ₂, σ₁⁻¹, σ₂⁻¹ in Mat2K_40_Ext
# σ₁ = diag(R1, Rτ); σ₂ = F · σ₁ · F where F = ((φ⁻¹, φ⁻¹·w), (φ⁻¹·w, -φ⁻¹))
# R1 = -ζ⁴ in QCyc40 (c_4 = -1)
R1_q = qcyc40_zero(); R1_q[4] = Fraction(-1)
# Rτ = ζ¹² (c_12 = 1)
Rtau_q = qcyc40_zero(); Rtau_q[12] = Fraction(1)
# R1⁻¹ = e^(i4π/5) = ζ_5^{-3} = ζ_5² = ζ_40^16 = ζ_40^12 - ζ_40^8 + ζ_40^4 - 1
R1_inv_q = qcyc40_zero()
R1_inv_q[0] = Fraction(-1)
R1_inv_q[4] = Fraction(1)
R1_inv_q[8] = Fraction(-1)
R1_inv_q[12] = Fraction(1)
# Verify R1 · R1_inv = 1
test = qcyc40_mul(R1_q, R1_inv_q)
assert test == qcyc40_one(), f"R1·R1⁻¹ != 1: {test}"
# Rτ⁻¹ = e^(-i3π/5) = ζ_10^{-3} = ζ_10^7 = ζ_40^28 = -ζ_40^8 (since ζ^20=-1, ζ^28 = ζ^8 · -1)
Rtau_inv_q = qcyc40_zero(); Rtau_inv_q[8] = Fraction(-1)
test = qcyc40_mul(Rtau_q, Rtau_inv_q)
assert test == qcyc40_one(), f"Rτ·Rτ⁻¹ != 1: {test}"
print("  R-matrix entries verified")

# φ⁻¹ in QCyc40Ext (with im=0)
phi_inv_ext = ext_of_qcyc40(phi_inv)
# φ⁻¹·w (off-diagonal of F)
phi_inv_w = (qcyc40_zero(), phi_inv)  # 0 + (phiInv)·w

# Build 2x2 matrices as (4-tuple of QCyc40Ext) flat: [m00, m01, m10, m11]
def mat_make(m00, m01, m10, m11):
    return [m00, m01, m10, m11]

def mat_mul(A, B):
    """2x2 matrix multiply in QCyc40Ext."""
    a00, a01, a10, a11 = A
    b00, b01, b10, b11 = B
    return [
        ext_add(ext_mul(a00, b00), ext_mul(a01, b10)),  # (0,0)
        ext_add(ext_mul(a00, b01), ext_mul(a01, b11)),  # (0,1)
        ext_add(ext_mul(a10, b00), ext_mul(a11, b10)),  # (1,0)
        ext_add(ext_mul(a10, b01), ext_mul(a11, b11)),  # (1,1)
    ]

# σ₁_qubit (Mat2K_40_Ext): diag(R1, Rτ)
sigma1_mat = mat_make(
    ext_of_qcyc40(R1_q),
    ext_zero(),
    ext_zero(),
    ext_of_qcyc40(Rtau_q),
)
# σ₁⁻¹_qubit: diag(R1⁻¹, Rτ⁻¹)
sigma1_inv_mat = mat_make(
    ext_of_qcyc40(R1_inv_q),
    ext_zero(),
    ext_zero(),
    ext_of_qcyc40(Rtau_inv_q),
)
# F-matrix
F_mat = mat_make(
    phi_inv_ext,
    phi_inv_w,
    phi_inv_w,
    ext_neg(phi_inv_ext),
)
# σ₂ = F · σ₁ · F
sigma2_mat = mat_mul(mat_mul(F_mat, sigma1_mat), F_mat)
# σ₂⁻¹ = F · σ₁⁻¹ · F
sigma2_inv_mat = mat_mul(mat_mul(F_mat, sigma1_inv_mat), F_mat)

print("σ-matrices built. Computing braid product...")

# L=46 braid (seed 7)
LABELS = {'σp 0': 0, 'σp 1': 1, 'σn 0': 2, 'σn 1': 3}
w_letters = ['σn 1', 'σp 0', 'σn 1', 'σp 0', 'σp 1', 'σp 0', 'σp 1', 'σn 0', 'σn 1', 'σp 0',
             'σp 1', 'σp 1', 'σp 0', 'σn 1', 'σn 1', 'σn 0', 'σp 1', 'σp 1', 'σp 1', 'σp 1',
             'σp 0', 'σp 1', 'σp 0', 'σn 1', 'σp 0', 'σp 0', 'σp 0', 'σn 1', 'σn 0', 'σn 0',
             'σn 0', 'σn 0', 'σp 1', 'σn 0', 'σn 0', 'σn 0', 'σn 0', 'σn 0', 'σp 1', 'σn 0',
             'σn 1', 'σp 0', 'σn 1', 'σp 0', 'σn 1', 'σn 1']
w = [LABELS[s] for s in w_letters]

MATS = [sigma1_mat, sigma2_mat, sigma1_inv_mat, sigma2_inv_mat]

# Initial: identity 2x2
I_mat = mat_make(ext_one(), ext_zero(), ext_zero(), ext_one())
M = I_mat
import time
t0 = time.time()
for k, g in enumerate(w):
    M = mat_mul(M, MATS[g])
    if k % 10 == 0:
        print(f"  step {k}: elapsed={time.time()-t0:.1f}s")
print(f"Braid product computed; elapsed={time.time()-t0:.1f}s")

# Now compute target ζ_40^17 · T_NC
# T_NC[0,0] = 1, T_NC[1,1] = ζ_8 = ζ_40^5
# ζ_40^17 · 1 = ζ_40^17 (in 16-basis: c_1=-1, c_5=1, c_9=-1, c_13=1)
# ζ_40^17 · ζ_40^5 = ζ_40^22 = -ζ_40^2 (c_2=-1)
target_00 = qcyc40_zero()
target_00[1] = Fraction(-1); target_00[5] = Fraction(1); target_00[9] = Fraction(-1); target_00[13] = Fraction(1)
target_11 = qcyc40_zero()
target_11[2] = Fraction(-1)
T_shifted = mat_make(
    ext_of_qcyc40(target_00),
    ext_zero(),
    ext_zero(),
    ext_of_qcyc40(target_11),
)

# Compute D = M - T
D = [ext_sub(M[i], T_shifted[i]) for i in range(4)]

# frobNormSq_ext(M, N) = sum_{i,j} (D_ij)² (note: NO conjugation, just squaring)
# So: D_00² + D_01² + D_10² + D_11²
frob_sq = ext_zero()
for d in D:
    frob_sq = ext_add(frob_sq, ext_mul(d, d))

print()
print("Exact Frobenius² (in QCyc40Ext, no conjugation):")
print(f"  re = {frob_sq[0]}")
print(f"  im = {frob_sq[1]}")
# Float estimate
def qcyc40_to_complex(x):
    import math
    zeta = math.cos(2*math.pi/40) + 1j*math.sin(2*math.pi/40)
    return sum(float(x[k]) * zeta**k for k in range(16))
def ext_to_complex(x):
    import math
    phi_val = (1+math.sqrt(5))/2
    w_val = math.sqrt(phi_val)
    return qcyc40_to_complex(x[0]) + w_val * qcyc40_to_complex(x[1])

frob_sq_val = ext_to_complex(frob_sq)
print(f"  numerical value: {frob_sq_val}")
print(f"  abs: {abs(frob_sq_val):.6e}")
