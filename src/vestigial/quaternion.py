"""SU(2) quaternion algebra for SO(4) gauge-link Monte Carlo.

Unit quaternions q = (a, b, c, d) with a² + b² + c² + d² = 1
parameterize SU(2). All operations are vectorized over arrays of
shape (..., 4) for efficient lattice-wide computation.

The Hamilton product costs 16 flops vs 128 for 4×4 matrix multiply,
giving a 4× speedup for all plaquette and staple computations.

References:
    Creutz, "Quarks, Gluons and Lattices" (1983), Ch. 15
    Kennedy & Pendleton, PLB 156, 393 (1985) — heatbath
"""

import numpy as np

from src.core.formulas import quaternion_multiply


def conjugate(q):
    """Quaternion conjugate: (a, b, c, d) → (a, −b, −c, −d).

    For unit quaternions, conjugate = inverse.

    Args:
        q: quaternion array, shape (..., 4)

    Returns:
        Conjugate quaternion, same shape.
    """
    q = np.asarray(q, dtype=float)
    result = q.copy()
    result[..., 1:] *= -1
    return result


def norm_sq(q):
    """Squared norm |q|² = a² + b² + c² + d².

    Args:
        q: quaternion array, shape (..., 4)

    Returns:
        Squared norms, shape (...,)
    """
    q = np.asarray(q, dtype=float)
    return np.sum(q**2, axis=-1)


def normalize(q):
    """Project quaternion to unit norm.

    Corrects floating-point drift that accumulates during
    repeated multiplication. Should be called every ~50 sweeps.

    Args:
        q: quaternion array, shape (..., 4)

    Returns:
        Unit quaternion, same shape.
    """
    q = np.asarray(q, dtype=float)
    norms = np.sqrt(norm_sq(q))[..., np.newaxis]
    return q / norms


def trace(q):
    """SU(2) trace: Tr(U) = 2·Re(q) = 2a.

    For the 2×2 unitary matrix U corresponding to quaternion q,
    Tr(U) = 2a₀. This is used in the Wilson action.

    Args:
        q: quaternion array, shape (..., 4)

    Returns:
        Traces, shape (...,)
    """
    return 2.0 * np.asarray(q, dtype=float)[..., 0]


def identity(shape=()):
    """Identity quaternion (1, 0, 0, 0).

    Args:
        shape: batch shape for the output

    Returns:
        Identity quaternion(s), shape (*shape, 4)
    """
    if isinstance(shape, int):
        shape = (shape,)
    q = np.zeros((*shape, 4))
    q[..., 0] = 1.0
    return q


def haar_random(rng, shape=()):
    """Generate Haar-random SU(2) elements (uniform on S³).

    Uses the Marsaglia method: generate 4 Gaussian variates
    and normalize to the unit sphere.

    Args:
        rng: numpy random Generator
        shape: batch shape

    Returns:
        Unit quaternion(s), shape (*shape, 4)
    """
    if isinstance(shape, int):
        shape = (shape,)
    q = rng.standard_normal((*shape, 4))
    return normalize(q)


def to_matrix_2x2(q):
    """Convert unit quaternion to 2×2 SU(2) matrix.

    Convention: q = (a, b, c, d) maps to
      U = [[a + id, -c + ib],
           [c + ib,  a - id]]

    This corresponds to the identification i→iσ₃, j→iσ₁, k→-iσ₂
    (right-handed quaternion-to-SU(2) map). Verified properties:
    - UU† = I (unitary), det(U) = 1 (special unitary)
    - to_matrix(q₁·q₂) = to_matrix(q₁) @ to_matrix(q₂) (homomorphism)

    Source: Creutz, "Quarks, Gluons and Lattices" (1983), Ch. 15

    Args:
        q: single quaternion, shape (4,)

    Returns:
        2×2 complex matrix
    """
    a, b, c, d = q
    return np.array([
        [a + 1j*d, -c + 1j*b],
        [c + 1j*b,  a - 1j*d],
    ])


def kennedy_pendleton_heatbath(a, rng):
    """Kennedy-Pendleton SU(2) heatbath: sample from P(q) ∝ exp(a·Tr(q))·dμ_Haar.

    Generates a unit quaternion distributed according to the Boltzmann
    weight for the Wilson gauge action with effective coupling a = β·k
    where k = |staple|/2.

    The algorithm samples the real part x = a₀ from
    P(x) ∝ √(1−x²)·exp(2a·x) using rejection sampling,
    then generates the imaginary part uniformly on S².

    For a = 0, returns Haar random (correct β → 0 limit).
    For a → ∞, concentrates near identity (ordered limit).

    Args:
        a: effective coupling β·k (scalar or array)
        rng: numpy random Generator

    Returns:
        Unit quaternion(s), same batch shape as a, plus trailing 4.
    """
    a = np.asarray(a, dtype=float)
    scalar_input = a.ndim == 0
    if scalar_input:
        a = a.reshape(1)

    n = a.shape[0]
    result = np.zeros((n, 4))

    for i in range(n):
        ai = a[i]
        if ai < 1e-10:
            # Very weak coupling: Haar random
            result[i] = haar_random(rng)
            continue

        # Kennedy-Pendleton rejection sampling for a₀
        while True:
            x1 = rng.uniform(0, 1)
            x2 = rng.uniform(0, 1)
            x3 = rng.uniform(0, 1)

            x1 = max(x1, 1e-300)  # avoid log(0)
            x2 = max(x2, 1e-300)

            delta = -(np.log(x1) + np.log(x2) * np.cos(2 * np.pi * x3)**2) / (2 * ai)

            if rng.uniform() < np.sqrt(1.0 - delta / 2.0) if delta < 2.0 else False:
                break

        a0 = 1.0 - delta

        # Generate (a1, a2, a3) uniform on sphere of radius √(1 − a₀²)
        r = np.sqrt(max(1.0 - a0**2, 0.0))
        # Random direction on S²
        cos_theta = rng.uniform(-1, 1)
        sin_theta = np.sqrt(1.0 - cos_theta**2)
        phi = rng.uniform(0, 2 * np.pi)

        result[i, 0] = a0
        result[i, 1] = r * sin_theta * np.cos(phi)
        result[i, 2] = r * sin_theta * np.sin(phi)
        result[i, 3] = r * cos_theta

    if scalar_input:
        return result[0]
    return result
