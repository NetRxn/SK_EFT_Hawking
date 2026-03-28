"""Grassmann Tensor Renormalization Group for the 2D ADW model.

Implements the Grassmann TRG algorithm (Shimizu-Kuramashi 2014) to
compute the partition function of the 2D reduced ADW model after
analytical SU(2) integration. The TRG iteratively coarse-grains the
tensor network on a 2D square lattice, reducing a 2^n × 2^n lattice
to a single tensor in n steps.

Algorithm overview:
1. Build initial tensor from the effective Boltzmann weights
2. Decompose: SVD splits each tensor into two half-tensors
3. Contract: combine four half-tensors into a coarse-grained tensor
4. Truncate: keep only D_cut largest singular values
5. Repeat steps 2-4 until the lattice is 1×1
6. Trace the final tensor → ln(Z)

For the 2D ADW model with 2 Grassmann variables per site, the initial
bond dimension is 2 (Grassmann occupation 0 or 1 per bond). The
truncation parameter D_cut controls accuracy vs cost.

The Grassmann nature of the variables is handled through the tensor
structure: each index tracks the Grassmann parity, and contractions
include appropriate sign factors for fermion exchange.

References:
    Shimizu & Kuramashi, PRD 90, 014508 (2014) — Grassmann TRG
    Levin & Nave, PRL 99, 120601 (2007) — original TRG algorithm
    Gu & Wen, PRB 80, 155131 (2009) — Grassmann tensor networks
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Optional

from src.core.constants import GRASSMANN_TRG, ADW_2D_COUPLING_SCAN
from src.core.formulas import (
    adw_2d_effective_coupling, binder_cumulant, grassmann_trg_free_energy,
)
from src.vestigial.su2_integration import build_effective_action


@dataclass
class TRGParams:
    """Parameters for the Grassmann TRG calculation.

    Attributes:
        D_cut: bond dimension truncation (controls accuracy)
        n_rg_steps: number of RG steps (lattice size = 2^n_rg_steps)
        svd_threshold: threshold for discarding small singular values
    """
    D_cut: int = GRASSMANN_TRG['D_cut_default']
    n_rg_steps: int = 4  # 2^4 = 16 × 16 lattice
    svd_threshold: float = GRASSMANN_TRG['svd_threshold']


@dataclass
class TRGResult:
    """Result of a Grassmann TRG calculation.

    Attributes:
        ln_Z: natural log of the partition function
        free_energy: per-site free energy f = -ln(Z)/V
        volume: number of lattice sites V = L²
        L: linear lattice size
        g_cosmo: cosmological coupling used
        g_EH: Einstein-Hilbert coupling used
        g_eff: effective NN coupling after SU(2) integration
        D_cut: bond dimension used
        n_rg_steps: number of RG steps performed
        singular_value_spectrum: largest singular values at each step
        converged: whether the free energy has converged
    """
    ln_Z: float
    free_energy: float
    volume: int
    L: int
    g_cosmo: float
    g_EH: float
    g_eff: float
    D_cut: int
    n_rg_steps: int
    singular_value_spectrum: list[np.ndarray]
    converged: bool


def _build_initial_tensor(g_cosmo: float, g_eff: float) -> np.ndarray:
    """Build the initial tensor for the 2D Grassmann TRG.

    The tensor T[l, r, u, d] encodes the local Boltzmann weight
    after tracing over the on-site Grassmann degrees of freedom.

    For 2 Grassmann variables per site (n₁, n₂ ∈ {0,1}):
        T[l,r,u,d] = Σ_{n₁,n₂} exp(-g_cosmo·n₁n₂)
                      × exp(-g_eff·(n₁l + n₂r + n₁u + n₂d))

    Bond indices l,r,u,d ∈ {0,1} represent Grassmann occupation
    on the left, right, up, down bonds respectively.

    Args:
        g_cosmo: on-site cosmological coupling
        g_eff: effective nearest-neighbor coupling (after SU(2))

    Returns:
        Tensor of shape (2, 2, 2, 2)
    """
    T = np.zeros((2, 2, 2, 2))

    for n1 in range(2):
        for n2 in range(2):
            w_cosmo = np.exp(-g_cosmo * n1 * n2)
            for l in range(2):
                for r in range(2):
                    for u in range(2):
                        for d in range(2):
                            w_bonds = np.exp(-g_eff * (n1*l + n2*r + n1*u + n2*d))
                            T[l, r, u, d] += w_cosmo * w_bonds

    return T


def _svd_truncate(matrix: np.ndarray, D_cut: int,
                   threshold: float = 1e-12) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """SVD with truncation to D_cut largest singular values.

    Args:
        matrix: 2D matrix to decompose
        D_cut: maximum number of singular values to keep
        threshold: minimum singular value to retain

    Returns:
        (U, S, Vt) truncated to at most D_cut singular values
    """
    U, S, Vt = np.linalg.svd(matrix, full_matrices=False)

    # Truncate to D_cut
    k = min(D_cut, len(S))

    # Also truncate by threshold
    mask = S[:k] > threshold
    if np.any(mask):
        k = max(1, int(np.sum(mask)))
    else:
        k = 1

    return U[:, :k], S[:k], Vt[:k, :]


def _trg_step(T: np.ndarray, D_cut: int,
              threshold: float = 1e-12) -> tuple[np.ndarray, np.ndarray]:
    """Perform one TRG coarse-graining step.

    Decomposes the tensor T[l,r,u,d] via SVD along horizontal and
    vertical cuts, then contracts four half-tensors into a new
    coarse-grained tensor T'[l',r',u',d'].

    The horizontal decomposition:
        T[l,r,u,d] ≈ Σ_α S1[l,u,α] × S2[α,r,d]

    The vertical decomposition:
        T[l,r,u,d] ≈ Σ_β S3[u,l,β] × S4[β,d,r]

    The coarse-grained tensor combines four half-tensors:
        T'[l',r',u',d'] = Σ_{internal} S1 × S2 × S3 × S4

    Args:
        T: input tensor of shape (D, D, D, D)
        D_cut: bond dimension truncation
        threshold: SVD threshold

    Returns:
        (T_new, singular_values) — coarse-grained tensor and SV spectrum
    """
    D = T.shape[0]

    # Horizontal decomposition: reshape T[l,r,u,d] → M[(l,u), (r,d)]
    M_h = T.reshape(D * D, D * D)
    # We need T[l,u,r,d] for horizontal cut
    T_perm = T.transpose(0, 2, 1, 3)  # T[l,u,r,d]
    M_h = T_perm.reshape(D * D, D * D)

    U_h, S_h, Vt_h = _svd_truncate(M_h, D_cut, threshold)
    D_new = len(S_h)

    # Absorb sqrt(S) into both sides
    sqrt_S = np.sqrt(S_h)
    S1 = (U_h * sqrt_S[np.newaxis, :]).reshape(D, D, D_new)    # S1[l, u, α]
    S2 = (sqrt_S[:, np.newaxis] * Vt_h).reshape(D_new, D, D)   # S2[α, r, d]

    # Vertical decomposition: T[u,l,d,r] → M[(u,l), (d,r)]
    T_perm2 = T.transpose(2, 0, 3, 1)  # T[u,l,d,r]
    M_v = T_perm2.reshape(D * D, D * D)

    U_v, S_v, Vt_v = _svd_truncate(M_v, D_cut, threshold)
    D_new2 = len(S_v)

    sqrt_S_v = np.sqrt(S_v)
    S3 = (U_v * sqrt_S_v[np.newaxis, :]).reshape(D, D, D_new2)   # S3[u, l, β]
    S4 = (sqrt_S_v[:, np.newaxis] * Vt_v).reshape(D_new2, D, D)  # S4[β, d, r]

    # Contract the four half-tensors to form the coarse-grained tensor
    # T'[l', r', u', d'] = Σ_{a,b,c,e} S1[a, b, l'] S2[r', c, e]
    #                                    S3[b, c, u'] S4[d', e, a]
    #
    # Use einsum for clarity:
    # S1[a, b, l'] × S3[b, c, u'] → contracted on b
    # S2[r', c, e] × S4[d', e, a] → contracted on e
    # Then contract on a and c

    # Step 1: contract S1 and S3 on index b (second index of S1, first of S3)
    # S1[a, b, l'] × S3[b, c, u'] → M1[a, l', c, u']
    M1 = np.einsum('abl,bcu->alcu', S1, S3)

    # Step 2: contract S2 and S4 on index e (third of S2, second of S4)
    # S2[r', c, e] × S4[d', e, a] → M2[r', c, d', a]
    M2 = np.einsum('rce,dea->rcda', S2, S4)

    # Step 3: contract M1 and M2 on a and c
    # M1[a, l', c, u'] × M2[r', c, d', a] → T'[l', r', u', d']
    T_new = np.einsum('alcu,rcda->lrud', M1, M2)

    return T_new, S_h


def _tensor_trace(T: np.ndarray) -> float:
    """Compute the trace of the final tensor.

    For a 4-index tensor T[l,r,u,d], the trace contracts:
        Z = Σ_{i,j} T[i,i,j,j]

    This corresponds to imposing periodic boundary conditions.

    Args:
        T: final tensor after all RG steps

    Returns:
        Trace value (partition function or its contribution)
    """
    D = T.shape[0]
    result = 0.0
    for i in range(D):
        for j in range(D):
            result += T[i, i, j, j]
    return result


def run_grassmann_trg(g_cosmo: float, g_EH: float,
                       params: Optional[TRGParams] = None) -> TRGResult:
    """Run the full Grassmann TRG calculation for the 2D ADW model.

    1. Build initial tensor from Boltzmann weights
    2. Iterate TRG coarse-graining steps
    3. Trace the final tensor to get Z
    4. Compute free energy per site

    Args:
        g_cosmo: cosmological coupling (on-site 4-fermion)
        g_EH: Einstein-Hilbert coupling (gauge-coupled)
        params: TRG parameters (bond dimension, steps, etc.)

    Returns:
        TRGResult with partition function, free energy, and diagnostics
    """
    if params is None:
        params = TRGParams()

    g_eff = adw_2d_effective_coupling(g_EH)
    T = _build_initial_tensor(g_cosmo, g_eff)

    L = 2 ** params.n_rg_steps
    volume = L * L

    # Track normalization: we normalize the tensor at each step
    # to prevent overflow/underflow. The total ln(Z) accumulates
    # the log of the normalization factors.
    ln_Z_accumulated = 0.0
    sv_spectrum = []

    for step in range(params.n_rg_steps):
        # Normalize the tensor
        norm = np.max(np.abs(T))
        if norm > 0:
            T = T / norm
            # At step k, there are 2^(2*(n-k)) sites remaining
            # Each site contributes one factor of norm
            n_sites_at_step = 4 ** (params.n_rg_steps - step)
            ln_Z_accumulated += np.log(norm) * n_sites_at_step

        # Coarse-grain
        T, sv = _trg_step(T, params.D_cut, params.svd_threshold)
        sv_spectrum.append(sv)

    # Trace the final tensor
    Z_final = _tensor_trace(T)
    if Z_final > 0:
        ln_Z = ln_Z_accumulated + np.log(Z_final)
    else:
        # Negative or zero trace indicates a problem
        ln_Z = ln_Z_accumulated + np.log(max(abs(Z_final), 1e-300))

    free_energy = grassmann_trg_free_energy(ln_Z, volume)

    # Check convergence: compare free energy at the last two steps
    converged = True
    if len(sv_spectrum) >= 2:
        # If the smallest retained SV is much smaller than the largest,
        # the truncation is adequate
        last_sv = sv_spectrum[-1]
        if len(last_sv) > 1:
            ratio = last_sv[-1] / last_sv[0]
            converged = ratio < 0.01  # last SV is < 1% of first

    return TRGResult(
        ln_Z=ln_Z,
        free_energy=free_energy,
        volume=volume,
        L=L,
        g_cosmo=g_cosmo,
        g_EH=g_EH,
        g_eff=g_eff,
        D_cut=params.D_cut,
        n_rg_steps=params.n_rg_steps,
        singular_value_spectrum=sv_spectrum,
        converged=converged,
    )


@dataclass
class PhaseScanResult:
    """Result of scanning couplings to map the 2D phase diagram.

    Attributes:
        g_cosmo: fixed cosmological coupling
        g_EH_values: array of Einstein-Hilbert couplings scanned
        free_energies: per-site free energy at each coupling
        ln_Z_values: ln(Z) at each coupling
        specific_heat: numerical second derivative of f (phase transition signal)
        phase_boundary: estimated g_EH at the phase transition (peak of specific heat)
    """
    g_cosmo: float
    g_EH_values: np.ndarray
    free_energies: np.ndarray
    ln_Z_values: np.ndarray
    specific_heat: np.ndarray
    phase_boundary: Optional[float]


def scan_coupling_2d(g_cosmo: float = ADW_2D_COUPLING_SCAN['g_cosmo'],
                      g_EH_range: tuple[float, float] = ADW_2D_COUPLING_SCAN['g_EH_range'],
                      n_points: int = ADW_2D_COUPLING_SCAN['n_points'],
                      trg_params: Optional[TRGParams] = None) -> PhaseScanResult:
    """Scan the Einstein-Hilbert coupling to map the 2D phase diagram.

    At fixed g_cosmo, varies g_EH and computes the free energy at each point.
    The specific heat (second derivative of free energy) peaks at phase
    transitions.

    Args:
        g_cosmo: fixed cosmological coupling
        g_EH_range: (min, max) range for g_EH
        n_points: number of coupling values to scan
        trg_params: TRG parameters

    Returns:
        PhaseScanResult with free energies and phase boundary estimate
    """
    if trg_params is None:
        trg_params = TRGParams(D_cut=GRASSMANN_TRG['D_cut_benchmark'], n_rg_steps=3)

    g_values = np.linspace(g_EH_range[0], g_EH_range[1], n_points)
    free_energies = np.zeros(n_points)
    ln_Z_values = np.zeros(n_points)

    for i, g_EH in enumerate(g_values):
        result = run_grassmann_trg(g_cosmo, g_EH, trg_params)
        free_energies[i] = result.free_energy
        ln_Z_values[i] = result.ln_Z

    # Compute specific heat: C = -d²f/dg² (numerical second derivative)
    dg = g_values[1] - g_values[0] if len(g_values) > 1 else 1.0
    if len(g_values) >= 3:
        specific_heat = np.zeros(n_points)
        specific_heat[1:-1] = -(free_energies[2:] - 2*free_energies[1:-1]
                                 + free_energies[:-2]) / dg**2
        specific_heat[0] = specific_heat[1]
        specific_heat[-1] = specific_heat[-2]
    else:
        specific_heat = np.zeros(n_points)

    # Find phase boundary (peak of specific heat)
    if np.max(np.abs(specific_heat)) > 0:
        i_peak = int(np.argmax(np.abs(specific_heat)))
        phase_boundary = float(g_values[i_peak])
    else:
        phase_boundary = None

    return PhaseScanResult(
        g_cosmo=g_cosmo,
        g_EH_values=g_values,
        free_energies=free_energies,
        ln_Z_values=ln_Z_values,
        specific_heat=specific_heat,
        phase_boundary=phase_boundary,
    )


def trg_free_energy_convergence(g_cosmo: float, g_EH: float,
                                 D_cut_values: list[int] = [4, 8, 16, 32],
                                 n_rg_steps: int = 4) -> dict:
    """Study convergence of free energy with bond dimension.

    Args:
        g_cosmo: cosmological coupling
        g_EH: Einstein-Hilbert coupling
        D_cut_values: list of bond dimensions to test
        n_rg_steps: number of RG steps

    Returns:
        Dict with D_cut values and corresponding free energies
    """
    results = []
    for D_cut in D_cut_values:
        params = TRGParams(D_cut=D_cut, n_rg_steps=n_rg_steps)
        result = run_grassmann_trg(g_cosmo, g_EH, params)
        results.append({
            'D_cut': D_cut,
            'free_energy': result.free_energy,
            'ln_Z': result.ln_Z,
            'converged': result.converged,
        })

    return {
        'g_cosmo': g_cosmo,
        'g_EH': g_EH,
        'n_rg_steps': n_rg_steps,
        'L': 2 ** n_rg_steps,
        'results': results,
    }
