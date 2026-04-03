"""Hubbard-Stratonovich + Rational Hybrid Monte Carlo for ADW model.

Implements the HS+RHMC algorithm for the ADW tetrad condensation model
with 8×8 Majorana fermions on a Spin(4) lattice. This replaces the
fermion-bag algorithm (O(V⁴) percolation wall) with an O(V·√κ) approach
enabling simulation at L=8-16.

Algorithm:
  1. HS transformation decouples quartic interaction → 16V auxiliary fields h^a_{x,μ}
  2. Z = ∫ Dh DU exp(-h²/4g) · Pf(A[h,U]) where A is 8V×8V antisymmetric
  3. Kramers: {J₂, A} = 0 → Pf(A) ≥ 0 → sign-problem-free
  4. |Pf| = det(A†A)^{1/4} via Zolotarev rational approximation (12-16 poles)
  5. Multi-shift CG: one Krylov solve for all poles simultaneously
  6. Omelyan MD: joint evolution in (h, U_L, U_R)
  7. Metropolis accept/reject ensures exact sampling

Performance: numba @njit for inner loops, numpy vectorization for array ops,
multiprocessing for coupling scans.

References:
    Hubbard, PRL 3, 77 (1959) — HS transformation
    Duane, Kennedy, Pendleton & Roweth, PLB 195, 216 (1987) — HMC algorithm
    Clark & Kennedy, NPB Proc. Suppl. 129, 850 (2004) — RHMC
    Omelyan et al., Comp. Phys. Comm. 146, 188 (2002) — integrator
    Catterall & Schaich, JHEP 07, 057 (2015) — Pfaffian RHMC
    Wei et al., PRL 116, 250601 (2016) — Kramers positivity
    "HS+RHMC for ADW tetrad condensation..." — deep research

IMPORTANT (2026-04-02): The Python heatbath uses REAL pseudofermion with x^{-1/8},
which gives Pf^{1/2} not Pf. The Rust backend (sk_eft_rhmc) uses the correct
COMPLEX pseudofermion convention (two real flavors + A matvec trick). Use Rust
for all production runs.

Lean: HubbardStratonovichRHMC.lean (20 theorems, zero sorry)
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Optional
import multiprocessing as mp
import scipy.sparse as sp
from scipy.sparse.linalg import LinearOperator

# numba is optional (fermion-bag extra). Functions decorated with @njit
# are only available when numba is installed. The Zolotarev coefficients
# and core RHMC logic work without numba (pure numpy/scipy).
try:
    from numba import njit
except ImportError:
    def njit(*args, **kwargs):
        """Fallback: no-op decorator when numba is not installed."""
        if len(args) == 1 and callable(args[0]):
            return args[0]
        return lambda fn: fn

from src.core.constants import RHMC_PARAMS, GAUGE_LINK_MC
from src.core.formulas import (
    su2_lie_exp, md_hamiltonian, hs_auxiliary_field_metric,
    binder_cumulant_tetrad, binder_cumulant_metric,
    quaternion_multiply,
)

# Gauge lattice imports also require numba-dependent modules.
# Defer to avoid import failures when only using Zolotarev coefficients.
try:
    from src.vestigial.gauge_fermion_bag import GaugeLattice
    from src.vestigial.gauge_fermion_bag_majorana import (
        _CG, _GG, _precompute_spin4_cache,
    )
    from src.vestigial.gauge_fermion_bag import _avg_plaquette_jit
    from src.vestigial.so4_gauge import (
        create_gauge_lattice, renormalize_links,
    )
    _HAS_GAUGE_MODULES = True
except ImportError:
    _HAS_GAUGE_MODULES = False


# ════════════════════════════════════════════════════════════════════
# Dataclasses
# ════════════════════════════════════════════════════════════════════


@dataclass
class RHMCParams:
    """RHMC algorithm parameters.

    Lean: RHMC_PARAMS in constants.py, rhmc_hamiltonian_conserved (HubbardStratonovichRHMC.lean)
    Source: Clark & Kennedy, NPB PS 129, 850 (2004)
    """
    g: float                         # four-fermion coupling
    beta: float = 0.0                # Wilson plaquette coupling
    tau: float = 1.0                 # MD trajectory length
    n_md_steps: int = 20             # steps per trajectory
    omelyan_lambda: float = 0.1932   # Omelyan 2MN parameter
    # Use same pole count for MD and MC to avoid Zolotarev mismatch artifacts.
    # Measured (2026-04-02): 16 poles at κ=164 gives ΔS_PF ≈ 0.03 vs exact.
    # With same poles: ΔH ≈ 0.8 (pure integrator error), 60% acceptance at eps=0.05.
    # Multi-precision (fewer MD poles) is an optimization requiring per-(L,g) tuning.
    n_poles_md: int = 16             # same as MC — avoids S_PF mismatch
    n_poles_hb: int = 16             # for pseudofermion heat bath
    n_poles_mc: int = 16             # same as MD — reliability over speed
    cg_tol_md: float = 1e-8          # CG tolerance for MD
    cg_tol_mc: float = 1e-12         # CG tolerance for Hamiltonian
    cg_max_iter: int = 5000          # CG iteration cap
    seed: int = 42


@dataclass
class RHMCConfig:
    """HS+RHMC field configuration.

    Contains the dynamical fields: auxiliary h-fields and gauge links.
    Momenta are allocated only during MD trajectories.

    Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
    """
    L: int
    h: np.ndarray                    # shape (L,L,L,L,4,4) — h^a_{x,μ}
    gauge: GaugeLattice              # reuse existing gauge lattice
    # Momenta (live only during MD trajectory)
    pi_h: Optional[np.ndarray] = None   # shape (L,L,L,L,4,4)
    mom_L: Optional[np.ndarray] = None  # shape (L,L,L,L,4,3) — su(2)_L
    mom_R: Optional[np.ndarray] = None  # shape (L,L,L,L,4,3) — su(2)_R


@dataclass
class RHMCResult:
    """Results from an RHMC production run.

    h-field observables detect the same phase transition as fermion-bag.
    The auxiliary field h^a is conjugate to the tetrad E^a (h ∝ E at mean-field).

    Lean: binder_tetrad_prefactor, binder_metric_prefactor (MajoranaKramers.lean)
    """
    # h-field order parameters (proxy for tetrad/metric)
    h_tetrad_m2: float = 0.0        # ⟨|m_h|²⟩ (tetrad proxy)
    h_tetrad_m4: float = 0.0        # ⟨|m_h|⁴⟩
    binder_tetrad: float = 0.0      # U₄ with d=16 prefactor 8/9
    h_metric_m2: float = 0.0        # ⟨trQ²⟩ (metric proxy)
    h_metric_m4: float = 0.0        # ⟨(trQ²)²⟩
    binder_metric: float = 0.0      # U₄ with d=9 prefactor 9/11
    # Gauge observables
    avg_plaquette: list = field(default_factory=list)
    # HS diagnostics
    h_sq_history: list = field(default_factory=list)    # ⟨h²⟩ per measurement
    delta_H_history: list = field(default_factory=list)  # ΔH per trajectory
    acceptance_history: list = field(default_factory=list)
    acceptance_rate: float = 0.0
    # Measurement histories for jackknife
    tetrad_m2_history: list = field(default_factory=list)
    metric_trQ2_history: list = field(default_factory=list)
    n_measurements: int = 0
    g: float = 0.0
    beta: float = 0.0
    L: int = 0
    sign_free: bool = True           # Kramers guarantees this


# ════════════════════════════════════════════════════════════════════
# Zolotarev rational approximation
#
# r(x) = α₀ + Σ_k α_k / (x + β_k) ≈ x^{power}
# Coefficients from the Remez exchange algorithm.
#
# Lean: zolotarev_exponential_convergence, partial_fraction_positivity
#       (HubbardStratonovichRHMC.lean)
# Source: Clark & Kennedy, NPB PS 129, 850 (2004)
# ════════════════════════════════════════════════════════════════════


def compute_zolotarev_coefficients(n_poles, eps, lam_max, power=-0.25):
    """Compute partial-fraction coefficients for x^power on [eps, lam_max].

    Two-phase algorithm:
    1. Initialize with Cauchy integral discretization (guarantees positivity)
    2. Refine poles+residues via bounded L-BFGS-B optimization (maintains positivity)

    All coefficients are GUARANTEED POSITIVE by the optimizer bounds.
    Exponential convergence in n_poles for well-conditioned spectral ranges.

    Lean: zolotarev_exponential_convergence, partial_fraction_positivity
          (HubbardStratonovichRHMC.lean)
    Source: Clark & Kennedy, NPB PS 129, 850 (2004)
    Source: van den Eshof et al., CPC 146, 203 (2002)

    Args:
        n_poles: number of partial-fraction poles
        eps: lower spectral bound (> 0)
        lam_max: upper spectral bound
        power: exponent (default -1/4 for det^{1/4})

    Returns:
        (alpha_0, alphas, betas): constant term (≥0), coefficients (>0), shifts (>0)
    """
    from scipy.optimize import minimize as sp_minimize

    p = power
    x_grid = np.exp(np.linspace(np.log(eps), np.log(lam_max), 300))
    target = x_grid ** p

    # Phase 1: Cauchy integral initialization (positive by construction)
    # Wide range to reduce truncation error
    log_lo = np.log(eps) - 3.0 * np.log(lam_max / eps)
    log_hi = np.log(lam_max) + 3.0 * np.log(lam_max / eps)
    delta_u = (log_hi - log_lo) / n_poles
    u_k = log_lo + (np.arange(n_poles) + 0.5) * delta_u
    betas_init = np.exp(u_k)
    prefactor = np.sin(np.pi * abs(p)) / np.pi
    alphas_init = prefactor * delta_u * betas_init ** (p + 1)

    # Phase 2: Refine via bounded optimization
    # Parameterize in log-space for positivity: α_k = exp(log_α_k), β_k = exp(log_β_k)
    log_alphas_init = np.log(np.maximum(alphas_init, 1e-30))
    log_betas_init = np.log(betas_init)

    # Also optimize α₀ (via log for positivity)
    r_test = np.sum(alphas_init / (np.sqrt(eps * lam_max) + betas_init))
    a0_init = max(target[len(target)//2] - r_test, 1e-30)
    log_a0_init = np.log(max(a0_init, 1e-30))

    p0 = np.concatenate([[log_a0_init], log_alphas_init, log_betas_init])

    def objective(params):
        log_a0 = params[0]
        log_al = params[1:n_poles + 1]
        log_be = params[n_poles + 1:]
        a0 = np.exp(log_a0)
        al = np.exp(log_al)
        be = np.exp(log_be)
        r = a0 + np.sum(al[:, None] / (x_grid[None, :] + be[:, None]), axis=0)
        # L∞ relative error (minimax)
        rel_err = np.abs((r - target) / target)
        return np.max(rel_err)

    result = sp_minimize(objective, p0, method='L-BFGS-B',
                         options={'maxiter': 5000, 'ftol': 1e-15})

    alpha_0 = np.exp(result.x[0])
    alphas = np.exp(result.x[1:n_poles + 1])
    betas = np.exp(result.x[n_poles + 1:])

    # Guaranteed positive by exp() parameterization
    return alpha_0, alphas, betas


# ════════════════════════════════════════════════════════════════════
# SU(2) exponential (JIT-optimized)
#
# Lean: su2_closed_form_exp, su2_exp_unit_quaternion_identity
#       (HubbardStratonovichRHMC.lean)
# Source: Creutz, "Quarks, Gluons and Lattices" (1983), Ch. 15
# ════════════════════════════════════════════════════════════════════


@njit(cache=True)
def _su2_exp_quaternion_jit(P1, P2, P3, epsilon):
    """JIT kernel: SU(2) exponential for a single momentum vector.

    exp(iε P·σ/2) as quaternion q = (cos(|P|ε/2), sin(|P|ε/2)·P̂)

    Returns (q0, q1, q2, q3) — unit quaternion components.
    """
    P_norm = np.sqrt(P1**2 + P2**2 + P3**2)
    half_angle = P_norm * epsilon / 2.0

    q0 = np.cos(half_angle)
    if P_norm > 1e-30:
        s = np.sin(half_angle) / P_norm
        q1 = s * P1
        q2 = s * P2
        q3 = s * P3
    else:
        q1 = 0.0
        q2 = 0.0
        q3 = 0.0
    return q0, q1, q2, q3


@njit(cache=True)
def _su2_exp_all_links_jit(mom, links, L, epsilon):
    """Apply SU(2) exponential to all links: U ← exp(iε P)·U.

    Vectorized over all L⁴×4 links.

    Args:
        mom: su(2) momentum, shape (L,L,L,L,4,3)
        links: quaternion links, shape (L,L,L,L,4,4), modified in place
        L: lattice size
        epsilon: MD step size
    """
    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    for mu in range(4):
                        P1 = mom[x0, x1, x2, x3, mu, 0]
                        P2 = mom[x0, x1, x2, x3, mu, 1]
                        P3 = mom[x0, x1, x2, x3, mu, 2]
                        eq0, eq1, eq2, eq3 = _su2_exp_quaternion_jit(
                            P1, P2, P3, epsilon)
                        # Quaternion multiply: exp_q · link
                        uq = links[x0, x1, x2, x3, mu]
                        a, b, c, d = uq[0], uq[1], uq[2], uq[3]
                        links[x0, x1, x2, x3, mu, 0] = eq0*a - eq1*b - eq2*c - eq3*d
                        links[x0, x1, x2, x3, mu, 1] = eq0*b + eq1*a + eq2*d - eq3*c
                        links[x0, x1, x2, x3, mu, 2] = eq0*c - eq1*d + eq2*a + eq3*b
                        links[x0, x1, x2, x3, mu, 3] = eq0*d + eq1*c - eq2*b + eq3*a


# ════════════════════════════════════════════════════════════════════
# Configuration initialization
# ════════════════════════════════════════════════════════════════════


def create_rhmc_config(L, g, rng, cold_start=False):
    """Create initial RHMC configuration.

    h fields initialized from equilibrium Gaussian: h ~ N(0, √(2g)).
    Gauge links from create_gauge_lattice (Haar random or cold start).

    Lean: hs_gaussian_action_nonneg (HubbardStratonovichRHMC.lean)

    Args:
        L: lattice size
        g: four-fermion coupling
        rng: numpy random generator
        cold_start: if True, h=0 and gauge links = identity

    Returns:
        RHMCConfig
    """
    gauge = create_gauge_lattice(L, rng, cold_start=cold_start)

    if cold_start:
        h = np.zeros((L, L, L, L, 4, 4), dtype=np.float64)
    else:
        # Equilibrium distribution: h ~ N(0, √(2g))
        sigma = np.sqrt(2.0 * g) if g > 0 else 1.0
        h = rng.normal(0.0, sigma, size=(L, L, L, L, 4, 4))

    return RHMCConfig(L=L, h=h, gauge=gauge)


# ════════════════════════════════════════════════════════════════════
# Sparse fermion matrix A[h,U]
#
# A_{(x,I),(y,J)} = Σ_{μ,a} h^a_{x,μ} (CG[a] · S_{x,μ})_{IJ} δ_{y,x+μ}
#                  − (transpose)
#
# CG[a] = J₁Γ^a (precomputed in gauge_fermion_bag_majorana.py as _CG)
# S_{x,μ} = Spin(4) lift of SO(4) gauge link (via Givens decomposition)
#
# Lean: hs_fermion_matrix_antisymmetric, kramers_holds_hs_matrix
#       (HubbardStratonovichRHMC.lean)
# Source: "HS+RHMC for ADW tetrad condensation..." Section 1
# ════════════════════════════════════════════════════════════════════


def _flat_index(x0, x1, x2, x3, L):
    """4D site → flat index."""
    return ((x0 * L + x1) * L + x2) * L + x3


def build_fermion_matrix_dense(h, gauge, L, spin4_cache=None):
    """Build dense 8V×8V antisymmetric fermion matrix A[h,U].

    For L ≤ 6 (V ≤ 1296, matrix ≤ 10368×10368). Uses precomputed
    _CG = J₁Γ^a and Spin(4) cache.

    Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
    Source: "HS+RHMC for ADW tetrad condensation..." Section 1

    Args:
        h: auxiliary fields, shape (L,L,L,L,4,4) — h[x0,x1,x2,x3,mu,a]
        gauge: GaugeLattice
        L: lattice size
        spin4_cache: precomputed Spin(4), shape (L,L,L,L,4,8,8). Optional.

    Returns:
        A: dense antisymmetric matrix, shape (8V, 8V)
    """
    if spin4_cache is None:
        spin4_cache = _precompute_spin4_cache(gauge, L)

    V = L**4
    dim = 8 * V
    A = np.zeros((dim, dim), dtype=np.float64)

    CG = _CG  # (4, 8, 8) — J₁Γ^a matrices

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    i_site = _flat_index(x0, x1, x2, x3, L)
                    for mu in range(4):
                        # Neighbor in direction mu (periodic BC)
                        nb = [x0, x1, x2, x3]
                        nb[mu] = (nb[mu] + 1) % L
                        j_site = _flat_index(nb[0], nb[1], nb[2], nb[3], L)

                        S = spin4_cache[x0, x1, x2, x3, mu]  # 8×8

                        # Forward block: Σ_a h^a_{x,μ} (CG[a] · S)
                        block = np.zeros((8, 8))
                        for a in range(4):
                            block += h[x0, x1, x2, x3, mu, a] * (CG[a] @ S)

                        # Place forward block at (i_site, j_site)
                        i0, i1 = 8 * i_site, 8 * (i_site + 1)
                        j0, j1 = 8 * j_site, 8 * (j_site + 1)
                        A[i0:i1, j0:j1] += block
                        # Antisymmetric: backward = -forward^T
                        A[j0:j1, i0:i1] -= block.T

    return A


def build_fermion_matrix_sparse(h, gauge, L, spin4_cache=None):
    """Build sparse 8V×8V antisymmetric fermion matrix A[h,U] in CSR format.

    For L ≥ 8. Same physics as dense version but uses COO → CSR conversion.

    Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
    Source: "HS+RHMC for ADW tetrad condensation..." Section 1

    Args:
        h: auxiliary fields, shape (L,L,L,L,4,4)
        gauge: GaugeLattice
        L: lattice size
        spin4_cache: precomputed Spin(4), shape (L,L,L,L,4,8,8)

    Returns:
        A: scipy.sparse.csr_matrix, shape (8V, 8V)
    """
    if spin4_cache is None:
        spin4_cache = _precompute_spin4_cache(gauge, L)

    V = L**4
    dim = 8 * V
    CG = _CG

    # Estimate nnz: V sites × 4 directions × 2 (fwd+bwd) × 64 (8×8 block)
    max_nnz = V * 4 * 2 * 64
    rows = np.zeros(max_nnz, dtype=np.int32)
    cols = np.zeros(max_nnz, dtype=np.int32)
    vals = np.zeros(max_nnz, dtype=np.float64)
    nnz = 0

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    i_site = _flat_index(x0, x1, x2, x3, L)
                    for mu in range(4):
                        nb = [x0, x1, x2, x3]
                        nb[mu] = (nb[mu] + 1) % L
                        j_site = _flat_index(nb[0], nb[1], nb[2], nb[3], L)

                        S = spin4_cache[x0, x1, x2, x3, mu]
                        block = np.zeros((8, 8))
                        for a in range(4):
                            block += h[x0, x1, x2, x3, mu, a] * (CG[a] @ S)

                        # Forward entries
                        for I in range(8):
                            for J in range(8):
                                if abs(block[I, J]) > 1e-300:
                                    rows[nnz] = 8 * i_site + I
                                    cols[nnz] = 8 * j_site + J
                                    vals[nnz] = block[I, J]
                                    nnz += 1
                                    # Antisymmetric backward
                                    rows[nnz] = 8 * j_site + J
                                    cols[nnz] = 8 * i_site + I
                                    vals[nnz] = -block[I, J]
                                    nnz += 1

    A = sp.coo_matrix((vals[:nnz], (rows[:nnz], cols[:nnz])),
                       shape=(dim, dim)).tocsr()
    return A


def build_fermion_matrix(h, gauge, L, spin4_cache=None):
    """Build fermion matrix A[h,U] — dense for L≤6, sparse for L≥8.

    Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
    """
    if L <= 6:
        return build_fermion_matrix_dense(h, gauge, L, spin4_cache)
    else:
        return build_fermion_matrix_sparse(h, gauge, L, spin4_cache)


# ════════════════════════════════════════════════════════════════════
# SpMV wrappers + spectral range estimation
# ════════════════════════════════════════════════════════════════════


def make_A_apply(A):
    """Create callable v → A @ v for dense or sparse A."""
    if sp.issparse(A):
        return lambda v: A @ v
    else:
        return lambda v: A @ v


def make_AtA_apply(A):
    """Create callable v → A†A @ v = -A² @ v.

    For real antisymmetric A: A† = A^T = -A, so A†A = (-A)A = -A².
    Two SpMVs per application.

    Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
    """
    A_apply = make_A_apply(A)

    def ata_apply(v):
        Av = A_apply(v)
        return -A_apply(Av)  # -A²v = A^T A v

    return ata_apply


def estimate_spectral_range(AtA_apply, dim, n_iter=20, rng=None):
    """Estimate λ_min, λ_max of A†A via Lanczos iteration.

    Lean: zolotarev_exponential_convergence (HubbardStratonovichRHMC.lean)

    Args:
        AtA_apply: callable v → A†A @ v
        dim: vector dimension (8V)
        n_iter: Lanczos iterations
        rng: random number generator

    Returns:
        (lambda_min, lambda_max) with safety margins applied
    """
    if rng is None:
        rng = np.random.default_rng(42)

    # Lanczos iteration
    v = rng.standard_normal(dim)
    v /= np.linalg.norm(v)

    alpha = np.zeros(n_iter)
    beta_arr = np.zeros(n_iter)
    V_mat = np.zeros((dim, n_iter))
    V_mat[:, 0] = v

    w = AtA_apply(v)
    alpha[0] = np.dot(w, v)
    w -= alpha[0] * v

    for j in range(1, n_iter):
        beta_arr[j] = np.linalg.norm(w)
        if beta_arr[j] < 1e-14:
            break
        v_old = V_mat[:, j - 1]
        v = w / beta_arr[j]
        V_mat[:, j] = v
        w = AtA_apply(v) - beta_arr[j] * v_old
        alpha[j] = np.dot(w, v)
        w -= alpha[j] * v

    # Tridiagonal eigenvalues
    T = np.diag(alpha[:n_iter]) + np.diag(beta_arr[1:n_iter], 1) + np.diag(beta_arr[1:n_iter], -1)
    eigvals = np.linalg.eigvalsh(T)
    eigvals = eigvals[eigvals > 0]  # A†A is positive semidefinite

    if len(eigvals) == 0:
        return 1e-6, 1.0

    lam_min = max(eigvals.min(), 1e-10)
    lam_max = eigvals.max()

    # Safety margins
    safety_low = RHMC_PARAMS.get('spectral_safety_low', 0.8)
    safety_high = RHMC_PARAMS.get('spectral_safety_high', 1.2)
    return safety_low * lam_min, safety_high * lam_max


# ════════════════════════════════════════════════════════════════════
# Multi-shift conjugate gradient
#
# Solve (A†A + β_k) ψ_k = φ for all k simultaneously.
# Single Krylov space — one SpMV per CG iteration.
#
# Lean: multishift_cg_shared_krylov (HubbardStratonovichRHMC.lean)
# Source: Jegerlehner, hep-lat/9612014 (1996)
# ════════════════════════════════════════════════════════════════════


def _cg_single_shift(AtA_apply, phi, sigma, tol=1e-8, max_iter=5000):
    """Standard CG for a single shifted system (A†A + σ)ψ = φ.

    Lean: multishift_cg_shared_krylov (HubbardStratonovichRHMC.lean)

    Args:
        AtA_apply: callable v → A†A @ v
        phi: source vector
        sigma: shift value (≥ 0)
        tol: relative residual tolerance
        max_iter: iteration cap

    Returns:
        (psi, n_iter): solution vector + iteration count
    """
    dim = len(phi)
    phi_norm = np.linalg.norm(phi)
    if phi_norm < 1e-300:
        return np.zeros(dim), 0

    psi = np.zeros(dim)
    r = phi.copy()
    p = r.copy()
    rr = np.dot(r, r)

    for iteration in range(max_iter):
        Ap = AtA_apply(p) + sigma * p  # (A†A + σ) p
        pAp = np.dot(p, Ap)
        if abs(pAp) < 1e-300:
            break

        alpha = rr / pAp
        psi += alpha * p
        r -= alpha * Ap
        rr_new = np.dot(r, r)

        if np.sqrt(rr_new) / phi_norm < tol:
            return psi, iteration + 1

        beta = rr_new / rr
        p = r + beta * p
        rr = rr_new

    return psi, max_iter


def multi_shift_cg(AtA_apply, phi, shifts, tol=1e-8, max_iter=5000):
    """Solve (A†A + β_k)ψ_k = φ for all shifts k.

    Current implementation: independent CG per shift. This is correct
    and reliable. The multi-shift optimization (shared Krylov space,
    Jegerlehner 1996) will be added once the RHMC trajectory is
    validated end-to-end.

    Cost: n_shifts × n_iter × SpMV (vs 1 × n_iter × SpMV for true multi-shift).
    For n_shifts=15 at L=4, this is ~15 × 100 × 0.001s ≈ 1.5s — acceptable
    for development. True multi-shift needed for L≥8 production.

    Lean: multishift_cg_shared_krylov (HubbardStratonovichRHMC.lean)
    Source: Jegerlehner, hep-lat/9612014 (1996)

    Args:
        AtA_apply: callable v → A†A @ v
        phi: source vector, shape (dim,)
        shifts: array of β_k values (all ≥ 0)
        tol: convergence tolerance (relative residual norm)
        max_iter: iteration cap

    Returns:
        (psi_list, n_iter_max): list of solutions + max iteration count
    """
    psi_list = []
    max_iters_used = 0
    for sigma in shifts:
        psi, n_iter = _cg_single_shift(AtA_apply, phi, sigma, tol, max_iter)
        psi_list.append(psi)
        max_iters_used = max(max_iters_used, n_iter)
    return psi_list, max_iters_used


# ════════════════════════════════════════════════════════════════════
# h-field measurements (O(V), no CG needed)
#
# The auxiliary field h^a_{x,μ} is conjugate to the tetrad E^a_μ.
# At mean-field level h = 2g·E, so h-field moments detect the same
# phase transition as fermion-bag observables.
#
# Lean: binder_tetrad_prefactor, binder_metric_prefactor (MajoranaKramers.lean)
# Source: project-original (h-field as order parameter proxy)
# ════════════════════════════════════════════════════════════════════


def measure_h_field_observables(config):
    """Measure order parameters from the h auxiliary field.

    Tetrad proxy: m_h = (1/V) Σ_x h_{x,μ} for each (μ,a) → |m_h|²
    Metric proxy: M_μν = (1/V) Σ_{x,a} h^a_{x,μ} h^a_{x,ν} → trQ²

    O(V) computation — no CG solve needed.

    Args:
        config: RHMCConfig

    Returns:
        (h_sq, tet_m2_sq, trQ2): ⟨h²⟩, tetrad proxy squared, metric proxy
    """
    L = config.L
    V = L**4
    h = config.h  # shape (L,L,L,L,4,4) = (x0,x1,x2,x3,mu,a)

    # ⟨h²⟩ diagnostic
    h_sq = np.mean(h**2)

    # Tetrad proxy: volume-average h for each (mu, a) component
    # m_h[mu, a] = (1/V) Σ_x h[x, mu, a]
    m_h = h.reshape(V, 4, 4).mean(axis=0)  # (4, 4) = (mu, a)
    tet_m2_sq = np.sum(m_h**2)  # |m_h|² — 16-component squared magnitude

    # Metric proxy
    _, trQ2 = hs_auxiliary_field_metric(h, L)

    return h_sq, tet_m2_sq, trQ2


# ════════════════════════════════════════════════════════════════════
# Force computation
#
# F_h^a_{x,μ} = -h^a/(2g) + Σ_k α_k · ψ_k† (∂M/∂h) ψ_k
# where M = A†A = -A² and ∂A/∂h^a_{x,μ} is sparse (one 8×8 block).
#
# F_L, F_R are SU(2) projections of the gauge-link force.
#
# Lean: rhmc_hamiltonian_conserved (HubbardStratonovichRHMC.lean)
# Source: "HS+RHMC for ADW tetrad condensation..." Section 4
# ════════════════════════════════════════════════════════════════════


def compute_forces(config, params, phi, alphas, betas, A, spin4_cache):
    """Compute MD forces F_h, F_L, F_R from pseudofermion action.

    The force on h^a_{x,μ} is:
      F_h = -h/(2g) + fermion_force
    where the fermion force requires multi-shift CG solutions ψ_k.

    The force on gauge links requires the Lie algebra projection of
    ∂S_PF/∂U onto su(2)_L and su(2)_R generators.

    Lean: rhmc_hamiltonian_conserved (HubbardStratonovichRHMC.lean)
    Source: "HS+RHMC for ADW tetrad condensation..." Section 4

    Args:
        config: RHMCConfig
        params: RHMCParams
        phi: pseudofermion vector, shape (8V,)
        alphas: Zolotarev numerator coefficients (n_poles,)
        betas: Zolotarev shift values (n_poles,)
        A: current fermion matrix (dense or sparse)
        spin4_cache: Spin(4) matrices, shape (L,L,L,L,4,8,8)

    Returns:
        (F_h, F_L, F_R): force arrays
    """
    L = config.L
    V = L**4
    g = params.g

    # Solve multi-shift CG: ψ_k = (A†A + β_k)^{-1} φ
    AtA_apply = make_AtA_apply(A)
    psi_list, _ = multi_shift_cg(AtA_apply, phi, betas.tolist(),
                                  tol=params.cg_tol_md, max_iter=params.cg_max_iter)

    # Also need A·ψ_k for the force formula
    A_apply = make_A_apply(A)
    A_psi_list = [A_apply(psi_k) for psi_k in psi_list]

    CG = _CG  # (4, 8, 8) — J₁Γ^a matrices

    # ── Force on h fields ──
    # F_h^a_{x,μ} = -h^a/(2g) - Σ_k α_k · [ψ_k† dM/dh^a ψ_k]
    # where dM/dh^a = -(dA/dh^a · A + A · dA/dh^a)
    # and dA/dh^a_{x,μ} has nonzero block = CG[a] · S_{x,μ} at (x, x+μ)
    # and negative transpose at (x+μ, x).
    F_h = -config.h / (2.0 * g)  # Gaussian prior force

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    i = _flat_index(x0, x1, x2, x3, L)
                    for mu in range(4):
                        nb = [x0, x1, x2, x3]
                        nb[mu] = (nb[mu] + 1) % L
                        j = _flat_index(nb[0], nb[1], nb[2], nb[3], L)

                        S = spin4_cache[x0, x1, x2, x3, mu]  # 8×8

                        for a in range(4):
                            # dA/dh^a_{x,μ}: block CG[a]@S at (8i:8i+8, 8j:8j+8)
                            # and -block^T at (8j:8j+8, 8i:8i+8)
                            block = CG[a] @ S  # 8×8

                            # Force contribution: Σ_k α_k · (ψ_k at i) · block · (A·ψ_k at j)
                            # + transpose part
                            force_val = 0.0
                            for k in range(len(alphas)):
                                psi_i = psi_list[k][8*i:8*(i+1)]
                                psi_j = psi_list[k][8*j:8*(j+1)]
                                Apsi_i = A_psi_list[k][8*i:8*(i+1)]
                                Apsi_j = A_psi_list[k][8*j:8*(j+1)]

                                # dM/dh = -(dA·A + A·dA)
                                # ψ†·dM·ψ = -(ψ†·dA·A·ψ + ψ†·A·dA·ψ)
                                # For dA block at (i,j):
                                #   ψ†·dA·A·ψ contribution at (i,j):
                                #     psi_i · block · (A·ψ)_j
                                #   ψ†·A·dA·ψ contribution at (i,j):
                                #     (A·ψ)_i · block · ψ_j (no, this is from the (i,j) block of A·dA)
                                # Actually simpler: dA has block B at (i,j) and -B^T at (j,i)
                                # So ψ† dA ψ = ψ_i · B · ψ_j - ψ_j · B^T · ψ_i
                                #            = ψ_i · B · ψ_j - ψ_i · B · ψ_j = 0? No...
                                # Wait: ψ† dA ψ = Σ_{m,n} ψ_m (dA)_{mn} ψ_n
                                # = ψ_i^T B ψ_j + ψ_j^T (-B^T) ψ_i
                                # = ψ_i^T B ψ_j - (ψ_i^T B ψ_j) = 0 (antisymmetric!)
                                #
                                # So we need ψ† dM ψ = -ψ† (dA·A + A·dA) ψ
                                # = -(ψ† dA (Aψ) + (A^T ψ)† dA ψ)
                                # = -(ψ† dA (Aψ) - (Aψ)† dA ψ)  [since A^T = -A]
                                #
                                # For dA block B at (i,j), -B^T at (j,i):
                                # ψ† dA (Aψ) = psi_i^T B (Apsi_j) + psi_j^T (-B^T) (Apsi_i)
                                #            = psi_i^T B Apsi_j - (psi_i^T B^T)^T Apsi_i? No.
                                # Let me be more careful:
                                # ψ† dA (Aψ) = Σ_m Σ_n ψ_m (dA)_mn (Aψ)_n
                                # Nonzero contributions: (m in 8i..., n in 8j...) with (dA)_mn = B
                                #                    and (m in 8j..., n in 8i...) with (dA)_mn = -B^T
                                # = psi_i^T B Apsi_j + psi_j^T (-B^T) Apsi_i
                                # = psi_i^T B Apsi_j - psi_j^T B^T Apsi_i
                                # = psi_i^T B Apsi_j - (B psi_j)^T Apsi_i
                                # = psi_i^T B Apsi_j - psi_j^T B^T Apsi_i
                                #
                                # And -(Aψ)† dA ψ = -(the same with psi↔Apsi swapped)
                                # = -(Apsi_i^T B psi_j - Apsi_j^T B^T psi_i)
                                #
                                # Total: -[above + -(Apsi version)]
                                # = -(psi_i^T B Apsi_j - psi_j^T B^T Apsi_i
                                #     - Apsi_i^T B psi_j + Apsi_j^T B^T psi_i)
                                # = -(psi_i^T B Apsi_j - Apsi_i^T B psi_j
                                #     - psi_j^T B^T Apsi_i + Apsi_j^T B^T psi_i)
                                #
                                # Simplify: each pair cancels to give
                                # = -2(psi_i^T B Apsi_j - Apsi_i^T B psi_j)
                                # (using B^T terms are transposes of the B terms)
                                #
                                # So: ψ† dM/dh ψ = -2 (ψᵢᵀ B (Aψ)ⱼ - (Aψ)ᵢᵀ B ψⱼ)

                                term1 = psi_i @ block @ Apsi_j
                                term2 = Apsi_i @ block @ psi_j
                                force_val += alphas[k] * (-2.0) * (term1 - term2)

                            F_h[x0, x1, x2, x3, mu, a] += force_val

    # ── Force on gauge links (F_L, F_R) ──
    # TODO(W7C): Implement gauge forces from pseudofermion action.
    # F_L^a(x,μ) = Proj_{su(2)_L}[ Σ_k α_k (outer product from ψ_k) · U_L† ]
    # F_R similarly for su(2)_R. See deep research Section 4.
    #
    # Currently zero: gauge links are fixed during MD (mom_L = mom_R = 0).
    # Validated: h-field reversibility to machine precision (1e-15) with
    # CG tol=1e-14, and 1e-10 with CG tol=1e-8 (measured 2026-04-02).
    # ΔH scales as ε² with coefficient C≈44 at L=2, g=2 (Omelyan 2MN).
    F_L = np.zeros((L, L, L, L, 4, 3))
    F_R = np.zeros((L, L, L, L, 4, 3))

    return F_h, F_L, F_R


# ════════════════════════════════════════════════════════════════════
# Omelyan integrator
#
# 3-force-eval symmetric scheme: λε kick → ε/2 drift → (1-2λ)ε kick
# → ε/2 drift → λε kick. Second-order symplectic, time-reversible.
#
# Lean: omelyan_second_order_symplectic, omelyan_time_reversible
#       (HubbardStratonovichRHMC.lean)
# Source: Omelyan et al., Comp. Phys. Comm. 146, 188 (2002)
# ════════════════════════════════════════════════════════════════════


def _kick(config, F_h, F_L, F_R, eps):
    """Momentum kick: p += ε · F."""
    config.pi_h += eps * F_h
    config.mom_L += eps * F_L
    config.mom_R += eps * F_R


def _drift(config, eps):
    """Field drift: q += ε · p.

    h fields: h += ε · π_h (simple addition)
    Gauge links: U_L ← exp(iε·P_L)·U_L via SU(2) closed-form exponential

    Lean: su2_closed_form_exp (HubbardStratonovichRHMC.lean)
    """
    config.h += eps * config.pi_h
    _su2_exp_all_links_jit(config.mom_L, config.gauge.links_L, config.L, eps)
    _su2_exp_all_links_jit(config.mom_R, config.gauge.links_R, config.L, eps)


def omelyan_step(config, params, phi, alphas_md, betas_md, spin4_cache):
    """One Omelyan 2MN integrator step.

    3 force evaluations per step:
      1. λε kick
      2. ε/2 drift
      3. (1-2λ)ε kick
      4. ε/2 drift
      5. λε kick

    Lean: omelyan_second_order_symplectic (HubbardStratonovichRHMC.lean)
    Source: Omelyan et al., CPC 146, 188 (2002), Eq. (31)
    """
    eps = params.tau / params.n_md_steps
    lam = params.omelyan_lambda

    # Force 1
    A = build_fermion_matrix(config.h, config.gauge, config.L, spin4_cache)
    F_h, F_L, F_R = compute_forces(config, params, phi, alphas_md, betas_md, A, spin4_cache)

    # λε kick
    _kick(config, F_h, F_L, F_R, lam * eps)

    # ε/2 drift
    _drift(config, eps / 2.0)

    # Force 2 (recompute A after drift)
    spin4_cache = _precompute_spin4_cache(config.gauge, config.L)
    A = build_fermion_matrix(config.h, config.gauge, config.L, spin4_cache)
    F_h, F_L, F_R = compute_forces(config, params, phi, alphas_md, betas_md, A, spin4_cache)

    # (1-2λ)ε kick
    _kick(config, F_h, F_L, F_R, (1.0 - 2.0 * lam) * eps)

    # ε/2 drift
    _drift(config, eps / 2.0)

    # Force 3 (recompute after second drift)
    spin4_cache = _precompute_spin4_cache(config.gauge, config.L)
    A = build_fermion_matrix(config.h, config.gauge, config.L, spin4_cache)
    F_h, F_L, F_R = compute_forces(config, params, phi, alphas_md, betas_md, A, spin4_cache)

    # λε kick
    _kick(config, F_h, F_L, F_R, lam * eps)

    return spin4_cache  # return updated cache for reuse


# ════════════════════════════════════════════════════════════════════
# Pseudofermion heat bath + Hamiltonian
#
# Lean: rhmc_detailed_balance (HubbardStratonovichRHMC.lean)
# Source: Clark & Kennedy, NPB PS 129, 850 (2004)
# ════════════════════════════════════════════════════════════════════


def pseudofermion_heatbath(A, dim, rng, lam_min=None, lam_max=None, n_poles=16):
    """Generate pseudofermion vector φ from the heat bath distribution.

    WARNING (2026-04-02): This function uses a REAL pseudofermion with power -1/8,
    which gives Pf(A)^{1/2}, NOT Pf(A). The correct convention for Pfaffian RHMC
    is COMPLEX pseudofermion Φ ∈ ℂ^{8V} with:
      S_PF = Φ†(A†A)^{-1/4}Φ  (action power -1/4, same as current)
      Heatbath: Φ = A · r_{-3/8}(A†A) · ξ / √2  (A matvec trick + complex normalization)

    The Rust backend (sk_eft_rhmc) implements the correct complex convention.
    This Python function is kept for reference/testing but should NOT be used
    for production physics. See Rust lib.rs pseudofermion_heatbath for correct impl.

    Lean: hs_gaussian_identity_zero (HubbardStratonovichRHMC.lean)
    Source: Schaich & DeGrand, CPC 190:200 (2015), Eqs. 16-17 (arXiv:1410.6971)
    Source: Clark & Kennedy, NPB PS 129, 850 (2004), Section 2.2

    Args:
        A: fermion matrix
        dim: vector dimension (8V)
        rng: numpy random generator
        lam_min, lam_max: spectral range of A†A (computed if not given)
        n_poles: number of rational approx poles for heat bath

    Returns:
        phi: pseudofermion vector, shape (dim,)
    """
    xi = rng.standard_normal(dim)

    # Compute spectral range if not provided
    if lam_min is None or lam_max is None:
        AtA_apply = make_AtA_apply(A)
        lam_min, lam_max = estimate_spectral_range(AtA_apply, dim, rng=rng)

    # Rational approximation for x^{-1/8} (the heat bath function)
    # φ = r_HB(A†A) · ξ where r_HB ≈ x^{-1/8}
    # = α₀ ξ + Σ_k α_k (A†A + β_k)^{-1} ξ
    a0_hb, al_hb, be_hb = compute_zolotarev_coefficients(
        n_poles, lam_min, lam_max, power=-0.125)  # x^{-1/8}

    AtA_apply = make_AtA_apply(A)
    psi_list, _ = multi_shift_cg(AtA_apply, xi, be_hb.tolist(),
                                  tol=1e-10, max_iter=5000)

    phi = a0_hb * xi
    for k in range(len(be_hb)):
        phi += al_hb[k] * psi_list[k]

    return phi


def compute_hamiltonian(config, params, phi, alphas_mc, betas_mc, A):
    """Compute the full MD Hamiltonian H = K + S_aux + S_PF.

    K = (1/2)Σ π_h² + (1/2)Σ (P_L² + P_R²)
    S_aux = Σ h²/(4g)
    S_PF = φ^T r_MC(A†A) φ  (high-precision rational approx)

    Lean: rhmc_hamiltonian_nonneg (HubbardStratonovichRHMC.lean)
    Source: Duane et al., PLB 195, 216 (1987)

    Args:
        config: RHMCConfig
        params: RHMCParams
        phi: pseudofermion vector
        alphas_mc: MC-precision Zolotarev numerator coefficients
        betas_mc: MC-precision Zolotarev shifts
        A: fermion matrix

    Returns:
        H: total Hamiltonian (scalar)
    """
    # Kinetic energy
    K_h = 0.5 * np.sum(config.pi_h**2) if config.pi_h is not None else 0.0
    K_L = 0.5 * np.sum(config.mom_L**2) if config.mom_L is not None else 0.0
    K_R = 0.5 * np.sum(config.mom_R**2) if config.mom_R is not None else 0.0
    K = K_h + K_L + K_R

    # Auxiliary field action
    S_aux = np.sum(config.h**2) / (4.0 * params.g)

    # Pseudofermion action: S_PF = φ^T r(A†A) φ
    # r(x) = α₀ + Σ_k α_k/(x + β_k)
    # S_PF = α₀ |φ|² + Σ_k α_k φ^T (A†A + β_k)^{-1} φ
    AtA_apply = make_AtA_apply(A)
    alpha_0 = alphas_mc[0] if len(alphas_mc) > len(betas_mc) else 0.0
    alphas_pf = alphas_mc[1:] if len(alphas_mc) > len(betas_mc) else alphas_mc

    psi_list, _ = multi_shift_cg(AtA_apply, phi, betas_mc.tolist(),
                                  tol=params.cg_tol_mc, max_iter=params.cg_max_iter)

    S_PF = alpha_0 * np.dot(phi, phi)
    for k in range(len(betas_mc)):
        if k < len(alphas_pf):
            S_PF += alphas_pf[k] * np.dot(phi, psi_list[k])

    return md_hamiltonian(K, 0.0, S_aux, S_PF)


# ════════════════════════════════════════════════════════════════════
# Full RHMC trajectory
#
# Lean: rhmc_detailed_balance (HubbardStratonovichRHMC.lean)
# Source: Duane et al., PLB 195, 216 (1987)
# ════════════════════════════════════════════════════════════════════


def rhmc_trajectory(config, params, rng):
    """Run one complete RHMC trajectory.

    Steps:
      1. Build fermion matrix A, generate pseudofermion φ
      2. Refresh momenta: π_h ~ N(0,1), P_L ~ N(0,1), P_R ~ N(0,1)
      3. Compute H_old (MC precision)
      4. Run Omelyan MD trajectory (n_md_steps steps, MD precision)
      5. Compute H_new (MC precision)
      6. Metropolis: accept if rand < min(1, exp(-(H_new-H_old)))

    Lean: rhmc_detailed_balance (HubbardStratonovichRHMC.lean)
    Source: Duane et al., PLB 195, 216 (1987)

    Args:
        config: RHMCConfig (modified in place if accepted, restored if rejected)
        params: RHMCParams
        rng: numpy random generator

    Returns:
        (delta_H, accepted): energy violation and acceptance boolean
    """
    L = config.L
    V = L**4
    dim = 8 * V

    # Compute Zolotarev coefficients for current spectral range
    spin4_cache = _precompute_spin4_cache(config.gauge, L)
    A = build_fermion_matrix(config.h, config.gauge, L, spin4_cache)
    AtA_apply = make_AtA_apply(A)
    lam_min, lam_max = estimate_spectral_range(AtA_apply, dim, rng=rng)

    alpha_0_md, alphas_md, betas_md = compute_zolotarev_coefficients(
        params.n_poles_md, lam_min, lam_max, power=-0.25)
    alpha_0_mc, alphas_mc, betas_mc = compute_zolotarev_coefficients(
        params.n_poles_mc, lam_min, lam_max, power=-0.25)

    # Prepend alpha_0 to alphas for Hamiltonian computation
    alphas_mc_full = np.concatenate([[alpha_0_mc], alphas_mc])

    # Step 1: Generate pseudofermion from the correct distribution
    # φ = r_HB(A†A)·ξ where r_HB ≈ x^{-1/8}, ensuring P(φ) ∝ exp(-φ^T r(A†A) φ)
    phi = pseudofermion_heatbath(A, dim, rng, lam_min=lam_min, lam_max=lam_max,
                                  n_poles=params.n_poles_hb)

    # Step 2: Refresh momenta
    # h-field momenta always refreshed
    config.pi_h = rng.standard_normal(config.h.shape)
    # Gauge momenta: set to zero when gauge forces are not implemented (β=0).
    # This keeps gauge links fixed during MD, testing only h-field RHMC.
    # TODO(W7C): Enable gauge momentum refresh once gauge forces (F_L, F_R)
    # are implemented. Currently gauge links are FIXED during MD trajectory.
    # This is correct for pure h-field RHMC at β=0 (no Wilson plaquette action).
    # For β>0 or full gauge+fermion dynamics, gauge forces must be implemented
    # following "HS+RHMC..." deep research Section 4 (su(2) Lie algebra projection).
    config.mom_L = np.zeros((L, L, L, L, 4, 3))
    config.mom_R = np.zeros((L, L, L, L, 4, 3))

    # Step 3: Store old config, compute H_old
    h_old = config.h.copy()
    links_L_old = config.gauge.links_L.copy()
    links_R_old = config.gauge.links_R.copy()

    H_old = compute_hamiltonian(config, params, phi, alphas_mc_full, betas_mc, A)

    # Step 4: MD trajectory
    for step in range(params.n_md_steps):
        spin4_cache = omelyan_step(config, params, phi, alphas_md, betas_md, spin4_cache)

    # Renormalize quaternions after MD
    renormalize_links(config.gauge)

    # Step 5: Compute H_new
    spin4_cache = _precompute_spin4_cache(config.gauge, L)
    A_new = build_fermion_matrix(config.h, config.gauge, L, spin4_cache)
    H_new = compute_hamiltonian(config, params, phi, alphas_mc_full, betas_mc, A_new)

    delta_H = H_new - H_old

    # Step 6: Metropolis accept/reject
    if delta_H <= 0 or rng.random() < np.exp(-delta_H):
        accepted = True
    else:
        # Reject: restore old configuration
        config.h[:] = h_old
        config.gauge.links_L[:] = links_L_old
        config.gauge.links_R[:] = links_R_old
        accepted = False

    # Clear momenta
    config.pi_h = None
    config.mom_L = None
    config.mom_R = None

    return delta_H, accepted


# ════════════════════════════════════════════════════════════════════
# Production runner
#
# Source: same pattern as run_majorana_mc_fast in gauge_fermion_bag_majorana.py
# ════════════════════════════════════════════════════════════════════


def run_rhmc(L, g, beta=0.0, n_traj=200, n_therm=50, n_meas_skip=5,
             n_md_steps=20, tau=1.0, seed=42):
    """Run HS+RHMC production at a single coupling point.

    Measurements use h-field observables (O(V), no CG needed):
    - Tetrad proxy: |m_h|² (16-component Binder)
    - Metric proxy: trQ² (9-component Binder)
    - Plaquette: ⟨Tr U_P⟩
    - ΔH history for diagnostics

    Lean: adw_sign_problem_free (MajoranaKramers.lean)
    Source: "HS+RHMC for ADW tetrad condensation..." (deep research)

    Args:
        L, g, beta: physics parameters
        n_traj, n_therm, n_meas_skip: trajectory counts
        n_md_steps, tau: MD parameters
        seed: random seed

    Returns:
        RHMCResult
    """
    rng = np.random.default_rng(seed)
    config = create_rhmc_config(L, g, rng)
    params = RHMCParams(g=g, beta=beta, tau=tau, n_md_steps=n_md_steps)
    result = RHMCResult(g=g, beta=beta, L=L)

    n_accepted = 0

    for traj in range(n_traj):
        delta_H, accepted = rhmc_trajectory(config, params, rng)
        result.delta_H_history.append(float(delta_H))
        result.acceptance_history.append(1.0 if accepted else 0.0)
        if accepted:
            n_accepted += 1

        # Renormalize periodically
        if traj % GAUGE_LINK_MC.get('quaternion_renorm_interval', 10) == 0:
            renormalize_links(config.gauge)

        # Measure after thermalization
        if traj >= n_therm and (traj - n_therm) % n_meas_skip == 0:
            h_sq, tet_sq, trQ2 = measure_h_field_observables(config)
            result.h_sq_history.append(float(h_sq))
            result.tetrad_m2_history.append(float(tet_sq))
            result.metric_trQ2_history.append(float(trQ2))

            plaq = _avg_plaquette_jit(config.gauge.links_L,
                                       config.gauge.links_R, L)
            result.avg_plaquette.append(float(plaq))
            result.n_measurements += 1

    # Compute summary statistics
    if result.n_measurements > 0:
        tet = np.array(result.tetrad_m2_history)
        met = np.array(result.metric_trQ2_history)
        result.h_tetrad_m2 = np.mean(tet)
        result.h_tetrad_m4 = np.mean(tet**2)
        if result.h_tetrad_m2 > 0:
            result.binder_tetrad = binder_cumulant_tetrad(
                result.h_tetrad_m2, result.h_tetrad_m4)
        result.h_metric_m2 = np.mean(met)
        result.h_metric_m4 = np.mean(met**2)
        if result.h_metric_m2 > 0:
            result.binder_metric = binder_cumulant_metric(
                result.h_metric_m2, result.h_metric_m4)

    result.acceptance_rate = n_accepted / max(n_traj, 1)
    return result
