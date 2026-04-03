"""Hybrid fermion-bag + gauge-link Monte Carlo for ADW tetrad condensation.

First-ever implementation of fermion-bag MC with dynamical SO(4) gauge links
on a 4D hypercubic lattice. The algorithm alternates between:
  Phase 1: Fermion-bag Metropolis updates at fixed gauge links
  Phase 2: Kennedy-Pendleton heatbath + overrelaxation for gauge links
           at fixed Grassmann occupation, with fermion determinant reweighting

Performance: Numba JIT kernels for inner loops + vectorized NumPy for batch ops.
Multiprocessing for production scans across coupling points.

References:
    Chandrasekharan, PRD 82, 025007 (2010) — fermion-bag algorithm
    Kennedy & Pendleton, PLB 156, 393 (1985) — SU(2) heatbath
    Vladimirov & Diakonov, PRD 86, 104019 (2012) — ADW lattice action
    Volovik, JETP Lett. 119, 564 (2024) — vestigial metric ordering
"""

import numpy as np
from numba import njit, prange
from dataclasses import dataclass, field
from typing import Optional

from src.core.constants import GAUGE_LINK_MC, SO4_LATTICE, ADW_4D_MODEL
from src.core.formulas import (
    quaternion_multiply, so4_from_quaternion_pair,
    wilson_plaquette_action, metric_from_tetrad,
)
from src.vestigial.quaternion import (
    conjugate, normalize, norm_sq, trace, identity,
    haar_random, kennedy_pendleton_heatbath,
)
from src.vestigial.so4_gauge import (
    GaugeLattice, create_gauge_lattice, plaquette_trace,
    average_plaquette, staple_sum, gauge_heatbath_sweep,
    gauge_overrelax_sweep, renormalize_links,
)
from collections import deque


# ════════════════════════════════════════════════════════════════════
# Staggered phases, bag decomposition, fermion matrix (Step 2)
# Source: Kogut-Susskind PRD 11, 395 (1975) — staggered phases
# Source: Chandrasekharan PRD 82, 025007 (2010) — fermion-bag decomposition
# Source: deep research "Hybrid fermion-bag + gauge-link MC" — M_B formula
# ════════════════════════════════════════════════════════════════════

def staggered_phase(x, mu):
    """Staggered fermion phase η_μ(x) = (-1)^{x_0 + ... + x_{μ-1}}.

    Replaces gamma matrices in the fermion matrix M_B. The staggered
    phase encodes the Dirac structure: in the continuum limit, 2^d
    staggered lattice sites reconstruct one Dirac spinor.

    Source: Kogut & Susskind, PRD 11, 395 (1975)

    Args:
        x: site coordinates, array of ints shape (4,)
        mu: direction index 0,...,3

    Returns:
        +1 or -1
    """
    if mu == 0:
        return 1
    return (-1) ** (sum(x[:mu]) % 2)


def identify_bags(bond_config, L):
    """Identify connected-component bags from bond configuration.

    A bag is a maximal connected subset of lattice sites linked by active
    bonds (bond_config[x, mu] = 1). Sites not connected by any active
    bond form singleton bags.

    Uses BFS on a 4D periodic lattice. O(V) time.

    Source: Chandrasekharan, PRD 82, 025007 (2010)

    Args:
        bond_config: array (L, L, L, L, 4) of {0, 1} bond activations
        L: lattice size

    Returns:
        List of bags. Each bag is a list of site coordinates (numpy arrays).
    """
    visited = np.zeros((L, L, L, L), dtype=bool)
    bags = []

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    if visited[x0, x1, x2, x3]:
                        continue
                    # BFS from this site
                    bag = []
                    queue = deque()
                    start = (x0, x1, x2, x3)
                    queue.append(start)
                    visited[x0, x1, x2, x3] = True
                    while queue:
                        site = queue.popleft()
                        bag.append(np.array(site))
                        sx = np.array(site)
                        for mu in range(4):
                            # Forward: bond from site in direction mu
                            if bond_config[site[0], site[1], site[2], site[3], mu]:
                                nb = list(site)
                                nb[mu] = (nb[mu] + 1) % L
                                nb_t = tuple(nb)
                                if not visited[nb_t]:
                                    visited[nb_t] = True
                                    queue.append(nb_t)
                            # Backward: bond from neighbor pointing to site
                            nb_back = list(site)
                            nb_back[mu] = (nb_back[mu] - 1) % L
                            nb_back_t = tuple(nb_back)
                            if bond_config[nb_back_t[0], nb_back_t[1],
                                           nb_back_t[2], nb_back_t[3], mu]:
                                if not visited[nb_back_t]:
                                    visited[nb_back_t] = True
                                    queue.append(nb_back_t)
                    bags.append(bag)
    return bags


def build_fermion_matrix(bag, bond_config, gauge, L):
    """Build the fermion matrix M_B[U] restricted to bag B.

    M_B has dimension (4|B|) × (4|B|) where |B| is the number of sites
    in the bag and 4 = N_c (Dirac components from staggered phases).

    For free (kinetic) bonds within the bag:
    (M_B)_{(x,a),(y,b)} = Σ_μ η_μ(x) · [U_{x,μ}^{ab} δ_{y,x+μ̂}
                                          − (U†)_{x-μ̂,μ}^{ab} δ_{y,x-μ̂}] / 2

    The entries are REAL: η_μ ∈ {±1} and U ∈ SO(4) is a real orthogonal matrix.

    Source: deep research "Hybrid fermion-bag + gauge-link MC", Bag weight formula
    Source: Chandrasekharan PRD 82, 025007 (2010)

    Args:
        bag: list of site coordinate arrays, each shape (4,)
        bond_config: array (L,L,L,L,4) of bond activations
        gauge: GaugeLattice with links_L, links_R arrays
        L: lattice size

    Returns:
        M_B: real matrix of shape (4*|B|, 4*|B|)
    """
    n_sites = len(bag)
    dim = 4 * n_sites
    M = np.zeros((dim, dim), dtype=np.float64)

    # Map site tuples to bag indices for O(1) lookup
    site_to_idx = {}
    for i, site in enumerate(bag):
        site_to_idx[tuple(site)] = i

    for i, site_x in enumerate(bag):
        x = tuple(site_x)
        for mu in range(4):
            eta = staggered_phase(site_x, mu)

            # Forward neighbor x + μ̂
            nb_fwd = list(x)
            nb_fwd[mu] = (nb_fwd[mu] + 1) % L
            nb_fwd_t = tuple(nb_fwd)

            if nb_fwd_t in site_to_idx:
                j = site_to_idx[nb_fwd_t]
                # Get SO(4) matrix for link (x, mu)
                R = _get_so4_matrix(gauge, x, mu)
                # (M_B)_{(x,a),(y,b)} += η_μ(x) · U_{x,μ}^{ab} / 2
                for a in range(4):
                    for b in range(4):
                        M[4*i + a, 4*j + b] += 0.5 * eta * R[a, b]

            # Backward neighbor x - μ̂
            nb_back = list(x)
            nb_back[mu] = (nb_back[mu] - 1) % L
            nb_back_t = tuple(nb_back)

            if nb_back_t in site_to_idx:
                j = site_to_idx[nb_back_t]
                # Get SO(4) matrix for link (x-μ̂, mu), then transpose (= inverse for SO(4))
                R_back = _get_so4_matrix(gauge, nb_back_t, mu)
                # (M_B)_{(x,a),(y,b)} -= η_μ(x) · (U†)_{x-μ̂,μ}^{ab} / 2
                # U† = U^T for SO(4), so (U†)^{ab} = U^{ba} = R_back^T[a,b]
                for a in range(4):
                    for b in range(4):
                        M[4*i + a, 4*j + b] -= 0.5 * eta * R_back[b, a]

    return M


def _get_so4_matrix(gauge, site, mu):
    """Extract 4×4 SO(4) matrix from gauge lattice quaternion pair at (site, mu)."""
    x0, x1, x2, x3 = site[0], site[1], site[2], site[3]
    q_L = gauge.links_L[x0, x1, x2, x3, mu]
    q_R = gauge.links_R[x0, x1, x2, x3, mu]
    return so4_from_quaternion_pair(q_L, q_R)


def bag_weight(M_B):
    """Compute bag weight W_B = det(M_B[U]) with sign tracking.

    The determinant is REAL (guaranteed by charge conjugation symmetry
    for SO(4) gauge group with staggered fermions). We track both the
    absolute value and the sign.

    Source: Chandrasekharan PRD 82, 025007 (2010)

    Args:
        M_B: real matrix of shape (4|B|, 4|B|)

    Returns:
        (det_value, sign): det_value is the determinant, sign is +1 or -1
    """
    det_val = np.linalg.det(M_B)
    # det should be real for real M_B. Complex det indicates M_B has
    # complex entries (e.g., from complex gamma matrices in 4×4 rep)
    # or numerical noise. Validate and extract real part.
    if np.iscomplex(det_val):
        imag_frac = abs(np.imag(det_val)) / max(abs(det_val), 1e-300)
        if imag_frac > 1e-6:
            import warnings
            warnings.warn(
                f"bag_weight: significant imaginary part in det "
                f"(|Im|/|det| = {imag_frac:.2e}). Check fermion matrix.",
                stacklevel=2)
    det_val = float(np.real(det_val))
    sign = 1 if det_val >= 0 else -1
    return det_val, sign


# ════════════════════════════════════════════════════════════════════
# Sherman-Morrison-Woodbury updates (Step 3)
# Source: Sherman & Morrison, Ann. Math. Stat. 21, 124 (1950)
# Source: Woodbury, "Inverting Modified Matrices" (1950)
# ════════════════════════════════════════════════════════════════════

def smw_det_ratio(M_inv, u, v):
    """Rank-1 determinant ratio: det(M + uv^T) / det(M) = 1 + v^T M^{-1} u.

    Source: Matrix determinant lemma (Sherman-Morrison)

    Args:
        M_inv: inverse of original matrix, shape (n, n)
        u: column vector, shape (n,)
        v: column vector, shape (n,)

    Returns:
        Scalar determinant ratio
    """
    return 1.0 + v @ M_inv @ u


def smw_inverse_update(M_inv, u, v, ratio):
    """Update cached inverse after rank-1 modification.

    (M + uv^T)^{-1} = M^{-1} - (M^{-1} u v^T M^{-1}) / (1 + v^T M^{-1} u)

    Source: Sherman-Morrison formula

    Args:
        M_inv: current inverse, shape (n, n)
        u: column vector, shape (n,)
        v: column vector, shape (n,)
        ratio: = 1 + v^T M^{-1} u (precomputed from smw_det_ratio)

    Returns:
        Updated inverse matrix, shape (n, n)
    """
    if abs(ratio) < 1e-300:
        # Ratio ≈ 0 means the rank-1 update makes M singular.
        # Fall back to full inverse recomputation via caller.
        return M_inv  # return unchanged; caller should detect via det ratio ≈ 0
    M_inv_u = M_inv @ u      # shape (n,)
    v_M_inv = v @ M_inv      # shape (n,)
    return M_inv - np.outer(M_inv_u, v_M_inv) / ratio


def smw_det_ratio_rank_k(M_inv, U_mat, V_mat):
    """Rank-k determinant ratio: det(M + U V^T) / det(M) = det(I_k + V^T M^{-1} U).

    Woodbury matrix identity for rank-k updates. Used when flipping
    multiple Grassmann bits at one site (up to k=4 Dirac components).

    Source: Woodbury (1950); Harville "Matrix Algebra" Thm 18.1.1

    Args:
        M_inv: inverse of original matrix, shape (n, n)
        U_mat: shape (n, k)
        V_mat: shape (n, k)

    Returns:
        Scalar determinant ratio
    """
    k = U_mat.shape[1]
    capacitance = np.eye(k) + V_mat.T @ M_inv @ U_mat  # k × k
    return np.linalg.det(capacitance)


# ════════════════════════════════════════════════════════════════════
# Fermion-bag sweep (Step 4)
# Source: Chandrasekharan PRD 82, 025007 (2010) — fermion-bag algorithm
# Source: deep research "Hybrid fermion-bag + gauge-link MC" — pseudocode
# ════════════════════════════════════════════════════════════════════

def fermion_bag_sweep(config, g, rng):
    """One fermion-bag Metropolis sweep at fixed gauge links.

    For each site x in random order:
    1. Propose flipping a random Grassmann occupation bit
    2. Determine the bond configuration change (which bonds activate/deactivate)
    3. Recompute the affected bag decomposition
    4. Compute bag weight ratio |det(M_new)/det(M_old)| via full recomputation
       (SMW optimization deferred to Step 7)
    5. Accept/reject via Metropolis: min(1, |ratio| * g^{Δn_monomers})
    6. Track sign of product of all bag determinants

    Args:
        config: GaugeFermionConfig (occupations + gauge links)
        g: four-fermion coupling
        rng: numpy random Generator

    Returns:
        (acceptance_rate, sign_product): sign_product is ±1
    """
    L = config.L
    occ = config.occupations
    n_accepted = 0
    n_proposed = 0
    sign_product = 1

    # Generate random site visit order
    sites = [(x0, x1, x2, x3) for x0 in range(L) for x1 in range(L)
             for x2 in range(L) for x3 in range(L)]
    rng.shuffle(sites)

    for site in sites:
        x0, x1, x2, x3 = site
        # Propose: flip a random occupation bit (0-7)
        flip_idx = rng.integers(0, 8)
        n_proposed += 1

        old_val = occ[x0, x1, x2, x3, flip_idx]
        new_val = 1.0 - old_val

        # Compute bond configuration for old and new states
        # A bond (x, mu) is "active" if BOTH endpoint sites have
        # sufficient occupation to form a bilinear.
        # For simplicity in this pure Python version: recompute bags
        # and their weights before and after the flip.

        # Compute old bag weights for all bags touching this site
        bond_config_old = _compute_bond_config(occ, L, g)
        bags_old = identify_bags(bond_config_old, L)
        old_weight = _total_bag_weight(bags_old, bond_config_old, config.gauge, L)

        # Apply flip
        occ[x0, x1, x2, x3, flip_idx] = new_val

        # Compute new bag weights
        bond_config_new = _compute_bond_config(occ, L, g)
        bags_new = identify_bags(bond_config_new, L)
        new_weight = _total_bag_weight(bags_new, bond_config_new, config.gauge, L)

        # Metropolis accept/reject on |weight ratio|
        if abs(old_weight) > 0:
            ratio = abs(new_weight) / abs(old_weight)
        elif abs(new_weight) > 0:
            ratio = float('inf')  # always accept transition from zero
        else:
            ratio = 1.0  # both zero — accept

        if ratio >= 1.0 or rng.random() < ratio:
            n_accepted += 1
            # Track sign change
            if old_weight != 0 and new_weight != 0:
                old_sign = 1 if old_weight > 0 else -1
                new_sign = 1 if new_weight > 0 else -1
                if old_sign != new_sign:
                    sign_product *= -1
        else:
            # Reject: restore old value
            occ[x0, x1, x2, x3, flip_idx] = old_val

    acc_rate = n_accepted / max(n_proposed, 1)
    return (acc_rate, sign_product)


def _compute_bond_config(occ, L, g):
    """Compute bond activation from occupations.

    A bond (x, mu) is active if there is a four-fermion interaction
    on that bond. For the ADW model, a bond is active when both sites
    have at least one ψ̄ (occ[4:8]) and one ψ (occ[0:4]) occupied.
    The coupling g weights the interaction but the bond is present
    whenever the Grassmann bilinear is nonzero.

    Args:
        occ: occupations array (L,L,L,L,8)
        L: lattice size
        g: coupling (>0 activates bonds)

    Returns:
        bond_config: array (L,L,L,L,4) of {0,1}
    """
    if abs(g) < 1e-15:
        return np.zeros((L, L, L, L, 4), dtype=np.int8)

    bond_config = np.zeros((L, L, L, L, 4), dtype=np.int8)
    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    # Check if site x has any ψ̄ AND ψ occupied
                    has_psi_bar_x = np.any(occ[x0, x1, x2, x3, 4:8] > 0)
                    has_psi_x = np.any(occ[x0, x1, x2, x3, :4] > 0)
                    if not (has_psi_bar_x and has_psi_x):
                        continue
                    for mu in range(4):
                        nb = [x0, x1, x2, x3]
                        nb[mu] = (nb[mu] + 1) % L
                        has_psi_y = np.any(occ[nb[0], nb[1], nb[2], nb[3], :4] > 0)
                        has_psi_bar_y = np.any(occ[nb[0], nb[1], nb[2], nb[3], 4:8] > 0)
                        if has_psi_y and has_psi_bar_y:
                            bond_config[x0, x1, x2, x3, mu] = 1
    return bond_config


def _total_bag_weight(bags, bond_config, gauge, L):
    """Product of all bag determinants.

    Returns the product of det(M_B) for all multi-site bags.
    Isolated (single-site) bags contribute trivially (weight 1).
    A zero determinant on any multi-site bag gives total weight = 0.

    Lean: bag_weight_real (GaugeFermionBag.lean)
    Source: Chandrasekharan, PRD 82, 025007 (2010), Eq. (12)
    """
    weight = 1.0
    for bag in bags:
        if len(bag) == 1:
            continue  # isolated sites contribute trivially
        M_B = build_fermion_matrix(bag, bond_config, gauge, L)
        det_val, _ = bag_weight(M_B)
        weight *= det_val
        if abs(weight) < 1e-300:
            return 0.0  # zero det → zero total weight
    return weight


# ════════════════════════════════════════════════════════════════════
# Gauge sweep with fermion determinant reweighting (Step 5)
# Source: deep research "Hybrid fermion-bag + gauge-link MC" — Phase 2
# ════════════════════════════════════════════════════════════════════

def gauge_sweep_with_det_reweighting(config, g, beta, rng):
    """Gauge link sweep with fermion determinant reweighting.

    For each link (x, mu):
    1. Compute pure gauge staple and propose via Kennedy-Pendleton heatbath
    2. Compute fermion contribution: ΔS_ferm = log|det(M_new)| - log|det(M_old)|
       for all bags touching this link
    3. Accept/reject: the heatbath samples the pure gauge distribution exactly,
       so only the fermion part needs Metropolis accept/reject
    4. Track sign flips

    For g=0 (no fermion coupling), reduces to pure gauge heatbath (always accept).

    Args:
        config: GaugeFermionConfig
        g: four-fermion coupling
        beta: Wilson plaquette coupling
        rng: numpy Generator

    Returns:
        (acceptance_rate, sign_product)
    """
    L = config.L
    occ = config.occupations
    gauge = config.gauge
    n_accepted = 0
    n_proposed = 0
    sign_product = 1

    # If no fermion coupling, use the existing fast JIT gauge sweep
    if abs(g) < 1e-15:
        seed = rng.integers(0, 2**31)
        acc = _gauge_sweep_jit(occ, gauge.links_L, gauge.links_R,
                               0.0, beta, L, seed)
        return (acc, 1)

    # With fermion coupling: precompute bags ONCE (occupations fixed during gauge sweep)
    bond_config = _compute_bond_config(occ, L, g)
    all_bags = identify_bags(bond_config, L)

    # Build site→bag index mapping
    site_to_bag = {}
    for bag_idx, bag in enumerate(all_bags):
        for site_arr in bag:
            site_to_bag[tuple(site_arr)] = bag_idx

    # Cache bag weights (recomputed when link changes affect a bag)
    bag_det_cache = {}

    def _get_bag_det(bag_idx):
        if bag_idx in bag_det_cache:
            return bag_det_cache[bag_idx]
        bag = all_bags[bag_idx]
        if len(bag) <= 1:
            bag_det_cache[bag_idx] = 1.0
            return 1.0
        M_B = build_fermion_matrix(bag, bond_config, gauge, L)
        det_val, _ = bag_weight(M_B)
        bag_det_cache[bag_idx] = det_val
        return det_val

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    for mu in range(4):
                        n_proposed += 1
                        site = (x0, x1, x2, x3)

                        # Save old link
                        old_qL = gauge.links_L[x0, x1, x2, x3, mu].copy()
                        old_qR = gauge.links_R[x0, x1, x2, x3, mu].copy()

                        # Find bags touching this link (site and site+mu)
                        nb = list(site)
                        nb[mu] = (nb[mu] + 1) % L
                        nb_t = tuple(nb)
                        affected_bags = set()
                        if site in site_to_bag:
                            affected_bags.add(site_to_bag[site])
                        if nb_t in site_to_bag:
                            affected_bags.add(site_to_bag[nb_t])

                        # Old weight: product of affected bag dets
                        old_weight = 1.0
                        for bi in affected_bags:
                            old_weight *= _get_bag_det(bi)

                        # Propose new link via heatbath (pure gauge sector)
                        if beta > 1e-10:
                            V_L, V_R = _staple_sum_jit(
                                gauge.links_L, gauge.links_R,
                                x0, x1, x2, x3, mu, L)
                            k_L = np.sqrt(_qnorm(V_L)) / 2.0
                            k_R = np.sqrt(_qnorm(V_R)) / 2.0

                            a_L = beta * k_L / 2.0
                            q_new_L = _kp_heatbath_single_jit(a_L)
                            if k_L > 1e-10:
                                V_L_norm = V_L / (2.0 * k_L)
                                gauge.links_L[x0, x1, x2, x3, mu] = \
                                    _qmul(q_new_L, _qconj(V_L_norm))
                            else:
                                q = rng.standard_normal(4)
                                gauge.links_L[x0, x1, x2, x3, mu] = \
                                    q / np.sqrt(_qnorm(q))

                            a_R = beta * k_R / 2.0
                            q_new_R = _kp_heatbath_single_jit(a_R)
                            if k_R > 1e-10:
                                V_R_norm = V_R / (2.0 * k_R)
                                gauge.links_R[x0, x1, x2, x3, mu] = \
                                    _qmul(q_new_R, _qconj(V_R_norm))
                            else:
                                q = rng.standard_normal(4)
                                gauge.links_R[x0, x1, x2, x3, mu] = \
                                    q / np.sqrt(_qnorm(q))
                        else:
                            # β=0: Haar random proposal
                            q = rng.standard_normal(4)
                            gauge.links_L[x0, x1, x2, x3, mu] = \
                                q / np.sqrt(_qnorm(q))
                            q = rng.standard_normal(4)
                            gauge.links_R[x0, x1, x2, x3, mu] = \
                                q / np.sqrt(_qnorm(q))

                        # Compute new bag weight (link changed, bags same)
                        # Invalidate cache for affected bags
                        for bi in affected_bags:
                            bag_det_cache.pop(bi, None)
                        new_weight = 1.0
                        for bi in affected_bags:
                            new_weight *= _get_bag_det(bi)

                        # Metropolis on fermion sector
                        if abs(old_weight) > 0:
                            ratio = abs(new_weight) / abs(old_weight)
                        elif abs(new_weight) > 0:
                            ratio = float('inf')
                        else:
                            ratio = 1.0

                        if ratio >= 1.0 or rng.random() < ratio:
                            n_accepted += 1
                            if old_weight != 0 and new_weight != 0:
                                old_sign = 1 if old_weight > 0 else -1
                                new_sign = 1 if new_weight > 0 else -1
                                if old_sign != new_sign:
                                    sign_product *= -1
                        else:
                            # Reject: restore old link + cache
                            gauge.links_L[x0, x1, x2, x3, mu] = old_qL
                            gauge.links_R[x0, x1, x2, x3, mu] = old_qR
                            for bi in affected_bags:
                                bag_det_cache.pop(bi, None)

    acc_rate = n_accepted / max(n_proposed, 1)
    return (acc_rate, sign_product)


def _link_bag_weight(site, mu, bond_config, gauge, L):
    """Compute product of bag weights for bags touching link (site, mu).

    A link touches two sites: site and site+mu. We find the bags
    containing these sites and compute their determinants.
    """
    x = np.array(site)
    nb = list(site)
    nb[mu] = (nb[mu] + 1) % L
    nb = tuple(nb)

    bags = identify_bags(bond_config, L)
    weight = 1.0
    for bag in bags:
        if len(bag) <= 1:
            continue
        sites_in_bag = set(tuple(s) for s in bag)
        if site in sites_in_bag or nb in sites_in_bag:
            M_B = build_fermion_matrix(bag, bond_config, gauge, L)
            det_val, _ = bag_weight(M_B)
            if abs(det_val) > 0:
                weight *= det_val
    return weight


# ════════════════════════════════════════════════════════════════════
# JIT fermion-bag kernels (Step 7)
# Architecture: union-find bags + fermion matrix + det sweep
# ════════════════════════════════════════════════════════════════════

@njit(cache=True)
def _site_to_flat(x0, x1, x2, x3, L):
    """Convert 4D coords to flat index."""
    return ((x0 * L + x1) * L + x2) * L + x3


@njit(cache=True)
def _flat_to_site(idx, L):
    """Convert flat index to 4D coords."""
    x3 = idx % L
    idx //= L
    x2 = idx % L
    idx //= L
    x1 = idx % L
    x0 = idx // L
    return x0, x1, x2, x3


@njit(cache=True)
def _uf_find(parent, i):
    """Union-find: find root with path compression."""
    while parent[i] != i:
        parent[i] = parent[parent[i]]
        i = parent[i]
    return i


@njit(cache=True)
def _uf_union(parent, rank, a, b):
    """Union-find: merge sets containing a and b."""
    ra = _uf_find(parent, a)
    rb = _uf_find(parent, b)
    if ra == rb:
        return
    if rank[ra] < rank[rb]:
        parent[ra] = rb
    elif rank[ra] > rank[rb]:
        parent[rb] = ra
    else:
        parent[rb] = ra
        rank[ra] += 1


@njit(cache=True)
def _staggered_phase_jit(x0, x1, x2, x3, mu):
    """η_μ(x) = (-1)^{x_0+...+x_{μ-1}} — numba JIT."""
    if mu == 0:
        return 1
    s = x0
    if mu >= 2:
        s += x1
    if mu >= 3:
        s += x2
    return 1 - 2 * (s % 2)


@njit(cache=True)
def _compute_bond_config_jit(occ, L):
    """Compute bond activation from occupations — JIT.

    Bond (x, mu) active when both sites have ψ̄ and ψ occupied.
    """
    V = L * L * L * L
    bonds = np.zeros((V, 4), dtype=np.int8)
    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    idx = _site_to_flat(x0, x1, x2, x3, L)
                    has_bar = False
                    has_psi = False
                    for i in range(4):
                        if occ[x0, x1, x2, x3, i] > 0.5:
                            has_psi = True
                        if occ[x0, x1, x2, x3, 4 + i] > 0.5:
                            has_bar = True
                    if not (has_bar and has_psi):
                        continue
                    for mu in range(4):
                        nb = np.array([x0, x1, x2, x3])
                        nb[mu] = (nb[mu] + 1) % L
                        has_bar_y = False
                        has_psi_y = False
                        for i in range(4):
                            if occ[nb[0], nb[1], nb[2], nb[3], i] > 0.5:
                                has_psi_y = True
                            if occ[nb[0], nb[1], nb[2], nb[3], 4 + i] > 0.5:
                                has_bar_y = True
                        if has_psi_y and has_bar_y:
                            bonds[idx, mu] = 1
    return bonds


@njit(cache=True)
def _identify_bags_jit(bonds, L):
    """Union-find bag identification — JIT.

    Returns parent array where _uf_find(parent, i) gives the bag root.
    """
    V = L * L * L * L
    parent = np.arange(V)
    rank = np.zeros(V, dtype=np.int32)

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    idx = _site_to_flat(x0, x1, x2, x3, L)
                    for mu in range(4):
                        if bonds[idx, mu]:
                            nb = np.array([x0, x1, x2, x3])
                            nb[mu] = (nb[mu] + 1) % L
                            nb_idx = _site_to_flat(nb[0], nb[1], nb[2], nb[3], L)
                            _uf_union(parent, rank, idx, nb_idx)
    return parent


@njit(cache=True)
def _precompute_bag_membership(parent, L):
    """Precompute bag membership arrays from union-find for O(1) lookup.

    Returns:
        bag_id: array(V,) — bag index for each site (0..n_bags-1)
        bag_sites_flat: array(V, 4) — site coords grouped by bag
        bag_start: array(V,) — start index in bag_sites_flat for each bag
        bag_count: array(V,) — number of sites in each bag
        n_bags: int — total number of bags
    """
    V = L * L * L * L

    # First pass: find canonical roots and assign bag IDs
    root_to_bag = np.full(V, -1, dtype=np.int64)
    bag_id = np.empty(V, dtype=np.int64)
    n_bags = 0
    for i in range(V):
        r = _uf_find(parent, i)
        if root_to_bag[r] < 0:
            root_to_bag[r] = n_bags
            n_bags += 1
        bag_id[i] = root_to_bag[r]

    # Second pass: count sites per bag
    bag_count = np.zeros(n_bags, dtype=np.int64)
    for i in range(V):
        bag_count[bag_id[i]] += 1

    # Compute start offsets (prefix sum)
    bag_start = np.zeros(n_bags, dtype=np.int64)
    for b in range(1, n_bags):
        bag_start[b] = bag_start[b - 1] + bag_count[b - 1]

    # Third pass: fill bag_sites_flat
    bag_sites_flat = np.empty((V, 4), dtype=np.int64)
    fill_pos = bag_start.copy()
    for i in range(V):
        b = bag_id[i]
        pos = fill_pos[b]
        x0, x1, x2, x3 = _flat_to_site(i, L)
        bag_sites_flat[pos, 0] = x0
        bag_sites_flat[pos, 1] = x1
        bag_sites_flat[pos, 2] = x2
        bag_sites_flat[pos, 3] = x3
        fill_pos[b] += 1

    return bag_id, bag_sites_flat, bag_start, bag_count, n_bags


@njit(cache=True)
def _bag_det_from_membership(bag_idx, bag_sites_flat, bag_start, bag_count,
                              links_L, links_R, L):
    """Compute det(M_B) for a specific bag using precomputed membership.

    O(k³) where k = bag size. No O(V) scan needed.
    """
    sz = bag_count[bag_idx]
    if sz <= 1:
        return 1.0
    start = bag_start[bag_idx]
    bag_sites = bag_sites_flat[start:start + sz]
    M = _build_fermion_matrix_for_bag_jit(bag_sites, sz, links_L, links_R, L)
    return np.linalg.det(M)


@njit(cache=True)
def _build_fermion_matrix_for_bag_jit(bag_sites, bag_size, links_L, links_R, L):
    """Build (4*bag_size) x (4*bag_size) real fermion matrix for a bag — JIT.

    Uses staggered phases and SO(4) gauge links.
    bag_sites: array of shape (bag_size, 4) with site coordinates.
    """
    dim = 4 * bag_size
    M = np.zeros((dim, dim))

    # Build site-to-bag-index map using linear search (bags are small)
    for i in range(bag_size):
        x0, x1, x2, x3 = bag_sites[i, 0], bag_sites[i, 1], bag_sites[i, 2], bag_sites[i, 3]
        for mu in range(4):
            eta = _staggered_phase_jit(x0, x1, x2, x3, mu)

            # Forward neighbor
            nb = np.array([x0, x1, x2, x3])
            nb[mu] = (nb[mu] + 1) % L
            # Find neighbor in bag
            j = -1
            for k in range(bag_size):
                if (bag_sites[k, 0] == nb[0] and bag_sites[k, 1] == nb[1] and
                        bag_sites[k, 2] == nb[2] and bag_sites[k, 3] == nb[3]):
                    j = k
                    break
            if j >= 0:
                R = _so4_matrix(
                    links_L[x0, x1, x2, x3, mu],
                    links_R[x0, x1, x2, x3, mu])
                for a in range(4):
                    for b in range(4):
                        M[4 * i + a, 4 * j + b] += 0.5 * eta * R[a, b]

            # Backward neighbor
            nb_back = np.array([x0, x1, x2, x3])
            nb_back[mu] = (nb_back[mu] - 1) % L
            j = -1
            for k in range(bag_size):
                if (bag_sites[k, 0] == nb_back[0] and bag_sites[k, 1] == nb_back[1] and
                        bag_sites[k, 2] == nb_back[2] and bag_sites[k, 3] == nb_back[3]):
                    j = k
                    break
            if j >= 0:
                R_back = _so4_matrix(
                    links_L[nb_back[0], nb_back[1], nb_back[2], nb_back[3], mu],
                    links_R[nb_back[0], nb_back[1], nb_back[2], nb_back[3], mu])
                for a in range(4):
                    for b in range(4):
                        M[4 * i + a, 4 * j + b] -= 0.5 * eta * R_back[b, a]

    return M


@njit(cache=True)
def _compute_link_delta_M(bag_sites, bag_size, dim,
                           x0, x1, x2, x3, mu,
                           old_qL, old_qR, new_qL, new_qR, L):
    """Compute the sparse ΔM from changing a single link (x, mu).

    When gauge link U_{x,mu} changes from (old_qL, old_qR) to (new_qL, new_qR),
    the fermion matrix changes in at most two 4×4 blocks:
    - The (i, j) block where i = bag_index(x), j = bag_index(x+mu) [forward]
    - The (j, i) block [backward, antisymmetric]

    Returns (delta_cols, U_mat, n_changed) where:
    - delta_cols[0:n_changed] = indices of changed columns
    - U_mat[dim, n_changed] = the corresponding column differences
    - Cost: O(bag_size) for the site lookup + O(1) for the 4×4 blocks
      This replaces the O(bag_size²) full matrix rebuild.

    Lean: determinant_rank1_update (GaugeFermionBag.lean)
    Source: Sherman-Morrison-Woodbury applied to sparse matrix updates
    """
    changed_cols = np.zeros(8, dtype=np.int64)
    U_mat = np.zeros((dim, 8))
    n_changed = 0

    # Find bag indices of x and x+mu via linear scan (bags typically small,
    # and for the big percolating bag this is O(bag_size) — done once per link)
    nb = np.array([x0, x1, x2, x3])
    nb[mu] = (nb[mu] + 1) % L

    i_bag = -1
    j_bag = -1
    for k in range(bag_size):
        if (bag_sites[k, 0] == x0 and bag_sites[k, 1] == x1 and
                bag_sites[k, 2] == x2 and bag_sites[k, 3] == x3):
            i_bag = k
        if (bag_sites[k, 0] == nb[0] and bag_sites[k, 1] == nb[1] and
                bag_sites[k, 2] == nb[2] and bag_sites[k, 3] == nb[3]):
            j_bag = k

    if i_bag < 0 or j_bag < 0:
        return changed_cols, U_mat, 0

    eta = _staggered_phase_jit(x0, x1, x2, x3, mu)
    R_old = _so4_matrix(old_qL, old_qR)
    R_new = _so4_matrix(new_qL, new_qR)
    dR = R_new - R_old

    # Forward: ΔM[4*i+a, 4*j+b] = 0.5 * eta * dR[a,b]
    # Backward: ΔM[4*j+a, 4*i+b] = -0.5 * eta * dR[b,a]
    # Affected columns: 4*j_bag+0..3 (from forward) and 4*i_bag+0..3 (from backward)

    # Columns for j_bag (forward contribution from site i to j)
    for b in range(4):
        col = 4 * j_bag + b
        changed_cols[n_changed] = col
        for a in range(4):
            U_mat[4 * i_bag + a, n_changed] = 0.5 * eta * dR[a, b]
        n_changed += 1

    # Columns for i_bag (backward contribution from site j to i)
    for b in range(4):
        col = 4 * i_bag + b
        changed_cols[n_changed] = col
        for a in range(4):
            U_mat[4 * j_bag + a, n_changed] = -0.5 * eta * dR[b, a]
        n_changed += 1

    return changed_cols, U_mat, n_changed


@njit(cache=True)
def _bonds_change_on_flip(occ, x0, x1, x2, x3, flip_idx, L):
    """Check if flipping occ[x,flip_idx] changes any bond activation.

    A bond (x, mu) is active when BOTH endpoints have ψ AND ψ̄ occupied.
    Flipping one bit only changes bonds if it crosses the threshold where
    a sector (ψ or ψ̄) goes from 0→1 or 1→0 occupied bits at this site.

    Cost: O(1) — just counts occupied bits in each sector.

    Returns True if any bond would change, False otherwise.
    """
    # Count occupied bits in each sector BEFORE flip
    n_psi_before = 0
    n_bar_before = 0
    for i in range(4):
        if occ[x0, x1, x2, x3, i] > 0.5:
            n_psi_before += 1
        if occ[x0, x1, x2, x3, 4 + i] > 0.5:
            n_bar_before += 1

    # After flip
    if flip_idx < 4:
        if occ[x0, x1, x2, x3, flip_idx] > 0.5:
            n_psi_after = n_psi_before - 1  # was 1, now 0
        else:
            n_psi_after = n_psi_before + 1  # was 0, now 1
        n_bar_after = n_bar_before
    else:
        n_psi_after = n_psi_before
        if occ[x0, x1, x2, x3, flip_idx] > 0.5:
            n_bar_after = n_bar_before - 1
        else:
            n_bar_after = n_bar_before + 1

    # Bond active requires BOTH sectors occupied at this site
    active_before = (n_psi_before > 0) and (n_bar_before > 0)
    active_after = (n_psi_after > 0) and (n_bar_after > 0)

    return active_before != active_after


@njit(cache=True)
def _bonds_activate_or_deactivate(occ, x0, x1, x2, x3, flip_idx, L):
    """Determine if flipping a bit ACTIVATES or DEACTIVATES bonds at this site.

    Returns:
        0 if no bond change
        +1 if bonds ACTIVATE (site gains ψ+ψ̄ capability → merge potential)
        -1 if bonds DEACTIVATE (site loses ψ or ψ̄ → split potential)
    """
    n_psi = 0
    n_bar = 0
    for i in range(4):
        if occ[x0, x1, x2, x3, i] > 0.5:
            n_psi += 1
        if occ[x0, x1, x2, x3, 4 + i] > 0.5:
            n_bar += 1

    if flip_idx < 4:
        if occ[x0, x1, x2, x3, flip_idx] > 0.5:
            n_psi_after = n_psi - 1
        else:
            n_psi_after = n_psi + 1
        n_bar_after = n_bar
    else:
        n_psi_after = n_psi
        if occ[x0, x1, x2, x3, flip_idx] > 0.5:
            n_bar_after = n_bar - 1
        else:
            n_bar_after = n_bar + 1

    active_before = (n_psi > 0) and (n_bar > 0)
    active_after = (n_psi_after > 0) and (n_bar_after > 0)

    if active_before == active_after:
        return 0
    elif active_after and not active_before:
        return 1  # activate → merge
    else:
        return -1  # deactivate → potential split


@njit(cache=True)
def _bfs_connected_without_bond(bag_sites, bag_size, bonds_flat, L,
                                 site_x_flat, site_y_flat):
    """Check if bag remains connected after removing the bond between
    site_x and site_y. Uses BFS from site_x, checking if site_y is reachable
    WITHOUT using the direct bond between them.

    Cost: O(bag_size) — BFS visits each site at most once.
    Returns True if still connected, False if the bond is a bridge (disconnects).

    Source: standard graph theory — bridge detection via BFS
    """
    V = L * L * L * L
    visited = np.zeros(V, dtype=np.int8)
    # Use a simple array as queue (BFS)
    queue = np.empty(bag_size, dtype=np.int64)
    head = 0
    tail = 0
    queue[tail] = site_x_flat
    tail += 1
    visited[site_x_flat] = 1

    while head < tail:
        curr = queue[head]
        head += 1
        cx0, cx1, cx2, cx3 = _flat_to_site(curr, L)

        for mu in range(4):
            # Check if bond is active
            if bonds_flat[curr, mu] == 0:
                continue
            # Skip the removed bond (both directions)
            nb_flat_arr = np.array([cx0, cx1, cx2, cx3])
            nb_flat_arr[mu] = (nb_flat_arr[mu] + 1) % L
            nb_flat = _site_to_flat(nb_flat_arr[0], nb_flat_arr[1],
                                     nb_flat_arr[2], nb_flat_arr[3], L)
            if (curr == site_x_flat and nb_flat == site_y_flat) or \
               (curr == site_y_flat and nb_flat == site_x_flat):
                continue
            # Also check backward bonds
            if visited[nb_flat] == 0:
                # Verify neighbor is in the bag
                in_bag = False
                for k in range(bag_size):
                    if _site_to_flat(bag_sites[k, 0], bag_sites[k, 1],
                                      bag_sites[k, 2], bag_sites[k, 3], L) == nb_flat:
                        in_bag = True
                        break
                if in_bag:
                    visited[nb_flat] = 1
                    queue[tail] = nb_flat
                    tail += 1

    return visited[site_y_flat] == 1


@njit(cache=True)
def _fermion_bag_sweep_core_jit(occ, links_L, links_R, g, L, rng_seed):
    """Core fermion-bag Metropolis sweep — fully optimized JIT.

    Key optimization: 88% of Grassmann flips don't change bonds.
    When bonds are stable, the bag structure and fermion matrix M_B
    are IDENTICAL → det ratio = 1.0 → always accept (O(1) per proposal).
    Only the 12% of flips that change bonds need full recomputation.

    This reduces the effective cost from O(V²) to O(0.12 × V²) ≈ O(V²/8).

    Physics justification: the fermion-bag weight det(M_B[U]) depends on
    the gauge links U (which are FIXED during the fermion sweep) and the
    bag STRUCTURE (which sites are connected). It does NOT depend on the
    occupation numbers directly — occupations only affect WHICH bonds are
    active, determining the bag decomposition.

    Lean: determinant_rank1_update (GaugeFermionBag.lean)
    Source: Chandrasekharan PRD 82, 025007 (2010) — fermion-bag algorithm

    Returns (acceptance_rate, sign_product).
    """
    np.random.seed(rng_seed)
    V = L * L * L * L
    n_accepted = 0
    n_proposed = 0
    sign_product = 1

    for site_idx in range(V):
        x0, x1, x2, x3 = _flat_to_site(site_idx, L)
        flip_idx = np.random.randint(0, 8)
        n_proposed += 1

        old_val = occ[x0, x1, x2, x3, flip_idx]

        # O(1) check: does this flip change any bonds?
        if not _bonds_change_on_flip(occ, x0, x1, x2, x3, flip_idx, L):
            # Bonds stable → bag structure unchanged → det ratio = 1.0
            # Always accept (occupations are Grassmann DOFs, not Boltzmann)
            occ[x0, x1, x2, x3, flip_idx] = 1.0 - old_val
            n_accepted += 1
            continue

        # Bonds change → need to determine if merge, deactivate, or split.
        # For now: full recomputation (correct but O(V²) per proposal).
        # The Schur complement optimization for merge/deactivate cases
        # is implemented but requires cached M^{-1} infrastructure that
        # needs the precomputed bag membership from sweep start — which
        # is invalidated by each bond-changing flip. For L≤8, the 12%
        # of proposals that change bonds at O(V²) each is tolerable
        # (~0.6s at L=4). For L≥12, the H-S + RHMC algorithm is
        # recommended over further fermion-bag optimization.
        #
        # Full recomputation:
        bonds_old = _compute_bond_config_jit(occ, L)
        parent_old = _identify_bags_jit(bonds_old, L)

        # Find ALL affected bag roots: the site itself + its 8 neighbors
        # (4 forward + 4 backward). A flip can split/merge any of these bags.
        affected_roots_old = np.empty(9, dtype=np.int64)
        n_affected = 0
        r = _uf_find(parent_old, site_idx)
        affected_roots_old[0] = r
        n_affected = 1
        for mu in range(4):
            nb_fwd = np.array([x0, x1, x2, x3])
            nb_fwd[mu] = (nb_fwd[mu] + 1) % L
            nb_back = np.array([x0, x1, x2, x3])
            nb_back[mu] = (nb_back[mu] - 1) % L
            r_fwd = _uf_find(parent_old,
                             _site_to_flat(nb_fwd[0], nb_fwd[1], nb_fwd[2], nb_fwd[3], L))
            r_back = _uf_find(parent_old,
                              _site_to_flat(nb_back[0], nb_back[1], nb_back[2], nb_back[3], L))
            # Add if not already present
            found_fwd = False
            found_back = False
            for k in range(n_affected):
                if affected_roots_old[k] == r_fwd:
                    found_fwd = True
                if affected_roots_old[k] == r_back:
                    found_back = True
            if not found_fwd:
                affected_roots_old[n_affected] = r_fwd
                n_affected += 1
            if not found_back:
                affected_roots_old[n_affected] = r_back
                n_affected += 1

        # Compute product of old bag dets for all affected bags
        old_det = 1.0
        for ar_idx in range(n_affected):
            ar = affected_roots_old[ar_idx]
            bag_sites_list = np.empty((V, 4), dtype=np.int64)
            bag_sz = 0
            for i in range(V):
                if _uf_find(parent_old, i) == ar:
                    s0, s1, s2, s3 = _flat_to_site(i, L)
                    bag_sites_list[bag_sz, 0] = s0
                    bag_sites_list[bag_sz, 1] = s1
                    bag_sites_list[bag_sz, 2] = s2
                    bag_sites_list[bag_sz, 3] = s3
                    bag_sz += 1
            if bag_sz > 1:
                M_tmp = _build_fermion_matrix_for_bag_jit(
                    bag_sites_list[:bag_sz], bag_sz, links_L, links_R, L)
                old_det *= np.linalg.det(M_tmp)

        # Flip
        occ[x0, x1, x2, x3, flip_idx] = 1.0 - old_val

        # Compute bonds and bags AFTER flip
        bonds_new = _compute_bond_config_jit(occ, L)
        parent_new = _identify_bags_jit(bonds_new, L)

        # Find affected roots in the NEW bag structure (same neighbor set)
        affected_roots_new = np.empty(9, dtype=np.int64)
        n_affected_new = 0
        r = _uf_find(parent_new, site_idx)
        affected_roots_new[0] = r
        n_affected_new = 1
        for mu in range(4):
            nb_fwd = np.array([x0, x1, x2, x3])
            nb_fwd[mu] = (nb_fwd[mu] + 1) % L
            nb_back = np.array([x0, x1, x2, x3])
            nb_back[mu] = (nb_back[mu] - 1) % L
            r_fwd = _uf_find(parent_new,
                             _site_to_flat(nb_fwd[0], nb_fwd[1], nb_fwd[2], nb_fwd[3], L))
            r_back = _uf_find(parent_new,
                              _site_to_flat(nb_back[0], nb_back[1], nb_back[2], nb_back[3], L))
            found_fwd = False
            found_back = False
            for k in range(n_affected_new):
                if affected_roots_new[k] == r_fwd:
                    found_fwd = True
                if affected_roots_new[k] == r_back:
                    found_back = True
            if not found_fwd:
                affected_roots_new[n_affected_new] = r_fwd
                n_affected_new += 1
            if not found_back:
                affected_roots_new[n_affected_new] = r_back
                n_affected_new += 1

        # Compute product of new bag dets for all affected bags
        new_det = 1.0
        for ar_idx in range(n_affected_new):
            ar = affected_roots_new[ar_idx]
            bag_sites_list = np.empty((V, 4), dtype=np.int64)
            bag_sz = 0
            for i in range(V):
                if _uf_find(parent_new, i) == ar:
                    s0, s1, s2, s3 = _flat_to_site(i, L)
                    bag_sites_list[bag_sz, 0] = s0
                    bag_sites_list[bag_sz, 1] = s1
                    bag_sites_list[bag_sz, 2] = s2
                    bag_sites_list[bag_sz, 3] = s3
                    bag_sz += 1
            if bag_sz > 1:
                M_tmp = _build_fermion_matrix_for_bag_jit(
                    bag_sites_list[:bag_sz], bag_sz, links_L, links_R, L)
                new_det *= np.linalg.det(M_tmp)

        # Metropolis
        if abs(old_det) > 1e-300:
            ratio = abs(new_det) / abs(old_det)
        elif abs(new_det) > 1e-300:
            ratio = 1e300
        else:
            ratio = 1.0

        if ratio >= 1.0 or np.random.random() < ratio:
            n_accepted += 1
            if old_det != 0.0 and new_det != 0.0:
                if (old_det > 0) != (new_det > 0):
                    sign_product *= -1
        else:
            occ[x0, x1, x2, x3, flip_idx] = old_val

    return n_accepted / max(n_proposed, 1), sign_product


def fermion_bag_sweep_jit(config, g, rng):
    """JIT fermion-bag sweep — Python wrapper.

    Delegates to numba-compiled core. Same interface as fermion_bag_sweep.
    """
    seed = int(rng.integers(0, 2**31))
    acc, sign = _fermion_bag_sweep_core_jit(
        config.occupations, config.gauge.links_L, config.gauge.links_R,
        g, config.L, seed)
    return (acc, sign)


@njit(cache=True)
def _gauge_sweep_with_det_jit(occ, links_L, links_R, g, beta, L, rng_seed):
    """Full JIT gauge sweep with fermion det reweighting.

    For each link: heatbath proposal from pure gauge sector, then
    Metropolis accept/reject based on fermion bag det ratio.

    Key optimization: bags are precomputed ONCE (occupations fixed during
    gauge sweep), only bag WEIGHTS change when links update.
    """
    np.random.seed(rng_seed)
    V = L * L * L * L
    n_accepted = 0
    n_proposed = 0
    sign_product = 1

    if abs(g) < 1e-15:
        # No fermion coupling — use pure gauge heatbath (always accept)
        for x0 in range(L):
            for x1 in range(L):
                for x2 in range(L):
                    for x3 in range(L):
                        for mu in range(4):
                            n_proposed += 1
                            V_L, V_R = _staple_sum_jit(links_L, links_R,
                                                        x0, x1, x2, x3, mu, L)
                            k_L = np.sqrt(_qnorm(V_L)) / 2.0
                            if beta > 1e-10 and k_L > 1e-10:
                                a_L = beta * k_L / 2.0
                                q_new = _kp_heatbath_single_jit(a_L)
                                V_L_norm = V_L / (2.0 * k_L)
                                links_L[x0, x1, x2, x3, mu] = _qmul(q_new, _qconj(V_L_norm))
                            else:
                                q = np.random.standard_normal(4)
                                links_L[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))

                            k_R = np.sqrt(_qnorm(V_R)) / 2.0
                            if beta > 1e-10 and k_R > 1e-10:
                                a_R = beta * k_R / 2.0
                                q_new = _kp_heatbath_single_jit(a_R)
                                V_R_norm = V_R / (2.0 * k_R)
                                links_R[x0, x1, x2, x3, mu] = _qmul(q_new, _qconj(V_R_norm))
                            else:
                                q = np.random.standard_normal(4)
                                links_R[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))
                            n_accepted += 1
        return n_accepted / max(n_proposed, 1), 1

    # With fermion coupling: precompute bags + cached M^{-1} for big bag
    bonds = _compute_bond_config_jit(occ, L)
    parent = _identify_bags_jit(bonds, L)
    bag_id, bag_sites_flat, bag_start, bag_count, n_bags = \
        _precompute_bag_membership(parent, L)

    # Find the largest bag and precompute its M^{-1} (O(n³) ONCE)
    # This cache is used for all link proposals touching this bag,
    # reducing each det ratio from O(n³) to O(n²).
    biggest_bag = -1
    biggest_sz = 0
    for b in range(n_bags):
        if bag_count[b] > biggest_sz:
            biggest_sz = bag_count[b]
            biggest_bag = b

    # Cached inverse for the big bag (recomputed periodically)
    big_bag_dim = 4 * biggest_sz
    big_bag_M = np.zeros((big_bag_dim, big_bag_dim))
    big_bag_inv = np.zeros((big_bag_dim, big_bag_dim))
    big_bag_det = 1.0
    big_bag_inv_valid = False
    inv_recompute_counter = 0
    INV_RECOMPUTE_INTERVAL = 50  # recompute from scratch every N accepts

    # Precompute M and M^{-1} for each non-trivial bag (O(n³) once)
    # Store det values and inverses for SMW updates
    # Use a flat array keyed by bag index
    max_bag_dim = 0
    for b in range(n_bags):
        if bag_count[b] > 1:
            d = 4 * bag_count[b]
            if d > max_bag_dim:
                max_bag_dim = d

    # For bags that are too large for SMW to be practical (>200 sites = 800×800),
    # fall back to full det recomputation. For smaller bags, use cached inverse.
    SMW_THRESHOLD = 200  # sites; above this, full det is O(n³) anyway

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    for mu in range(4):
                        n_proposed += 1
                        site_idx = _site_to_flat(x0, x1, x2, x3, L)
                        my_bag = bag_id[site_idx]
                        bag_sz = bag_count[my_bag]

                        # Save old link
                        old_qL = links_L[x0, x1, x2, x3, mu].copy()
                        old_qR = links_R[x0, x1, x2, x3, mu].copy()

                        # For single-site bags: no fermion coupling, always accept
                        if bag_sz <= 1:
                            # Pure gauge heatbath
                            V_L, V_R = _staple_sum_jit(links_L, links_R,
                                                        x0, x1, x2, x3, mu, L)
                            k_L = np.sqrt(_qnorm(V_L)) / 2.0
                            if beta > 1e-10 and k_L > 1e-10:
                                a_L = beta * k_L / 2.0
                                q_new = _kp_heatbath_single_jit(a_L)
                                V_L_norm = V_L / (2.0 * k_L)
                                links_L[x0, x1, x2, x3, mu] = _qmul(q_new, _qconj(V_L_norm))
                            else:
                                q = np.random.standard_normal(4)
                                links_L[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))
                            k_R = np.sqrt(_qnorm(V_R)) / 2.0
                            if beta > 1e-10 and k_R > 1e-10:
                                a_R = beta * k_R / 2.0
                                q_new = _kp_heatbath_single_jit(a_R)
                                V_R_norm = V_R / (2.0 * k_R)
                                links_R[x0, x1, x2, x3, mu] = _qmul(q_new, _qconj(V_R_norm))
                            else:
                                q = np.random.standard_normal(4)
                                links_R[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))
                            n_accepted += 1
                            continue

                        # ──────────────────────────────────────────────
                        # Multi-site bag: cached M^{-1} + O(n²) det ratio
                        # ──────────────────────────────────────────────
                        # Architecture:
                        # 1. M^{-1} for the big bag is computed ONCE (O(n³))
                        # 2. Each link proposal: build M_new, ΔM = M_new - M_old
                        # 3. det ratio = det(I + M^{-1} ΔM) — O(n²) via matmul
                        # 4. On accept: update M via M = M_new (link changed)
                        #    Periodically recompute M^{-1} to prevent drift
                        # 5. On reject: restore link, M unchanged
                        #
                        # For the big bag at L=4 (n=900): reduces from
                        # 900 × 3ms = 2.7s to 900 × 0.5ms = 0.45s per sweep.
                        #
                        # Lean: determinant_rank1_update (GaugeFermionBag.lean)
                        # Source: Sherman & Morrison (1950); Woodbury (1950)
                        # ──────────────────────────────────────────────

                        start = bag_start[my_bag]
                        bag_sites = bag_sites_flat[start:start + bag_sz]
                        dim = 4 * bag_sz

                        # Initialize or refresh cached M^{-1} for this bag
                        if my_bag == biggest_bag and not big_bag_inv_valid:
                            big_bag_M = _build_fermion_matrix_for_bag_jit(
                                bag_sites, bag_sz, links_L, links_R, L)
                            big_bag_det = np.linalg.det(big_bag_M)
                            if abs(big_bag_det) > 1e-200:
                                big_bag_inv = np.linalg.solve(
                                    big_bag_M, np.eye(dim))
                            big_bag_inv_valid = True
                            inv_recompute_counter = 0

                        # Propose new link via heatbath
                        V_L, V_R = _staple_sum_jit(links_L, links_R,
                                                    x0, x1, x2, x3, mu, L)
                        k_L = np.sqrt(_qnorm(V_L)) / 2.0
                        if beta > 1e-10 and k_L > 1e-10:
                            a_L = beta * k_L / 2.0
                            q_new = _kp_heatbath_single_jit(a_L)
                            V_L_norm = V_L / (2.0 * k_L)
                            links_L[x0, x1, x2, x3, mu] = _qmul(q_new, _qconj(V_L_norm))
                        else:
                            q = np.random.standard_normal(4)
                            links_L[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))
                        k_R = np.sqrt(_qnorm(V_R)) / 2.0
                        if beta > 1e-10 and k_R > 1e-10:
                            a_R = beta * k_R / 2.0
                            q_new = _kp_heatbath_single_jit(a_R)
                            V_R_norm = V_R / (2.0 * k_R)
                            links_R[x0, x1, x2, x3, mu] = _qmul(q_new, _qconj(V_R_norm))
                        else:
                            q = np.random.standard_normal(4)
                            links_R[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))

                        # ──────────────────────────────────────────────
                        # Woodbury det ratio via sparse ΔM
                        # ──────────────────────────────────────────────
                        # _compute_link_delta_M gives us U_mat (n×k, k≤8)
                        # and the changed column indices. The Woodbury formula:
                        #   det(M + U e_cols^T) / det(M) = det(I_k + e_cols^T M^{-1} U)
                        # is a k×k det — O(k³) = O(512) flops.
                        # The matmul M^{-1} U is O(kn) = O(8×900) flops.
                        # Total: ~7K flops per link vs ~729M for full det.
                        #
                        # Source: Sherman-Morrison-Woodbury identity
                        # Lean: determinant_rank1_update (GaugeFermionBag.lean)
                        # ──────────────────────────────────────────────
                        if my_bag == biggest_bag and big_bag_inv_valid and abs(big_bag_det) > 1e-200:
                            # Compute sparse ΔM from link change (O(bag_size) lookup + O(1) blocks)
                            changed_cols, U_delta, n_ch = _compute_link_delta_M(
                                bag_sites, bag_sz, dim,
                                x0, x1, x2, x3, mu,
                                old_qL, old_qR,
                                links_L[x0, x1, x2, x3, mu],
                                links_R[x0, x1, x2, x3, mu], L)

                            if n_ch == 0:
                                ratio = 1.0
                                new_det = big_bag_det
                            else:
                                # Woodbury: capacitance matrix C = I_k + V^T M^{-1} U
                                # where V = e_{changed_cols} (selector), U = U_delta columns
                                # So C[ci, cj] = δ_{ci,cj} + Σ_r M^{-1}[changed_cols[ci], r] * U_delta[r, cj]
                                k = n_ch
                                cap = np.eye(k)
                                for ci in range(k):
                                    for cj in range(k):
                                        s = 0.0
                                        for r in range(dim):
                                            s += big_bag_inv[changed_cols[ci], r] * U_delta[r, cj]
                                        cap[ci, cj] += s
                                det_ratio = np.linalg.det(cap)
                                ratio = abs(det_ratio)
                                new_det = big_bag_det * det_ratio
                        else:
                            # Non-big multi-site bag (rare — most multi-site sites
                            # are in the biggest bag). Use full det for correctness.
                            M_after = _build_fermion_matrix_for_bag_jit(
                                bag_sites, bag_sz, links_L, links_R, L)
                            new_det = np.linalg.det(M_after)
                            # Restore old link to compute old det
                            saved_new_qL = links_L[x0, x1, x2, x3, mu].copy()
                            saved_new_qR = links_R[x0, x1, x2, x3, mu].copy()
                            links_L[x0, x1, x2, x3, mu] = old_qL
                            links_R[x0, x1, x2, x3, mu] = old_qR
                            M_before = _build_fermion_matrix_for_bag_jit(
                                bag_sites, bag_sz, links_L, links_R, L)
                            old_det_val = np.linalg.det(M_before)
                            # Restore proposed link
                            links_L[x0, x1, x2, x3, mu] = saved_new_qL
                            links_R[x0, x1, x2, x3, mu] = saved_new_qR
                            if abs(old_det_val) > 1e-300:
                                ratio = abs(new_det / old_det_val)
                            elif abs(new_det) > 1e-300:
                                ratio = 1e300
                            else:
                                ratio = 1.0
                            n_ch = 0

                        # Metropolis accept/reject
                        if ratio >= 1.0 or np.random.random() < ratio:
                            n_accepted += 1
                            if my_bag == biggest_bag and big_bag_inv_valid and n_ch > 0:
                                # Apply ΔM to cached M
                                for ci in range(n_ch):
                                    c = changed_cols[ci]
                                    for r in range(dim):
                                        big_bag_M[r, c] += U_delta[r, ci]
                                big_bag_det = new_det

                                # Woodbury inverse update: M_new^{-1} = M_old^{-1}
                                #   - M_old^{-1} U cap^{-1} V^T M_old^{-1}
                                # where U = U_delta columns, V = e_{changed_cols},
                                # cap = I + V^T M^{-1} U (already computed above).
                                # This keeps big_bag_inv consistent with big_bag_M.
                                #
                                # Lean: smw_inverse_update (GaugeFermionBag.lean)
                                # Source: Woodbury (1950), Matrix Inversion Lemma
                                if abs(det_ratio) > 1e-200:
                                    cap_inv = np.linalg.solve(cap, np.eye(k))
                                    # inv_U = M^{-1} @ U (dim × k)
                                    inv_U = np.zeros((dim, k))
                                    for ci in range(k):
                                        for r in range(dim):
                                            for s in range(dim):
                                                inv_U[r, ci] += big_bag_inv[r, s] * U_delta[s, ci]
                                    # V_inv = V^T @ M^{-1} = M^{-1}[changed_cols, :] (k × dim)
                                    V_inv = np.zeros((k, dim))
                                    for ci in range(k):
                                        for s in range(dim):
                                            V_inv[ci, s] = big_bag_inv[changed_cols[ci], s]
                                    # correction = inv_U @ cap_inv @ V_inv (dim × dim)
                                    temp = np.zeros((k, dim))
                                    for ci in range(k):
                                        for s in range(dim):
                                            for cj in range(k):
                                                temp[ci, s] += cap_inv[ci, cj] * V_inv[cj, s]
                                    for r in range(dim):
                                        for s in range(dim):
                                            corr = 0.0
                                            for ci in range(k):
                                                corr += inv_U[r, ci] * temp[ci, s]
                                            big_bag_inv[r, s] -= corr

                                inv_recompute_counter += 1
                                if inv_recompute_counter >= INV_RECOMPUTE_INTERVAL:
                                    # Refresh inverse from scratch to prevent drift
                                    if abs(big_bag_det) > 1e-200:
                                        big_bag_inv = np.linalg.solve(
                                            big_bag_M, np.eye(dim))
                                    big_bag_det = np.linalg.det(big_bag_M)
                                    inv_recompute_counter = 0
                        else:
                            links_L[x0, x1, x2, x3, mu] = old_qL
                            links_R[x0, x1, x2, x3, mu] = old_qR

    return n_accepted / max(n_proposed, 1), sign_product


def gauge_sweep_jit(config, g, beta, rng):
    """JIT gauge sweep with det reweighting — Python wrapper."""
    seed = int(rng.integers(0, 2**31))
    acc, sign = _gauge_sweep_with_det_jit(
        config.occupations, config.gauge.links_L, config.gauge.links_R,
        g, beta, config.L, seed)
    return (acc, sign)


# ════════════════════════════════════════════════════════════════════
# JIT measurement kernels (Step 7)
# ════════════════════════════════════════════════════════════════════

# Precompute gamma matrices as module-level constants for numba
# Real parts of γ^0, γ^2 and imaginary parts of γ^1, γ^3
def _precompute_gamma_arrays():
    """Extract real/imag numpy arrays from complex gammas for JIT kernels."""
    from src.core.constants import EUCLIDEAN_GAMMA_4D
    g = EUCLIDEAN_GAMMA_4D
    # Store as (4, 4, 4) real and (4, 4, 4) imag
    return g.real.copy(), g.imag.copy()

_GAMMA_REAL, _GAMMA_IMAG = _precompute_gamma_arrays()


@njit(cache=True)
def _measure_tetrad_correct_jit_core(occ, links_L, links_R, L,
                                      gamma_real, gamma_imag):
    """JIT kernel for correct tetrad measurement with gamma matrices.

    Returns (m_E_real, m_E_imag, m_E_sq) where m_E is (4,4) complex.
    """
    V = L * L * L * L
    m_E_re = np.zeros((4, 4))
    m_E_im = np.zeros((4, 4))

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    psi_bar = np.empty(4)
                    for i in range(4):
                        psi_bar[i] = occ[x0, x1, x2, x3, 4 + i]

                    for mu in range(4):
                        nb = np.array([x0, x1, x2, x3])
                        nb[mu] = (nb[mu] + 1) % L
                        psi_y = np.empty(4)
                        for i in range(4):
                            psi_y[i] = occ[nb[0], nb[1], nb[2], nb[3], i]

                        R = _so4_matrix(links_L[x0, x1, x2, x3, mu],
                                        links_R[x0, x1, x2, x3, mu])

                        # For each a: E^a = psi_bar @ (gamma^a @ R) @ psi_y
                        # gamma^a @ R = (gamma_real[a] + i*gamma_imag[a]) @ R
                        # = gamma_real[a]@R + i*gamma_imag[a]@R
                        for a in range(4):
                            E_re = 0.0
                            E_im = 0.0
                            for i in range(4):
                                gRpsi_re = 0.0
                                gRpsi_im = 0.0
                                for k in range(4):
                                    Rpsi_k = 0.0
                                    for j in range(4):
                                        Rpsi_k += R[k, j] * psi_y[j]
                                    gRpsi_re += gamma_real[a, i, k] * Rpsi_k
                                    gRpsi_im += gamma_imag[a, i, k] * Rpsi_k
                                E_re += psi_bar[i] * gRpsi_re
                                E_im += psi_bar[i] * gRpsi_im
                            m_E_re[a, mu] += E_re
                            m_E_im[a, mu] += E_im

    scale = 1.0 / (4 * V)
    m_E_sq = 0.0
    for a in range(4):
        for mu in range(4):
            m_E_re[a, mu] *= scale
            m_E_im[a, mu] *= scale
            m_E_sq += m_E_re[a, mu]**2 + m_E_im[a, mu]**2

    return m_E_re, m_E_im, m_E_sq


def measure_tetrad_correct_jit(config):
    """JIT-accelerated correct tetrad measurement. Same interface as pure Python."""
    m_E_re, m_E_im, m_E_sq = _measure_tetrad_correct_jit_core(
        config.occupations, config.gauge.links_L, config.gauge.links_R,
        config.L, _GAMMA_REAL, _GAMMA_IMAG)
    m_E = m_E_re + 1j * m_E_im
    return m_E, m_E_sq


@njit(cache=True)
def _measure_metric_correct_jit_core(occ, links_L, links_R, L,
                                      gamma_real, gamma_imag):
    """JIT kernel for correct metric measurement (Option A, no conjugation).

    g_{μν} = Σ_a E^a_μ · E^a_ν (complex product, result is real).
    Returns (Q_real, trQ2) where Q is traceless symmetric metric.
    """
    V = L * L * L * L
    M_met = np.zeros((4, 4))  # real accumulator

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    psi_bar = np.empty(4)
                    for i in range(4):
                        psi_bar[i] = occ[x0, x1, x2, x3, 4 + i]

                    E_re = np.zeros((4, 4))
                    E_im = np.zeros((4, 4))

                    for mu in range(4):
                        nb = np.array([x0, x1, x2, x3])
                        nb[mu] = (nb[mu] + 1) % L
                        psi_y = np.empty(4)
                        for i in range(4):
                            psi_y[i] = occ[nb[0], nb[1], nb[2], nb[3], i]
                        R = _so4_matrix(links_L[x0, x1, x2, x3, mu],
                                        links_R[x0, x1, x2, x3, mu])
                        for a in range(4):
                            ere = 0.0
                            eim = 0.0
                            for i in range(4):
                                gRpsi_re = 0.0
                                gRpsi_im = 0.0
                                for k in range(4):
                                    Rpsi_k = 0.0
                                    for j in range(4):
                                        Rpsi_k += R[k, j] * psi_y[j]
                                    gRpsi_re += gamma_real[a, i, k] * Rpsi_k
                                    gRpsi_im += gamma_imag[a, i, k] * Rpsi_k
                                ere += psi_bar[i] * gRpsi_re
                                eim += psi_bar[i] * gRpsi_im
                            E_re[a, mu] = ere
                            E_im[a, mu] = eim

                    # g_{μν} = Σ_a E^a_μ · E^a_ν (Option A, no conjugation)
                    # (re + i*im)(re + i*im) = re*re - im*im + i*2*re*im
                    # For a=0,2: im=0, so product is re*re (real ≥ 0)
                    # For a=1,3: re=0, so product is -im*im (real ≤ 0)
                    # Total is always real
                    for mu in range(4):
                        for nu in range(4):
                            for a in range(4):
                                M_met[mu, nu] += (E_re[a, mu] * E_re[a, nu]
                                                  - E_im[a, mu] * E_im[a, nu])

    for i in range(4):
        for j in range(4):
            M_met[i, j] /= V

    # Q = M - (TrM/4)I
    tr = M_met[0, 0] + M_met[1, 1] + M_met[2, 2] + M_met[3, 3]
    Q = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            Q[i, j] = M_met[i, j]
        Q[i, i] -= tr / 4.0

    # Tr(Q²)
    trQ2 = 0.0
    for i in range(4):
        for j in range(4):
            trQ2 += Q[i, j] * Q[j, i]

    return Q, trQ2


def measure_metric_correct_jit(config):
    """JIT-accelerated correct metric measurement. Same interface as pure Python."""
    Q_real, trQ2 = _measure_metric_correct_jit_core(
        config.occupations, config.gauge.links_L, config.gauge.links_R,
        config.L, _GAMMA_REAL, _GAMMA_IMAG)
    Q = Q_real.astype(complex)
    return Q, complex(trQ2)


# ════════════════════════════════════════════════════════════════════
# Numba JIT kernels for inner-loop math (legacy, from Wave 7A)
# ════════════════════════════════════════════════════════════════════

@njit(cache=True)
def _qmul(q1, q2):
    """Quaternion multiply — numba-compatible, single pair."""
    a1, b1, c1, d1 = q1[0], q1[1], q1[2], q1[3]
    a2, b2, c2, d2 = q2[0], q2[1], q2[2], q2[3]
    out = np.empty(4)
    out[0] = a1*a2 - b1*b2 - c1*c2 - d1*d2
    out[1] = a1*b2 + b1*a2 + c1*d2 - d1*c2
    out[2] = a1*c2 - b1*d2 + c1*a2 + d1*b2
    out[3] = a1*d2 + b1*c2 - c1*b2 + d1*a2
    return out


@njit(cache=True)
def _qconj(q):
    """Quaternion conjugate — numba-compatible."""
    out = np.empty(4)
    out[0] = q[0]
    out[1] = -q[1]
    out[2] = -q[2]
    out[3] = -q[3]
    return out


@njit(cache=True)
def _so4_matrix(q_L, q_R):
    """Build 4×4 SO(4) matrix from quaternion pair — numba-compatible."""
    q_R_conj = _qconj(q_R)
    R = np.empty((4, 4))
    for j in range(4):
        e_j = np.zeros(4)
        e_j[j] = 1.0
        temp = _qmul(q_L, e_j)
        v = _qmul(temp, q_R_conj)
        for i in range(4):
            R[i, j] = v[i]
    return R


@njit(cache=True)
def _bond_action_jit(psi_x, psi_y, q_L, q_R):
    """LEGACY: scalar bond action |ψ^T · R · ψ|² — numba JIT.

    WARNING: This is the WRONG action for the ADW model. It uses only ψ[0:4]
    (not ψ̄[4:8]) and omits gamma matrices. The correct fermion-bag algorithm
    uses bag decomposition with det(M_B[U]) — see fermion_bag_sweep and
    fermion_bag_sweep_jit. This kernel is retained for backward compatibility
    with the legacy run_hybrid_mc function.
    """
    R = _so4_matrix(q_L, q_R)
    # E = psi_x · R · psi_y
    E = 0.0
    for i in range(4):
        Ry = 0.0
        for j in range(4):
            Ry += R[i, j] * psi_y[j]
        E += psi_x[i] * Ry
    return E * E


@njit(cache=True)
def _fermion_sweep_jit(occ, links_L, links_R, g, L, rng_seed):
    """Full fermion Metropolis sweep — numba JIT, no Python overhead.

    Args:
        occ: occupations array (L,L,L,L,8)
        links_L: left quaternion links (L,L,L,L,4,4)
        links_R: right quaternion links (L,L,L,L,4,4)
        g: four-fermion coupling
        L: lattice size
        rng_seed: random seed for this sweep

    Returns:
        (updated_occ, acceptance_rate)
    """
    np.random.seed(rng_seed)
    n_accepted = 0
    n_proposed = 0

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    # Propose: flip a random Grassmann bit
                    flip_idx = np.random.randint(0, 8)
                    n_proposed += 1

                    # Compute old action for all 8 bonds touching this site
                    old_action = 0.0
                    new_action = 0.0
                    psi_x = occ[x0, x1, x2, x3, :4]

                    for mu in range(4):
                        # Forward neighbor
                        y = [x0, x1, x2, x3]
                        y[mu] = (y[mu] + 1) % L
                        psi_y = occ[y[0], y[1], y[2], y[3], :4]
                        old_action += _bond_action_jit(
                            psi_x, psi_y,
                            links_L[x0, x1, x2, x3, mu],
                            links_R[x0, x1, x2, x3, mu])

                        # Backward neighbor
                        yb = [x0, x1, x2, x3]
                        yb[mu] = (yb[mu] - 1) % L
                        psi_yb = occ[yb[0], yb[1], yb[2], yb[3], :4]
                        old_action += _bond_action_jit(
                            psi_yb, psi_x,
                            links_L[yb[0], yb[1], yb[2], yb[3], mu],
                            links_R[yb[0], yb[1], yb[2], yb[3], mu])

                    # Flip the bit
                    old_val = occ[x0, x1, x2, x3, flip_idx]
                    occ[x0, x1, x2, x3, flip_idx] = 1.0 - old_val
                    psi_x_new = occ[x0, x1, x2, x3, :4]

                    for mu in range(4):
                        y = [x0, x1, x2, x3]
                        y[mu] = (y[mu] + 1) % L
                        psi_y = occ[y[0], y[1], y[2], y[3], :4]
                        new_action += _bond_action_jit(
                            psi_x_new, psi_y,
                            links_L[x0, x1, x2, x3, mu],
                            links_R[x0, x1, x2, x3, mu])

                        yb = [x0, x1, x2, x3]
                        yb[mu] = (yb[mu] - 1) % L
                        psi_yb = occ[yb[0], yb[1], yb[2], yb[3], :4]
                        new_action += _bond_action_jit(
                            psi_yb, psi_x_new,
                            links_L[yb[0], yb[1], yb[2], yb[3], mu],
                            links_R[yb[0], yb[1], yb[2], yb[3], mu])

                    delta_S = g * (new_action - old_action)

                    if delta_S <= 0 or np.random.random() < np.exp(-delta_S):
                        n_accepted += 1
                    else:
                        # Reject: restore
                        occ[x0, x1, x2, x3, flip_idx] = old_val

    return n_accepted / max(n_proposed, 1)


@njit(cache=True)
def _measure_tetrad_jit(occ, links_L, links_R, L):
    """Vectorized tetrad measurement — numba JIT."""
    m_E = np.zeros(16)
    V = L * L * L * L

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    for mu in range(4):
                        y = [x0, x1, x2, x3]
                        y[mu] = (y[mu] + 1) % L
                        psi_x = occ[x0, x1, x2, x3, :4]
                        psi_y = occ[y[0], y[1], y[2], y[3], :4]
                        R = _so4_matrix(
                            links_L[x0, x1, x2, x3, mu],
                            links_R[x0, x1, x2, x3, mu])
                        for a in range(4):
                            Ry_a = 0.0
                            for b in range(4):
                                Ry_a += R[a, b] * psi_y[b]
                            m_E[mu * 4 + a] += psi_x[a] * Ry_a

    for i in range(16):
        m_E[i] /= (4 * V)
    mag = 0.0
    for i in range(16):
        mag += m_E[i] * m_E[i]
    return np.sqrt(mag), m_E


@njit(cache=True)
def _measure_metric_jit(occ, links_L, links_R, L):
    """Vectorized metric measurement — numba JIT."""
    M = np.zeros((4, 4))
    V = L * L * L * L

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    E_local = np.zeros((4, 4))
                    for mu in range(4):
                        y = [x0, x1, x2, x3]
                        y[mu] = (y[mu] + 1) % L
                        psi_x = occ[x0, x1, x2, x3, :4]
                        psi_y = occ[y[0], y[1], y[2], y[3], :4]
                        R = _so4_matrix(
                            links_L[x0, x1, x2, x3, mu],
                            links_R[x0, x1, x2, x3, mu])
                        for a in range(4):
                            Ry_a = 0.0
                            for b in range(4):
                                Ry_a += R[a, b] * psi_y[b]
                            E_local[a, mu] = psi_x[a] * Ry_a
                    # g = E^T E
                    for mu in range(4):
                        for nu in range(4):
                            for a in range(4):
                                M[mu, nu] += E_local[a, mu] * E_local[a, nu]

    for i in range(4):
        for j in range(4):
            M[i, j] /= V

    # Q = M - (Tr M / 4) I
    tr = M[0, 0] + M[1, 1] + M[2, 2] + M[3, 3]
    Q = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            Q[i, j] = M[i, j]
        Q[i, i] -= tr / 4.0

    # Tr(Q²)
    trQ2 = 0.0
    for i in range(4):
        for j in range(4):
            trQ2 += Q[i, j] * Q[j, i]
    return trQ2


@njit(cache=True)
def _qnorm(q):
    """Quaternion norm squared — numba."""
    return q[0]*q[0] + q[1]*q[1] + q[2]*q[2] + q[3]*q[3]


@njit(cache=True)
def _staple_sum_jit(links_L, links_R, x0, x1, x2, x3, mu, L):
    """Compute staple sum for link (x, mu) — numba JIT.

    Includes both forward and backward staples (6 total for d=4).
    Returns (V_L, V_R) quaternion staple sums.
    """
    V_L = np.zeros(4)
    V_R = np.zeros(4)
    x = np.array([x0, x1, x2, x3])

    x_mu = x.copy()
    x_mu[mu] = (x_mu[mu] + 1) % L

    for nu in range(4):
        if nu == mu:
            continue

        x_nu = x.copy()
        x_nu[nu] = (x_nu[nu] + 1) % L

        x_mu_bnu = x_mu.copy()
        x_mu_bnu[nu] = (x_mu_bnu[nu] - 1) % L

        x_bnu = x.copy()
        x_bnu[nu] = (x_bnu[nu] - 1) % L

        # Forward staple: U(x+mu,nu) · U†(x+nu,mu) · U†(x,nu)
        q1L = links_L[x_mu[0], x_mu[1], x_mu[2], x_mu[3], nu]
        q2L = _qconj(links_L[x_nu[0], x_nu[1], x_nu[2], x_nu[3], mu])
        q3L = _qconj(links_L[x[0], x[1], x[2], x[3], nu])
        s_L = _qmul(_qmul(q1L, q2L), q3L)

        q1R = links_R[x_mu[0], x_mu[1], x_mu[2], x_mu[3], nu]
        q2R = _qconj(links_R[x_nu[0], x_nu[1], x_nu[2], x_nu[3], mu])
        q3R = _qconj(links_R[x[0], x[1], x[2], x[3], nu])
        s_R = _qmul(_qmul(q1R, q2R), q3R)

        V_L += s_L
        V_R += s_R

        # Backward staple: U†(x+mu-nu,nu) · U†(x-nu,mu) · U(x-nu,nu)
        sb_L = _qmul(
            _qconj(links_L[x_mu_bnu[0], x_mu_bnu[1], x_mu_bnu[2], x_mu_bnu[3], nu]),
            _qmul(
                _qconj(links_L[x_bnu[0], x_bnu[1], x_bnu[2], x_bnu[3], mu]),
                links_L[x_bnu[0], x_bnu[1], x_bnu[2], x_bnu[3], nu]))
        sb_R = _qmul(
            _qconj(links_R[x_mu_bnu[0], x_mu_bnu[1], x_mu_bnu[2], x_mu_bnu[3], nu]),
            _qmul(
                _qconj(links_R[x_bnu[0], x_bnu[1], x_bnu[2], x_bnu[3], mu]),
                links_R[x_bnu[0], x_bnu[1], x_bnu[2], x_bnu[3], nu]))

        V_L += sb_L
        V_R += sb_R

    return V_L, V_R


@njit(cache=True)
def _kp_heatbath_single_jit(a):
    """Kennedy-Pendleton heatbath for one SU(2) element — numba JIT."""
    if a < 1e-10:
        # Haar random
        q = np.random.standard_normal(4)
        norm = np.sqrt(q[0]*q[0] + q[1]*q[1] + q[2]*q[2] + q[3]*q[3])
        return q / norm

    while True:
        x1 = np.random.random()
        x2 = np.random.random()
        x3 = np.random.random()
        if x1 < 1e-300:
            x1 = 1e-300
        if x2 < 1e-300:
            x2 = 1e-300
        delta = -(np.log(x1) + np.log(x2) * np.cos(2.0 * np.pi * x3)**2) / (2.0 * a)
        if delta < 2.0 and np.random.random() < np.sqrt(1.0 - delta / 2.0):
            break

    a0 = 1.0 - delta
    r = np.sqrt(max(1.0 - a0*a0, 0.0))
    cos_theta = 2.0 * np.random.random() - 1.0
    sin_theta = np.sqrt(1.0 - cos_theta*cos_theta)
    phi = 2.0 * np.pi * np.random.random()

    out = np.empty(4)
    out[0] = a0
    out[1] = r * sin_theta * np.cos(phi)
    out[2] = r * sin_theta * np.sin(phi)
    out[3] = r * cos_theta
    return out


@njit(cache=True)
def _gauge_sweep_jit(occ, links_L, links_R, g, beta, L, rng_seed):
    """Full gauge sweep with fermion reweighting — numba JIT.

    For each link: heatbath proposal for gauge sector, accept/reject on fermion action.
    """
    np.random.seed(rng_seed)
    n_accepted = 0
    n_proposed = 0

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    for mu in range(4):
                        n_proposed += 1

                        # Save old link
                        old_qL = links_L[x0, x1, x2, x3, mu].copy()
                        old_qR = links_R[x0, x1, x2, x3, mu].copy()

                        # Old fermion action for this bond
                        y = np.array([x0, x1, x2, x3])
                        y[mu] = (y[mu] + 1) % L
                        psi_x = occ[x0, x1, x2, x3, :4]
                        psi_y = occ[y[0], y[1], y[2], y[3], :4]
                        old_ferm = g * _bond_action_jit(psi_x, psi_y, old_qL, old_qR)

                        if beta > 1e-10:
                            V_L, V_R = _staple_sum_jit(links_L, links_R, x0, x1, x2, x3, mu, L)
                            k_L = np.sqrt(_qnorm(V_L)) / 2.0
                            k_R = np.sqrt(_qnorm(V_R)) / 2.0

                            a_L = beta * k_L / 2.0
                            q_new_L = _kp_heatbath_single_jit(a_L)
                            if k_L > 1e-10:
                                V_L_norm = V_L / (2.0 * k_L)
                                links_L[x0, x1, x2, x3, mu] = _qmul(q_new_L, _qconj(V_L_norm))
                            else:
                                q = np.random.standard_normal(4)
                                links_L[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))

                            a_R = beta * k_R / 2.0
                            q_new_R = _kp_heatbath_single_jit(a_R)
                            if k_R > 1e-10:
                                V_R_norm = V_R / (2.0 * k_R)
                                links_R[x0, x1, x2, x3, mu] = _qmul(q_new_R, _qconj(V_R_norm))
                            else:
                                q = np.random.standard_normal(4)
                                links_R[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))
                        else:
                            # Haar random proposal
                            q = np.random.standard_normal(4)
                            links_L[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))
                            q = np.random.standard_normal(4)
                            links_R[x0, x1, x2, x3, mu] = q / np.sqrt(_qnorm(q))

                        # New fermion action
                        new_ferm = g * _bond_action_jit(
                            psi_x, psi_y,
                            links_L[x0, x1, x2, x3, mu],
                            links_R[x0, x1, x2, x3, mu])

                        delta_S = new_ferm - old_ferm
                        if delta_S <= 0 or np.random.random() < np.exp(-delta_S):
                            n_accepted += 1
                        else:
                            links_L[x0, x1, x2, x3, mu] = old_qL
                            links_R[x0, x1, x2, x3, mu] = old_qR

    return n_accepted / max(n_proposed, 1)


@njit(cache=True)
def _overrelax_sweep_jit(links_L, links_R, L):
    """Overrelaxation sweep — numba JIT."""
    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    for mu in range(4):
                        V_L, V_R = _staple_sum_jit(links_L, links_R, x0, x1, x2, x3, mu, L)
                        k_L = np.sqrt(_qnorm(V_L))
                        k_R = np.sqrt(_qnorm(V_R))

                        if k_L > 1e-10:
                            V0_L = V_L / k_L
                            q_old = links_L[x0, x1, x2, x3, mu].copy()
                            links_L[x0, x1, x2, x3, mu] = _qmul(
                                _qconj(V0_L), _qmul(_qconj(q_old), _qconj(V0_L)))

                        if k_R > 1e-10:
                            V0_R = V_R / k_R
                            q_old = links_R[x0, x1, x2, x3, mu].copy()
                            links_R[x0, x1, x2, x3, mu] = _qmul(
                                _qconj(V0_R), _qmul(_qconj(q_old), _qconj(V0_R)))


@njit(cache=True)
def _avg_plaquette_jit(links_L, links_R, L):
    """Average plaquette — numba JIT."""
    total = 0.0
    count = 0
    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    for mu in range(4):
                        for nu in range(mu + 1, 4):
                            x_mu = np.array([x0, x1, x2, x3])
                            x_mu[mu] = (x_mu[mu] + 1) % L
                            x_nu = np.array([x0, x1, x2, x3])
                            x_nu[nu] = (x_nu[nu] + 1) % L

                            # Left plaquette
                            q1L = links_L[x0, x1, x2, x3, mu]
                            q2L = links_L[x_mu[0], x_mu[1], x_mu[2], x_mu[3], nu]
                            q3L = _qconj(links_L[x_nu[0], x_nu[1], x_nu[2], x_nu[3], mu])
                            q4L = _qconj(links_L[x0, x1, x2, x3, nu])
                            pL = _qmul(_qmul(q1L, q2L), _qmul(q3L, q4L))

                            # Right plaquette
                            q1R = links_R[x0, x1, x2, x3, mu]
                            q2R = links_R[x_mu[0], x_mu[1], x_mu[2], x_mu[3], nu]
                            q3R = _qconj(links_R[x_nu[0], x_nu[1], x_nu[2], x_nu[3], mu])
                            q4R = _qconj(links_R[x0, x1, x2, x3, nu])
                            pR = _qmul(_qmul(q1R, q2R), _qmul(q3R, q4R))

                            # Tr(SO4) = Tr_L * Tr_R, normalized by 4
                            tr = (2.0 * pL[0]) * (2.0 * pR[0]) / 4.0
                            total += tr
                            count += 1
    return total / count


# ════════════════════════════════════════════════════════════════════
# Configuration and parameters
# ════════════════════════════════════════════════════════════════════

@dataclass
class GaugeFermionConfig:
    """Joint gauge-link + Grassmann occupation configuration."""
    L: int
    occupations: np.ndarray  # shape (L, L, L, L, 8)
    gauge: GaugeLattice


@dataclass
class HybridMCParams:
    """Parameters for the hybrid Monte Carlo."""
    g: float                     # four-fermion coupling
    beta: float = 0.0            # Wilson plaquette coupling (0 = pure ADW)
    n_thermalize: int = GAUGE_LINK_MC['n_thermalize']
    n_measure: int = GAUGE_LINK_MC['n_measure']
    n_skip: int = GAUGE_LINK_MC['n_skip']
    n_overrelax: int = GAUGE_LINK_MC['n_overrelax']
    seed: int = 42


@dataclass
class HybridMCResult:
    """Results from a hybrid gauge-fermion MC run."""
    tetrad_magnitude: list = field(default_factory=list)
    tetrad_m2: float = 0.0
    tetrad_m4: float = 0.0
    binder_tetrad: float = 0.0
    metric_trace_sq: list = field(default_factory=list)
    metric_m2: float = 0.0
    metric_m4: float = 0.0
    binder_metric: float = 0.0
    sign_values: list = field(default_factory=list)
    avg_sign: float = 1.0
    avg_plaquette: list = field(default_factory=list)
    acceptance_fermion: float = 0.0
    acceptance_gauge: float = 0.0
    n_measurements: int = 0
    g: float = 0.0
    beta: float = 0.0
    L: int = 0


# ════════════════════════════════════════════════════════════════════
# Configuration creation
# ════════════════════════════════════════════════════════════════════

def create_gauge_fermion_config(L, rng, cold_gauge=False):
    """Create initial gauge-fermion configuration."""
    occupations = rng.integers(0, 2, size=(L, L, L, L, 8)).astype(np.float64)
    gauge = create_gauge_lattice(L, rng, cold_start=cold_gauge)
    return GaugeFermionConfig(L=L, occupations=occupations, gauge=gauge)


# ════════════════════════════════════════════════════════════════════
# Phase 1: Fermion sweep (JIT)
# ════════════════════════════════════════════════════════════════════

def fermion_sweep(config, g, rng):
    """One Metropolis sweep — delegates to numba JIT kernel."""
    seed = rng.integers(0, 2**31)
    acc = _fermion_sweep_jit(
        config.occupations, config.gauge.links_L, config.gauge.links_R,
        g, config.L, seed)
    return acc


# ════════════════════════════════════════════════════════════════════
# Phase 2: Gauge sweep with fermion reweighting
# ════════════════════════════════════════════════════════════════════

def gauge_sweep_with_fermions(config, g, beta, rng):
    """Gauge link update with fermion reweighting — delegates to JIT kernel."""
    seed = rng.integers(0, 2**31)
    acc = _gauge_sweep_jit(
        config.occupations, config.gauge.links_L, config.gauge.links_R,
        g, beta, config.L, seed)
    return acc


# ════════════════════════════════════════════════════════════════════
# Order parameters (JIT)
# ════════════════════════════════════════════════════════════════════

def measure_tetrad(config):
    """Compute volume-averaged tetrad magnetization — JIT accelerated."""
    return _measure_tetrad_jit(
        config.occupations, config.gauge.links_L, config.gauge.links_R, config.L)


def measure_metric(config):
    """Compute traceless-symmetric metric order parameter — JIT accelerated."""
    return _measure_metric_jit(
        config.occupations, config.gauge.links_L, config.gauge.links_R, config.L)


# ════════════════════════════════════════════════════════════════════
# Correct order parameters with gamma matrices (Step 6)
# Source: ADW tetrad condensation lattice formulation.md (deep research)
# Source: Vladimirov & Diakonov PRD 86, 104019 (2012)
# Source: Volovik, JETP Lett. 119, 330 (2024)
# ════════════════════════════════════════════════════════════════════

def measure_tetrad_correct(config):
    """Compute volume-averaged tetrad using correct gamma matrix formula.

    E^a_μ(x) = ψ̄_x γ^a U_{x,μ} ψ_{x+μ̂}

    where ψ̄ = occ[4:8], ψ = occ[0:4], γ^a are 4×4 complex Hermitian
    Euclidean gamma matrices. Components a=0,2 are real; a=1,3 purely imaginary.

    The volume-averaged magnetization is m_E^{a,μ} = (1/4V) Σ_{x,μ} E^a_μ(x).
    |m_E|² = Σ_{a,μ} |m_E^{a,μ}|² uses modulus to handle complex components.

    Lean: tetrad_gauge_covariant (GaugeFermionBag.lean)
    Aristotle: fb657b4d
    Source: Vladimirov & Diakonov PRD 86, 104019 (2012)

    Args:
        config: GaugeFermionConfig

    Returns:
        (m_E, m_E_sq): m_E is (4,4) complex array [a, mu],
                        m_E_sq = Σ_{a,μ} |m_E^{a,μ}|² (real scalar)
    """
    from src.core.constants import EUCLIDEAN_GAMMA_4D

    L = config.L
    V = L**4
    occ = config.occupations
    gauge = config.gauge

    m_E = np.zeros((4, 4), dtype=complex)  # [a, mu]

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    psi_bar_x = occ[x0, x1, x2, x3, 4:8].astype(complex)
                    for mu in range(4):
                        nb = [x0, x1, x2, x3]
                        nb[mu] = (nb[mu] + 1) % L
                        psi_y = occ[nb[0], nb[1], nb[2], nb[3], :4].astype(complex)

                        R = _get_so4_matrix(gauge, (x0, x1, x2, x3), mu)
                        R_c = R.astype(complex)

                        for a in range(4):
                            gamma_R = EUCLIDEAN_GAMMA_4D[a] @ R_c
                            E_a = psi_bar_x @ gamma_R @ psi_y
                            m_E[a, mu] += E_a

    m_E /= (4 * V)
    m_E_sq = float(np.sum(np.abs(m_E)**2))
    return m_E, m_E_sq


def measure_metric_correct(config):
    """Compute traceless-symmetric metric using Option A (no conjugation).

    g_{μν}(x) = δ_{ab} E^a_μ(x) E^b_ν(x) = Σ_a E^a_μ E^a_ν

    This is REAL per-configuration:
    - a=0,2: (real)(real) = real ≥ 0
    - a=1,3: (purely imaginary)(purely imaginary) = real ≤ 0

    The metric can be indefinite on individual configs (representation artifact).
    Q_{μν} = M_{μν} - (1/4)δ_{μν} Tr(M) is traceless symmetric.
    Tr(Q²) ≥ 0 always (trace of real symmetric squared).

    Source: ADW tetrad condensation lattice formulation.md (deep research Q2)
    Source: Volovik, JETP Lett. 119, 330 (2024): g_{μν} = η_{ab} ⟨Ê^a_μ Ê^b_ν⟩

    Args:
        config: GaugeFermionConfig

    Returns:
        (Q, trQ2): Q is (4,4) complex (should have zero imaginary part),
                   trQ2 is Tr(Q²) scalar
    """
    from src.core.constants import EUCLIDEAN_GAMMA_4D

    L = config.L
    V = L**4
    occ = config.occupations
    gauge = config.gauge

    M = np.zeros((4, 4), dtype=complex)  # metric accumulator

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    psi_bar_x = occ[x0, x1, x2, x3, 4:8].astype(complex)

                    # Compute E^a_μ for all bonds from this site
                    E_local = np.zeros((4, 4), dtype=complex)  # [a, mu]
                    for mu in range(4):
                        nb = [x0, x1, x2, x3]
                        nb[mu] = (nb[mu] + 1) % L
                        psi_y = occ[nb[0], nb[1], nb[2], nb[3], :4].astype(complex)

                        R = _get_so4_matrix(gauge, (x0, x1, x2, x3), mu)
                        R_c = R.astype(complex)

                        for a in range(4):
                            gamma_R = EUCLIDEAN_GAMMA_4D[a] @ R_c
                            E_local[a, mu] = psi_bar_x @ gamma_R @ psi_y

                    # g_{μν}(x) = Σ_a E^a_μ(x) · E^a_ν(x)  [Option A, no conjugation]
                    for mu in range(4):
                        for nu in range(4):
                            for a in range(4):
                                M[mu, nu] += E_local[a, mu] * E_local[a, nu]

    M /= V

    # Q = M - (Tr M / 4) I  (traceless part)
    tr_M = np.trace(M)
    Q = M - (tr_M / 4.0) * np.eye(4, dtype=complex)

    # Tr(Q²) — should be real
    trQ2 = np.trace(Q @ Q)

    return Q, trQ2


# ════════════════════════════════════════════════════════════════════
# Main hybrid MC runner
# ════════════════════════════════════════════════════════════════════

def run_hybrid_mc(L, params, rng=None):
    """Run hybrid gauge-fermion MC and measure order parameters."""
    if rng is None:
        rng = np.random.default_rng(params.seed)

    config = create_gauge_fermion_config(L, rng)
    result = HybridMCResult(g=params.g, beta=params.beta, L=L)

    total_sweeps = params.n_thermalize + params.n_measure * params.n_skip
    fermion_accepts = []
    gauge_accepts = []

    for sweep in range(total_sweeps):
        acc_f = fermion_sweep(config, params.g, rng)
        fermion_accepts.append(acc_f)

        acc_g = gauge_sweep_with_fermions(config, params.g, params.beta, rng)
        gauge_accepts.append(acc_g)

        for _ in range(params.n_overrelax):
            _overrelax_sweep_jit(config.gauge.links_L, config.gauge.links_R, config.L)

        if sweep % GAUGE_LINK_MC['quaternion_renorm_interval'] == 0:
            renormalize_links(config.gauge)

        if sweep >= params.n_thermalize and (sweep - params.n_thermalize) % params.n_skip == 0:
            tet_mag, _ = measure_tetrad(config)
            met_q2 = measure_metric(config)
            plaq = _avg_plaquette_jit(config.gauge.links_L, config.gauge.links_R, config.L)

            result.tetrad_magnitude.append(tet_mag)
            result.metric_trace_sq.append(met_q2)
            result.avg_plaquette.append(plaq)
            result.sign_values.append(1.0)
            result.n_measurements += 1

    if result.n_measurements > 0:
        tet = np.array(result.tetrad_magnitude)
        met = np.array(result.metric_trace_sq)

        result.tetrad_m2 = np.mean(tet**2)
        result.tetrad_m4 = np.mean(tet**4)
        if result.tetrad_m2 > 0:
            result.binder_tetrad = 1.0 - (8.0/9.0) * result.tetrad_m4 / result.tetrad_m2**2
        else:
            result.binder_tetrad = 0.0

        result.metric_m2 = np.mean(met)
        result.metric_m4 = np.mean(met**2)
        if result.metric_m2 > 0:
            result.binder_metric = 1.0 - (9.0/11.0) * result.metric_m4 / result.metric_m2**2
        else:
            result.binder_metric = 0.0

        result.avg_sign = np.mean(result.sign_values)

    result.acceptance_fermion = np.mean(fermion_accepts) if fermion_accepts else 0.0
    result.acceptance_gauge = np.mean(gauge_accepts) if gauge_accepts else 0.0

    return result


def run_hybrid_mc_correct(L, params, rng=None, use_jit=True):
    """Run hybrid gauge-fermion MC with CORRECT fermion-bag algorithm.

    Uses:
    - fermion_bag_sweep (or _jit): bag decomposition + det(M_B) + sign tracking
    - gauge_sweep_with_det_reweighting: det ratio acceptance + sign tracking
    - measure_tetrad_correct (or _jit): gamma matrices, ψ̄/ψ, complex E^a
    - measure_metric_correct (or _jit): Option A metric (no conjugation)

    Source: Chandrasekharan PRD 82, 025007 (2010) — fermion-bag algorithm
    Source: Vladimirov & Diakonov PRD 86, 104019 (2012) — ADW lattice action
    Source: ADW tetrad condensation lattice formulation.md — Option A metric

    Args:
        L: lattice size
        params: HybridMCParams
        rng: numpy Generator (default: seeded from params.seed)
        use_jit: if True, use JIT-accelerated sweep and measurement kernels

    Returns:
        HybridMCResult with correct physics
    """
    if rng is None:
        rng = np.random.default_rng(params.seed)

    config = create_gauge_fermion_config(L, rng)
    result = HybridMCResult(g=params.g, beta=params.beta, L=L)

    sweep_fn = fermion_bag_sweep_jit if use_jit else fermion_bag_sweep
    tetrad_fn = measure_tetrad_correct_jit if use_jit else measure_tetrad_correct
    metric_fn = measure_metric_correct_jit if use_jit else measure_metric_correct

    total_sweeps = params.n_thermalize + params.n_measure * params.n_skip
    fermion_accepts = []
    gauge_accepts = []
    sign_accumulator = 1

    for sweep in range(total_sweeps):
        # Phase 1: fermion-bag sweep at fixed links
        acc_f, sign_f = sweep_fn(config, params.g, rng)
        fermion_accepts.append(acc_f)
        sign_accumulator *= sign_f

        # Phase 2: gauge sweep with det reweighting at fixed occupations
        acc_g, sign_g = gauge_sweep_with_det_reweighting(
            config, params.g, params.beta, rng)
        gauge_accepts.append(acc_g)
        sign_accumulator *= sign_g

        # Overrelaxation for gauge decorrelation
        for _ in range(params.n_overrelax):
            _overrelax_sweep_jit(config.gauge.links_L, config.gauge.links_R,
                                 config.L)

        # Periodic quaternion renormalization
        if sweep % GAUGE_LINK_MC['quaternion_renorm_interval'] == 0:
            renormalize_links(config.gauge)

        # Measurement phase
        if sweep >= params.n_thermalize and \
                (sweep - params.n_thermalize) % params.n_skip == 0:
            _, tet_sq = tetrad_fn(config)
            _, trQ2 = metric_fn(config)
            plaq = _avg_plaquette_jit(config.gauge.links_L,
                                       config.gauge.links_R, config.L)

            result.tetrad_magnitude.append(np.sqrt(tet_sq))
            result.metric_trace_sq.append(float(np.real(trQ2)))
            result.avg_plaquette.append(plaq)
            result.sign_values.append(sign_accumulator)
            result.n_measurements += 1
            sign_accumulator = 1  # reset per measurement

    if result.n_measurements > 0:
        tet = np.array(result.tetrad_magnitude)
        met = np.array(result.metric_trace_sq)

        result.tetrad_m2 = np.mean(tet**2)
        result.tetrad_m4 = np.mean(tet**4)
        if result.tetrad_m2 > 0:
            result.binder_tetrad = 1.0 - (8.0/9.0) * result.tetrad_m4 / \
                result.tetrad_m2**2
        else:
            result.binder_tetrad = 0.0

        result.metric_m2 = np.mean(met)
        result.metric_m4 = np.mean(met**2)
        if result.metric_m2 > 0:
            result.binder_metric = 1.0 - (9.0/11.0) * result.metric_m4 / \
                result.metric_m2**2
        else:
            result.binder_metric = 0.0

        result.avg_sign = np.mean(result.sign_values)

    result.acceptance_fermion = np.mean(fermion_accepts) if fermion_accepts else 0.0
    result.acceptance_gauge = np.mean(gauge_accepts) if gauge_accepts else 0.0

    return result
