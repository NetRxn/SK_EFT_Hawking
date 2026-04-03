//! Matrix-free HS+RHMC for ADW tetrad condensation.
//!
//! The entire RHMC hot path in Rust: matrix-free fermion matrix apply,
//! batched multi-shift CG, force computation, FSAL Omelyan integrator,
//! pseudofermion heat bath, Hamiltonian, and Metropolis accept/reject.
//!
//! The fermion matrix A[h] is NEVER stored — A@v is computed on-the-fly
//! from the h-field using a nearest-neighbor stencil with the 32 nonzero
//! entries of CG[a] = J₁ @ Γ^a (all ±1, no floating-point multiply needed).
//!
//! Lean: HubbardStratonovichRHMC.lean (20 theorems, zero sorry)
//! Source: "HS+RHMC for ADW tetrad condensation..." (deep research)

use numpy::{PyArray1, PyReadonlyArray1, PyReadonlyArray3};
use pyo3::prelude::*;
use rand::Rng;
use rand_chacha::ChaCha20Rng;
use rand::SeedableRng;

// ═══════════════════════════════════════════════════════════════════
// CG[a] = J₁ @ Γ^a — charge conjugation bilinear matrices
//
// 4 matrices × 8×8, but only 32 nonzero entries (all ±1).
// Stored as (channel_a, row_I, col_J, sign) for the stencil.
//
// Lean: kramers_holds_hs_matrix (HubbardStratonovichRHMC.lean)
// Source: Wei et al., PRL 116, 250601 (2016)
// ═══════════════════════════════════════════════════════════════════

/// CG stencil entry: (channel_a, row_I, col_J, value).
/// Computed at Python init from constants.py: CG[a] = MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a].
/// Pipeline invariant: constants.py is canonical for all physics constants.
/// These are passed from Python at runtime — never hardcoded.
struct CgEntry {
    a: usize,
    i: usize,
    j: usize,
    val: f64,
}

/// Parse CG entries from flat numpy arrays passed by Python.
/// Input: cg_a, cg_i, cg_j, cg_val — each length nnz.
fn parse_cg_entries(cg_a: &[i64], cg_i: &[i64], cg_j: &[i64], cg_val: &[f64]) -> Vec<CgEntry> {
    cg_a.iter().zip(cg_i.iter()).zip(cg_j.iter()).zip(cg_val.iter())
        .map(|(((a, i), j), v)| CgEntry { a: *a as usize, i: *i as usize, j: *j as usize, val: *v })
        .collect()
}

// ═══════════════════════════════════════════════════════════════════
// Lattice neighbor table
// ═══════════════════════════════════════════════════════════════════

/// Build neighbor tables for L^4 periodic lattice.
/// fwd[site][mu] = flat index of site + e_mu (forward neighbor).
/// bwd[site][mu] = flat index of site - e_mu (backward neighbor).
fn build_neighbors(l: usize) -> (Vec<[usize; 4]>, Vec<[usize; 4]>) {
    let v = l * l * l * l;
    let mut fwd = vec![[0usize; 4]; v];
    let mut bwd = vec![[0usize; 4]; v];
    for site in 0..v {
        let x0 = site / (l * l * l);
        let x1 = (site / (l * l)) % l;
        let x2 = (site / l) % l;
        let x3 = site % l;
        fwd[site][0] = ((x0 + 1) % l) * l * l * l + x1 * l * l + x2 * l + x3;
        fwd[site][1] = x0 * l * l * l + ((x1 + 1) % l) * l * l + x2 * l + x3;
        fwd[site][2] = x0 * l * l * l + x1 * l * l + ((x2 + 1) % l) * l + x3;
        fwd[site][3] = x0 * l * l * l + x1 * l * l + x2 * l + (x3 + 1) % l;
        bwd[site][0] = ((x0 + l - 1) % l) * l * l * l + x1 * l * l + x2 * l + x3;
        bwd[site][1] = x0 * l * l * l + ((x1 + l - 1) % l) * l * l + x2 * l + x3;
        bwd[site][2] = x0 * l * l * l + x1 * l * l + ((x2 + l - 1) % l) * l + x3;
        bwd[site][3] = x0 * l * l * l + x1 * l * l + x2 * l + (x3 + l - 1) % l;
    }
    (fwd, bwd)
}

// ═══════════════════════════════════════════════════════════════════
// Matrix-free A[h] @ v — the core stencil
//
// A_{(x,I),(y,J)} = Σ_{μ,a} h^a_{x,μ} · CG[a]_{IJ} · δ_{y,x+μ̂} − (transpose)
//
// NEVER stores the matrix. Computes the product on-the-fly from h.
// Cost: O(V × 4 directions × 32 nnz) = O(128V) FLOPs per matvec.
// Memory: reads h (16V floats) + v (8V floats), writes out (8V floats).
//
// Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
// Source: "HS+RHMC for ADW tetrad condensation..." Section 1
// ═══════════════════════════════════════════════════════════════════

/// Apply A[h] @ v matrix-free, single-pass scatter stencil.
///
/// For each bond (site, μ), reads h[site,μ,a] once and computes both:
///   forward:  out[site,I] += CG_{IJ} · h · v[nb,J]    (gather into site)
///   backward: out[nb,J]   -= CG_{IJ} · h · v[site,I]  (scatter to nb, antisymmetric)
///
/// Half the memory accesses of a two-pass gather-only approach.
/// Not thread-safe (scatter writes to neighbor output), but production uses
/// 14 independent single-threaded workers — embarrassingly parallel across
/// coupling points is more efficient than within-stencil threading.
///
/// Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
fn apply_fermion_matrix(
    h: &[f64], v: &[f64], out: &mut [f64],
    fwd: &[[usize; 4]], _bwd: &[[usize; 4]],
    n_sites: usize, cg_entries: &[CgEntry], _n_threads: usize,
) {
    for x in out.iter_mut() { *x = 0.0; }

    for site in 0..n_sites {
        for mu in 0..4usize {
            let nb = fwd[site][mu];
            for entry in cg_entries {
                let h_val = h[site * 16 + mu * 4 + entry.a];
                if h_val == 0.0 { continue; }
                let c = entry.val * h_val;
                out[8 * site + entry.i] += c * v[8 * nb + entry.j];
                out[8 * nb + entry.j] -= c * v[8 * site + entry.i];
            }
        }
    }
}

/// Apply (A†A + σI) @ v = (-A² + σI) @ v using two matrix-free applications.
/// A†A = -A² because A is real antisymmetric (A^T = -A → A^T A = -A²).
fn apply_shifted_ata(
    h: &[f64], v: &[f64], out: &mut [f64],
    sigma: f64, fwd: &[[usize; 4]], bwd: &[[usize; 4]], n_sites: usize,
    scratch: &mut [f64], cg_entries: &[CgEntry], n_threads: usize,
) {
    let dim = 8 * n_sites;
    // scratch = A @ v
    apply_fermion_matrix(h, v, scratch, fwd, bwd, n_sites, cg_entries, n_threads);
    // out = A @ scratch = A² @ v
    apply_fermion_matrix(h, scratch, out, fwd, bwd, n_sites, cg_entries, n_threads);
    // out = -A² @ v + σ v = A†A @ v + σ v
    for i in 0..dim {
        out[i] = -out[i] + sigma * v[i];
    }
}

// ═══════════════════════════════════════════════════════════════════
// Lanczos spectral range estimation — matrix-free
//
// Estimates λ_min and λ_max of A†A using n_iter Lanczos iterations.
// Works at ANY lattice size since it only uses matrix-free matvec.
// Cost: n_iter × 2 stencil applications (same as 1 CG iteration).
//
// Source: Golub & Van Loan, "Matrix Computations," Chapter 10
// ═══════════════════════════════════════════════════════════════════

/// Estimate (λ_min, λ_max) of A†A via Lanczos. Returns with safety margins.
fn estimate_spectral_range(
    h: &[f64], fwd: &[[usize; 4]], bwd: &[[usize; 4]], n_sites: usize,
    cg_entries: &[CgEntry], n_iter: usize, rng: &mut ChaCha20Rng, n_threads: usize,
) -> (f64, f64) {
    let dim = 8 * n_sites;
    let mut scratch = vec![0.0; dim];
    let mut ata_v = vec![0.0; dim];

    // Random starting vector, normalized
    let mut q: Vec<f64> = (0..dim).map(|_| rand_normal(rng)).collect();
    let norm = dot(&q, &q).sqrt();
    for x in q.iter_mut() { *x /= norm; }

    let mut alphas_lanczos = Vec::with_capacity(n_iter);
    let mut betas_lanczos = Vec::with_capacity(n_iter);
    let mut q_prev = vec![0.0; dim];
    let mut beta_prev = 0.0;

    for _ in 0..n_iter {
        // w = A†A @ q (matrix-free: two stencil applications)
        apply_fermion_matrix(h, &q, &mut scratch, fwd, bwd, n_sites, cg_entries, n_threads);
        apply_fermion_matrix(h, &scratch, &mut ata_v, fwd, bwd, n_sites, cg_entries, n_threads);
        // A†A = -A² for real antisymmetric
        for i in 0..dim { ata_v[i] = -ata_v[i]; }

        let alpha = dot(&q, &ata_v);
        alphas_lanczos.push(alpha);

        // w = w - alpha * q - beta_prev * q_prev
        for i in 0..dim {
            ata_v[i] -= alpha * q[i] + beta_prev * q_prev[i];
        }

        let beta = dot(&ata_v, &ata_v).sqrt();
        if beta < 1e-14 { break; }
        betas_lanczos.push(beta);

        // Prepare next iteration
        q_prev.copy_from_slice(&q);
        for i in 0..dim { q[i] = ata_v[i] / beta; }
        beta_prev = beta;
    }

    // Compute eigenvalues of the Lanczos tridiagonal matrix T.
    // T is n×n with diagonal α and sub/super-diagonal β.
    // At n~30, we use QR iteration (simple, exact for this size).
    let n = alphas_lanczos.len();
    if n == 0 { return (0.1, 100.0); }
    if n == 1 { return ((alphas_lanczos[0] * 0.8).max(1e-6), alphas_lanczos[0] * 1.2); }

    // Eigenvalues of tridiagonal via Sturm bisection (n ≤ 30, instant)
    let eigs = tridiag_eigenvalues(&alphas_lanczos, &betas_lanczos);

    let lam_min_est = eigs.iter().cloned().fold(f64::INFINITY, f64::min);
    let lam_max_est = eigs.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

    // Safety margins + ensure positive (A†A is PSD, eigenvalues ≥ 0)
    let lam_min = (lam_min_est * 0.8).max(1e-6);
    let lam_max = lam_max_est * 1.2;

    (lam_min, lam_max)
}

/// Eigenvalues of symmetric tridiagonal matrix.
/// Uses Sturm bisection — simple, robust, exact for n ≤ 30.
fn tridiag_eigenvalues(alpha: &[f64], beta: &[f64]) -> Vec<f64> {
    bisection_eigenvalues(alpha, beta)
}

/// Bisection method for ALL eigenvalues of symmetric tridiagonal matrix.
/// Uses Sturm sequence to count eigenvalues below a threshold.
fn bisection_eigenvalues(alpha: &[f64], beta: &[f64]) -> Vec<f64> {
    let n = alpha.len();
    if n == 1 { return vec![alpha[0]]; }

    // Gershgorin bounds for initial interval
    let mut lo = alpha[0] - beta.first().map_or(0.0, |b| b.abs());
    let mut hi = alpha[0] + beta.first().map_or(0.0, |b| b.abs());
    for i in 0..n {
        let b_left = if i > 0 { beta[i-1].abs() } else { 0.0 };
        let b_right = if i < beta.len() { beta[i].abs() } else { 0.0 };
        lo = lo.min(alpha[i] - b_left - b_right);
        hi = hi.max(alpha[i] + b_left + b_right);
    }
    lo -= 1.0; hi += 1.0;

    /// Count eigenvalues < x using Sturm sequence
    fn sturm_count(alpha: &[f64], beta: &[f64], x: f64) -> usize {
        let n = alpha.len();
        let mut count = 0;
        let mut d = alpha[0] - x;
        if d < 0.0 { count += 1; }
        for i in 1..n {
            let b2 = beta[i-1] * beta[i-1];
            d = alpha[i] - x - if d.abs() > 1e-30 { b2 / d } else { b2 / 1e-30 };
            if d < 0.0 { count += 1; }
        }
        count
    }

    // Find each eigenvalue by bisection
    let mut eigs = Vec::with_capacity(n);
    for k in 0..n {
        let mut a = lo;
        let mut b = hi;
        // Find interval containing k-th eigenvalue
        for _ in 0..100 {
            let mid = (a + b) / 2.0;
            if sturm_count(alpha, beta, mid) <= k {
                a = mid;
            } else {
                b = mid;
            }
            if b - a < 1e-12 * hi.abs().max(1.0) { break; }
        }
        eigs.push((a + b) / 2.0);
    }
    eigs
}

// ═══════════════════════════════════════════════════════════════════
// Multi-shift CG solver (shared Krylov space)
//
// Solves (A†A + σ_k) ψ_k = φ for k = 0..K-1 simultaneously.
// All K shifts share ONE Krylov space — only ONE matvec per iteration.
// Shifted systems maintained via the ζ recurrence (Jegerlehner 1996).
// Total matvecs: 2 × n_iter (one A@v for A†A = -A², independent of K).
//
// σ₀ (smallest shift) is the base system; larger shifts converge faster.
// f64 ζ recurrence is stable for σ_max/σ_min ~ 10⁶ over ~200 iterations.
//
// Lean: multishift_krylov_shift_invariance, multishift_residual_collinearity
//       (HubbardStratonovichRHMC.lean)
// Source: Jegerlehner, hep-lat/9612014 (1996); Frommer, Computing 70 (2003)
// ═══════════════════════════════════════════════════════════════════

/// Result of multi-shift CG solve.
struct CgResult {
    solutions: Vec<Vec<f64>>,  // one per shift (in original shift order)
    n_iter: usize,
}

/// Multi-shift CG: all shifts share one matvec per iteration via ζ recurrence.
///
/// Shifts are internally sorted ascending (smallest = base = hardest).
/// Solutions are returned in the ORIGINAL shift order.
fn multishift_cg(
    h: &[f64],
    phi: &[f64],
    shifts: &[f64],
    tol: f64,
    max_iter: usize,
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    cg_entries: &[CgEntry],
    n_threads: usize,
) -> CgResult {
    let dim = 8 * n_sites;
    let ns = shifts.len();

    if ns == 0 {
        return CgResult { solutions: vec![], n_iter: 0 };
    }

    // Sort shifts ascending; σ₀ (smallest) is the base system
    let mut order: Vec<usize> = (0..ns).collect();
    order.sort_by(|&a, &b| shifts[a].partial_cmp(&shifts[b]).unwrap());
    let sorted_shifts: Vec<f64> = order.iter().map(|&i| shifts[i]).collect();
    let sigma0 = sorted_shifts[0];

    // Per-shift state: solution x_k, search direction p_k
    let mut x: Vec<Vec<f64>> = vec![vec![0.0; dim]; ns];
    let mut p: Vec<Vec<f64>> = vec![phi.to_vec(); ns];

    // Shared residual (base system)
    let mut r = phi.to_vec();
    let b_norm_sq = dot(phi, phi);
    if b_norm_sq < 1e-30 {
        return CgResult { solutions: x, n_iter: 0 };
    }
    let tol_sq = tol * tol * b_norm_sq;
    let mut r_sq = b_norm_sq;

    // ζ recurrence state (one per shift)
    let mut zeta_cur = vec![1.0_f64; ns];
    let mut zeta_old = vec![1.0_f64; ns];
    let mut converged = vec![false; ns];

    // CG scalars for recurrence history
    // CRITICAL: ζ recurrence uses α^{n-1} and β^{n-1} (previous iteration),
    // not the current iteration's values. Off-by-one here corrupts all shifts.
    let mut alpha = 0.0_f64;
    let mut alpha_old = 1.0_f64;
    let mut beta = 0.0_f64;
    let mut beta_old = 0.0_f64;

    // Scratch buffers for matvec (reused across iterations)
    let mut scratch = vec![0.0; dim];
    let mut w = vec![0.0; dim];  // (A†A + σ₀) @ p₀

    let mut n_iter = 0;
    while n_iter < max_iter {
        // Check if all converged
        if converged.iter().all(|&c| c) { break; }

        // ═══ SINGLE MATVEC: w = (A†A + σ₀) @ p₀ ═══
        apply_shifted_ata(h, &p[0], &mut w, sigma0, fwd, bwd, n_sites, &mut scratch, cg_entries, n_threads);

        let pap = dot(&p[0], &w);
        if pap.abs() < 1e-30 { break; }
        alpha = r_sq / pap;

        let r_sq_old = r_sq;

        // Update base system residual: r -= α·w
        axpy(-alpha, &w, &mut r);
        r_sq = dot(&r, &r);

        // Base system: update solution and search direction
        axpy(alpha, &p[0], &mut x[0]);
        beta = r_sq / r_sq_old.max(1e-30);

        // p₀ = r + β·p₀
        for i in 0..dim {
            p[0][i] = r[i] + beta * p[0][i];
        }

        // Check base convergence
        if r_sq < tol_sq { converged[0] = true; }

        // ═══ UPDATE SHIFTED SYSTEMS via ζ recurrence (cheap vector ops) ═══
        for k in 1..ns {
            if converged[k] { continue; }

            // ζ recurrence (Jegerlehner 1996, Eq. 3.7)
            // CRITICAL: uses β^{n-1} (beta_old), NOT β^n (beta)
            let denom = alpha_old * zeta_old[k]
                * (1.0 + alpha * (sorted_shifts[k] - sigma0))
                + beta_old * alpha * (zeta_old[k] - zeta_cur[k]);

            if denom.abs() < 1e-30 {
                converged[k] = true;
                continue;
            }

            let zeta_new = (zeta_cur[k] * zeta_old[k] * alpha_old) / denom;
            let alpha_k = alpha * zeta_new / zeta_cur[k];
            let beta_k = (zeta_new / zeta_cur[k]).powi(2) * beta;

            // Update shifted solution: x_k += α_k·p_k
            axpy(alpha_k, &p[k], &mut x[k]);

            // Update shifted search direction: p_k = ζ_new·r + β_k·p_k
            for i in 0..dim {
                p[k][i] = zeta_new * r[i] + beta_k * p[k][i];
            }

            // Check shifted convergence: ||r_k||² = |ζ_k|²·||r||²
            if zeta_new * zeta_new * r_sq < tol_sq {
                converged[k] = true;
            }

            zeta_old[k] = zeta_cur[k];
            zeta_cur[k] = zeta_new;
        }

        alpha_old = alpha;
        beta_old = beta;
        n_iter += 1;
    }

    // Unsort: return solutions in original shift order
    let mut result = vec![vec![0.0; dim]; ns];
    for (sorted_idx, &orig_idx) in order.iter().enumerate() {
        std::mem::swap(&mut result[orig_idx], &mut x[sorted_idx]);
    }

    CgResult { solutions: result, n_iter }
}

// ═══════════════════════════════════════════════════════════════════
// Vector operations (will auto-vectorize to NEON)
// ═══════════════════════════════════════════════════════════════════

#[inline]
fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b.iter()).map(|(x, y)| x * y).sum()
}

#[inline]
fn axpy(alpha: f64, x: &[f64], y: &mut [f64]) {
    for (yi, xi) in y.iter_mut().zip(x.iter()) {
        *yi += alpha * *xi;
    }
}

// ═══════════════════════════════════════════════════════════════════
// Force computation
//
// F_h[site, mu, a] = -h/(2g) + Σ_k α_k · (force contraction from ψ_k)
//
// The pseudofermion force involves ψ_k and A@ψ_k, contracted with the
// CG stencil at each site. Matrix-free: A@ψ_k computed on-the-fly.
//
// Lean: rhmc_hamiltonian_conserved (HubbardStratonovichRHMC.lean)
// Source: "HS+RHMC for ADW tetrad condensation..." Section 3
// ═══════════════════════════════════════════════════════════════════

/// Pseudofermion force contribution from ONE real field (no Gaussian prior).
fn compute_pf_force(
    h: &[f64],
    phi: &[f64],
    zolotarev_alphas: &[f64],
    zolotarev_betas: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    cg_tol: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
    n_threads: usize,
    f_h: &mut [f64],
) {
    let dim = 8 * n_sites;
    let n_poles = zolotarev_betas.len();

    let cg_result = multishift_cg(h, phi, zolotarev_betas, cg_tol, cg_max_iter,
                                fwd, bwd, n_sites, cg_entries, n_threads);

    let mut a_psi: Vec<Vec<f64>> = Vec::with_capacity(n_poles);
    for k in 0..n_poles {
        let mut ap = vec![0.0; dim];
        apply_fermion_matrix(h, &cg_result.solutions[k], &mut ap, fwd, bwd, n_sites, cg_entries, n_threads);
        a_psi.push(ap);
    }

    for site in 0..n_sites {
        for mu in 0..4usize {
            let nb = fwd[site][mu];
            for a in 0..4usize {
                let mut force_val: f64 = 0.0;
                for k in 0..n_poles {
                    let psi = &cg_result.solutions[k];
                    let apsi = &a_psi[k];
                    let mut contraction: f64 = 0.0;
                    for entry in cg_entries {
                        if entry.a != a { continue; }
                        let psi_i = psi[8 * site + entry.i];
                        let apsi_j = apsi[8 * nb + entry.j];
                        let apsi_i = apsi[8 * site + entry.i];
                        let psi_j = psi[8 * nb + entry.j];
                        contraction += entry.val * (psi_i * apsi_j - apsi_i * psi_j);
                    }
                    force_val += zolotarev_alphas[k] * (-2.0) * contraction;
                }
                f_h[site * 16 + mu * 4 + a] += force_val;
            }
        }
    }
}

/// Full force: Gaussian prior + pseudofermion forces from both complex components.
fn compute_forces(
    h: &[f64],
    g: f64,
    phi_r: &[f64],
    phi_i: &[f64],
    zolotarev_alphas: &[f64],
    zolotarev_betas: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    cg_tol: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
    n_threads: usize,
) -> Vec<f64> {
    let mut f_h = vec![0.0; n_sites * 16];

    // Gaussian prior: F = -h / (2g) — applied once
    for i in 0..n_sites * 16 {
        f_h[i] = -h[i] / (2.0 * g);
    }

    // PF force from Φ_R (real part of complex pseudofermion)
    compute_pf_force(h, phi_r, zolotarev_alphas, zolotarev_betas,
                     fwd, bwd, n_sites, cg_tol, cg_max_iter, cg_entries, n_threads, &mut f_h);
    // PF force from Φ_I (imaginary part)
    compute_pf_force(h, phi_i, zolotarev_alphas, zolotarev_betas,
                     fwd, bwd, n_sites, cg_tol, cg_max_iter, cg_entries, n_threads, &mut f_h);

    f_h
}

// ═══════════════════════════════════════════════════════════════════
// Hamiltonian evaluation
//
// H = K + S_aux + S_PF
// K = 0.5 Σ π_h²
// S_aux = Σ h² / (4g)
// S_PF = α₀ φ·φ + Σ_k α_k φ·ψ_k where (A†A + β_k)ψ_k = φ
//
// Lean: rhmc_hamiltonian_nonneg (HubbardStratonovichRHMC.lean)
// Source: Duane et al., PLB 195, 216 (1987)
// ═══════════════════════════════════════════════════════════════════

/// Pseudofermion action for ONE real field: φ^T r(A†A) φ where r ≈ x^{-1/4}.
fn compute_spf(
    h: &[f64], phi: &[f64],
    alpha_0: f64, zolotarev_alphas: &[f64], zolotarev_betas: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]], n_sites: usize,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry], n_threads: usize,
) -> f64 {
    let cg_result = multishift_cg(h, phi, zolotarev_betas, cg_tol, cg_max_iter,
                                fwd, bwd, n_sites, cg_entries, n_threads);
    let mut s = alpha_0 * dot(phi, phi);
    for k in 0..zolotarev_betas.len() {
        s += zolotarev_alphas[k] * dot(phi, &cg_result.solutions[k]);
    }
    s
}

fn compute_hamiltonian(
    h: &[f64], pi_h: &[f64], g: f64, phi_r: &[f64], phi_i: &[f64],
    alpha_0: f64, zolotarev_alphas: &[f64], zolotarev_betas: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]], n_sites: usize,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry], n_threads: usize,
) -> f64 {
    let k_energy: f64 = 0.5 * dot(pi_h, pi_h);
    let s_aux: f64 = dot(h, h) / (4.0 * g);
    // Complex pseudofermion: S_PF = Φ_R^T r Φ_R + Φ_I^T r Φ_I
    let s_pf = compute_spf(h, phi_r, alpha_0, zolotarev_alphas, zolotarev_betas,
                           fwd, bwd, n_sites, cg_tol, cg_max_iter, cg_entries, n_threads)
             + compute_spf(h, phi_i, alpha_0, zolotarev_alphas, zolotarev_betas,
                           fwd, bwd, n_sites, cg_tol, cg_max_iter, cg_entries, n_threads);
    k_energy + s_aux + s_pf
}

// ═══════════════════════════════════════════════════════════════════
// Pseudofermion heat bath — complex pseudofermion convention
//
// For Pf(A) = det(A†A)^{1/4}, the complex pseudofermion action is:
//   S_PF = Φ†(A†A)^{-1/4}Φ  where Φ ∈ ℂ^{8V}
//
// Since A†A is real, Φ_R and Φ_I decouple:
//   S_PF = Φ_R^T (A†A)^{-1/4} Φ_R + Φ_I^T (A†A)^{-1/4} Φ_I
//
// Heatbath uses the A trick to compute (A†A)^{1/8}·ξ:
//   Φ = A · r_{-3/8}(A†A) · ξ  where r_{-3/8} ≈ x^{-3/8}
//
// Verification: ||Φ||² in eigenspace λ = λ·λ^{-3/4}·||ξ||² = λ^{1/4}·||ξ||²
// → covariance (A†A)^{1/4} → correct Gaussian for S_PF = Φ†(A†A)^{-1/4}Φ.
//
// Lean: hs_gaussian_identity_zero (HubbardStratonovichRHMC.lean)
// Source: Schaich & DeGrand, CPC 190:200 (2015), Eqs. 16-17 (arXiv:1410.6971)
// ═══════════════════════════════════════════════════════════════════

/// Generate complex pseudofermion (Φ_R, Φ_I) from the correct Pfaffian distribution.
/// Returns two real vectors representing Re(Φ) and Im(Φ).
fn pseudofermion_heatbath(
    h: &[f64], rng: &mut ChaCha20Rng,
    alpha_0_hb: f64, alphas_hb: &[f64], betas_hb: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]], n_sites: usize,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry], n_threads: usize,
) -> (Vec<f64>, Vec<f64>) {
    let dim = 8 * n_sites;

    // Generate two independent noise vectors (real + imaginary parts of complex ξ)
    let xi_r: Vec<f64> = (0..dim).map(|_| rand_normal(rng)).collect();
    let xi_i: Vec<f64> = (0..dim).map(|_| rand_normal(rng)).collect();

    // For each component: η = r_{-3/8}(A†A) · ξ via multi-shift CG
    let cg_r = multishift_cg(h, &xi_r, betas_hb, cg_tol, cg_max_iter,
                              fwd, bwd, n_sites, cg_entries, n_threads);
    let cg_i = multishift_cg(h, &xi_i, betas_hb, cg_tol, cg_max_iter,
                              fwd, bwd, n_sites, cg_entries, n_threads);

    // η = α₀ξ + Σ αₖψₖ (partial fraction form of r_{-3/8})
    let mut eta_r = vec![0.0; dim];
    let mut eta_i = vec![0.0; dim];
    for i in 0..dim {
        eta_r[i] = alpha_0_hb * xi_r[i];
        eta_i[i] = alpha_0_hb * xi_i[i];
    }
    for k in 0..betas_hb.len() {
        axpy(alphas_hb[k], &cg_r.solutions[k], &mut eta_r);
        axpy(alphas_hb[k], &cg_i.solutions[k], &mut eta_i);
    }

    // Φ = A · η / √2 (the A matvec trick + complex Gaussian normalization)
    // The 1/√2 accounts for the complex Gaussian convention: each real component
    // of Φ has variance Q^{-1}/2 (not Q^{-1}), ensuring P(Φ) ∝ exp(-Φ†QΦ).
    let mut phi_r = vec![0.0; dim];
    let mut phi_i = vec![0.0; dim];
    apply_fermion_matrix(h, &eta_r, &mut phi_r, fwd, bwd, n_sites, cg_entries, n_threads);
    apply_fermion_matrix(h, &eta_i, &mut phi_i, fwd, bwd, n_sites, cg_entries, n_threads);
    let inv_sqrt2 = 1.0 / f64::sqrt(2.0);
    for i in 0..dim { phi_r[i] *= inv_sqrt2; }
    for i in 0..dim { phi_i[i] *= inv_sqrt2; }

    (phi_r, phi_i)
}

/// Box-Muller normal random variate
fn rand_normal(rng: &mut ChaCha20Rng) -> f64 {
    let u1: f64 = rng.random::<f64>();
    let u2: f64 = rng.random::<f64>();
    (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
}

// ═══════════════════════════════════════════════════════════════════
// h-field measurements — O(V), no CG needed
//
// Lean: binder_tetrad_prefactor, binder_metric_prefactor (MajoranaKramers.lean)
// ═══════════════════════════════════════════════════════════════════

/// Returns (h_sq, tetrad_m2, metric_trQ2)
fn measure_observables(h: &[f64], n_sites: usize) -> (f64, f64, f64) {
    let v = n_sites as f64;

    // ⟨h²⟩
    let h_sq: f64 = dot(h, h) / (16.0 * v);

    // Tetrad proxy: m_h = (1/V) Σ_x h^a_{x,μ}; |m_h|²
    let mut m_h = [0.0f64; 16]; // (4 mu, 4 a)
    for site in 0..n_sites {
        for i in 0..16 {
            m_h[i] += h[site * 16 + i];
        }
    }
    let tet_m2: f64 = m_h.iter().map(|x| (x / v) * (x / v)).sum();

    // Metric proxy: M_μν = (1/V) Σ_{x,a} h^a_{x,μ} h^a_{x,ν}; Q = M - TrM/4 I; trQ²
    let mut m_matrix = [[0.0f64; 4]; 4]; // M[mu][nu]
    for site in 0..n_sites {
        for mu in 0..4 {
            for nu in 0..4 {
                for a in 0..4 {
                    m_matrix[mu][nu] += h[site * 16 + mu * 4 + a]
                                      * h[site * 16 + nu * 4 + a];
                }
            }
        }
    }
    let tr_m: f64 = (0..4).map(|i| m_matrix[i][i]).sum::<f64>() / v;
    let mut tr_q2: f64 = 0.0;
    for mu in 0..4 {
        for nu in 0..4 {
            let m_val = m_matrix[mu][nu] / v;
            let q_val = m_val - if mu == nu { tr_m / 4.0 } else { 0.0 };
            tr_q2 += q_val * q_val;
        }
    }

    (h_sq, tet_m2, tr_q2)
}

// ═══════════════════════════════════════════════════════════════════
// Full RHMC trajectory
//
// Omelyan 2MN integrator with FSAL optimization.
// At β=0: gauge links fixed to identity, only h-fields evolve.
//
// Lean: omelyan_second_order_symplectic, rhmc_detailed_balance
//       (HubbardStratonovichRHMC.lean)
// ═══════════════════════════════════════════════════════════════════

#[derive(Clone)]
struct TrajectoryResult {
    delta_h: f64,
    accepted: bool,
    h_sq: f64,
    tet_m2: f64,
    tr_q2: f64,
}

fn rhmc_trajectory(
    h: &mut Vec<f64>,
    g: f64,
    tau: f64,
    n_md_steps: usize,
    alpha_0: f64, alphas: &[f64], betas: &[f64],
    alpha_0_hb: f64, alphas_hb: &[f64], betas_hb: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    rng: &mut ChaCha20Rng,
    cg_entries: &[CgEntry],
    n_threads: usize,
) -> TrajectoryResult {
    let dim = 8 * n_sites;
    let n_h = n_sites * 16;
    let eps = tau / n_md_steps as f64;
    let lam = 0.1932; // Omelyan 2MN parameter

    // CG tolerances: float64 throughout in Rust (no mixed precision needed)
    let cg_tol_md = 1e-8;
    let cg_tol_mc = 1e-12;
    let cg_max_iter = 2000;

    // Heat bath: complex Φ = (Φ_R, Φ_I) via A·r_{-3/8}(A†A)·ξ trick
    let (phi_r, phi_i) = pseudofermion_heatbath(h, rng, alpha_0_hb, alphas_hb, betas_hb,
                                     fwd, bwd, n_sites, cg_tol_md, cg_max_iter, cg_entries, n_threads);

    // Refresh momenta: π ~ N(0, 1)
    let mut pi_h: Vec<f64> = (0..n_h).map(|_| rand_normal(rng)).collect();

    // Store old state
    let h_old = h.clone();

    // H_old (tight tolerance for Metropolis)
    let h_old_val = compute_hamiltonian(h, &pi_h, g, &phi_r, &phi_i,
        alpha_0, alphas, betas, fwd, bwd, n_sites, cg_tol_mc, cg_max_iter, cg_entries, n_threads);

    // ── FSAL Omelyan MD ──
    // Initial force (before loop)
    let mut f_h = compute_forces(h, g, &phi_r, &phi_i, alphas, betas, fwd, bwd,
                                  n_sites, cg_tol_md, cg_max_iter, cg_entries, n_threads);

    for _step in 0..n_md_steps {
        // λε kick
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
        // ε/2 drift
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }

        // Middle force
        f_h = compute_forces(h, g, &phi_r, &phi_i, alphas, betas, fwd, bwd,
                              n_sites, cg_tol_md, cg_max_iter, cg_entries, n_threads);

        // (1-2λ)ε kick
        for i in 0..n_h { pi_h[i] += (1.0 - 2.0 * lam) * eps * f_h[i]; }
        // ε/2 drift
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }

        // Final force (= initial force of next step via FSAL)
        f_h = compute_forces(h, g, &phi_r, &phi_i, alphas, betas, fwd, bwd,
                              n_sites, cg_tol_md, cg_max_iter, cg_entries, n_threads);

        // λε kick
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
    }

    // H_new
    let h_new_val = compute_hamiltonian(h, &pi_h, g, &phi_r, &phi_i,
        alpha_0, alphas, betas, fwd, bwd, n_sites, cg_tol_mc, cg_max_iter, cg_entries, n_threads);

    let delta_h = h_new_val - h_old_val;

    // Metropolis accept/reject
    let accepted = if delta_h <= 0.0 {
        true
    } else {
        let u: f64 = rng.random();
        u < (-delta_h).exp()
    };

    if !accepted {
        *h = h_old;
    }

    // Measure
    let (h_sq, tet_m2, tr_q2) = measure_observables(h, n_sites);

    TrajectoryResult { delta_h, accepted, h_sq, tet_m2, tr_q2 }
}

// ═══════════════════════════════════════════════════════════════════
// PyO3 Python bindings
// ═══════════════════════════════════════════════════════════════════

/// Run a batch of RHMC trajectories, returning per-trajectory results.
///
/// Args:
///     l: lattice size
///     g: four-fermion coupling
///     n_traj: total trajectories
///     n_therm: thermalization trajectories (not measured)
///     n_meas_skip: trajectories between measurements
///     n_md_steps: Omelyan steps per trajectory
///     tau: MD trajectory length
///     alpha_0: Zolotarev constant for x^{-1/4}
///     alphas: Zolotarev residues for x^{-1/4}
///     betas: Zolotarev shifts for x^{-1/4}
///     alpha_0_hb: Zolotarev constant for x^{-1/8} (heat bath)
///     alphas_hb: Zolotarev residues for x^{-1/8}
///     betas_hb: Zolotarev shifts for x^{-1/8}
///     seed: random seed
///
/// Returns:
///     dict with h_sq_history, delta_h_history, tet_m2_history, tr_q2_history,
///     acceptance_rate, n_measurements
#[pyfunction]
fn run_rhmc_rust<'py>(
    py: Python<'py>,
    l: usize,
    g: f64,
    n_traj: usize,
    n_therm: usize,
    n_meas_skip: usize,
    n_md_steps: usize,
    tau: f64,
    alpha_0: f64,
    alphas: PyReadonlyArray1<'py, f64>,
    betas: PyReadonlyArray1<'py, f64>,
    alpha_0_hb: f64,
    alphas_hb: PyReadonlyArray1<'py, f64>,
    betas_hb: PyReadonlyArray1<'py, f64>,
    seed: u64,
    // CG stencil entries from constants.py (pipeline invariant: constants.py is canonical)
    cg_a: PyReadonlyArray1<'py, i64>,
    cg_i: PyReadonlyArray1<'py, i64>,
    cg_j: PyReadonlyArray1<'py, i64>,
    cg_val: PyReadonlyArray1<'py, f64>,
    // Optional: resume from a saved h-field (skips random initialization)
    h_init: Option<PyReadonlyArray1<'py, f64>>,
) -> PyResult<PyObject> {
    let n_threads = 1;  // single-threaded; production parallelism is across workers
    let alphas = alphas.as_slice()?;
    let betas = betas.as_slice()?;
    let alphas_hb = alphas_hb.as_slice()?;
    let betas_hb = betas_hb.as_slice()?;
    let cg_entries = parse_cg_entries(cg_a.as_slice()?, cg_i.as_slice()?,
                                       cg_j.as_slice()?, cg_val.as_slice()?);

    let n_sites = l * l * l * l;
    let (fwd, bwd) = build_neighbors(l);

    let mut rng = ChaCha20Rng::seed_from_u64(seed);

    // Initialize h: from checkpoint if provided, else random
    let mut h: Vec<f64> = if let Some(h_in) = h_init {
        h_in.as_slice()?.to_vec()
    } else {
        let sigma_h = (2.0 * g).sqrt();
        (0..n_sites * 16).map(|_| rand_normal(&mut rng) * sigma_h).collect()
    };

    let mut h_sq_hist = Vec::new();
    let mut delta_h_hist = Vec::new();
    let mut tet_m2_hist = Vec::new();
    let mut tr_q2_hist = Vec::new();
    let mut n_accepted: usize = 0;

    for traj in 0..n_traj {
        // Allow Python interrupts periodically
        if traj % 10 == 0 {
            py.check_signals()?;
        }

        let result = rhmc_trajectory(
            &mut h, g, tau, n_md_steps,
            alpha_0, alphas, betas,
            alpha_0_hb, alphas_hb, betas_hb,
            &fwd, &bwd, n_sites, &mut rng, &cg_entries,
            n_threads,
        );

        delta_h_hist.push(result.delta_h);
        if result.accepted { n_accepted += 1; }

        if traj >= n_therm && (traj - n_therm) % n_meas_skip == 0 {
            h_sq_hist.push(result.h_sq);
            tet_m2_hist.push(result.tet_m2);
            tr_q2_hist.push(result.tr_q2);
        }
    }

    // Build Python dict result
    let dict = pyo3::types::PyDict::new(py);
    dict.set_item("h_sq_history", h_sq_hist)?;
    dict.set_item("delta_h_history", delta_h_hist)?;
    let n_meas = tet_m2_hist.len();
    dict.set_item("tet_m2_history", tet_m2_hist)?;
    dict.set_item("tr_q2_history", tr_q2_hist)?;
    dict.set_item("acceptance_rate", n_accepted as f64 / n_traj as f64)?;
    dict.set_item("n_measurements", n_meas)?;
    dict.set_item("sign_free", true)?;
    dict.set_item("g", g)?;
    dict.set_item("L", l)?;
    // Return final h-field for checkpointing/resume
    dict.set_item("h_final", h)?;

    Ok(dict.into())
}

/// Apply the fermion matrix A[h] @ v (for testing/validation).
/// Apply the fermion matrix A[h] @ v (for testing/validation).
/// CG entries passed from Python to maintain constants.py as canonical source.
#[pyfunction]
fn apply_fermion_matrix_py<'py>(
    py: Python<'py>,
    h: PyReadonlyArray3<'py, f64>,  // (V, 4, 4)
    v: PyReadonlyArray1<'py, f64>,
    l: usize,
    cg_a: PyReadonlyArray1<'py, i64>,
    cg_i: PyReadonlyArray1<'py, i64>,
    cg_j: PyReadonlyArray1<'py, i64>,
    cg_val: PyReadonlyArray1<'py, f64>,
) -> PyResult<Py<PyArray1<f64>>> {
    let h_slice = h.as_slice()?;
    let v_slice = v.as_slice()?;
    let n_sites = l * l * l * l;
    let dim = 8 * n_sites;
    let (fwd, bwd) = build_neighbors(l);
    let cg_entries = parse_cg_entries(cg_a.as_slice()?, cg_i.as_slice()?,
                                       cg_j.as_slice()?, cg_val.as_slice()?);

    let mut out = vec![0.0; dim];
    apply_fermion_matrix(h_slice, v_slice, &mut out, &fwd, &bwd, n_sites, &cg_entries, 1);

    Ok(PyArray1::from_vec(py, out).into())
}

/// Estimate spectral range (λ_min, λ_max) of A†A via Lanczos iteration.
/// Matrix-free — works at any lattice size.
///
/// Args:
///     l: lattice size
///     g: coupling (used to generate initial h ~ N(0, √(2g)))
///     seed: random seed
///     n_lanczos: Lanczos iterations (default 30, more = tighter bounds)
///     cg_a/i/j/val: CG stencil entries from constants.py
///
/// Returns:
///     (lam_min, lam_max) with safety margins applied
#[pyfunction]
fn estimate_spectral_range_py<'py>(
    _py: Python<'py>,
    l: usize,
    g: f64,
    seed: u64,
    n_lanczos: usize,
    cg_a: PyReadonlyArray1<'py, i64>,
    cg_i: PyReadonlyArray1<'py, i64>,
    cg_j: PyReadonlyArray1<'py, i64>,
    cg_val: PyReadonlyArray1<'py, f64>,
) -> PyResult<(f64, f64)> {
    let cg_entries = parse_cg_entries(cg_a.as_slice()?, cg_i.as_slice()?,
                                       cg_j.as_slice()?, cg_val.as_slice()?);
    let n_sites = l * l * l * l;
    let (fwd, bwd) = build_neighbors(l);
    let mut rng = ChaCha20Rng::seed_from_u64(seed);

    // Generate h ~ N(0, √(2g)) for spectral estimation
    let sigma_h = (2.0 * g).sqrt();
    let h: Vec<f64> = (0..n_sites * 16).map(|_| rand_normal(&mut rng) * sigma_h).collect();

    let (lam_min, lam_max) = estimate_spectral_range(
        &h, &fwd, &bwd, n_sites, &cg_entries, n_lanczos, &mut rng, 1);

    Ok((lam_min, lam_max))
}

#[pymodule]
fn sk_eft_rhmc(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(run_rhmc_rust, m)?)?;
    m.add_function(wrap_pyfunction!(apply_fermion_matrix_py, m)?)?;
    m.add_function(wrap_pyfunction!(estimate_spectral_range_py, m)?)?;
    Ok(())
}
