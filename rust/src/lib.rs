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
// Even-odd site decomposition
//
// On a 4D hypercubic lattice, site (x0,x1,x2,x3) has parity
// (x0+x1+x2+x3) mod 2. Every forward neighbor of an even site is odd
// and vice versa. Since A[h] has ONLY nearest-neighbor hops, A_ee = 0
// and A_oo = 0 — the operator is purely off-diagonal in the even-odd
// basis. This means A†A = -A² = diag(M_e, M_o) is block-diagonal,
// where M_e = A_eo·A_eo^T operates on even sites only at half cost.
//
// Physics: Pf(A) = det(A†A)^{1/4} = det(M_e)^{1/2}. The x^{-1/2}
// Zolotarev approximation on the half-lattice operator M_e replaces
// x^{-1/4} on the full A†A. Same Krylov sharing, half the dimension.
//
// Lean: hs_fermion_matrix_antisymmetric (bipartite → block-diagonal)
// Source: DeGrand & DeTar, "Lattice Methods for QCD" Ch. 8
// ═══════════════════════════════════════════════════════════════════

/// Even-odd lattice tables for half-lattice stencil operations.
struct EvenOddTables {
    even_sites: Vec<usize>,      // full-lattice indices of even sites
    odd_sites: Vec<usize>,       // full-lattice indices of odd sites
    compact_idx: Vec<usize>,     // full index → compact index within parity sector
    is_even: Vec<bool>,          // full index → true if even
    n_even: usize,
    n_odd: usize,
}

fn build_even_odd(l: usize) -> EvenOddTables {
    let v = l * l * l * l;
    let mut even_sites = Vec::with_capacity(v / 2);
    let mut odd_sites = Vec::with_capacity(v / 2);
    let mut compact_idx = vec![0usize; v];
    let mut is_even = vec![false; v];

    for site in 0..v {
        let x0 = site / (l * l * l);
        let x1 = (site / (l * l)) % l;
        let x2 = (site / l) % l;
        let x3 = site % l;
        if (x0 + x1 + x2 + x3) % 2 == 0 {
            compact_idx[site] = even_sites.len();
            is_even[site] = true;
            even_sites.push(site);
        } else {
            compact_idx[site] = odd_sites.len();
            odd_sites.push(site);
        }
    }

    EvenOddTables {
        n_even: even_sites.len(),
        n_odd: odd_sites.len(),
        even_sites,
        odd_sites,
        compact_idx,
        is_even,
    }
}

// ═══════════════════════════════════════════════════════════════════
// Half-lattice hops: A_eo (odd→even) and A_eo^T (even→odd)
//
// A_eo gathers odd-site spinor values into even-site output.
// A_eo^T scatters even-site spinor values into odd-site output.
// M_e = A_eo · A_eo^T is applied as two half-hops at half the cost
// of the full A†A = -A² (which requires two full-lattice stencils).
//
// Cost: each half-hop visits V/2 sites × 8 bonds × 32 CG entries
//       = 128V FMAs, vs 256V for a full A application.
//       M_e = 2 × 128V = 256V, vs A†A = 2 × 256V = 512V. → 2× saving.
// ═══════════════════════════════════════════════════════════════════

/// Apply A_eo: maps odd-site vector → even-site vector.
/// For each even site e: gathers from forward odd neighbor (using h_e)
///                        and backward odd neighbor (using h_bwd).
fn apply_aeo(
    h: &[f64], v_odd: &[f64], out_even: &mut [f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables, cg_entries: &[CgEntry],
) {
    for x in out_even.iter_mut() { *x = 0.0; }

    for &e in &eo.even_sites {
        let e_compact = eo.compact_idx[e];
        for mu in 0..4usize {
            // Forward: even site e gathers from odd fwd neighbor
            let nb_fwd = fwd[e][mu];
            let nb_fwd_compact = eo.compact_idx[nb_fwd];
            for entry in cg_entries {
                let h_val = h[e * 16 + mu * 4 + entry.a];
                if h_val == 0.0 { continue; }
                let c = entry.val * h_val;
                out_even[8 * e_compact + entry.i] += c * v_odd[8 * nb_fwd_compact + entry.j];
            }

            // Backward: even site e gathers from odd bwd neighbor
            let nb_bwd = bwd[e][mu];
            let nb_bwd_compact = eo.compact_idx[nb_bwd];
            for entry in cg_entries {
                let h_val = h[nb_bwd * 16 + mu * 4 + entry.a];
                if h_val == 0.0 { continue; }
                let c = entry.val * h_val;
                // Antisymmetry: backward gather has transposed indices and minus sign
                out_even[8 * e_compact + entry.j] -= c * v_odd[8 * nb_bwd_compact + entry.i];
            }
        }
    }
}

/// Apply A_eo^T: maps even-site vector → odd-site vector.
/// This is the transpose of A_eo: for each even site e, scatters to
/// forward and backward odd neighbors.
fn apply_aeot(
    h: &[f64], v_even: &[f64], out_odd: &mut [f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables, cg_entries: &[CgEntry],
) {
    for x in out_odd.iter_mut() { *x = 0.0; }

    for &e in &eo.even_sites {
        let e_compact = eo.compact_idx[e];
        for mu in 0..4usize {
            // Transpose of forward gather: scatter from even to fwd odd neighbor
            let nb_fwd = fwd[e][mu];
            let nb_fwd_compact = eo.compact_idx[nb_fwd];
            for entry in cg_entries {
                let h_val = h[e * 16 + mu * 4 + entry.a];
                if h_val == 0.0 { continue; }
                let c = entry.val * h_val;
                // Transpose swaps (e,I)↔(nb,J): out_odd[nb,J] += c * v_even[e,I]
                out_odd[8 * nb_fwd_compact + entry.j] += c * v_even[8 * e_compact + entry.i];
            }

            // Transpose of backward gather: scatter from even to bwd odd neighbor
            let nb_bwd = bwd[e][mu];
            let nb_bwd_compact = eo.compact_idx[nb_bwd];
            for entry in cg_entries {
                let h_val = h[nb_bwd * 16 + mu * 4 + entry.a];
                if h_val == 0.0 { continue; }
                let c = entry.val * h_val;
                // Transpose of (out_e[J] -= c * v_o[I]) → (out_o[I] -= c * v_e[J])
                out_odd[8 * nb_bwd_compact + entry.i] -= c * v_even[8 * e_compact + entry.j];
            }
        }
    }
}

/// Apply (M_e + σ) to an even-site vector: out = A_eo(A_eo^T v) + σv.
/// Cost: two half-hops = one full A application (vs two for A†A).
fn apply_me_shifted(
    h: &[f64], v_even: &[f64], out_even: &mut [f64],
    sigma: f64,
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    scratch_odd: &mut [f64],
    cg_entries: &[CgEntry],
) {
    let dim_even = 8 * eo.n_even;
    // Step 1: scratch_odd = A_eo^T · v_even (even → odd)
    apply_aeot(h, v_even, scratch_odd, fwd, bwd, eo, cg_entries);
    // Step 2: out_even = A_eo · scratch_odd (odd → even)
    apply_aeo(h, scratch_odd, out_even, fwd, bwd, eo, cg_entries);
    // Step 3: add shift: out += σ · v
    for i in 0..dim_even {
        out_even[i] += sigma * v_even[i];
    }
}

// ═══════════════════════════════════════════════════════════════════
// Matrix-free A[h] @ v — the core stencil (full lattice, kept for
// validation and observables that need the full operator)
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
// Low-mode deflation: Lanczos eigensolver + deflation data
//
// Computes K smallest eigenpairs of M_e = A_eo·A_eo^T for use in
// deflated multi-shift CG. Reduces effective κ from ~6000 to ~26
// with K=30, cutting CG iterations from ~1200 to ~100.
//
// Algorithm: thick-restart Lanczos with full reorthogonalization.
// At dim_e = 16384 (L=8), K=30 eigenpairs cost ~3000 matvecs
// (~1-2 seconds). Warm-start from previous trajectory cuts this
// to ~500-800 matvecs.
//
// Source: Bloch et al., arXiv:0910.2927 (deflated multi-shift CG)
//         Birk & Frommer, Numer. Algorithms (2014)
//         Kalkreuter & Simma, CPC 93:33 (1996) (warm-start)
// ═══════════════════════════════════════════════════════════════════

/// Deflation data: K smallest eigenpairs of M_e.
struct DeflationData {
    /// Eigenvectors, each of length dim_e. Column-major: evecs[j][i].
    evecs: Vec<Vec<f64>>,
    /// Eigenvalues (sorted ascending).
    evals: Vec<f64>,
    /// Number of converged eigenpairs.
    k: usize,
}

/// Eigendecomposition of symmetric tridiagonal matrix T (n×n) via
/// Jacobi rotation method on the dense representation.
///
/// For n ≤ 100 this is trivially fast and handles degenerate eigenvalues
/// (Kramers quartets) robustly — no special cases needed.
///
/// Returns (eigenvalues sorted ascending, eigenvectors as rows).
fn tridiag_eigen_jacobi(alpha: &[f64], beta: &[f64]) -> (Vec<f64>, Vec<Vec<f64>>) {
    let n = alpha.len();

    // Build dense symmetric matrix from tridiagonal
    let mut a = vec![vec![0.0_f64; n]; n]; // A[i][j]
    for i in 0..n {
        a[i][i] = alpha[i];
        if i + 1 < n && i < beta.len() {
            a[i][i + 1] = beta[i];
            a[i + 1][i] = beta[i];
        }
    }

    // Eigenvector matrix V (starts as identity)
    let mut v = vec![vec![0.0_f64; n]; n];
    for i in 0..n { v[i][i] = 1.0; }

    // Jacobi sweeps: rotate to zero each off-diagonal element
    let max_sweeps = 100;
    for _sweep in 0..max_sweeps {
        // Find max off-diagonal element
        let mut max_off = 0.0_f64;
        for i in 0..n {
            for j in (i + 1)..n {
                max_off = max_off.max(a[i][j].abs());
            }
        }
        if max_off < 1e-14 { break; } // converged

        // Sweep all off-diagonal pairs
        for p in 0..n {
            for q in (p + 1)..n {
                if a[p][q].abs() < 1e-15 { continue; }

                // Compute rotation angle
                let tau = (a[q][q] - a[p][p]) / (2.0 * a[p][q]);
                let t = if tau.abs() > 1e15 {
                    // Avoid overflow: t ≈ 1/(2τ)
                    0.5 / tau
                } else {
                    let sign_tau = if tau >= 0.0 { 1.0 } else { -1.0 };
                    sign_tau / (tau.abs() + (1.0 + tau * tau).sqrt())
                };
                let c = 1.0 / (1.0 + t * t).sqrt();
                let s = t * c;
                let tau_val = s / (1.0 + c); // for the update formula

                // Update A: apply rotation from both sides
                let a_pq = a[p][q];
                a[p][q] = 0.0;
                a[q][p] = 0.0;
                a[p][p] -= t * a_pq;
                a[q][q] += t * a_pq;

                // Update remaining rows/columns
                for r in 0..n {
                    if r == p || r == q { continue; }
                    let a_rp = a[r][p];
                    let a_rq = a[r][q];
                    a[r][p] = a_rp - s * (a_rq + tau_val * a_rp);
                    a[p][r] = a[r][p];
                    a[r][q] = a_rq + s * (a_rp - tau_val * a_rq);
                    a[q][r] = a[r][q];
                }

                // Update eigenvectors: V[:, p] and V[:, q]
                for r in 0..n {
                    let v_rp = v[r][p];
                    let v_rq = v[r][q];
                    v[r][p] = v_rp - s * (v_rq + tau_val * v_rp);
                    v[r][q] = v_rq + s * (v_rp - tau_val * v_rq);
                }
            }
        }
    }

    // Extract eigenvalues (diagonal of A) and sort ascending
    let mut eig_pairs: Vec<(f64, usize)> = (0..n).map(|i| (a[i][i], i)).collect();
    eig_pairs.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

    let evals: Vec<f64> = eig_pairs.iter().map(|&(e, _)| e).collect();
    let evecs: Vec<Vec<f64>> = eig_pairs.iter()
        .map(|&(_, idx)| (0..n).map(|r| v[r][idx]).collect())
        .collect();

    (evals, evecs)
}

/// Thick-restart Lanczos for K smallest eigenpairs of M_e.
///
/// Uses the even-odd operator apply_me_shifted(σ=0) as the matvec.
/// Full reorthogonalization ensures numerical stability.
///
/// Args:
///   h: current h-field (full lattice)
///   k_want: number of eigenpairs desired
///   m: Lanczos subspace dimension per restart cycle (typically 2*k_want)
///   tol: convergence tolerance on residual norm
///   max_restarts: maximum restart cycles
///   warm_start: optional initial eigenvector guesses (from previous trajectory)
///
/// Returns: DeflationData with converged eigenpairs.
fn lanczos_smallest_eigenpairs_eo(
    h: &[f64],
    k_want: usize,
    m: usize,
    tol: f64,
    max_restarts: usize,
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_entries: &[CgEntry],
    warm_start: Option<&[Vec<f64>]>,
    rng: &mut ChaCha20Rng,
) -> DeflationData {
    let dim_e = 8 * eo.n_even;
    let m = m.min(dim_e).max(k_want + 1);
    let mut scratch_odd = vec![0.0_f64; 8 * eo.n_odd];

    // Lanczos basis vectors Q = [q_0, q_1, ..., q_{m-1}]
    let mut q_basis: Vec<Vec<f64>> = Vec::with_capacity(m);

    // Initial vector: use first warm-start vector or random
    let mut q0: Vec<f64> = if let Some(ws) = warm_start {
        if !ws.is_empty() { ws[0].clone() } else {
            (0..dim_e).map(|_| rand_normal(rng)).collect()
        }
    } else {
        (0..dim_e).map(|_| rand_normal(rng)).collect()
    };
    let norm0 = dot(&q0, &q0).sqrt();
    for x in q0.iter_mut() { *x /= norm0; }

    let mut best_evals = Vec::new();
    let mut best_evecs: Vec<Vec<f64>> = Vec::new();

    for _restart in 0..max_restarts {
        q_basis.clear();
        q_basis.push(q0.clone());

        let mut alphas_l = Vec::with_capacity(m);
        let mut betas_l = Vec::with_capacity(m);
        let mut beta_prev = 0.0_f64;
        let mut q_prev = vec![0.0_f64; dim_e];

        // Build Lanczos tridiagonal
        for j in 0..m {
            // w = M_e @ q_j (via apply_me_shifted with σ=0)
            let mut w = vec![0.0_f64; dim_e];
            apply_me_shifted(h, &q_basis[j], &mut w, 0.0, fwd, bwd, eo, &mut scratch_odd, cg_entries);

            let alpha_j = dot(&q_basis[j], &w);
            alphas_l.push(alpha_j);

            // w = w - alpha * q_j - beta_prev * q_{j-1}
            for i in 0..dim_e {
                w[i] -= alpha_j * q_basis[j][i] + beta_prev * q_prev[i];
            }

            // Full reorthogonalization against all basis vectors
            for qk in &q_basis {
                let proj = dot(&w, qk);
                axpy(-proj, qk, &mut w);
            }

            let beta_j = dot(&w, &w).sqrt();

            if j < m - 1 {
                betas_l.push(beta_j);
                if beta_j < 1e-14 {
                    // Invariant subspace found — lucky breakdown
                    break;
                }
                q_prev = q_basis[j].clone();
                let mut q_new = w;
                for x in q_new.iter_mut() { *x /= beta_j; }
                q_basis.push(q_new);
                beta_prev = beta_j;
            }
        }

        // Solve tridiagonal eigenvalue problem via Jacobi (robust for clusters)
        let n_lanczos = alphas_l.len();
        if n_lanczos == 0 { break; }

        let (evals_t_sorted, evecs_t_sorted) = tridiag_eigen_jacobi(&alphas_l, &betas_l);
        let k_actual = k_want.min(evals_t_sorted.len());

        // Take k_actual smallest eigenpairs (already sorted ascending)
        let target_evals: Vec<f64> = evals_t_sorted[..k_actual].to_vec();
        let evecs_t: Vec<Vec<f64>> = evecs_t_sorted[..k_actual].to_vec();

        // Ritz vectors: v_j = Q @ s_j (transform tridiag eigenvectors to full space)
        let mut ritz_vecs: Vec<Vec<f64>> = Vec::with_capacity(k_actual);
        let mut ritz_residuals: Vec<f64> = Vec::with_capacity(k_actual);

        for j in 0..k_actual {
            let s = &evecs_t[j]; // tridiag eigenvector, length n_lanczos
            let mut v = vec![0.0_f64; dim_e];
            for (l_idx, sl) in s.iter().enumerate() {
                if l_idx < q_basis.len() {
                    axpy(*sl, &q_basis[l_idx], &mut v);
                }
            }
            // Normalize (should be ~1 already but enforce)
            let vnorm = dot(&v, &v).sqrt();
            if vnorm > 1e-15 {
                for x in v.iter_mut() { *x /= vnorm; }
            }

            // Compute residual: || M_e v - λ v ||
            let mut mv = vec![0.0_f64; dim_e];
            apply_me_shifted(h, &v, &mut mv, 0.0, fwd, bwd, eo, &mut scratch_odd, cg_entries);
            let lambda = target_evals[j];
            for i in 0..dim_e { mv[i] -= lambda * v[i]; }
            let res = dot(&mv, &mv).sqrt();
            ritz_residuals.push(res);
            ritz_vecs.push(v);
        }

        // Check convergence
        let max_res = ritz_residuals.iter().cloned().fold(0.0_f64, f64::max);
        best_evals = target_evals;
        best_evecs = ritz_vecs;

        if max_res < tol {
            break; // All converged
        }

        // Thick restart: use the best Ritz vector as starting vector
        q0 = best_evecs[0].clone();
    }

    DeflationData {
        k: best_evecs.len(),
        evecs: best_evecs,
        evals: best_evals,
    }
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
// Note: chronological CG (independent per-shift with initial guess)
// was tested and found ineffective at L=8: the condition number κ≈6000
// means ε×κ≈38, so previous solutions are WORSE than zero as initial
// guesses for the ill-conditioned base system. Multi-shift CG's Krylov
// sharing is essential — it solves all shifts in ~1200 shared iterations
// vs 12×1200 independent iterations.
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
    cg_tol_md: f64,
    cg_tol_mc: f64,
) -> TrajectoryResult {
    let n_h = n_sites * 16;
    let eps = tau / n_md_steps as f64;
    let lam = 0.1932; // Omelyan 2MN parameter
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

    // ── FSAL Omelyan MD (multi-shift CG, relaxed MD tolerance) ──
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

    // H_new (tight tolerance, uses multi-shift CG — no chrono)
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
// Even-odd RHMC — half-lattice Krylov + force on full h-field
//
// Physics identity: Pf(A) = det(A†A)^{1/4} = det(M_e)^{1/2}
// because A is block-off-diagonal → A†A = diag(M_e, M_o) with M_e = M_o.
//
// Consequence: the Zolotarev approximation changes from x^{-1/4} (full)
// to x^{-1/2} (EO), and the heatbath approximation changes from
// x^{-3/8} (full) to x^{-3/4} (EO):
//   Full: Φ = A · r_{-3/8}(A†A) · ξ  →  S_PF = Φ_R^T (A†A)^{-1/4} Φ_R + ...
//   EO:   Φ_e = M_e · r_{-3/4}(M_e) · ξ_e / √2  →  S_PF = Φ_e^T M_e^{-1/2} Φ_e
//
// The h-field is always FULL LATTICE (n_sites × 16).  Only the CG vectors
// and pseudofermion fields live on the half-lattice (dim = 8 × n_even).
// Forces F_h are accumulated to the full h-field at ALL sites.
//
// Lean: hs_fermion_matrix_antisymmetric (bipartite → EO block-diagonal)
// Source: DeGrand & DeTar, "Lattice Methods for QCD" Ch. 8, Sec. 8.3
// ═══════════════════════════════════════════════════════════════════

// ─────────────────────────────────────────────────────────────────
// 1. multishift_cg_eo
//
// Solves (M_e + σ_k) ψ_{e,k} = φ_e on EVEN sites only.
// Identical ζ-recurrence as multishift_cg; calls apply_me_shifted
// instead of apply_shifted_ata.  Scratch for the odd-site temp
// vector is allocated internally (size 8 × n_odd).
// ─────────────────────────────────────────────────────────────────

/// Multi-shift CG on even sites: (M_e + σ_k) ψ_{e,k} = φ_e.
/// Half-lattice dimension: dim_e = 8 × eo.n_even.
fn multishift_cg_eo(
    h: &[f64],
    phi_e: &[f64],
    shifts: &[f64],
    tol: f64,
    max_iter: usize,
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_entries: &[CgEntry],
) -> CgResult {
    let dim_e = 8 * eo.n_even;
    let ns = shifts.len();

    if ns == 0 {
        return CgResult { solutions: vec![], n_iter: 0 };
    }

    // Sort shifts ascending; σ₀ (smallest) is the base system
    let mut order: Vec<usize> = (0..ns).collect();
    order.sort_by(|&a, &b| shifts[a].partial_cmp(&shifts[b]).unwrap());
    let sorted_shifts: Vec<f64> = order.iter().map(|&i| shifts[i]).collect();
    let sigma0 = sorted_shifts[0];

    // Per-shift state
    let mut x: Vec<Vec<f64>> = vec![vec![0.0; dim_e]; ns];
    let mut p: Vec<Vec<f64>> = vec![phi_e.to_vec(); ns];

    // Shared residual for base system
    let mut r = phi_e.to_vec();
    let b_norm_sq = dot(phi_e, phi_e);

    if b_norm_sq < 1e-30 {
        return CgResult { solutions: x, n_iter: 0 };
    }
    let tol_sq = tol * tol * b_norm_sq;
    let mut r_sq = b_norm_sq;

    // ζ recurrence state
    let mut zeta_cur = vec![1.0_f64; ns];
    let mut zeta_old = vec![1.0_f64; ns];
    let mut converged = vec![false; ns];

    let mut alpha = 0.0_f64;
    let mut alpha_old = 1.0_f64;
    let mut beta = 0.0_f64;
    let mut beta_old = 0.0_f64;

    // Scratch buffers — odd-site temp allocated here once
    let mut scratch_odd = vec![0.0_f64; 8 * eo.n_odd];
    let mut w = vec![0.0_f64; dim_e];  // (M_e + σ₀) @ p₀

    let mut n_iter = 0;
    while n_iter < max_iter {
        if converged.iter().all(|&c| c) { break; }

        // Single matvec: w = (M_e + σ₀) @ p₀
        apply_me_shifted(h, &p[0], &mut w, sigma0, fwd, bwd, eo, &mut scratch_odd, cg_entries);

        let pap = dot(&p[0], &w);
        if pap.abs() < 1e-30 { break; }
        alpha = r_sq / pap;

        let r_sq_old = r_sq;

        // Update base residual
        axpy(-alpha, &w, &mut r);
        r_sq = dot(&r, &r);

        // Base system: update solution and search direction
        axpy(alpha, &p[0], &mut x[0]);
        beta = r_sq / r_sq_old.max(1e-30);

        for i in 0..dim_e {
            p[0][i] = r[i] + beta * p[0][i];
        }

        if r_sq < tol_sq { converged[0] = true; }

        // Shifted systems via ζ recurrence
        for k in 1..ns {
            if converged[k] { continue; }

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

            axpy(alpha_k, &p[k], &mut x[k]);

            for i in 0..dim_e {
                p[k][i] = zeta_new * r[i] + beta_k * p[k][i];
            }

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

    // Unsort: return in original shift order
    let mut result = vec![vec![0.0; dim_e]; ns];
    for (sorted_idx, &orig_idx) in order.iter().enumerate() {
        std::mem::swap(&mut result[orig_idx], &mut x[sorted_idx]);
    }

    CgResult { solutions: result, n_iter }
}

// ─────────────────────────────────────────────────────────────────
// 1b. deflated_multishift_cg_eo
//
// Wraps multishift_cg_eo with low-mode deflation.
//
// Given K eigenpairs (λ_j, v_j) of M_e:
//   1. Project: c_j = v_j^T · b
//   2. Exact low-mode: x_low_k = Σ_j c_j/(λ_j + σ_k) · v_j
//   3. Deflated residual: r₀ = b - Σ_j c_j · v_j
//   4. Standard multi-shift CG on r₀ (κ_eff = λ_max/(λ_{K+1}))
//   5. Combine: x_k = x_low_k + x_perp_k
//
// The CG inner loop is UNCHANGED. Only pre/post-processing added.
// Source: Bloch et al., arXiv:0910.2927
// ─────────────────────────────────────────────────────────────────

/// Deflated multi-shift CG on even sites.
///
/// If deflation data is None or empty, falls back to plain multishift_cg_eo.
fn deflated_multishift_cg_eo(
    h: &[f64],
    phi_e: &[f64],
    shifts: &[f64],
    tol: f64,
    max_iter: usize,
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_entries: &[CgEntry],
    defl: Option<&DeflationData>,
) -> CgResult {
    let ns = shifts.len();
    let dim_e = 8 * eo.n_even;

    // No deflation data → fall back to plain CG
    let defl = match defl {
        Some(d) if d.k > 0 => d,
        _ => return multishift_cg_eo(h, phi_e, shifts, tol, max_iter, fwd, bwd, eo, cg_entries),
    };

    // Step 1: Project b onto low-mode subspace
    // c_j = v_j^T · b
    let projections: Vec<f64> = defl.evecs.iter()
        .map(|v| dot(v, phi_e))
        .collect();

    // Step 2: Exact low-mode solution for each shift
    // x_low_k = Σ_j c_j / (λ_j + σ_k) · v_j
    let mut x_low: Vec<Vec<f64>> = vec![vec![0.0; dim_e]; ns];
    for k in 0..ns {
        for j in 0..defl.k {
            let coeff = projections[j] / (defl.evals[j] + shifts[k]);
            axpy(coeff, &defl.evecs[j], &mut x_low[k]);
        }
    }

    // Step 3: Deflated residual (shift-independent)
    // r₀ = b - Σ_j c_j · v_j = b - P·b where P projects onto low modes
    let mut r0 = phi_e.to_vec();
    for j in 0..defl.k {
        axpy(-projections[j], &defl.evecs[j], &mut r0);
    }

    // Step 4: Standard multi-shift CG on deflated residual
    // Now κ_eff ≈ λ_max / λ_{K+1} instead of λ_max / λ_min
    let cg_result = multishift_cg_eo(h, &r0, shifts, tol, max_iter, fwd, bwd, eo, cg_entries);

    // Step 5: Combine x_k = x_low_k + x_perp_k
    let mut solutions = Vec::with_capacity(ns);
    for k in 0..ns {
        let mut x_k = x_low[k].clone();
        for i in 0..dim_e {
            x_k[i] += cg_result.solutions[k][i];
        }
        solutions.push(x_k);
    }

    CgResult { solutions, n_iter: cg_result.n_iter }
}

// ─────────────────────────────────────────────────────────────────
// 2. compute_spf_eo
//
// Pseudofermion action for one real even-site field:
//   S_PF = α₀ φ_e·φ_e + Σ_k α_k φ_e·ψ_{e,k}
// where (M_e + β_k) ψ_{e,k} = φ_e.
// Approximates φ_e^T M_e^{-1/2} φ_e (Zolotarev x^{-1/2}).
// ─────────────────────────────────────────────────────────────────

/// Pseudofermion action on even sites: φ_e^T r(M_e) φ_e ≈ φ_e^T M_e^{-1/2} φ_e.
fn compute_spf_eo(
    h: &[f64], phi_e: &[f64],
    alpha_0: f64, zolotarev_alphas: &[f64], zolotarev_betas: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry],
) -> f64 {
    let cg_result = multishift_cg_eo(h, phi_e, zolotarev_betas, cg_tol, cg_max_iter,
                                     fwd, bwd, eo, cg_entries);
    let mut s = alpha_0 * dot(phi_e, phi_e);
    for k in 0..zolotarev_betas.len() {
        s += zolotarev_alphas[k] * dot(phi_e, &cg_result.solutions[k]);
    }
    s
}

// ─────────────────────────────────────────────────────────────────
// 3. compute_pf_force_eo
//
// PF force from one even-site field onto the FULL h-field.
//
// After solving (M_e + β_k) ψ_{e,k} = φ_e, the force on bond
// (e, fwd[e][μ]) involves both ψ_{e,k} (even side) and the
// scatter w_{o,k} = A_eo^T ψ_{e,k} (odd side).
//
// Force contraction at even-odd bond (e even, nb odd, direction μ):
//   ΔF[e, μ, a]     += Σ_k α_k (-2) Σ_{I,J} CG[a]_{IJ}
//                       × (ψ_e[I] × w_o[nb,J] − w_o[nb,I] × ψ_e[J])
//   ΔF[nb_bwd,μ,a]  — contribution from the same bond seen from the
//                       backward odd site acting as bond source.
//
// Both even-site h[e,μ,a] (from forward bonds) and odd-site
// h[nb_bwd,μ,a] (from backward bonds seen at even site e) receive
// contributions, covering the entire h-field.
// ─────────────────────────────────────────────────────────────────

/// PF force from one even-site field, accumulated onto full h-field f_h.
fn compute_pf_force_eo(
    h: &[f64],
    phi_e: &[f64],
    zolotarev_alphas: &[f64],
    zolotarev_betas: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_tol: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
    f_h: &mut [f64],
) {
    let n_poles = zolotarev_betas.len();

    let cg_result = multishift_cg_eo(h, phi_e, zolotarev_betas, cg_tol, cg_max_iter,
                                     fwd, bwd, eo, cg_entries);

    // w_{o,k} = A_eo^T ψ_{e,k}  (scatter even→odd, one per pole)
    let mut w_odd: Vec<Vec<f64>> = Vec::with_capacity(n_poles);
    {
        let mut scratch_odd = vec![0.0_f64; 8 * eo.n_odd];
        for k in 0..n_poles {
            let mut wo = vec![0.0_f64; 8 * eo.n_odd];
            apply_aeot(h, &cg_result.solutions[k], &mut wo, fwd, bwd, eo, cg_entries);
            w_odd.push(wo);
            let _ = &mut scratch_odd; // keep alive
        }
    }

    // Loop over even sites, contribute to bonds in all 4 directions.
    // For each even site e and direction μ:
    //   • Forward bond: h[e, μ, a]  → force from pair (ψ_e[e], w_o[fwd[e][μ]])
    //   • Backward bond: h[nb_bwd, μ, a] where nb_bwd = bwd[e][μ]
    //     → force from pair (ψ_e[e], w_o[nb_bwd])
    //     BUT note: in apply_aeo the backward gather uses h at nb_bwd with
    //     transposed/negated indices.  The force must be the exact derivative
    //     of the action with respect to h at that bond.
    //
    // Derivation matches apply_aeo exactly:
    //   Forward contribution  to (A_eo v)_e[I]:  + CG[a]_{IJ} h[e,μ,a] v_o[nb_fwd,J]
    //   Backward contribution to (A_eo v)_e[J]:  - CG[a]_{IJ} h[nb_bwd,μ,a] v_o[nb_bwd,I]
    //
    // The PF action S = Σ_k α_k φ_e^T ψ_{e,k} involves ψ = M_e^{-1}(M_e+β) ψ
    // and dS/dh appears via d(A_eo A_eo^T)/dh.  Using the product rule:
    //   dS/dh[e,μ,a] = Σ_k α_k (-2) × (contraction of ψ_{e,k} and A_eo^T ψ_{e,k})
    //
    // The (-2) factor comes from d/dh[h_{IJ} x_I y_J - h_{IJ} y_I x_J] = 2(x_I y_J - y_I x_J).

    for &e in &eo.even_sites {
        let e_compact = eo.compact_idx[e];
        for mu in 0..4usize {
            // ── Forward bond: h at even site e, direction mu ──
            let nb_fwd = fwd[e][mu];
            let nb_fwd_compact = eo.compact_idx[nb_fwd];
            for a in 0..4usize {
                let mut fval: f64 = 0.0;
                for k in 0..n_poles {
                    let psi = &cg_result.solutions[k];
                    let wo  = &w_odd[k];
                    let mut c: f64 = 0.0;
                    for entry in cg_entries {
                        if entry.a != a { continue; }
                        let psi_i = psi[8 * e_compact + entry.i];
                        let wo_j  = wo[8 * nb_fwd_compact + entry.j];
                        // Forward: d(A_eo)_{(e,I),(nb,J)}/dh[e,mu,a] = CG_{IJ} = entry.val
                        // psi^T (dA_eo/dh) w = Σ entry.val * psi_I * w_J
                        c += entry.val * psi_i * wo_j;
                    }
                    // F = -dS/dh = +Σ_k α_k · ψ^T(dM_e/dh)ψ = +Σ_k α_k · 2 · ψ^T(dA_eo/dh)w
                    // Verified numerically: matches finite-difference to 1e-7.
                    fval += zolotarev_alphas[k] * 2.0 * c;
                }
                f_h[e * 16 + mu * 4 + a] += fval;
            }

            // ── Backward bond: h at odd site nb_bwd, direction mu ──
            // In apply_aeo the backward gather is:
            //   out_e[e_compact, J] -= CG[a]_{IJ} h[nb_bwd,μ,a] v_o[nb_bwd_compact, I]
            // So d(S)/d(h[nb_bwd,μ,a]) has the opposite contraction pattern:
            //   ΔF = Σ_k α_k (-2) × Σ_{I,J} entry.val × (-1)
            //        × (ψ_e[e,J] × wo[nb_bwd,I] − wo[nb_bwd,J] × ψ_e[e,I])
            // The extra minus from the minus sign in apply_aeo backward gather:
            //   net sign: (-2) × (-1) = +2, and the (x·y - y·x) reverses → same form.
            let nb_bwd = bwd[e][mu];
            let nb_bwd_compact = eo.compact_idx[nb_bwd];
            for a in 0..4usize {
                let mut fval: f64 = 0.0;
                for k in 0..n_poles {
                    let psi = &cg_result.solutions[k];
                    let wo  = &w_odd[k];
                    let mut c: f64 = 0.0;
                    for entry in cg_entries {
                        if entry.a != a { continue; }
                        // Backward: d(A_eo)_{(e,J),(nb_bwd,I)}/dh[nb_bwd,mu,a] = -CG_{IJ}
                        // psi^T(dA_eo/dh)w = Σ (-entry.val) * psi_{e,J} * w_{nb_bwd,I}
                        let psi_j = psi[8 * e_compact + entry.j];
                        let wo_i  = wo[8 * nb_bwd_compact + entry.i];
                        c -= entry.val * psi_j * wo_i;
                    }
                    // F = +Σ_k α_k · 2 · ψ^T(dA_eo/dh)w (same sign as forward)
                    // Verified numerically: matches finite-difference to 1e-7.
                    fval += zolotarev_alphas[k] * 2.0 * c;
                }
                f_h[nb_bwd * 16 + mu * 4 + a] += fval;
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────
// 4. compute_forces_eo
//
// Full force on h: Gaussian prior + PF forces from both complex
// components (real and imaginary even-site pseudofermion fields).
// ─────────────────────────────────────────────────────────────────

/// Full force on h-field (all sites): Gaussian prior + 2 EO PF forces.
fn compute_forces_eo(
    h: &[f64],
    g: f64,
    phi_r_e: &[f64],
    phi_i_e: &[f64],
    zolotarev_alphas: &[f64],
    zolotarev_betas: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    cg_tol: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
) -> Vec<f64> {
    let mut f_h = vec![0.0; n_sites * 16];

    // Gaussian prior: F = -h / (2g)
    for i in 0..n_sites * 16 {
        f_h[i] = -h[i] / (2.0 * g);
    }

    // PF force from Φ_R (real component on even sites)
    compute_pf_force_eo(h, phi_r_e, zolotarev_alphas, zolotarev_betas,
                        fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);
    // PF force from Φ_I (imaginary component on even sites)
    compute_pf_force_eo(h, phi_i_e, zolotarev_alphas, zolotarev_betas,
                        fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);

    f_h
}

// ─────────────────────────────────────────────────────────────────
// 5. compute_hamiltonian_eo
//
// H = K + S_aux + S_PF
// K = 0.5 Σ π_h²  (full h-field momenta)
// S_aux = Σ h² / (4g)  (full h-field)
// S_PF = S_PF_R + S_PF_I using compute_spf_eo on even sites
// ─────────────────────────────────────────────────────────────────

fn compute_hamiltonian_eo(
    h: &[f64], pi_h: &[f64], g: f64,
    phi_r_e: &[f64], phi_i_e: &[f64],
    alpha_0: f64, zolotarev_alphas: &[f64], zolotarev_betas: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry],
) -> f64 {
    let k_energy: f64 = 0.5 * dot(pi_h, pi_h);
    let s_aux: f64 = dot(h, h) / (4.0 * g);
    // Complex pseudofermion on even sites
    let s_pf = compute_spf_eo(h, phi_r_e, alpha_0, zolotarev_alphas, zolotarev_betas,
                               fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries)
             + compute_spf_eo(h, phi_i_e, alpha_0, zolotarev_alphas, zolotarev_betas,
                               fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries);
    k_energy + s_aux + s_pf
}

// ─────────────────────────────────────────────────────────────────
// 6. pseudofermion_heatbath_eo
//
// Generate Φ_e = M_e^{1/4} ξ_e / √2 via the A-trick on even sites.
//
// Physics: det(M_e)^{1/2} with pseudofermion action S_PF = Φ_e^T M_e^{-1/2} Φ_e.
// Correct distribution requires Φ_e ~ M_e^{1/4} Gaussian.
//
// Heatbath construction (A-trick adapted for M_e):
//   1. ξ_e ~ N(0, 1) on even sites
//   2. η_e = r_{-3/4}(M_e) ξ_e via multishift_cg_eo with heatbath shifts
//      (η = α₀_hb ξ + Σ_k α_k_hb ψ_{e,k})
//   3. Φ_e = M_e · η_e = A_eo (A_eo^T η_e)  (one M_e application)
//   4. Divide by √2 (complex Gaussian normalization)
//
// Verification in eigenspace with eigenvalue λ of M_e:
//   η → λ^{-3/4} ξ  (from step 2)
//   Φ → λ · λ^{-3/4} ξ = λ^{1/4} ξ  (from step 3)
//   Covariance: λ^{1/2} / 2 (after /√2 for each of R,I)
//   → S_PF = Φ_e^T (2 M_e^{-1/2}) Φ_e / 2 = Φ_e^T M_e^{-1/2} Φ_e ✓
//
// Lean: hs_gaussian_identity_zero (HubbardStratonovichRHMC.lean)
// Source: Schaich & DeGrand, CPC 190:200 (2015), Eqs. 16-17 (adapted for EO)
// ─────────────────────────────────────────────────────────────────

/// Generate complex EO pseudofermion (Φ_R_e, Φ_I_e) on even sites only.
fn pseudofermion_heatbath_eo(
    h: &[f64], rng: &mut ChaCha20Rng,
    alpha_0_hb: f64, alphas_hb: &[f64], betas_hb: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry],
) -> (Vec<f64>, Vec<f64>) {
    let dim_e = 8 * eo.n_even;

    // Step 1: ξ ~ N(0,1) on even sites only
    let xi_r: Vec<f64> = (0..dim_e).map(|_| rand_normal(rng)).collect();
    let xi_i: Vec<f64> = (0..dim_e).map(|_| rand_normal(rng)).collect();

    // Step 2: η = r_{-3/4}(M_e) ξ via multi-shift CG on even sites
    let cg_r = multishift_cg_eo(h, &xi_r, betas_hb, cg_tol, cg_max_iter,
                                 fwd, bwd, eo, cg_entries);
    let cg_i = multishift_cg_eo(h, &xi_i, betas_hb, cg_tol, cg_max_iter,
                                 fwd, bwd, eo, cg_entries);

    // η = α₀ ξ + Σ_k α_k ψ_{e,k}
    let mut eta_r = vec![0.0; dim_e];
    let mut eta_i = vec![0.0; dim_e];
    for i in 0..dim_e {
        eta_r[i] = alpha_0_hb * xi_r[i];
        eta_i[i] = alpha_0_hb * xi_i[i];
    }
    for k in 0..betas_hb.len() {
        axpy(alphas_hb[k], &cg_r.solutions[k], &mut eta_r);
        axpy(alphas_hb[k], &cg_i.solutions[k], &mut eta_i);
    }

    // Step 3: Φ_e = M_e η = A_eo (A_eo^T η) — two half-hops
    let mut scratch_odd = vec![0.0_f64; 8 * eo.n_odd];
    let mut phi_r_e = vec![0.0; dim_e];
    let mut phi_i_e = vec![0.0; dim_e];

    // M_e η_r
    apply_aeot(h, &eta_r, &mut scratch_odd, fwd, bwd, eo, cg_entries);
    apply_aeo(h, &scratch_odd, &mut phi_r_e, fwd, bwd, eo, cg_entries);

    // M_e η_i (reuse scratch_odd)
    apply_aeot(h, &eta_i, &mut scratch_odd, fwd, bwd, eo, cg_entries);
    apply_aeo(h, &scratch_odd, &mut phi_i_e, fwd, bwd, eo, cg_entries);

    // Step 4: divide by √2 for complex Gaussian normalization
    let inv_sqrt2 = 1.0 / f64::sqrt(2.0);
    for i in 0..dim_e { phi_r_e[i] *= inv_sqrt2; }
    for i in 0..dim_e { phi_i_e[i] *= inv_sqrt2; }

    (phi_r_e, phi_i_e)
}

// ─────────────────────────────────────────────────────────────────
// 7. rhmc_trajectory_eo
//
// Same Omelyan 2MN structure as rhmc_trajectory; uses EO functions
// throughout.  The h-field is full-lattice; pseudofermions live on
// even sites only.  Observables measured on full lattice via the
// existing measure_observables function.
// ─────────────────────────────────────────────────────────────────

fn rhmc_trajectory_eo(
    h: &mut Vec<f64>,
    g: f64,
    tau: f64,
    n_md_steps: usize,
    alpha_0: f64, alphas: &[f64], betas: &[f64],
    alpha_0_hb: f64, alphas_hb: &[f64], betas_hb: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    rng: &mut ChaCha20Rng,
    cg_entries: &[CgEntry],
    cg_tol_md: f64,
    cg_tol_mc: f64,
) -> TrajectoryResult {
    let n_h = n_sites * 16;
    let eps = tau / n_md_steps as f64;
    let lam = 0.1932; // Omelyan 2MN parameter
    let cg_max_iter = 2000;

    // Heat bath: complex Φ_e = (Φ_R_e, Φ_I_e) on even sites
    let (phi_r_e, phi_i_e) = pseudofermion_heatbath_eo(
        h, rng, alpha_0_hb, alphas_hb, betas_hb,
        fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries,
    );

    // Refresh momenta: π ~ N(0, 1) (full h-field momenta)
    let mut pi_h: Vec<f64> = (0..n_h).map(|_| rand_normal(rng)).collect();

    // Store old state
    let h_old = h.clone();

    // H_old (tight tolerance for Metropolis)
    let h_old_val = compute_hamiltonian_eo(
        h, &pi_h, g, &phi_r_e, &phi_i_e,
        alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries,
    );

    // ── FSAL Omelyan 2MN MD ──
    // Initial force
    let mut f_h = compute_forces_eo(
        h, g, &phi_r_e, &phi_i_e, alphas, betas,
        fwd, bwd, n_sites, eo, cg_tol_md, cg_max_iter, cg_entries,
    );

    for _step in 0..n_md_steps {
        // λε kick
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
        // ε/2 drift
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }

        // Middle force
        f_h = compute_forces_eo(
            h, g, &phi_r_e, &phi_i_e, alphas, betas,
            fwd, bwd, n_sites, eo, cg_tol_md, cg_max_iter, cg_entries,
        );

        // (1-2λ)ε kick
        for i in 0..n_h { pi_h[i] += (1.0 - 2.0 * lam) * eps * f_h[i]; }
        // ε/2 drift
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }

        // Final force (= initial force of next step via FSAL)
        f_h = compute_forces_eo(
            h, g, &phi_r_e, &phi_i_e, alphas, betas,
            fwd, bwd, n_sites, eo, cg_tol_md, cg_max_iter, cg_entries,
        );

        // λε kick
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
    }

    // H_new (tight tolerance)
    let h_new_val = compute_hamiltonian_eo(
        h, &pi_h, g, &phi_r_e, &phi_i_e,
        alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries,
    );

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

    // Observables on full lattice (unchanged function)
    let (h_sq, tet_m2, tr_q2) = measure_observables(h, n_sites);

    TrajectoryResult { delta_h, accepted, h_sq, tet_m2, tr_q2 }
}

// ═══════════════════════════════════════════════════════════════════
// Clark-Kennedy 2-pseudofermion even-odd RHMC
//
// Physics: det(M_e)^{1/2} = [det(M_e)^{1/4}]^2  (exact identity)
//
// Uses TWO independent complex pseudofermion fields on M_e, each
// with x^{-1/4} Zolotarev action. Each field contributes det(M_e)^{1/4};
// the product gives det(M_e)^{1/2} = Pf(A), the correct Pfaffian weight.
//
// This resolves the x^{-1/2} numerical pathology: the |ΔH|≈2.35
// step-size-independent floor caused by CG residual amplification
// in the x^{-1/2} rational approximation at κ≈6000. The x^{-1/4}
// power is well-behaved (tested at |ΔH|<1 for 12 poles).
//
// Cost: 2× the CG inversions per MD step (4 PF fields vs 2), but
// reduced force variance allows ~2× larger step size, yielding
// comparable net efficiency. The half-lattice dimension (dim_e = 4V
// vs 8V) provides an additional ~2× per-inversion speedup.
//
// Reference: Clark & Kennedy, PRL 98:051601 (2007) [hep-lat/0608015]
// Lean: clark_kennedy_det_splitting (HubbardStratonovichRHMC.lean)
// ═══════════════════════════════════════════════════════════════════

/// Full force on h-field: Gaussian prior + forces from 2 complex PFs
/// (4 real PF fields total), each with x^{-1/4} Zolotarev.
fn compute_forces_eo_2pf(
    h: &[f64],
    g: f64,
    phi1_r_e: &[f64], phi1_i_e: &[f64],
    phi2_r_e: &[f64], phi2_i_e: &[f64],
    zolotarev_alphas: &[f64],
    zolotarev_betas: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    cg_tol: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
) -> Vec<f64> {
    let mut f_h = vec![0.0; n_sites * 16];

    // Gaussian prior: F = -h / (2g)
    for i in 0..n_sites * 16 {
        f_h[i] = -h[i] / (2.0 * g);
    }

    // PF forces from field 1 (real + imaginary)
    compute_pf_force_eo(h, phi1_r_e, zolotarev_alphas, zolotarev_betas,
                        fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);
    compute_pf_force_eo(h, phi1_i_e, zolotarev_alphas, zolotarev_betas,
                        fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);

    // PF forces from field 2 (real + imaginary)
    compute_pf_force_eo(h, phi2_r_e, zolotarev_alphas, zolotarev_betas,
                        fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);
    compute_pf_force_eo(h, phi2_i_e, zolotarev_alphas, zolotarev_betas,
                        fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);

    f_h
}

/// Hamiltonian with 2 complex PFs: H = K + S_aux + S_PF1 + S_PF2.
fn compute_hamiltonian_eo_2pf(
    h: &[f64], pi_h: &[f64], g: f64,
    phi1_r_e: &[f64], phi1_i_e: &[f64],
    phi2_r_e: &[f64], phi2_i_e: &[f64],
    alpha_0: f64, zolotarev_alphas: &[f64], zolotarev_betas: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry],
) -> f64 {
    let k_energy: f64 = 0.5 * dot(pi_h, pi_h);
    let s_aux: f64 = dot(h, h) / (4.0 * g);

    // PF action from field 1
    let s_pf1 = compute_spf_eo(h, phi1_r_e, alpha_0, zolotarev_alphas, zolotarev_betas,
                                fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries)
              + compute_spf_eo(h, phi1_i_e, alpha_0, zolotarev_alphas, zolotarev_betas,
                                fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries);

    // PF action from field 2
    let s_pf2 = compute_spf_eo(h, phi2_r_e, alpha_0, zolotarev_alphas, zolotarev_betas,
                                fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries)
              + compute_spf_eo(h, phi2_i_e, alpha_0, zolotarev_alphas, zolotarev_betas,
                                fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries);

    k_energy + s_aux + s_pf1 + s_pf2
}

/// Clark-Kennedy 2-PF even-odd RHMC trajectory.
///
/// Identical Omelyan 2MN integration as rhmc_trajectory_eo, but with
/// TWO independent complex pseudofermion fields, each contributing
/// det(M_e)^{1/4}. The product gives det(M_e)^{1/2} = Pf(A).
///
/// Zolotarev powers (passed from Python):
///   action:   x^{-1/4} (same as full-lattice — well-behaved at κ≈6000)
///   heatbath: x^{-7/8} (generates M_e^{1/8} distribution for x^{-1/4} action)
fn rhmc_trajectory_eo_2pf(
    h: &mut Vec<f64>,
    g: f64,
    tau: f64,
    n_md_steps: usize,
    alpha_0: f64, alphas: &[f64], betas: &[f64],
    alpha_0_hb: f64, alphas_hb: &[f64], betas_hb: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    rng: &mut ChaCha20Rng,
    cg_entries: &[CgEntry],
    cg_tol_md: f64,
    cg_tol_mc: f64,
) -> TrajectoryResult {
    let n_h = n_sites * 16;
    let eps = tau / n_md_steps as f64;
    let lam = 0.1932; // Omelyan 2MN parameter
    let cg_max_iter = 2000;

    // Heat bath: TWO independent complex PFs on even sites
    let (phi1_r_e, phi1_i_e) = pseudofermion_heatbath_eo(
        h, rng, alpha_0_hb, alphas_hb, betas_hb,
        fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries,
    );
    let (phi2_r_e, phi2_i_e) = pseudofermion_heatbath_eo(
        h, rng, alpha_0_hb, alphas_hb, betas_hb,
        fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries,
    );

    // Refresh momenta
    let mut pi_h: Vec<f64> = (0..n_h).map(|_| rand_normal(rng)).collect();

    // Store old state
    let h_old = h.clone();

    // H_old (tight tolerance for Metropolis)
    let h_old_val = compute_hamiltonian_eo_2pf(
        h, &pi_h, g,
        &phi1_r_e, &phi1_i_e, &phi2_r_e, &phi2_i_e,
        alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries,
    );

    // ── FSAL Omelyan 2MN MD ──
    let mut f_h = compute_forces_eo_2pf(
        h, g, &phi1_r_e, &phi1_i_e, &phi2_r_e, &phi2_i_e,
        alphas, betas, fwd, bwd, n_sites, eo, cg_tol_md, cg_max_iter, cg_entries,
    );

    for _step in 0..n_md_steps {
        // λε kick
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
        // ε/2 drift
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }

        // Middle force
        f_h = compute_forces_eo_2pf(
            h, g, &phi1_r_e, &phi1_i_e, &phi2_r_e, &phi2_i_e,
            alphas, betas, fwd, bwd, n_sites, eo, cg_tol_md, cg_max_iter, cg_entries,
        );

        // (1-2λ)ε kick
        for i in 0..n_h { pi_h[i] += (1.0 - 2.0 * lam) * eps * f_h[i]; }
        // ε/2 drift
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }

        // Final force (= initial force of next step via FSAL)
        f_h = compute_forces_eo_2pf(
            h, g, &phi1_r_e, &phi1_i_e, &phi2_r_e, &phi2_i_e,
            alphas, betas, fwd, bwd, n_sites, eo, cg_tol_md, cg_max_iter, cg_entries,
        );

        // λε kick
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
    }

    // H_new (tight tolerance)
    let h_new_val = compute_hamiltonian_eo_2pf(
        h, &pi_h, g,
        &phi1_r_e, &phi1_i_e, &phi2_r_e, &phi2_i_e,
        alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries,
    );

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

    let (h_sq, tet_m2, tr_q2) = measure_observables(h, n_sites);

    TrajectoryResult { delta_h, accepted, h_sq, tet_m2, tr_q2 }
}

// ═══════════════════════════════════════════════════════════════════
// Deflated Clark-Kennedy 2-PF even-odd RHMC
//
// Combines CK 2-PF (correct Pfaffian) with low-mode deflation
// (12-15× CG speedup). Computes K=30 eigenpairs of M_e at trajectory
// start, uses deflated multi-shift CG for all solves.
//
// Expected: ~100 CG iters (vs ~1200), half-dimension → 25× total.
// ═══════════════════════════════════════════════════════════════════

/// Deflated PF action: uses deflated_multishift_cg_eo.
fn compute_spf_eo_defl(
    h: &[f64], phi_e: &[f64],
    alpha_0: f64, zolotarev_alphas: &[f64], zolotarev_betas: &[f64],
    fwd: &[[usize; 4]], bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_tol: f64, cg_max_iter: usize,
    cg_entries: &[CgEntry],
    defl: Option<&DeflationData>,
) -> f64 {
    let cg_result = deflated_multishift_cg_eo(h, phi_e, zolotarev_betas, cg_tol, cg_max_iter,
                                               fwd, bwd, eo, cg_entries, defl);
    let mut s = alpha_0 * dot(phi_e, phi_e);
    for k in 0..zolotarev_betas.len() {
        s += zolotarev_alphas[k] * dot(phi_e, &cg_result.solutions[k]);
    }
    s
}

/// Deflated PF force: uses deflated_multishift_cg_eo.
fn compute_pf_force_eo_defl(
    h: &[f64],
    phi_e: &[f64],
    zolotarev_alphas: &[f64],
    zolotarev_betas: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    eo: &EvenOddTables,
    cg_tol: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
    f_h: &mut [f64],
    defl: Option<&DeflationData>,
) {
    let n_poles = zolotarev_betas.len();
    let cg_result = deflated_multishift_cg_eo(h, phi_e, zolotarev_betas, cg_tol, cg_max_iter,
                                               fwd, bwd, eo, cg_entries, defl);
    // w_{o,k} = A_eo^T ψ_{e,k}
    let mut w_odd: Vec<Vec<f64>> = Vec::with_capacity(n_poles);
    for k in 0..n_poles {
        let mut wo = vec![0.0_f64; 8 * eo.n_odd];
        apply_aeot(h, &cg_result.solutions[k], &mut wo, fwd, bwd, eo, cg_entries);
        w_odd.push(wo);
    }
    // Force contraction — identical to compute_pf_force_eo
    for &e in &eo.even_sites {
        let e_compact = eo.compact_idx[e];
        for mu in 0..4usize {
            let nb_fwd = fwd[e][mu];
            let nb_fwd_compact = eo.compact_idx[nb_fwd];
            for a in 0..4usize {
                let mut fval: f64 = 0.0;
                for k in 0..n_poles {
                    let psi = &cg_result.solutions[k];
                    let wo  = &w_odd[k];
                    let mut c: f64 = 0.0;
                    for entry in cg_entries {
                        if entry.a != a { continue; }
                        c += entry.val * psi[8 * e_compact + entry.i] * wo[8 * nb_fwd_compact + entry.j];
                    }
                    fval += zolotarev_alphas[k] * 2.0 * c;
                }
                f_h[e * 16 + mu * 4 + a] += fval;
            }
            let nb_bwd = bwd[e][mu];
            let nb_bwd_compact = eo.compact_idx[nb_bwd];
            for a in 0..4usize {
                let mut fval: f64 = 0.0;
                for k in 0..n_poles {
                    let psi = &cg_result.solutions[k];
                    let wo  = &w_odd[k];
                    let mut c: f64 = 0.0;
                    for entry in cg_entries {
                        if entry.a != a { continue; }
                        c -= entry.val * psi[8 * e_compact + entry.j] * wo[8 * nb_bwd_compact + entry.i];
                    }
                    fval += zolotarev_alphas[k] * 2.0 * c;
                }
                f_h[nb_bwd * 16 + mu * 4 + a] += fval;
            }
        }
    }
}

/// Deflated CK 2-PF trajectory.
///
/// ext_defl: if provided, uses these eigenvectors instead of computing via Lanczos.
fn rhmc_trajectory_eo_2pf_defl(
    h: &mut Vec<f64>,
    g: f64,
    tau: f64,
    n_md_steps: usize,
    alpha_0: f64, alphas: &[f64], betas: &[f64],
    alpha_0_hb: f64, alphas_hb: &[f64], betas_hb: &[f64],
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    rng: &mut ChaCha20Rng,
    cg_entries: &[CgEntry],
    cg_tol_md: f64,
    cg_tol_mc: f64,
    n_defl: usize,
    prev_evecs: Option<&[Vec<f64>]>,
    ext_defl: Option<&DeflationData>,
) -> (TrajectoryResult, DeflationData) {
    let n_h = n_sites * 16;
    let eps = tau / n_md_steps as f64;
    let lam = 0.1932;
    let cg_max_iter = 2000;

    // Use external deflation data if provided, else compute via Lanczos
    let defl = if let Some(ext) = ext_defl {
        DeflationData {
            k: ext.k,
            evecs: ext.evecs.clone(),
            evals: ext.evals.clone(),
        }
    } else if n_defl > 0 {
        lanczos_smallest_eigenpairs_eo(
            h, n_defl, 2 * n_defl, 1e-8, 10,
            fwd, bwd, eo, cg_entries, prev_evecs, rng,
        )
    } else {
        DeflationData { k: 0, evecs: vec![], evals: vec![] }
    };
    let defl_ref = if defl.k > 0 { Some(&defl) } else { None };

    // Heat bath: 2 complex PFs (heatbath doesn't benefit much from deflation
    // since it runs once — use plain CG for simplicity)
    let (phi1_r_e, phi1_i_e) = pseudofermion_heatbath_eo(
        h, rng, alpha_0_hb, alphas_hb, betas_hb,
        fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries,
    );
    let (phi2_r_e, phi2_i_e) = pseudofermion_heatbath_eo(
        h, rng, alpha_0_hb, alphas_hb, betas_hb,
        fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries,
    );

    let mut pi_h: Vec<f64> = (0..n_h).map(|_| rand_normal(rng)).collect();
    let h_old = h.clone();

    // H_old with deflated CG (eigenvectors are exact for current h)
    let h_old_val = {
        let k = 0.5 * dot(&pi_h, &pi_h);
        let s_aux = dot(h, h) / (4.0 * g);
        let s_pf =
            compute_spf_eo_defl(h, &phi1_r_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries, defl_ref)
          + compute_spf_eo_defl(h, &phi1_i_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries, defl_ref)
          + compute_spf_eo_defl(h, &phi2_r_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries, defl_ref)
          + compute_spf_eo_defl(h, &phi2_i_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries, defl_ref);
        k + s_aux + s_pf
    };

    // NOTE: Forces use standard (non-deflated) CG below — see comment at compute_forces.

    // Force helper — NON-DEFLATED. Deflation vectors become stale during MD
    // (h changes every step), causing catastrophic force-Hamiltonian mismatch.
    // Standard CG for forces; deflation only for Hamiltonian evaluations where
    // h matches the eigenvector computation.
    let compute_forces = |h: &[f64]| -> Vec<f64> {
        let mut f_h = vec![0.0; n_sites * 16];
        for i in 0..n_sites * 16 { f_h[i] = -h[i] / (2.0 * g); }
        compute_pf_force_eo(h, &phi1_r_e, alphas, betas, fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries, &mut f_h);
        compute_pf_force_eo(h, &phi1_i_e, alphas, betas, fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries, &mut f_h);
        compute_pf_force_eo(h, &phi2_r_e, alphas, betas, fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries, &mut f_h);
        compute_pf_force_eo(h, &phi2_i_e, alphas, betas, fwd, bwd, eo, cg_tol_md, cg_max_iter, cg_entries, &mut f_h);
        f_h
    };

    // FSAL Omelyan 2MN MD
    let mut f_h = compute_forces(h);

    for _step in 0..n_md_steps {
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }
        f_h = compute_forces(h);
        for i in 0..n_h { pi_h[i] += (1.0 - 2.0 * lam) * eps * f_h[i]; }
        for i in 0..n_h { h[i] += (eps / 2.0) * pi_h[i]; }
        f_h = compute_forces(h);
        for i in 0..n_h { pi_h[i] += lam * eps * f_h[i]; }
    }

    // H_new: standard (non-deflated) CG. The h-field changed during MD,
    // making the initial eigenvectors stale. Rust Lanczos needs fixing
    // before it can recompute for h_new. For now, non-deflated is correct.
    // TODO: fix Rust Lanczos eigenvector extraction, then recompute here.
    let h_new_val = {
        let k = 0.5 * dot(&pi_h, &pi_h);
        let s_aux = dot(h, h) / (4.0 * g);
        let s_pf =
            compute_spf_eo(h, &phi1_r_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries)
          + compute_spf_eo(h, &phi1_i_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries)
          + compute_spf_eo(h, &phi2_r_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries)
          + compute_spf_eo(h, &phi2_i_e, alpha_0, alphas, betas, fwd, bwd, eo, cg_tol_mc, cg_max_iter, cg_entries);
        k + s_aux + s_pf
    };

    let delta_h = h_new_val - h_old_val;
    let accepted = if delta_h <= 0.0 { true } else { let u: f64 = rng.random(); u < (-delta_h).exp() };
    if !accepted { *h = h_old; }

    let (h_sq, tet_m2, tr_q2) = measure_observables(h, n_sites);
    (TrajectoryResult { delta_h, accepted, h_sq, tet_m2, tr_q2 }, defl)
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
            n_threads, 1e-6, 1e-12,
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

/// Even-odd RHMC: half-lattice CG with x^{-1/2} Zolotarev.
/// Physics: Pf(A) = det(M_e)^{1/2} where M_e = A_eo·A_eo^T on even sites.
/// Zolotarev powers: action x^{-1/2}, heatbath x^{-3/4} (passed from Python).
/// Same interface as run_rhmc_rust — drop-in replacement.
#[pyfunction]
fn run_rhmc_rust_eo<'py>(
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
    cg_a: PyReadonlyArray1<'py, i64>,
    cg_i: PyReadonlyArray1<'py, i64>,
    cg_j: PyReadonlyArray1<'py, i64>,
    cg_val: PyReadonlyArray1<'py, f64>,
    h_init: Option<PyReadonlyArray1<'py, f64>>,
) -> PyResult<PyObject> {
    let alphas = alphas.as_slice()?;
    let betas = betas.as_slice()?;
    let alphas_hb = alphas_hb.as_slice()?;
    let betas_hb = betas_hb.as_slice()?;
    let cg_entries = parse_cg_entries(cg_a.as_slice()?, cg_i.as_slice()?,
                                       cg_j.as_slice()?, cg_val.as_slice()?);

    let n_sites = l * l * l * l;
    let (fwd, bwd) = build_neighbors(l);
    let eo = build_even_odd(l);

    let mut rng = ChaCha20Rng::seed_from_u64(seed);

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
        if traj % 10 == 0 {
            py.check_signals()?;
        }

        let result = rhmc_trajectory_eo(
            &mut h, g, tau, n_md_steps,
            alpha_0, alphas, betas,
            alpha_0_hb, alphas_hb, betas_hb,
            &fwd, &bwd, n_sites, &eo,
            &mut rng, &cg_entries,
            1e-10, 1e-12,
        );

        delta_h_hist.push(result.delta_h);
        if result.accepted { n_accepted += 1; }

        if traj >= n_therm && (traj - n_therm) % n_meas_skip == 0 {
            h_sq_hist.push(result.h_sq);
            tet_m2_hist.push(result.tet_m2);
            tr_q2_hist.push(result.tr_q2);
        }
    }

    let dict = pyo3::types::PyDict::new(py);
    dict.set_item("h_sq_history", h_sq_hist)?;
    dict.set_item("delta_h_history", delta_h_hist)?;
    let n_meas = tet_m2_hist.len();
    dict.set_item("tet_m2_history", tet_m2_hist)?;
    dict.set_item("tr_q2_history", tr_q2_hist)?;
    dict.set_item("acceptance_rate", n_accepted as f64 / n_traj as f64)?;
    dict.set_item("n_measurements", n_meas)?;
    dict.set_item("sign_free", true)?;
    dict.set_item("even_odd", true)?;
    dict.set_item("g", g)?;
    dict.set_item("L", l)?;
    dict.set_item("h_final", h)?;

    Ok(dict.into())
}

/// Clark-Kennedy 2-pseudofermion even-odd RHMC.
///
/// Physics: det(M_e)^{1/2} = [det(M_e)^{1/4}]^2. Two independent complex
/// pseudofermion fields, each with x^{-1/4} Zolotarev action on M_e.
/// Resolves the x^{-1/2} |ΔH|≈2.35 pathology at κ≈6000.
///
/// Zolotarev powers (passed from Python):
///   action coefficients (alpha_0, alphas, betas): x^{-1/4} on M_e eigenvalues
///   heatbath coefficients (alpha_0_hb, alphas_hb, betas_hb): x^{-7/8} on M_e
///
/// Same interface as run_rhmc_rust_eo — drop-in replacement.
///
/// Reference: Clark & Kennedy, PRL 98:051601 (2007) [hep-lat/0608015]
#[pyfunction]
fn run_rhmc_rust_eo_2pf<'py>(
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
    cg_a: PyReadonlyArray1<'py, i64>,
    cg_i: PyReadonlyArray1<'py, i64>,
    cg_j: PyReadonlyArray1<'py, i64>,
    cg_val: PyReadonlyArray1<'py, f64>,
    h_init: Option<PyReadonlyArray1<'py, f64>>,
) -> PyResult<PyObject> {
    let alphas = alphas.as_slice()?;
    let betas = betas.as_slice()?;
    let alphas_hb = alphas_hb.as_slice()?;
    let betas_hb = betas_hb.as_slice()?;
    let cg_entries = parse_cg_entries(cg_a.as_slice()?, cg_i.as_slice()?,
                                       cg_j.as_slice()?, cg_val.as_slice()?);

    let n_sites = l * l * l * l;
    let (fwd, bwd) = build_neighbors(l);
    let eo = build_even_odd(l);

    let mut rng = ChaCha20Rng::seed_from_u64(seed);

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
        if traj % 10 == 0 {
            py.check_signals()?;
        }

        let result = rhmc_trajectory_eo_2pf(
            &mut h, g, tau, n_md_steps,
            alpha_0, alphas, betas,
            alpha_0_hb, alphas_hb, betas_hb,
            &fwd, &bwd, n_sites, &eo,
            &mut rng, &cg_entries,
            1e-10, 1e-12,
        );

        delta_h_hist.push(result.delta_h);
        if result.accepted { n_accepted += 1; }

        if traj >= n_therm && (traj - n_therm) % n_meas_skip == 0 {
            h_sq_hist.push(result.h_sq);
            tet_m2_hist.push(result.tet_m2);
            tr_q2_hist.push(result.tr_q2);
        }
    }

    let dict = pyo3::types::PyDict::new(py);
    dict.set_item("h_sq_history", h_sq_hist)?;
    dict.set_item("delta_h_history", delta_h_hist)?;
    let n_meas = tet_m2_hist.len();
    dict.set_item("tet_m2_history", tet_m2_hist)?;
    dict.set_item("tr_q2_history", tr_q2_hist)?;
    dict.set_item("acceptance_rate", n_accepted as f64 / n_traj as f64)?;
    dict.set_item("n_measurements", n_meas)?;
    dict.set_item("sign_free", true)?;
    dict.set_item("even_odd", true)?;
    dict.set_item("clark_kennedy_2pf", true)?;
    dict.set_item("g", g)?;
    dict.set_item("L", l)?;
    dict.set_item("h_final", h)?;

    Ok(dict.into())
}

/// Deflated Clark-Kennedy 2-PF even-odd RHMC.
///
/// Combines CK 2-PF (correct Pfaffian via two x^{-1/4} fields) with
/// low-mode deflation (K eigenpairs of M_e, ~12-15× CG speedup).
///
/// Eigenvectors can be provided externally (computed in Python via scipy)
/// or computed internally via Lanczos. External is recommended for now.
///
/// defl_evecs_flat: K eigenvectors of M_e, flattened row-major (K * dim_e,)
/// defl_evals: K eigenvalues, ascending
/// If both provided, uses them directly. Otherwise uses internal Lanczos.
#[pyfunction]
fn run_rhmc_rust_eo_2pf_defl<'py>(
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
    cg_a: PyReadonlyArray1<'py, i64>,
    cg_i: PyReadonlyArray1<'py, i64>,
    cg_j: PyReadonlyArray1<'py, i64>,
    cg_val: PyReadonlyArray1<'py, f64>,
    h_init: Option<PyReadonlyArray1<'py, f64>>,
    n_deflation_vectors: usize,
    defl_evecs_flat: Option<PyReadonlyArray1<'py, f64>>,
    defl_evals: Option<PyReadonlyArray1<'py, f64>>,
) -> PyResult<PyObject> {
    let alphas = alphas.as_slice()?;
    let betas = betas.as_slice()?;
    let alphas_hb = alphas_hb.as_slice()?;
    let betas_hb = betas_hb.as_slice()?;
    let cg_entries = parse_cg_entries(cg_a.as_slice()?, cg_i.as_slice()?,
                                       cg_j.as_slice()?, cg_val.as_slice()?);

    let n_sites = l * l * l * l;
    let (fwd, bwd) = build_neighbors(l);
    let eo = build_even_odd(l);

    let mut rng = ChaCha20Rng::seed_from_u64(seed);

    let mut h: Vec<f64> = if let Some(h_in) = h_init {
        h_in.as_slice()?.to_vec()
    } else {
        let sigma_h = (2.0 * g).sqrt();
        (0..n_sites * 16).map(|_| rand_normal(&mut rng) * sigma_h).collect()
    };

    // Parse external eigenvectors if provided
    let dim_e = 8 * eo.n_even;
    let ext_defl: Option<DeflationData> = match (defl_evecs_flat.as_ref(), defl_evals.as_ref()) {
        (Some(evecs_flat), Some(evals)) => {
            let evals_slice = evals.as_slice()?;
            let evecs_slice = evecs_flat.as_slice()?;
            let k = evals_slice.len();
            if evecs_slice.len() == k * dim_e && k > 0 {
                let evecs: Vec<Vec<f64>> = (0..k)
                    .map(|j| evecs_slice[j * dim_e..(j + 1) * dim_e].to_vec())
                    .collect();
                Some(DeflationData {
                    k,
                    evecs,
                    evals: evals_slice.to_vec(),
                })
            } else {
                None
            }
        }
        _ => None,
    };

    let mut h_sq_hist = Vec::new();
    let mut delta_h_hist = Vec::new();
    let mut tet_m2_hist = Vec::new();
    let mut tr_q2_hist = Vec::new();
    let mut n_accepted: usize = 0;
    let mut prev_evecs: Option<Vec<Vec<f64>>> = None;
    let mut total_defl_k: usize = 0;

    for traj in 0..n_traj {
        if traj % 10 == 0 {
            py.check_signals()?;
        }

        // Use external eigenvectors if provided, otherwise warm-start from previous traj
        let prev_ref = if ext_defl.is_some() {
            ext_defl.as_ref().map(|d| d.evecs.as_slice())
        } else {
            prev_evecs.as_ref().map(|v| v.as_slice())
        };

        let (result, defl_data) = rhmc_trajectory_eo_2pf_defl(
            &mut h, g, tau, n_md_steps,
            alpha_0, alphas, betas,
            alpha_0_hb, alphas_hb, betas_hb,
            &fwd, &bwd, n_sites, &eo,
            &mut rng, &cg_entries,
            1e-10, 1e-12,
            n_deflation_vectors,
            prev_ref,
            ext_defl.as_ref(),
        );

        // Save eigenvectors for warm-start on next trajectory
        total_defl_k = defl_data.k;
        prev_evecs = Some(defl_data.evecs);

        delta_h_hist.push(result.delta_h);
        if result.accepted { n_accepted += 1; }

        if traj >= n_therm && (traj - n_therm) % n_meas_skip == 0 {
            h_sq_hist.push(result.h_sq);
            tet_m2_hist.push(result.tet_m2);
            tr_q2_hist.push(result.tr_q2);
        }
    }

    let dict = pyo3::types::PyDict::new(py);
    dict.set_item("h_sq_history", h_sq_hist)?;
    dict.set_item("delta_h_history", delta_h_hist)?;
    let n_meas = tet_m2_hist.len();
    dict.set_item("tet_m2_history", tet_m2_hist)?;
    dict.set_item("tr_q2_history", tr_q2_hist)?;
    dict.set_item("acceptance_rate", n_accepted as f64 / n_traj as f64)?;
    dict.set_item("n_measurements", n_meas)?;
    dict.set_item("sign_free", true)?;
    dict.set_item("even_odd", true)?;
    dict.set_item("clark_kennedy_2pf", true)?;
    dict.set_item("deflation_k", total_defl_k)?;
    dict.set_item("g", g)?;
    dict.set_item("L", l)?;
    dict.set_item("h_final", h)?;

    Ok(dict.into())
}

// ═══════════════════════════════════════════════════════════════════
// Hasenbusch K-level mass-split RHMC with nested Omelyan integrator
//
// Splits det(M_e)^{1/4} into K+1 well-conditioned factors:
//   det(M_e+mu_K^2)^{1/4} × Π det[(M_e+mu_k)/(M_e+mu_{k+1})]^{1/4}
//
// Each factor uses CK 2-PF (2 complex PFs). Nested 3-level Omelyan
// puts expensive (lightest) forces on coarsest timescale, cheap
// (heaviest) forces on finest timescale.
//
// Expected 10-20× speedup: kappa/factor ~16 vs ~6000 original.
//
// Source: Deep research "Hasenbusch mass splitting..." Sections 1-8
// ═══════════════════════════════════════════════════════════════════

/// Nested Omelyan 2MN integrator (recursive multi-level).
///
/// Each level has a set of factor indices whose forces are computed at
/// that timescale. The deepest level performs pure position updates.
fn nested_omelyan(
    h: &mut [f64],
    pi: &mut [f64],
    tau: f64,
    level: usize,
    n_levels: usize,
    n_steps: &[usize],
    // Per-factor data (indexed by factor_id)
    factor_levels: &[usize],
    factor_action_a0: &[f64],
    factor_action_al: &[&[f64]],
    factor_action_be: &[&[f64]],
    factor_phi_r: &[&[Vec<f64>]],  // [factor][pf_idx] -> even-site vector
    factor_phi_i: &[&[Vec<f64>]],
    // Lattice
    g: f64,
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    cg_tol_md: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
) {
    let n_h = n_sites * 16;
    if level >= n_levels {
        // Leaf: pure position update
        for i in 0..n_h { h[i] += tau * pi[i]; }
        return;
    }

    let dt = tau / n_steps[level] as f64;
    let lam = 0.1932; // Omelyan 2MN parameter

    for _step in 0..n_steps[level] {
        // Position block: λ·dt via deeper levels
        nested_omelyan(h, pi, lam * dt, level + 1, n_levels, n_steps,
            factor_levels, factor_action_a0, factor_action_al, factor_action_be,
            factor_phi_r, factor_phi_i, g, fwd, bwd, n_sites, eo,
            cg_tol_md, cg_max_iter, cg_entries);

        // Momentum kick: dt/2 from this level's forces
        hasenbusch_level_kick(pi, dt / 2.0, level, n_levels,
            factor_levels, factor_action_a0, factor_action_al, factor_action_be,
            factor_phi_r, factor_phi_i, h, g, fwd, bwd, n_sites, eo,
            cg_tol_md, cg_max_iter, cg_entries);

        // Position block: (1-2λ)·dt
        nested_omelyan(h, pi, (1.0 - 2.0 * lam) * dt, level + 1, n_levels, n_steps,
            factor_levels, factor_action_a0, factor_action_al, factor_action_be,
            factor_phi_r, factor_phi_i, g, fwd, bwd, n_sites, eo,
            cg_tol_md, cg_max_iter, cg_entries);

        // Momentum kick: dt/2
        hasenbusch_level_kick(pi, dt / 2.0, level, n_levels,
            factor_levels, factor_action_a0, factor_action_al, factor_action_be,
            factor_phi_r, factor_phi_i, h, g, fwd, bwd, n_sites, eo,
            cg_tol_md, cg_max_iter, cg_entries);

        // Position block: λ·dt
        nested_omelyan(h, pi, lam * dt, level + 1, n_levels, n_steps,
            factor_levels, factor_action_a0, factor_action_al, factor_action_be,
            factor_phi_r, factor_phi_i, g, fwd, bwd, n_sites, eo,
            cg_tol_md, cg_max_iter, cg_entries);
    }
}

/// Apply momentum kicks from all factors assigned to a given level.
/// Gaussian prior is included only on the finest (deepest) level.
fn hasenbusch_level_kick(
    pi: &mut [f64],
    dt: f64,
    level: usize,
    n_levels: usize,
    factor_levels: &[usize],
    factor_action_a0: &[f64],
    factor_action_al: &[&[f64]],
    factor_action_be: &[&[f64]],
    factor_phi_r: &[&[Vec<f64>]],
    factor_phi_i: &[&[Vec<f64>]],
    h: &[f64],
    g: f64,
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    cg_tol: f64,
    cg_max_iter: usize,
    cg_entries: &[CgEntry],
) {
    let n_h = n_sites * 16;
    let mut f_h = vec![0.0; n_h];

    // Gaussian prior on finest level only
    if level == n_levels - 1 {
        for i in 0..n_h { f_h[i] = -h[i] / (2.0 * g); }
    }

    // PF forces from all factors assigned to this level
    for (fk, &fl) in factor_levels.iter().enumerate() {
        if fl != level { continue; }
        // CK 2-PF: 2 complex PFs per factor, each with real + imaginary
        for pf_idx in 0..2 {
            compute_pf_force_eo(
                h, &factor_phi_r[fk][pf_idx],
                factor_action_al[fk], factor_action_be[fk],
                fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);
            compute_pf_force_eo(
                h, &factor_phi_i[fk][pf_idx],
                factor_action_al[fk], factor_action_be[fk],
                fwd, bwd, eo, cg_tol, cg_max_iter, cg_entries, &mut f_h);
        }
    }

    // Apply kick: pi += dt * f
    for i in 0..n_h { pi[i] += dt * f_h[i]; }
}

/// Hasenbusch CK 2-PF trajectory with nested Omelyan.
fn rhmc_trajectory_eo_2pf_hasenbusch(
    h: &mut Vec<f64>,
    g: f64,
    tau: f64,
    n_factors: usize,
    n_poles: usize,
    // Flattened per-factor action coefficients
    act_a0s: &[f64],
    act_als: &[f64],
    act_bes: &[f64],
    // Flattened per-factor heatbath coefficients
    hb_a0s: &[f64],
    hb_als: &[f64],
    hb_bes: &[f64],
    // Integrator config
    n_steps: &[usize],
    factor_levels: &[usize],
    is_heavy: &[bool],
    mu_sq_vals: &[f64],       // heavy factor mu_K^2 (or 0 for ratio)
    mu_lo_vals: &[f64],       // ratio factor mu_lo (for heatbath A-trick)
    mu_hi_vals: &[f64],       // ratio factor mu_hi
    // Lattice
    fwd: &[[usize; 4]],
    bwd: &[[usize; 4]],
    n_sites: usize,
    eo: &EvenOddTables,
    rng: &mut ChaCha20Rng,
    cg_entries: &[CgEntry],
    cg_tol_md: f64,
    cg_tol_mc: f64,
) -> TrajectoryResult {
    let n_h = n_sites * 16;
    let dim_e = 8 * eo.n_even;
    let n_levels = n_steps.len();
    let cg_max_iter = 2000;
    let inv_sqrt2 = 1.0 / f64::sqrt(2.0);

    // Slice per-factor coefficients
    let act_al_slices: Vec<&[f64]> = (0..n_factors)
        .map(|f| &act_als[f * n_poles..(f + 1) * n_poles])
        .collect();
    let act_be_slices: Vec<&[f64]> = (0..n_factors)
        .map(|f| &act_bes[f * n_poles..(f + 1) * n_poles])
        .collect();

    // ── HEATBATH: generate 2 complex PFs per factor ──
    let mut phi_r: Vec<Vec<Vec<f64>>> = Vec::with_capacity(n_factors);
    let mut phi_i: Vec<Vec<Vec<f64>>> = Vec::with_capacity(n_factors);
    let mut scratch_odd = vec![0.0_f64; 8 * eo.n_odd];

    for fk in 0..n_factors {
        let hb_al = &hb_als[fk * n_poles..(fk + 1) * n_poles];
        let hb_be = &hb_bes[fk * n_poles..(fk + 1) * n_poles];
        let hb_a0 = hb_a0s[fk];

        let mut factor_phi_r = Vec::with_capacity(2);
        let mut factor_phi_i = Vec::with_capacity(2);

        for _pf in 0..2 {
            let xi_r: Vec<f64> = (0..dim_e).map(|_| rand_normal(rng)).collect();
            let xi_i: Vec<f64> = (0..dim_e).map(|_| rand_normal(rng)).collect();

            // CG solve for heatbath: eta = [a0*xi + Σ al_j*(M_e+be_j)^{-1}*xi]
            let cg_r = multishift_cg_eo(h, &xi_r, hb_be, cg_tol_md, cg_max_iter,
                                         fwd, bwd, eo, cg_entries);
            let cg_i = multishift_cg_eo(h, &xi_i, hb_be, cg_tol_md, cg_max_iter,
                                         fwd, bwd, eo, cg_entries);

            let mut eta_r = vec![0.0; dim_e];
            let mut eta_i = vec![0.0; dim_e];
            for i in 0..dim_e {
                eta_r[i] = hb_a0 * xi_r[i];
                eta_i[i] = hb_a0 * xi_i[i];
            }
            for k in 0..n_poles {
                axpy(hb_al[k], &cg_r.solutions[k], &mut eta_r);
                axpy(hb_al[k], &cg_i.solutions[k], &mut eta_i);
            }

            if is_heavy[fk] {
                // Heavy factor: phi = (M_e + mu_K^2) * eta / sqrt(2)
                let mu_sq = mu_sq_vals[fk];
                let mut pr = vec![0.0; dim_e];
                let mut pi_f = vec![0.0; dim_e];
                apply_me_shifted(h, &eta_r, &mut pr, mu_sq, fwd, bwd, eo,
                                 &mut scratch_odd, cg_entries);
                apply_me_shifted(h, &eta_i, &mut pi_f, mu_sq, fwd, bwd, eo,
                                 &mut scratch_odd, cg_entries);
                for i in 0..dim_e { pr[i] *= inv_sqrt2; }
                for i in 0..dim_e { pi_f[i] *= inv_sqrt2; }
                factor_phi_r.push(pr);
                factor_phi_i.push(pi_f);
            } else {
                // Ratio factor: heatbath uses Q^{-7/8} (already computed) + Q application
                // Q * v = (M_e+mu_lo)/(M_e+mu_hi) * v
                //   step 1: w = (M_e+mu_hi)^{-1} v (CG with single shift mu_hi)
                //   step 2: phi = (M_e+mu_lo) w     (apply_me_shifted with sigma=mu_lo)
                let mu_lo = mu_lo_vals[fk];
                let mu_hi = mu_hi_vals[fk];

                // Step 1: solve (M_e + mu_hi) w = eta
                let cg_q_r = multishift_cg_eo(h, &eta_r, &[mu_hi], cg_tol_md, cg_max_iter,
                                               fwd, bwd, eo, cg_entries);
                let cg_q_i = multishift_cg_eo(h, &eta_i, &[mu_hi], cg_tol_md, cg_max_iter,
                                               fwd, bwd, eo, cg_entries);

                // Step 2: phi = (M_e + mu_lo) * w / sqrt(2)
                let mut pr = vec![0.0; dim_e];
                let mut pi_f = vec![0.0; dim_e];
                apply_me_shifted(h, &cg_q_r.solutions[0], &mut pr, mu_lo, fwd, bwd, eo,
                                 &mut scratch_odd, cg_entries);
                apply_me_shifted(h, &cg_q_i.solutions[0], &mut pi_f, mu_lo, fwd, bwd, eo,
                                 &mut scratch_odd, cg_entries);
                for i in 0..dim_e { pr[i] *= inv_sqrt2; }
                for i in 0..dim_e { pi_f[i] *= inv_sqrt2; }
                factor_phi_r.push(pr);
                factor_phi_i.push(pi_f);
            }
        }
        phi_r.push(factor_phi_r);
        phi_i.push(factor_phi_i);
    }

    // Refresh momenta
    let mut pi_h: Vec<f64> = (0..n_h).map(|_| rand_normal(rng)).collect();
    let h_old = h.clone();

    // ── H_old ──
    let h_old_val = {
        let k_energy = 0.5 * dot(&pi_h, &pi_h);
        let s_aux = dot(h, h) / (4.0 * g);
        let mut s_pf = 0.0;
        for fk in 0..n_factors {
            for pf_idx in 0..2 {
                s_pf += compute_spf_eo(h, &phi_r[fk][pf_idx], act_a0s[fk],
                    act_al_slices[fk], act_be_slices[fk], fwd, bwd, eo,
                    cg_tol_mc, cg_max_iter, cg_entries);
                s_pf += compute_spf_eo(h, &phi_i[fk][pf_idx], act_a0s[fk],
                    act_al_slices[fk], act_be_slices[fk], fwd, bwd, eo,
                    cg_tol_mc, cg_max_iter, cg_entries);
            }
        }
        k_energy + s_aux + s_pf
    };

    // ── Nested Omelyan MD ──
    // Build references for the integrator
    let phi_r_refs: Vec<&[Vec<f64>]> = phi_r.iter().map(|v| v.as_slice()).collect();
    let phi_i_refs: Vec<&[Vec<f64>]> = phi_i.iter().map(|v| v.as_slice()).collect();

    nested_omelyan(
        h, &mut pi_h, tau, 0, n_levels, n_steps,
        factor_levels, act_a0s, &act_al_slices, &act_be_slices,
        &phi_r_refs, &phi_i_refs,
        g, fwd, bwd, n_sites, eo, cg_tol_md, cg_max_iter, cg_entries);

    // ── H_new ──
    let h_new_val = {
        let k_energy = 0.5 * dot(&pi_h, &pi_h);
        let s_aux = dot(h, h) / (4.0 * g);
        let mut s_pf = 0.0;
        for fk in 0..n_factors {
            for pf_idx in 0..2 {
                s_pf += compute_spf_eo(h, &phi_r[fk][pf_idx], act_a0s[fk],
                    act_al_slices[fk], act_be_slices[fk], fwd, bwd, eo,
                    cg_tol_mc, cg_max_iter, cg_entries);
                s_pf += compute_spf_eo(h, &phi_i[fk][pf_idx], act_a0s[fk],
                    act_al_slices[fk], act_be_slices[fk], fwd, bwd, eo,
                    cg_tol_mc, cg_max_iter, cg_entries);
            }
        }
        k_energy + s_aux + s_pf
    };

    let delta_h = h_new_val - h_old_val;
    let accepted = if delta_h <= 0.0 { true } else {
        let u: f64 = rng.random();
        u < (-delta_h).exp()
    };
    if !accepted { *h = h_old; }

    let (h_sq, tet_m2, tr_q2) = measure_observables(h, n_sites);
    TrajectoryResult { delta_h, accepted, h_sq, tet_m2, tr_q2 }
}

/// Hasenbusch K-level mass-split RHMC (PyO3 binding).
///
/// Coefficients are flattened: action_alphas[f*n_poles..(f+1)*n_poles] for factor f.
/// Factor levels assign each factor to a nested integrator timescale.
/// is_heavy flags control heatbath construction (heavy uses A-trick on M_e+mu^2).
#[pyfunction]
fn run_rhmc_rust_eo_2pf_hasenbusch<'py>(
    py: Python<'py>,
    l: usize,
    g: f64,
    n_traj: usize,
    n_therm: usize,
    n_meas_skip: usize,
    tau: f64,
    n_factors: usize,
    n_poles_per_factor: usize,
    action_alpha0s: PyReadonlyArray1<'py, f64>,
    action_alphas: PyReadonlyArray1<'py, f64>,
    action_betas: PyReadonlyArray1<'py, f64>,
    hb_alpha0s: PyReadonlyArray1<'py, f64>,
    hb_alphas: PyReadonlyArray1<'py, f64>,
    hb_betas: PyReadonlyArray1<'py, f64>,
    n_steps_per_level: PyReadonlyArray1<'py, i64>,
    factor_levels_arr: PyReadonlyArray1<'py, i64>,
    is_heavy_flags: PyReadonlyArray1<'py, i64>,
    mu_sq_values: PyReadonlyArray1<'py, f64>,
    mu_lo_values: PyReadonlyArray1<'py, f64>,
    mu_hi_values: PyReadonlyArray1<'py, f64>,
    seed: u64,
    cg_a: PyReadonlyArray1<'py, i64>,
    cg_i: PyReadonlyArray1<'py, i64>,
    cg_j: PyReadonlyArray1<'py, i64>,
    cg_val: PyReadonlyArray1<'py, f64>,
    h_init: Option<PyReadonlyArray1<'py, f64>>,
) -> PyResult<PyObject> {
    let act_a0s = action_alpha0s.as_slice()?;
    let act_als = action_alphas.as_slice()?;
    let act_bes = action_betas.as_slice()?;
    let hb_a0s = hb_alpha0s.as_slice()?;
    let hb_als = hb_alphas.as_slice()?;
    let hb_bes = hb_betas.as_slice()?;
    let n_steps_raw = n_steps_per_level.as_slice()?;
    let n_steps: Vec<usize> = n_steps_raw.iter().map(|&x| x as usize).collect();
    let factor_levels_raw = factor_levels_arr.as_slice()?;
    let factor_levels: Vec<usize> = factor_levels_raw.iter().map(|&x| x as usize).collect();
    let is_heavy_raw = is_heavy_flags.as_slice()?;
    let is_heavy: Vec<bool> = is_heavy_raw.iter().map(|&x| x != 0).collect();
    let mu_sq = mu_sq_values.as_slice()?;
    let mu_lo = mu_lo_values.as_slice()?;
    let mu_hi = mu_hi_values.as_slice()?;
    let cg_entries = parse_cg_entries(cg_a.as_slice()?, cg_i.as_slice()?,
                                       cg_j.as_slice()?, cg_val.as_slice()?);

    let n_sites = l * l * l * l;
    let (fwd, bwd) = build_neighbors(l);
    let eo = build_even_odd(l);
    let mut rng = ChaCha20Rng::seed_from_u64(seed);

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
        if traj % 5 == 0 { py.check_signals()?; }

        let result = rhmc_trajectory_eo_2pf_hasenbusch(
            &mut h, g, tau, n_factors, n_poles_per_factor,
            act_a0s, act_als, act_bes, hb_a0s, hb_als, hb_bes,
            &n_steps, &factor_levels, &is_heavy, mu_sq, mu_lo, mu_hi,
            &fwd, &bwd, n_sites, &eo, &mut rng, &cg_entries,
            1e-6, 1e-10,
        );

        delta_h_hist.push(result.delta_h);
        if result.accepted { n_accepted += 1; }

        if traj >= n_therm && (traj - n_therm) % n_meas_skip == 0 {
            h_sq_hist.push(result.h_sq);
            tet_m2_hist.push(result.tet_m2);
            tr_q2_hist.push(result.tr_q2);
        }
    }

    let dict = pyo3::types::PyDict::new(py);
    dict.set_item("h_sq_history", h_sq_hist)?;
    dict.set_item("delta_h_history", delta_h_hist)?;
    let n_meas = tet_m2_hist.len();
    dict.set_item("tet_m2_history", tet_m2_hist)?;
    dict.set_item("tr_q2_history", tr_q2_hist)?;
    dict.set_item("acceptance_rate", n_accepted as f64 / n_traj as f64)?;
    dict.set_item("n_measurements", n_meas)?;
    dict.set_item("hasenbusch", true)?;
    dict.set_item("n_factors", n_factors)?;
    dict.set_item("g", g)?;
    dict.set_item("L", l)?;
    dict.set_item("h_final", h)?;

    Ok(dict.into())
}

#[pymodule]
fn sk_eft_rhmc(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(run_rhmc_rust, m)?)?;
    m.add_function(wrap_pyfunction!(run_rhmc_rust_eo, m)?)?;
    m.add_function(wrap_pyfunction!(run_rhmc_rust_eo_2pf, m)?)?;
    m.add_function(wrap_pyfunction!(run_rhmc_rust_eo_2pf_defl, m)?)?;
    m.add_function(wrap_pyfunction!(run_rhmc_rust_eo_2pf_hasenbusch, m)?)?;
    m.add_function(wrap_pyfunction!(apply_fermion_matrix_py, m)?)?;
    m.add_function(wrap_pyfunction!(estimate_spectral_range_py, m)?)?;
    Ok(())
}
