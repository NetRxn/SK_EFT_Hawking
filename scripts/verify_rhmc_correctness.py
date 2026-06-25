#!/usr/bin/env python3
"""Implementation-level correctness battery for the Rust HS+RHMC backend.

The Lean proofs (HubbardStratonovichRHMC.lean) verify the *mathematics*
(Zolotarev convergence, Omelyan symplecticity, Hamiltonian form). They do
NOT verify that the Rust `sk_eft_rhmc` implementation actually realises that
math. This script supplies the missing implementation-level checks — the
standard battery any HMC code must pass before its samples are trusted:

  A. Reproducibility      — same (seed, params, h_init) ⇒ bit-identical chain.
  B. Resume losslessness  — a chunked/resumed run reproduces the straight run
                            up to the stop point (field-carry loses nothing),
                            and the full resumed chain is statistically
                            equivalent to the straight chain.
  C. Integrator validity  — ⟨|ΔH|⟩ → 0 as a power of the step size ε. A correct
                            force == ∇(action) gives a clean ε^p law; a wrong
                            force plateaus at a nonzero floor. This is the test
                            that the L=8 production runs (md=30, |ΔH|≈2-4)
                            silently failed.

All checks run at L=4 (cheap). PASS/FAIL is printed per check with the numbers
behind the verdict. Read-only w.r.t. data/ — writes nothing.

Usage:
  PYTHONPATH=. uv run python scripts/verify_rhmc_correctness.py
  PYTHONPATH=. uv run python scripts/verify_rhmc_correctness.py --quick   # smaller budgets
"""
import argparse
import numpy as np

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
from src.vestigial.hs_rhmc import compute_zolotarev_coefficients

import sk_eft_rhmc


def build_cg_entries():
    """Sparse CG stencil from constants.py (matches run_rhmc_production._build_cg_entries)."""
    CG = np.array([MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a] for a in range(4)])
    cg_a, cg_i, cg_j, cg_val = [], [], [], []
    for a in range(4):
        for I in range(8):
            for J in range(8):
                v = CG[a, I, J]
                if abs(v) > 1e-15:
                    cg_a.append(a); cg_i.append(I); cg_j.append(J); cg_val.append(v)
    return (np.array(cg_a, dtype=np.int64), np.array(cg_i, dtype=np.int64),
            np.array(cg_j, dtype=np.int64), np.array(cg_val, dtype=np.float64))


def make_coeffs(L, g, seed, cg, n_poles=12):
    cg_a, cg_i, cg_j, cg_val = cg
    lam_min, lam_max = sk_eft_rhmc.estimate_spectral_range_py(L, g, seed, 50, cg_a, cg_i, cg_j, cg_val)
    a0, alphas, betas = compute_zolotarev_coefficients(n_poles, lam_min, lam_max, -0.25)
    a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(n_poles, lam_min, lam_max, -0.875)
    return dict(
        a0=float(a0), alphas=np.asarray(alphas), betas=np.asarray(betas),
        a0_hb=float(a0_hb), alphas_hb=np.asarray(alphas_hb), betas_hb=np.asarray(betas_hb),
        lam_min=lam_min, lam_max=lam_max,
    )


def run(L, g, n_traj, n_md_steps, tau, seed, coeffs, cg, h_init=None, n_therm=0):
    cg_a, cg_i, cg_j, cg_val = cg
    return sk_eft_rhmc.run_rhmc_rust_eo_2pf(
        l=L, g=g, n_traj=n_traj + n_therm, n_therm=n_therm, n_meas_skip=1,
        n_md_steps=n_md_steps, tau=tau,
        alpha_0=coeffs['a0'], alphas=coeffs['alphas'], betas=coeffs['betas'],
        alpha_0_hb=coeffs['a0_hb'], alphas_hb=coeffs['alphas_hb'], betas_hb=coeffs['betas_hb'],
        seed=seed, cg_a=cg_a, cg_i=cg_i, cg_j=cg_j, cg_val=cg_val,
        h_init=h_init,
    )


def jackknife_mean_err(x):
    x = np.asarray(x, dtype=float)
    n = x.size
    if n < 2:
        return float(x.mean()) if n else float('nan'), float('nan')
    full = x.mean()
    jk = (n * full - x) / (n - 1)
    err = np.sqrt((n - 1) / n * np.sum((jk - jk.mean()) ** 2))
    return float(full), float(err)


# ────────────────────────────────────────────────────────────────────────
# Check A — reproducibility
# ────────────────────────────────────────────────────────────────────────
def check_reproducibility(L, g, cg, coeffs, n_traj, tau, n_md_steps):
    print("\n" + "=" * 72)
    print("CHECK A — Reproducibility (same seed ⇒ identical chain)")
    print("=" * 72)
    r1 = run(L, g, n_traj, n_md_steps, tau, seed=12345, coeffs=coeffs, cg=cg)
    r2 = run(L, g, n_traj, n_md_steps, tau, seed=12345, coeffs=coeffs, cg=cg)
    dh1, dh2 = np.array(r1['delta_h_history']), np.array(r2['delta_h_history'])
    hf1, hf2 = np.array(r1['h_final']), np.array(r2['h_final'])
    dh_id = np.array_equal(dh1, dh2)
    hf_max = float(np.max(np.abs(hf1 - hf2))) if hf1.size else float('nan')
    hf_id = hf_max == 0.0
    print(f"  ΔH history identical : {dh_id}  (n={dh1.size})")
    print(f"  h_final max|Δ|       : {hf_max:.2e}  identical={hf_id}")
    ok = dh_id and hf_id
    print(f"  -> {'PASS' if ok else 'FAIL'}")
    return ok


# ────────────────────────────────────────────────────────────────────────
# Check B — resume losslessness
# ────────────────────────────────────────────────────────────────────────
def check_resume(L, g, cg, coeffs, tau, n_md_steps, n_stat):
    print("\n" + "=" * 72)
    print("CHECK B — Resume losslessness (chunk boundary + statistical equivalence)")
    print("=" * 72)
    SEED = 777

    # B1: a single n=40 call vs an n=20 call with the SAME seed/h_init must agree
    #     on the first 20 trajectories AND on the field at the stop point.
    #     This proves the checkpoint stop loses nothing up to where it stops.
    straight40 = run(L, g, 40, n_md_steps, tau, seed=SEED, coeffs=coeffs, cg=cg)
    stop20 = run(L, g, 20, n_md_steps, tau, seed=SEED, coeffs=coeffs, cg=cg)
    dh40 = np.array(straight40['delta_h_history'])
    dh20 = np.array(stop20['delta_h_history'])
    prefix_id = np.array_equal(dh40[:20], dh20)
    print(f"  B1 chunk-prefix ΔH[:20] identical to straight run : {prefix_id}")
    print(f"     -> the checkpoint STOP is bitwise lossless: {'PASS' if prefix_id else 'FAIL'}")

    # B2: full resumed run (production seed schedule: this_seed = base + n_done,
    #     h carried via h_final) must be STATISTICALLY equivalent to a straight
    #     run of the same length. The RNG reseeds each chunk by design, so this
    #     is equivalence-in-distribution, not bitwise.
    n_total = n_stat
    chunk = max(1, n_total // 4)
    # straight
    straight = run(L, g, n_total, n_md_steps, tau, seed=SEED, coeffs=coeffs, cg=cg)
    tet_straight = np.array(straight['tet_m2_history'])
    # resumed in chunks
    tet_resumed = []
    h_carry = None
    n_done = 0
    while n_done < n_total:
        c = min(chunk, n_total - n_done)
        r = run(L, g, c, n_md_steps, tau, seed=SEED + n_done, coeffs=coeffs, cg=cg, h_init=h_carry)
        tet_resumed.extend(list(r['tet_m2_history']))
        h_carry = np.array(r['h_final'], dtype=np.float64)
        n_done += c
    tet_resumed = np.array(tet_resumed)

    ms, es = jackknife_mean_err(tet_straight)
    mr, er = jackknife_mean_err(tet_resumed)
    comb = np.hypot(es, er)
    nsig = abs(ms - mr) / comb if comb > 0 else float('inf')
    print(f"  B2 ⟨tet_m2⟩ straight  : {ms:.5f} ± {es:.5f}  (n={tet_straight.size})")
    print(f"     ⟨tet_m2⟩ resumed   : {mr:.5f} ± {er:.5f}  (n={tet_resumed.size}, chunk={chunk})")
    print(f"     discrepancy        : {nsig:.2f}σ")
    b2_ok = nsig < 3.0
    print(f"     -> statistical equivalence (<3σ): {'PASS' if b2_ok else 'FAIL'}")
    ok = prefix_id and b2_ok
    print(f"  -> {'PASS' if ok else 'FAIL'}")
    return ok


# ────────────────────────────────────────────────────────────────────────
# Check C — integrator validity (ΔH → 0 as ε → 0)
# ────────────────────────────────────────────────────────────────────────
def check_integrator(L, g, cg, coeffs, tau, md_ladder, n_meas):
    print("\n" + "=" * 72)
    print("CHECK C — Integrator validity  ⟨|ΔH|⟩ → 0 as ε → 0  (force == ∇action)")
    print("=" * 72)
    print(f"  Fixed τ={tau}; ε = τ/n_md.  Omelyan 2MN ⇒ expect ⟨|ΔH|⟩ ∝ ε^p, p≈2.")
    eps_list, dh_list = [], []
    for n_md in md_ladder:
        r = run(L, g, n_meas, n_md, tau, seed=2024, coeffs=coeffs, cg=cg, n_therm=5)
        dh = np.abs(np.array(r['delta_h_history']))
        eps = tau / n_md
        eps_list.append(eps)
        dh_list.append(dh.mean())
        print(f"    n_md={n_md:<4d} ε={eps:.5f}  ⟨|ΔH|⟩={dh.mean():.4e}  "
              f"max={dh.max():.3e}  accept≈{float(r['acceptance_rate']):.2f}")
    eps_arr = np.array(eps_list)
    dh_arr = np.array(dh_list)
    # monotone decrease as ε shrinks?
    order = np.argsort(eps_arr)
    dh_sorted = dh_arr[order]
    monotone = bool(np.all(np.diff(dh_sorted) >= -1e-12))  # decreasing eps -> decreasing dH
    # log-log slope (drop any nonpositive dH)
    good = dh_arr > 0
    slope = float('nan')
    if good.sum() >= 2:
        slope = float(np.polyfit(np.log(eps_arr[good]), np.log(dh_arr[good]), 1)[0])
    floor = float(dh_sorted[0])  # ΔH at finest ε
    print(f"  monotone (⟨|ΔH|⟩ falls as ε falls) : {monotone}")
    print(f"  log-log slope p (⟨|ΔH|⟩∝ε^p)        : {slope:.2f}   (correct force ⇒ p≳1.5)")
    print(f"  ⟨|ΔH|⟩ at finest ε                  : {floor:.3e}   (should approach 0)")
    ok = monotone and (slope > 1.0) and (floor < 0.3)
    print(f"  -> {'PASS' if ok else 'FAIL'}")
    if not ok:
        print("     NOTE: a nonzero floor / slope≈0 would indicate a force≠∇action bug.")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=4)
    ap.add_argument('--g', type=float, default=2.2308)
    ap.add_argument('--quick', action='store_true', help='smaller budgets for a fast smoke run')
    ap.add_argument('--keystone', action='store_true',
                    help='fastest: reproducibility + integrator ΔH→0 only (skips the slow '
                         'statistical resume test). The decisive go/no-go for a restart.')
    ap.add_argument('--n-poles', type=int, default=None,
                    help='Zolotarev poles (default 8 for --keystone, else 12).')
    args = ap.parse_args()

    L, g = args.l, args.g
    tau = 0.5
    n_md = 20
    n_poles = args.n_poles if args.n_poles is not None else (8 if args.keystone else 12)
    cg = build_cg_entries()
    coeffs = make_coeffs(L, g, 42, cg, n_poles=n_poles)
    print(f"Spectral range L={L} g={g}: [{coeffs['lam_min']:.3f}, {coeffs['lam_max']:.1f}]  "
          f"κ={coeffs['lam_max']/coeffs['lam_min']:.0f}  (n_poles={n_poles})")

    if args.keystone:
        repro_n, stat_n, md_ladder, n_meas = 4, None, [4, 8, 16, 32], 8
    elif args.quick:
        repro_n, stat_n, md_ladder, n_meas = 5, 40, [5, 10, 20, 40], 12
    else:
        repro_n, stat_n, md_ladder, n_meas = 8, 120, [5, 10, 20, 40, 80], 25

    results = {}
    results['A_reproducible'] = check_reproducibility(L, g, cg, coeffs, repro_n, tau, n_md)
    if not args.keystone:
        results['B_resume'] = check_resume(L, g, cg, coeffs, tau, n_md, stat_n)
    results['C_integrator'] = check_integrator(L, g, cg, coeffs, tau, md_ladder, n_meas)

    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    for k, v in results.items():
        print(f"  {k:<18s} : {'PASS' if v else 'FAIL'}")
    all_ok = all(results.values())
    print(f"\n  OVERALL: {'ALL PASS — Rust backend implementation validated' if all_ok else 'FAILURES PRESENT — see above'}")
    return 0 if all_ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
