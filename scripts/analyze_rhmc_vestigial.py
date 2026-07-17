#!/usr/bin/env python3
"""Vestigial-phase analysis for HS+RHMC production scans (L*_m* data dirs).

Why this exists
---------------
The raw saved order parameters are CONFOUNDED and must not be read directly:

  - tet_m2 = |(1/V) Σ_x h_x|²   (tetrad proxy, |⟨h⟩_vol|²)
            has a finite-volume noise floor ≈ 16·⟨h²⟩/V even in a fully
            DISORDERED phase, because the volume average of a fluctuating
            field is ~1/√V per component. A "rising tet_m2" can be pure
            noise floor tracking ⟨h²⟩, which itself grows ∝ g² (h ≈ 2g·E).

  - tr_q2 = Tr Q̃²  with Q̃ = M − (TrM/4)I, M_μν = (1/V) Σ_{x,a} h^a_μ h^a_ν
            is the TRACELESS (nematic / vestigial) metric order parameter —
            the disconnected trace is already subtracted. But it ALSO has a
            finite-V noise floor ~ ⟨h²⟩²/V from incomplete cancellation, so
            Tr Q̃² ∝ ⟨h²⟩² is the signature of NO order, not of order.

So both channels need their disordered noise floor subtracted/compared before
any "transition" or "vestigial split" claim. This script does that:

  1. Creutz unbiasedness identity ⟨exp(−ΔH)⟩ = 1  (Metropolis correctness).
  2. Tetrad: tet_m2 vs the 16·⟨h²⟩/V noise floor (ratio ≈ 1 ⟹ no condensate).
  3. Metric/vestigial: Tr Q̃²(h_final) vs a SPATIALLY-SHUFFLED baseline that
     destroys all spatial coherence at fixed per-component magnitude
     (ratio ≈ 1 ⟹ no nematic order; ≫ 1 ⟹ genuine vestigial order).
  4. Connected susceptibilities χ_O = V·Var(O) with autocorrelation-aware errors.
  5. m→0 extrapolation of the noise-subtracted order parameters when ≥2 masses
     are present at the same L (the chiral-regulator deliverable).

Usage:
  PYTHONPATH=. uv run python scripts/analyze_rhmc_vestigial.py
  PYTHONPATH=. uv run python scripts/analyze_rhmc_vestigial.py --therm 150 --glob 'data/rhmc/L*_m*'
"""
import argparse
import glob
import os
import re
import numpy as np

from src.vestigial.hs_rhmc import hs_auxiliary_field_metric


def integrated_autocorr_time(x):
    """Sokal-windowed integrated autocorrelation time τ_int (≥ 0.5)."""
    x = np.asarray(x, float)
    x = x - x.mean()
    n = len(x)
    if n < 4 or x.std() == 0:
        return 0.5
    c0 = np.dot(x, x) / n
    tau = 0.5
    for t in range(1, n // 2):
        rho = np.dot(x[:-t], x[t:]) / ((n - t) * c0)
        tau += rho
        if t > 6 * tau:
            break
    return max(tau, 0.5)


def autocorr_mean_err(x, therm):
    """Mean and autocorrelation-corrected std error of the mean."""
    x = np.asarray(x, float)[therm:]
    n = len(x)
    if n == 0:
        return np.nan, np.nan, np.nan
    tau = integrated_autocorr_time(x)
    neff = n / (2 * tau)
    err = x.std(ddof=1) / np.sqrt(max(neff, 1.0)) if n > 1 else np.nan
    return x.mean(), err, tau


def connected_susceptibility(x, therm, V):
    """χ = V·Var(O) with a coarse variance error ~ χ·sqrt(2/N_eff)."""
    x = np.asarray(x, float)[therm:]
    n = len(x)
    tau = integrated_autocorr_time(x)
    neff = n / (2 * tau)
    chi = V * x.var(ddof=1)
    return chi, chi * np.sqrt(2.0 / max(neff, 1.0))


def binder_cumulant(x, therm):
    """Binder cumulant U = 1 − ⟨O²⟩/(3⟨O⟩²) for O the SQUARED order parameter
    (tet_m2 or trQ2, which are already |m|²). The FSS discriminant: U(g) curves
    for different L CROSS at a critical point; flat / non-crossing ⟹ no transition.
    Caveat — O is a 16-component field, so even the fully-DISORDERED value is ≈0.6
    (a 16-dof χ² gives ⟨O²⟩/⟨O⟩²≈1.125 ⟹ U≈0.625), NOT 0. So the single-L VALUE is
    not a clean order/disorder flag; the L-DEPENDENCE (crossing) is the signal."""
    x = np.asarray(x, float)[therm:]
    if len(x) < 2 or x.mean() == 0:
        return np.nan
    return 1.0 - (x * x).mean() / (3.0 * x.mean() ** 2)


def shuffle_noise_floor(h_flat, L, n_shuffle, rng):
    """Tr Q̃² of spatially-shuffled copies (per-component magnitude preserved,
    all spatial coherence destroyed) → the disordered noise floor."""
    V = L ** 4
    vals = []
    for _ in range(n_shuffle):
        hs = np.empty_like(h_flat)
        for mu in range(4):
            for a in range(4):
                hs[:, mu, a] = rng.permutation(h_flat[:, mu, a])
        _, trq2 = hs_auxiliary_field_metric(hs.reshape(L, L, L, L, 4, 4), L)
        vals.append(trq2)
    return float(np.mean(vals)), float(np.std(vals))


def coupling_of(path):
    return float(os.path.basename(path)[1:-4])  # g0.5000.npz -> 0.5


def mass_of_dir(d):
    m = re.search(r'_m([0-9.]+)', os.path.basename(d.rstrip('/')))
    return float(m.group(1)) if m else 0.0


def effective_therm(user_therm, data_is_post_thermalized):
    """Resolve the analysis thermalization cut, avoiding a DOUBLE cut. The run driver
    (run_rhmc_gpu_production.py, both mlx and torch paths) already discards its --n-therm
    trajectories and saves MEASUREMENT-ONLY history, marking that with `n_therm_done` in the
    npz. For such data the analysis must NOT re-thermalize by default — that silently drops
    measurement samples (n_therm=150 driver + old 150 analysis default analyzed a 400-sample
    run on 250). So: post-thermalized data → cut 0; legacy full-chain data (no n_therm_done)
    → the historical 150. An explicit user --therm always wins."""
    if user_therm is not None:
        return user_therm
    return 0 if data_is_post_thermalized else 150


def analyze_dataset(d, user_therm, n_shuffle, rng):
    """Return per-coupling records for one L*_m* directory. `user_therm` may be None →
    per-file auto-resolution of the thermalization cut (see effective_therm)."""
    files = sorted(glob.glob(os.path.join(d, 'g*.npz')), key=coupling_of)
    if not files:
        return None
    d0 = np.load(files[0])
    L = int(d0['L'])
    mass = float(d0['mass']) if 'mass' in d0 else mass_of_dir(d)
    V = L ** 4
    recs = []
    for f in files:
        dd = np.load(f)
        therm = effective_therm(user_therm, 'n_therm_done' in dd.files)
        g = float(dd['g'])
        hsq = autocorr_mean_err(dd['h_sq_history'], therm)[0]
        tet, tet_e, tet_tau = autocorr_mean_err(dd['tet_m2_history'], therm)
        trq, trq_e, trq_tau = autocorr_mean_err(dd['tr_q2_history'], therm)
        # Creutz identity on post-therm ΔH
        dh = np.asarray(dd['delta_h_history'], float)
        dh = dh[therm:] if len(dh) > therm else dh
        creutz = float(np.mean(np.exp(-dh)))
        # tetrad noise floor
        tet_floor = 16.0 * hsq / V
        # traceless-metric shuffle test on the saved final config
        h_flat = dd['h_final'].reshape(V, 4, 4)
        _, trq2_real = hs_auxiliary_field_metric(dd['h_final'].reshape(L, L, L, L, 4, 4), L)
        trq2_noise, trq2_noise_sd = shuffle_noise_floor(h_flat, L, n_shuffle, rng)
        chi_tet = connected_susceptibility(dd['tet_m2_history'], therm, V)
        chi_trq = connected_susceptibility(dd['tr_q2_history'], therm, V)
        recs.append(dict(
            g=g, hsq=hsq, tet=tet, tet_e=tet_e, tet_tau=tet_tau, tet_floor=tet_floor,
            tet_excess=tet - tet_floor, tet_ratio=tet / tet_floor if tet_floor else np.nan,
            trq=trq, trq_e=trq_e, trq_tau=trq_tau,
            trq2_real=trq2_real, trq2_noise=trq2_noise, trq2_noise_sd=trq2_noise_sd,
            trq2_ratio=trq2_real / trq2_noise if trq2_noise else np.nan,
            chi_tet=chi_tet[0], chi_trq=chi_trq[0], creutz=creutz,
            binder_tet=binder_cumulant(dd['tet_m2_history'], therm),
            binder_trq=binder_cumulant(dd['tr_q2_history'], therm),
        ))
    return dict(L=L, mass=mass, V=V, recs=recs)


def print_dataset(ds):
    print(f"\n{'='*92}\n  L={ds['L']}  m={ds['mass']:g}  V={ds['V']}  ({len(ds['recs'])} couplings)\n{'='*92}")
    print(f"{'g':>6} {'<exp-dH>':>9} | {'tet_m2':>9} {'floor':>9} {'t/flr':>6} | "
          f"{'TrQ2real':>9} {'TrQ2noise':>11} {'r/n':>6}  verdict")
    any_signal = False
    for r in ds['recs']:
        v_tet = 'cond' if r['tet_ratio'] > 1.5 else '~floor'
        v_trq = 'ORDER' if r['trq2_ratio'] > 2 else ('?' if r['trq2_ratio'] > 1.3 else 'noise')
        any_signal |= (r['tet_ratio'] > 1.5 or r['trq2_ratio'] > 2)
        print(f"{r['g']:6.3f} {r['creutz']:9.4f} | {r['tet']:9.5f} {r['tet_floor']:9.5f} "
              f"{r['tet_ratio']:6.2f} | {r['trq2_real']:9.4f} "
              f"{r['trq2_noise']:7.4f}±{r['trq2_noise_sd']:4.3f} {r['trq2_ratio']:6.2f}  {v_tet}/{v_trq}")
    print(f"  → {'SIGNAL present (see verdicts)' if any_signal else 'NO resolvable order: both channels consistent with noise floor at all g'}")
    print(f"\n  FSS-gate observables — the go/no-go for L=10/12 (compare these ACROSS L):")
    print(f"{'g':>6} {'χ_tet':>10} {'χ_trq':>10} {'U_tet':>7} {'U_trq':>7}")
    for r in ds['recs']:
        print(f"{r['g']:6.3f} {r['chi_tet']:10.3f} {r['chi_trq']:10.3f} "
              f"{r['binder_tet']:7.3f} {r['binder_trq']:7.3f}")
    print("  Read across volumes: χ growing/peaking as V↑, or Binder curves CROSSING across "
          "L=8/10/12 ⟹ transition (run L=10/12).")
    print("  Flat χ + no Binder crossing across L ⟹ no transition (ship the null; skip L=10/12). "
          "Single-L Binder≈0.6 is the disordered baseline, not order.")


def extrapolate_mzero(datasets):
    """Linear m→0 extrapolation of noise-subtracted order params, per (L, g)."""
    by_L = {}
    for ds in datasets:
        by_L.setdefault(ds['L'], []).append(ds)
    for L, dss in sorted(by_L.items()):
        if len(dss) < 2:
            continue
        masses = sorted(d['mass'] for d in dss)
        print(f"\n{'='*92}\n  m→0 EXTRAPOLATION at L={L}  (masses {masses})\n{'='*92}")
        gs = [r['g'] for r in dss[0]['recs']]
        print(f"{'g':>6} {'tet_excess(m→0)':>16} {'TrQ2-noise(m→0)':>17}")
        for gi, g in enumerate(gs):
            ms, tet_x, trq_x = [], [], []
            for ds in sorted(dss, key=lambda d: d['mass']):
                r = next((x for x in ds['recs'] if abs(x['g'] - g) < 1e-6), None)
                if r is None:
                    continue
                ms.append(ds['mass'])
                tet_x.append(r['tet_excess'])
                trq_x.append(r['trq2_real'] - r['trq2_noise'])
            if len(ms) < 2:
                continue
            tet0 = np.polyfit(ms, tet_x, 1)[1]
            trq0 = np.polyfit(ms, trq_x, 1)[1]
            print(f"{g:6.3f} {tet0:16.5f} {trq0:17.5f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--glob', default='data/rhmc/L*_m*', help='dataset dir glob')
    ap.add_argument('--therm', type=int, default=None,
                    help='thermalization cut (trajectories). Default AUTO: 0 for data the run '
                         'driver already thermalized (n_therm_done in the npz — avoids a double '
                         'cut), 150 for legacy full-chain data. Pass an int to override.')
    ap.add_argument('--n-shuffle', type=int, default=8, help='shuffle replicas for the noise floor')
    ap.add_argument('--seed', type=int, default=0)
    args = ap.parse_args()

    rng = np.random.default_rng(args.seed)
    dirs = sorted(d for d in glob.glob(args.glob) if os.path.isdir(d))
    if not dirs:
        print(f"No dataset dirs matched {args.glob!r}")
        return 1
    therm_desc = 'auto (0 for driver data, 150 legacy)' if args.therm is None else str(args.therm)
    print(f"Analyzing {len(dirs)} dataset(s); therm-cut={therm_desc}, shuffle×{args.n_shuffle}")
    datasets = []
    for d in dirs:
        ds = analyze_dataset(d, args.therm, args.n_shuffle, rng)
        if ds:
            datasets.append(ds)
            print_dataset(ds)
    extrapolate_mzero(datasets)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
