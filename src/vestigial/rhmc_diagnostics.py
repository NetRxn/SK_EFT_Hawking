"""Canonical RHMC run diagnostics + early-stop verdict logic.

Shared by the post-hoc analyzer (`scripts/analyze_rhmc_vestigial.py`) and the
live monitor (`scripts/rhmc_monitor.py`). One source of truth for:

  * autocorrelation-aware statistics (τ_int, effective sample size, errors),
  * the two CONFOUND-corrected order-parameter signals
      - tetrad excess over the finite-V noise floor 16·⟨h²⟩/V,
      - traceless-metric excess over the spatially-shuffled noise floor,
  * the Creutz unbiasedness identity ⟨exp(−ΔH)⟩ = 1, and
  * the per-coupling / aggregate EARLY-STOP verdict.

Early-stop philosophy ("signal when further computation is more likely wasted
than productive"). Three ways compute becomes wasted, plus a correctness alarm:

  RED_BIAS  — the chain is WRONG: ⟨exp(−ΔH)⟩ drifts from 1 (e.g. an FP32 GPU
              force that biases the distribution) or acceptance collapses.
              Every further trajectory is wasted until fixed. (Doubles as the
              mixed-precision certification gate for the GPU port.)
  RED_SLOW  — METHOD-LIMITED: τ_int has grown comparable to the run length, so
              the error bar is unreliable and shrinks far slower than 1/√N.
              More of the SAME compute won't resolve it (needs deflation /
              multigrid / a longer chain than budgeted).
  RED_NULL  — NULL PROVEN: both confound-corrected signals are consistent with
              zero AND the error is already below the smallest effect we care
              about (a fraction `eff_threshold` of the noise floor). Further
              trajectories only shrink an error bar around zero — wasted for
              THIS (L, m) point.
  GREEN     — PRODUCTIVE: a confound-corrected signal exceeds `sig`·error → keep
              going to tighten it (FSS is worth it).
  YELLOW    — INCONCLUSIVE-BUT-PRODUCTIVE: no significant signal yet, but the
              chain is healthy and the error is still above threshold → more
              statistics still buy resolution.
"""
from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np

from src.vestigial.hs_rhmc import hs_auxiliary_field_metric


# ───────────────────────────── statistics ──────────────────────────────

def integrated_autocorr_time(x) -> float:
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
    """Return (mean, std-error-of-mean, τ_int, N_eff) with autocorrelation
    correction. N_eff = N/(2τ); error = std/√N_eff."""
    x = np.asarray(x, float)[therm:]
    n = len(x)
    if n == 0:
        return np.nan, np.nan, np.nan, 0.0
    tau = integrated_autocorr_time(x)
    neff = n / (2 * tau)
    err = x.std(ddof=1) / np.sqrt(max(neff, 1.0)) if n > 1 else np.nan
    return x.mean(), err, tau, neff


def creutz_identity(delta_h, therm):
    """⟨exp(−ΔH)⟩ over post-thermalization ΔH, with a jackknife-free error.
    Equals 1 for an unbiased chain; deviation flags a biased force."""
    dh = np.asarray(delta_h, float)
    dh = dh[therm:] if len(dh) > therm else dh
    if len(dh) == 0:
        return np.nan, np.nan
    w = np.exp(-dh)
    tau = integrated_autocorr_time(w)
    neff = len(w) / (2 * tau)
    return float(w.mean()), float(w.std(ddof=1) / np.sqrt(max(neff, 1.0)))


def tetrad_noise_floor(hsq_mean, V):
    """Finite-volume noise floor of tet_m2 = |⟨h⟩_vol|²  (≈ 16·⟨h²⟩/V)."""
    return 16.0 * hsq_mean / V


def shuffle_metric_floor(h_final, L, n_shuffle, rng):
    """Disordered noise floor of Tr Q̃²: mean ± sd of Tr Q̃² over spatial
    shuffles of the final config (per-component magnitude preserved, all
    spatial coherence destroyed)."""
    V = L ** 4
    h_flat = np.asarray(h_final, float).reshape(V, 4, 4)
    vals = []
    for _ in range(n_shuffle):
        hs = np.empty_like(h_flat)
        for mu in range(4):
            for a in range(4):
                hs[:, mu, a] = rng.permutation(h_flat[:, mu, a])
        _, trq2 = hs_auxiliary_field_metric(hs.reshape(L, L, L, L, 4, 4), L)
        vals.append(trq2)
    return float(np.mean(vals)), float(np.std(vals))


# ───────────────────────── early-stop verdict ──────────────────────────

@dataclass
class StopThresholds:
    therm_frac: float = 1.0 / 3.0   # therm cut = min(therm_abs, therm_frac·N)
    therm_abs: int = 150
    sig: float = 3.0                # signal significance → GREEN
    null_sig: float = 2.0           # below this → consistent with null
    eff_threshold: float = 0.25     # resolve/exclude an excess of this·floor
    neff_min: float = 10.0          # < this many independent samples → error
    #                                 untrustworthy; a null is not yet airtight
    slow_frac: float = 0.15         # τ > slow_frac·N_meas → critical slowing.
    #                                 N_eff = N/(2τ) < 1/(2·0.15) ≈ 3 independent
    #                                 samples: genuinely method-limited (the
    #                                 windowed τ estimator also saturates near
    #                                 N/6, so this is its practical ceiling).
    creutz_tol: float = 0.10        # |⟨e^-ΔH⟩−1| beyond max(tol, 3σ) → biased
    #                                 (the exp estimator is high-variance and
    #                                  skews high at small g for healthy chains;
    #                                  a genuine FP32 bias drifts well past 10%)
    acc_floor: float = 0.60         # acceptance below this → unhealthy chain
    n_shuffle: int = 12


@dataclass
class CouplingVerdict:
    g: float
    n_traj: int
    n_meas: int
    acceptance: float
    creutz: float
    creutz_err: float
    tet_excess: float
    tet_err: float
    tet_sig: float
    tet_floor: float
    met_excess: float
    met_err: float
    met_sig: float
    met_floor: float
    tau_tet: float
    tau_met: float
    neff: float
    status: str = "YELLOW"
    reasons: list = field(default_factory=list)


def assess_coupling(d, thr: StopThresholds, rng) -> CouplingVerdict:
    """Assess one coupling's saved arrays (an npz mapping) → CouplingVerdict."""
    g = float(d["g"])
    L = int(d["L"])
    V = L ** 4
    n_traj = len(d["h_sq_history"])
    therm = min(thr.therm_abs, int(thr.therm_frac * n_traj))
    n_meas = max(n_traj - therm, 0)

    hsq, *_ = autocorr_mean_err(d["h_sq_history"], therm)
    tet, tet_e, tau_tet, neff_t = autocorr_mean_err(d["tet_m2_history"], therm)
    _trq, _trq_e, tau_met, neff_m = autocorr_mean_err(d["tr_q2_history"], therm)
    creutz, creutz_e = creutz_identity(d["delta_h_history"], therm)
    acc = float(d["acceptance_rate"]) if "acceptance_rate" in d else np.nan

    # Tetrad channel — HISTORY-based, the trustworthy signal: mean and floor
    # (16⟨h²⟩/V) are both derived from the same trajectory history.
    tet_floor = tetrad_noise_floor(hsq, V)
    tet_excess = tet - tet_floor
    tet_sig = tet_excess / tet_e if tet_e and tet_e > 0 else 0.0
    # "resolved" requires BOTH a small error AND enough independent samples that
    # the error (and τ) are themselves trustworthy.
    tet_resolved = (tet_e is not None and tet_e < thr.eff_threshold * tet_floor
                    and neff_t >= thr.neff_min)

    # Metric channel — SNAPSHOT-only z-score until per-traj Q is instrumented:
    # compare Tr Q̃² of the (un-shuffled) final config against its own shuffle
    # floor. One config ⟹ low statistical power ⟹ DISPLAY/flag, never the sole
    # driver of a hard verdict (the very gap workstream-2 instrumentation closes).
    _, trq2_real = hs_auxiliary_field_metric(np.asarray(d["h_final"], float).reshape(L, L, L, L, 4, 4), L)
    met_floor, met_floor_sd = shuffle_metric_floor(d["h_final"], L, thr.n_shuffle, rng)
    met_excess = trq2_real - met_floor
    met_z = met_excess / met_floor_sd if met_floor_sd > 0 else 0.0

    neff = min(neff_t, neff_m)
    v = CouplingVerdict(
        g=g, n_traj=n_traj, n_meas=n_meas, acceptance=acc,
        creutz=creutz, creutz_err=creutz_e,
        tet_excess=tet_excess, tet_err=tet_e, tet_sig=tet_sig, tet_floor=tet_floor,
        met_excess=met_excess, met_err=met_floor_sd, met_sig=met_z, met_floor=met_floor,
        tau_tet=tau_tet, tau_met=tau_met, neff=neff,
    )
    met_note = f"[metric snapshot {met_z:+.1f}z, low-confidence]"

    # 1) Correctness alarm — wrong chain (or FP32-biased GPU force).
    if not np.isnan(creutz) and abs(creutz - 1.0) > max(thr.creutz_tol, 3 * creutz_e):
        v.status = "RED_BIAS"
        v.reasons.append(f"⟨e^-ΔH⟩={creutz:.3f}≠1 (±{creutz_e:.3f}) — biased force/precision")
        return v
    if not np.isnan(acc) and acc < thr.acc_floor:
        v.status = "RED_BIAS"
        v.reasons.append(f"acceptance {acc:.2f} < {thr.acc_floor:.2f} — chain unhealthy")
        return v

    # 2) Critical slowing — τ comparable to run length; error unreliable.
    if n_meas > 0 and max(tau_tet, tau_met) > thr.slow_frac * n_meas:
        v.status = "RED_SLOW"
        v.reasons.append(
            f"τ_int={max(tau_tet, tau_met):.0f} ≳ {thr.slow_frac:.0%}·{n_meas} measured "
            f"— autocorr unresolved, error won't shrink ~1/√N (needs deflation/longer chain)")
        return v

    # Signal is one-sided: only a POSITIVE excess over the floor is a condensate;
    # a downward fluctuation below the floor is still "no order".
    # 3) Productive — a trustworthy (tetrad) signal is significant.
    if tet_sig > thr.sig:
        v.status = "GREEN"
        v.reasons.append(f"SIGNAL: tetrad {tet_sig:.1f}σ over floor — keep going to tighten  {met_note}")
        return v

    # 4) Inconclusive but productive — a positive hint, a low-confidence metric
    #    snapshot, or simply not yet resolved → more statistics still buy us something.
    if tet_sig > thr.null_sig:
        v.status = "YELLOW"
        v.reasons.append(f"INCONCLUSIVE: tetrad +{tet_sig:.1f}σ positive hint (< {thr.sig:.0f}σ) "
                         f"— more statistics to confirm/deny  {met_note}")
        return v
    if met_z > thr.sig:
        v.status = "YELLOW"
        v.reasons.append(f"INCONCLUSIVE: metric snapshot +{met_z:.1f}z (low-confidence, needs per-traj Q) "
                         f"— instrument + more statistics  {met_note}")
        return v
    if not tet_resolved:
        v.status = "YELLOW"
        if neff_t < thr.neff_min:
            v.reasons.append(f"INCONCLUSIVE: only {neff_t:.0f} independent samples (< {thr.neff_min:.0f}); "
                             f"error/τ untrustworthy — more trajectories (or a better solver if N_eff stalls)  {met_note}")
        else:
            v.reasons.append(f"INCONCLUSIVE: tetrad error {tet_e/tet_floor:.0%} of floor, above the "
                             f"{thr.eff_threshold:.0%} target — more statistics productive  {met_note}")
        return v

    # 5) Null proven — tetrad ≤ null_sig (incl. downward) AND resolved below the
    #    interesting scale; metric snapshot not showing excess either.
    v.status = "RED_NULL"
    v.reasons.append(
        f"tetrad {tet_sig:+.1f}σ (≤ {thr.null_sig:.0f}σ) AND error < {thr.eff_threshold:.0%}·floor "
        f"— null proven; further trajectories only shrink an error bar around zero  {met_note}")
    return v


def aggregate_status(verdicts):
    """Roll up per-coupling verdicts into one scan-level recommendation."""
    statuses = [v.status for v in verdicts]
    if any(s == "RED_BIAS" for s in statuses):
        return "STOP-FIX", "correctness alarm on ≥1 coupling — results untrustworthy until fixed"
    if any(s == "GREEN" for s in statuses):
        n = sum(s == "GREEN" for s in statuses)
        return "KEEP-GOING", f"signal emerging on {n} coupling(s) — FSS is worth it"
    if any(s == "RED_SLOW" for s in statuses):
        n = sum(s == "RED_SLOW" for s in statuses)
        return "METHOD-LIMITED", f"{n} coupling(s) autocorrelation-limited — more of the same compute won't resolve"
    if statuses and all(s == "RED_NULL" for s in statuses):
        return "STOP-NULL", "null proven to precision at every coupling — stop this (L,m); compute now wasted"
    return "MORE-STATS", "inconclusive but healthy — more statistics still productive"
