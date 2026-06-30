#!/usr/bin/env python3
"""Live early-stop monitor for HS+RHMC production scans.

Emits a per-coupling + scan-level verdict answering the operator's question:
"is further computation more likely wasted than productive?"  See
`src/vestigial/rhmc_diagnostics.py` for the verdict philosophy (RED_BIAS /
RED_SLOW / RED_NULL / GREEN / YELLOW and the scan-level roll-up).

The RED_BIAS alarm (⟨exp(−ΔH)⟩ drifting from 1) is also the certification gate
for the mixed-precision GPU port: a float32 force that biases the chain trips it.

Usage:
  # one-shot report on a finished/partial scan
  PYTHONPATH=. uv run python scripts/rhmc_monitor.py data/rhmc/L8_m0.1

  # live watch (re-scan every 300 s) of a running scan
  PYTHONPATH=. uv run python scripts/rhmc_monitor.py data/rhmc/L8_m0.1 --watch 300

  # tighten what counts as an "interesting" effect (resolve excess > 10% of floor)
  PYTHONPATH=. uv run python scripts/rhmc_monitor.py data/rhmc/L8_m0.1 --eff-threshold 0.10
"""
import argparse
import glob
import os
import time

import numpy as np

from src.vestigial.rhmc_diagnostics import (
    StopThresholds, assess_coupling, aggregate_status,
)

# ANSI colors keyed by status (disabled with --no-color or when not a TTY)
_COLOR = {
    "GREEN": "\033[32m", "YELLOW": "\033[33m",
    "RED_NULL": "\033[31m", "RED_SLOW": "\033[35m", "RED_BIAS": "\033[1;41m",
}
_AGG_COLOR = {
    "KEEP-GOING": "\033[32m", "MORE-STATS": "\033[33m",
    "STOP-NULL": "\033[31m", "METHOD-LIMITED": "\033[35m", "STOP-FIX": "\033[1;41m",
}
_RESET = "\033[0m"


def _coupling_of(path):
    return float(os.path.basename(path)[1:-4])


def report(data_dir, thr, rng, use_color):
    files = sorted(glob.glob(os.path.join(data_dir, "g*.npz")), key=_coupling_of)
    if not files:
        print(f"  (no g*.npz in {data_dir} yet)")
        return None
    d0 = np.load(files[0])
    L = int(d0["L"])
    mass = float(d0["mass"]) if "mass" in d0 else float("nan")
    hdr = f"  {os.path.basename(data_dir)}  L={L}  m={mass:g}  ({len(files)} couplings)"
    print(hdr)
    print(f"  {'g':>6} {'N':>5} {'acc':>5} {'<e^-dH>':>8} "
          f"{'tet σ':>7} {'met z':>7} {'τmax':>5}  verdict   (met z = low-conf snapshot)")
    verdicts = []
    for f in files:
        try:
            v = assess_coupling(np.load(f), thr, rng)
        except Exception as e:  # a chunk mid-write, etc. — skip this poll
            print(f"  {_coupling_of(f):>6.3f}  (skipped: {type(e).__name__})")
            continue
        verdicts.append(v)
        c = _COLOR.get(v.status, "") if use_color else ""
        r = _RESET if use_color else ""
        print(f"  {v.g:>6.3f} {v.n_traj:>5} {v.acceptance:>5.2f} {v.creutz:>8.3f} "
              f"{v.tet_sig:>7.1f} {v.met_sig:>7.1f} {max(v.tau_tet, v.tau_met):>5.0f}  "
              f"{c}{v.status:<8}{r} {v.reasons[0] if v.reasons else ''}")
    if not verdicts:
        return None
    agg, why = aggregate_status(verdicts)
    c = _AGG_COLOR.get(agg, "") if use_color else ""
    r = _RESET if use_color else ""
    print(f"\n  ►► SCAN VERDICT: {c}{agg}{r} — {why}")
    return agg


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("data_dir", help="a data/rhmc/L*_m* directory (or parent for --all)")
    ap.add_argument("--all", action="store_true", help="treat data_dir as parent; scan every L*_m* child")
    ap.add_argument("--watch", type=float, default=0.0, metavar="SEC", help="re-scan every SEC seconds")
    ap.add_argument("--therm", type=int, default=150, help="absolute thermalization cut")
    ap.add_argument("--eff-threshold", type=float, default=0.25, help="resolve/exclude excess > this·floor")
    ap.add_argument("--sig", type=float, default=3.0, help="σ to declare GREEN signal")
    ap.add_argument("--null-sig", type=float, default=2.0, help="σ below which a channel is null")
    ap.add_argument("--n-shuffle", type=int, default=8, help="shuffle replicas for the metric floor")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--no-color", action="store_true")
    args = ap.parse_args()

    thr = StopThresholds(
        therm_abs=args.therm, eff_threshold=args.eff_threshold,
        sig=args.sig, null_sig=args.null_sig, n_shuffle=args.n_shuffle,
    )
    use_color = not args.no_color and os.isatty(1)
    rng = np.random.default_rng(args.seed)

    def scan_once():
        if args.all:
            dirs = sorted(d for d in glob.glob(os.path.join(args.data_dir, "L*_m*"))
                          if os.path.isdir(d))
        else:
            dirs = [args.data_dir]
        for d in dirs:
            report(d, thr, rng, use_color)
            print()

    if args.watch > 0:
        print(f"watching (every {args.watch:g}s; Ctrl-C to stop)\n")
        try:
            while True:
                print("\033[2J\033[H" if use_color else f"\n{'='*70}")
                print(time.strftime("%Y-%m-%d %H:%M:%S"))
                scan_once()
                time.sleep(args.watch)
        except KeyboardInterrupt:
            print("\nstopped.")
    else:
        scan_once()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
