#!/usr/bin/env python3
"""Production 8×8 Majorana fermion-bag MC with Kramers positivity.

Runs finite-size scaling analysis for the vestigial metric phase using
the sign-problem-free Majorana formulation (Wave 7B).

Key physics: {J₂, A} = 0 → Pf(A) definite sign → no sign problem.
Measurements: tetrad E^a, metric g_μν = δ_{ab} E^a E^b, plaquette.
Order parameters: Binder cumulants U₄(tetrad), U₄(metric).

Features:
  - Incremental save: results saved after EACH coupling point
  - Checkpoint/resume: --resume picks up where a previous run left off
  - Logging: real-time console + file log with timestamps
  - NaN/Inf validation on every measurement result

Output: JSON with full measurement history + summary statistics.

Usage:
  # L=4 quick test
  uv run python scripts/run_majorana_production.py --sizes 4 --n-measure 50

  # L=4 production
  uv run python scripts/run_majorana_production.py --sizes 4

  # Resume interrupted run
  uv run python scripts/run_majorana_production.py --resume docs/vestigial_mc_results/majorana_8x8_20260401T2200.json

  # Custom coupling range
  uv run python scripts/run_majorana_production.py --sizes 4 --g-min 0.5 --g-max 8.0 --n-couplings 16

Lean: adw_sign_problem_free (MajoranaKramers.lean)
Source: Wei/Wu/Li/Zhang/Xiang, PRL 116, 250601 (2016)
"""

import argparse
import json
import logging
import sys
import time
import numpy as np
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

OUT_DIR = Path("docs/vestigial_mc_results")

logger = logging.getLogger("majorana_production")


def setup_logging(out_file: Path):
    """Configure logging to console + file."""
    log_file = out_file.with_suffix(".log")
    fmt = logging.Formatter("%(asctime)s %(levelname)s %(message)s",
                            datefmt="%H:%M:%S")
    fh = logging.FileHandler(log_file, mode="a")
    fh.setFormatter(fmt)
    ch = logging.StreamHandler(sys.stdout)
    ch.setFormatter(fmt)
    logger.addHandler(fh)
    logger.addHandler(ch)
    logger.setLevel(logging.INFO)
    return log_file


def result_to_dict(r):
    """Convert a single MajoranaMCResult to a serializable dict."""
    return {
        "g": r.g,
        "beta": r.beta,
        "L": r.L,
        "n_measurements": r.n_measurements,
        "sign_free": r.sign_free,
        "tetrad_m2": r.tetrad_m2,
        "tetrad_m4": r.tetrad_m4,
        "binder_tetrad": r.binder_tetrad,
        "metric_m2": r.metric_m2,
        "metric_m4": r.metric_m4,
        "binder_metric": r.binder_metric,
        "acceptance_fermion": r.acceptance_fermion,
        "acceptance_gauge": r.acceptance_gauge,
        "avg_plaquette": float(np.mean(r.avg_plaquette)) if r.avg_plaquette else 0.0,
        "tetrad_magnitude_history": [float(x) for x in r.tetrad_magnitude],
        "metric_trace_sq_history": [float(x) for x in r.metric_trace_sq],
        "plaquette_history": [float(x) for x in r.avg_plaquette],
    }


def validate_result(pt: dict, g: float, L: int) -> list[str]:
    """Check for NaN/Inf in a single coupling point result."""
    issues = []
    for key in ["tetrad_m2", "tetrad_m4", "binder_tetrad",
                "metric_m2", "metric_m4", "binder_metric",
                "acceptance_fermion", "acceptance_gauge", "avg_plaquette"]:
        val = pt.get(key, 0)
        if np.isnan(val) or np.isinf(val):
            issues.append(f"L={L} g={g:.3f}: {key} = {val}")
    return issues


def save_checkpoint(data: dict, out_file: Path):
    """Atomically save checkpoint (write to tmp then rename)."""
    tmp = out_file.with_suffix(".tmp")
    with open(tmp, "w") as f:
        json.dump(data, f, indent=2)
    tmp.rename(out_file)


def load_checkpoint(path: Path) -> dict:
    """Load a previous run's data for resumption."""
    with open(path) as f:
        return json.load(f)


def get_completed_points(data: dict, L: int) -> set:
    """Return set of coupling values already completed for this L."""
    L_str = str(L)
    if L_str not in data.get("sizes", {}):
        return set()
    return {pt["g"] for pt in data["sizes"][L_str].get("points", [])}


def run_single_point(L, g, beta, n_therm, n_measure, n_skip, seed):
    """Run a single coupling point (no multiprocessing)."""
    from src.vestigial.gauge_fermion_bag_majorana import run_majorana_mc_fast
    return run_majorana_mc_fast(L, g, beta, n_therm, n_measure, n_skip, seed)


def main():
    parser = argparse.ArgumentParser(
        description="8×8 Majorana production MC scan (incremental + resumable)")
    parser.add_argument("--sizes", type=int, nargs="+", default=[4])
    parser.add_argument("--g-min", type=float, default=0.5)
    parser.add_argument("--g-max", type=float, default=8.0)
    parser.add_argument("--n-couplings", type=int, default=16)
    parser.add_argument("--beta", type=float, default=2.0)
    parser.add_argument("--n-therm", type=int, default=100)
    parser.add_argument("--n-measure", type=int, default=200)
    parser.add_argument("--n-skip", type=int, default=2)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--workers", type=int, default=None,
                        help="Max parallel workers (default: cpu_count - 2)")
    parser.add_argument("--output-dir", type=str, default=str(OUT_DIR))
    parser.add_argument("--resume", type=str, default=None,
                        help="Path to JSON checkpoint to resume from")
    args = parser.parse_args()

    g_values = np.linspace(args.g_min, args.g_max, args.n_couplings)
    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Load or create data structure
    if args.resume:
        data = load_checkpoint(Path(args.resume))
        out_file = Path(args.resume)
        logger.info(f"Resuming from {args.resume}")
    else:
        timestamp = datetime.now().strftime("%Y%m%dT%H%M%S")
        out_file = out_dir / f"majorana_8x8_{timestamp}.json"
        data = {
            "algorithm": "majorana_8x8_kramers",
            "sign_free": True,
            "timestamp": timestamp,
            "parameters": {
                "g_values": g_values.tolist(),
                "beta": args.beta,
                "n_therm": args.n_therm,
                "n_measure": args.n_measure,
                "n_skip": args.n_skip,
                "base_seed": args.seed,
            },
            "sizes": {},
        }

    log_file = setup_logging(out_file)
    logger.info(f"Majorana 8x8 Production Scan")
    logger.info(f"  Output: {out_file}")
    logger.info(f"  Log: {log_file}")
    logger.info(f"  Sizes: {args.sizes}, couplings: {len(g_values)}, "
                f"beta={args.beta}")
    logger.info(f"  therm={args.n_therm}, measure={args.n_measure}, "
                f"skip={args.n_skip}, seed={args.seed}")

    n_workers = args.workers
    if n_workers is None:
        import multiprocessing as mp
        n_workers = max(1, mp.cpu_count() - 2)

    all_issues = []
    total_t0 = time.time()

    for L in args.sizes:
        L_str = str(L)
        if L_str not in data["sizes"]:
            data["sizes"][L_str] = {
                "L": L, "elapsed_seconds": 0, "n_points": 0, "points": []
            }

        completed = get_completed_points(data, L)
        remaining = [(i, g) for i, g in enumerate(g_values)
                     if round(g, 10) not in {round(c, 10) for c in completed}]

        if not remaining:
            logger.info(f"L={L}: all {len(g_values)} points already complete, skipping")
            continue

        logger.info(f"L={L}: {len(remaining)} points remaining "
                    f"({len(completed)} already done)")

        L_t0 = time.time()
        for idx, (i, g) in enumerate(remaining):
            pt_t0 = time.time()
            seed = args.seed + i
            logger.info(f"  L={L} g={g:.3f} [{idx+1}/{len(remaining)}] "
                        f"seed={seed} ...")

            try:
                r = run_single_point(
                    L, g, args.beta, args.n_therm, args.n_measure,
                    args.n_skip, seed)
                pt = result_to_dict(r)
            except Exception as e:
                logger.error(f"  L={L} g={g:.3f} FAILED: {e}")
                continue

            # Validate
            issues = validate_result(pt, g, L)
            if issues:
                for iss in issues:
                    logger.warning(f"  VALIDATION: {iss}")
                all_issues.extend(issues)

            elapsed_pt = time.time() - pt_t0
            logger.info(
                f"  L={L} g={g:.3f} done in {elapsed_pt:.1f}s — "
                f"acc_f={pt['acceptance_fermion']:.3f} "
                f"acc_g={pt['acceptance_gauge']:.3f} "
                f"U4_tet={pt['binder_tetrad']:.6f} "
                f"U4_met={pt['binder_metric']:.6f}")

            # Append and save incrementally
            data["sizes"][L_str]["points"].append(pt)
            data["sizes"][L_str]["n_points"] = len(data["sizes"][L_str]["points"])
            data["sizes"][L_str]["elapsed_seconds"] = time.time() - L_t0
            save_checkpoint(data, out_file)

        logger.info(f"L={L} complete: {time.time()-L_t0:.1f}s")

    total_elapsed = time.time() - total_t0
    data["total_elapsed_seconds"] = total_elapsed
    save_checkpoint(data, out_file)

    logger.info(f"\nTotal: {total_elapsed:.1f}s ({total_elapsed/60:.1f} min)")
    logger.info(f"Results: {out_file}")
    if all_issues:
        logger.warning(f"\n{len(all_issues)} validation issues found!")
        for iss in all_issues:
            logger.warning(f"  {iss}")
    else:
        logger.info("All results validated (no NaN/Inf)")

    # Summary table
    print(f"\n{'='*80}")
    print(f"{'g':>6} {'tet_m2':>10} {'U4_tet':>10} {'met_m2':>10} "
          f"{'U4_met':>10} {'plaq':>8} {'acc_f':>7} {'acc_g':>7}")
    print(f"{'-'*80}")
    for L in args.sizes:
        L_str = str(L)
        if L_str not in data["sizes"]:
            continue
        print(f"  L={L}:")
        for pt in sorted(data["sizes"][L_str]["points"], key=lambda p: p["g"]):
            print(f"{pt['g']:6.2f} {pt['tetrad_m2']:10.6f} "
                  f"{pt['binder_tetrad']:10.6f} {pt['metric_m2']:10.6f} "
                  f"{pt['binder_metric']:10.6f} {pt['avg_plaquette']:8.4f} "
                  f"{pt['acceptance_fermion']:7.3f} {pt['acceptance_gauge']:7.3f}")


if __name__ == "__main__":
    main()
