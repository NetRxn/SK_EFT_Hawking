"""
Verified statistical analysis for RHMC Monte Carlo data.

Connects the formally verified statistical estimators (VerifiedJackknife.lean,
VerifiedStatistics.lean) to the RHMC production data. All statistics are
computed via canonical functions in formulas.py.

Usage:
    from src.vestigial.verified_analysis import analyze_rhmc_coupling

    results = analyze_rhmc_coupling('data/rhmc/L8/g5.6923.npz')
"""

import numpy as np
from pathlib import Path
from src.core.formulas import (
    jackknife_variance,
    autocovariance,
    integrated_autocorrelation_time,
    effective_sample_size,
    bootstrap_confidence_interval,
)
from src.adw.tetrad_observables import (
    tetrad_order_parameter,
    metric_order_parameter,
    binder_cumulant,
)


def analyze_rhmc_coupling(data_path, thermalization_fraction=0.2):
    """
    Full statistical analysis of an RHMC data file at a single coupling.

    Computes: mean, jackknife error, bootstrap CI, autocorrelation time,
    effective sample size for the h-field magnitude (tetrad proxy).

    Args:
        data_path: path to .npz file from run_rhmc_production.py
        thermalization_fraction: fraction of trajectories to discard

    Returns:
        dict with all statistical quantities
    """
    data = np.load(data_path)

    configs = data.get('configs', data.get('h_configs', None))
    if configs is None:
        return {'error': 'No configuration data found'}

    n_total = len(configs)
    n_therm = int(n_total * thermalization_fraction)
    configs = configs[n_therm:]
    n_meas = len(configs)

    if n_meas < 10:
        return {'error': f'Only {n_meas} measurements after thermalization'}

    # Tetrad order parameter: |<h>| (magnitude of h-field average per config)
    h_mag = np.array([np.mean(np.abs(c)) for c in configs])

    # h^2 for Binder cumulant
    h_sq = h_mag ** 2

    # Compute statistics using verified estimators
    mean_h, jk_var = jackknife_variance(h_mag)
    jk_err = np.sqrt(jk_var)

    _, ci_low, ci_high = bootstrap_confidence_interval(h_mag)

    n_eff, tau_int, W = effective_sample_size(h_mag)

    C = autocovariance(h_mag, min(n_meas // 4, 200))
    rho = C / C[0] if C[0] > 0 else np.zeros_like(C)

    # Binder cumulant: U4 = 1 - <h^4>/(3<h^2>^2)
    h4_mean = np.mean(h_mag ** 4)
    h2_mean = np.mean(h_sq)
    U4 = 1.0 - h4_mean / (3 * h2_mean ** 2) if h2_mean > 0 else 0.0

    # Extract coupling from filename
    coupling = None
    fname = Path(data_path).stem
    if '_g' in fname:
        try:
            coupling = float(fname.split('_g')[1])
        except ValueError:
            pass

    return {
        'coupling': coupling,
        'n_total': n_total,
        'n_meas': n_meas,
        'mean': mean_h,
        'jackknife_error': jk_err,
        'jackknife_variance': jk_var,
        'bootstrap_ci_low': ci_low,
        'bootstrap_ci_high': ci_high,
        'tau_int': tau_int,
        'tau_window': W,
        'n_eff': n_eff,
        'binder_U4': U4,
        'h2_mean': h2_mean,
        'autocorrelation': rho[:min(50, len(rho))].tolist(),
    }


def analyze_rhmc_scan(data_dir, lattice_size, thermalization_fraction=0.2):
    """
    Analyze all RHMC data files for a given lattice size.

    Args:
        data_dir: directory containing per-lattice subdirectories (e.g. data/rhmc)
        lattice_size: integer lattice size (4, 6, 8)
        thermalization_fraction: fraction to discard

    Returns:
        list of result dicts sorted by coupling
    """
    data_dir = Path(data_dir) / f'L{lattice_size}'
    pattern = 'g*.npz'
    files = sorted(data_dir.glob(pattern))

    results = []
    for f in files:
        result = analyze_rhmc_coupling(f, thermalization_fraction)
        if 'error' not in result:
            results.append(result)

    return sorted(results, key=lambda r: r.get('coupling', 0))
