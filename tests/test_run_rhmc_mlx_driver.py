"""Driver-level unit tests for the MLX backend of run_rhmc_gpu_production.

These cover the non-engine concerns: RNG decorrelation (review finding 2) and
resume/checkpoint correctness (review findings on stop/start). They import the
driver module directly; it guards its torch import so this works with or without
torch installed.
"""
import numpy as np
import pytest

pytest.importorskip("mlx.core")
import scripts.run_rhmc_gpu_production as drv


def test_fresh_trajectory_rng_decorrelated_from_init_config():
    # Review finding 2: on a FRESH run the trajectory RNG must not reuse the same numpy
    # stream as the initial-config RNG, or the first trajectory's noise correlates with
    # the starting configuration. init config uses default_rng(seed); the trajectory RNG
    # must be a decorrelated namespace, still advancing with n_done for resume.
    seed = 2026
    cfg_normals = np.random.default_rng(seed).standard_normal(256)      # what _fresh_config draws from
    traj_rng = drv._trajectory_rng(seed, 0)                            # fresh run: n_done = 0
    traj_normals = traj_rng.standard_normal(256)
    # the OLD code did default_rng(seed + 0) == default_rng(seed) -> identical stream (BUG)
    assert not np.allclose(cfg_normals, traj_normals)


def test_trajectory_rng_advances_with_n_done():
    # Resume continuation: different chunks (different n_done) get independent streams,
    # so a resumed run is a statistically-valid continuation, not a repeat.
    seed = 7
    a = drv._trajectory_rng(seed, 0).standard_normal(128)
    b = drv._trajectory_rng(seed, 100).standard_normal(128)
    assert not np.allclose(a, b)


def test_build_coeffs_lambda_bounds_true_spectrum():
    # Guards the reject-all failure mode: build_coeffs_mlx estimates λmax in FP32 for
    # speed (re-run every resume), then pads 1.25×. The returned (padded) lam MUST exceed
    # the true λmax of a matched-amplitude configuration, or the Zolotarev range is too
    # small and the rational approximation degrades → acceptance collapses. Checked at L=2
    # where a dense eigen-solve is the ground truth.
    import numpy as _np
    import mlx.core as mx
    import src.vestigial.hs_rhmc_mlx as me
    L, V, g, msq = 2, 2 ** 4, 2.0, 0.04
    _, lam_padded = drv.build_coeffs_mlx(L, g, msq, 12, seed=5)

    fwd, back = me.neighbor_tables(L)
    amp = _np.sqrt(2.0 * g)
    worst = 0.0
    for s in range(8):                                    # several matched-amplitude configs
        cfg = amp * _np.random.default_rng(1000 + s).standard_normal((V, 4, 4))
        blk = me.hopping_blocks(mx.array(cfg, dtype=mx.float64), L)
        # dense A†A via apply_AtA on the identity, then eigvalsh
        nF = V * 8
        cols = [_np.array(me.apply_AtA(mx.array(_np.eye(nF)[i].reshape(V, 8), dtype=mx.float64),
                                       blk, fwd, back)).reshape(nF) for i in range(nF)]
        lam_true = float(_np.linalg.eigvalsh(_np.stack(cols, 1)).max())
        worst = max(worst, lam_true)
    assert lam_padded > worst, (lam_padded, worst)


def test_fresh_config_matches_documented_formula():
    # _fresh_config is sqrt(2g)*N(0,1) from default_rng(seed) — pin it so a refactor
    # can't silently change the starting distribution.
    seed, g = 3, 2.0
    shape = (2, 16, 4, 4)
    got = drv._fresh_config(seed, g, shape)
    expected = np.sqrt(2 * g) * np.random.default_rng(seed).standard_normal(shape)
    assert np.allclose(got, expected)
