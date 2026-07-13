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


def test_fresh_config_matches_documented_formula():
    # _fresh_config is sqrt(2g)*N(0,1) from default_rng(seed) — pin it so a refactor
    # can't silently change the starting distribution.
    seed, g = 3, 2.0
    shape = (2, 16, 4, 4)
    got = drv._fresh_config(seed, g, shape)
    expected = np.sqrt(2 * g) * np.random.default_rng(seed).standard_normal(shape)
    assert np.allclose(got, expected)
