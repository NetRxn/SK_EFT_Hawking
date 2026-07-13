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


# --- checkpoint / resume (stop-start without losing work) ------------------------------------

def _write_ckpt(path, **extra):
    base = dict(h_sq_history=np.zeros(0), delta_h_history=np.zeros(0),
                tet_m2_history=np.zeros(0), tr_q2_history=np.zeros(0),
                m_h_history=np.zeros((0, 2, 4, 4)), Q_history=np.zeros((0, 2, 4, 4)),
                h_state=np.zeros((2, 16, 4, 4)), g=np.float64(2.0), L=np.int64(2))
    base.update(extra)
    np.savez(path, **base)


def test_resume_fresh_run(tmp_path):
    st = drv._load_checkpoint(str(tmp_path / "none.npz"), seed=5, g=2.0, shape=(2, 16, 4, 4), n_therm=100)
    assert st['n_done'] == 0 and st['n_therm_done'] == 0 and st['therm_left'] == 100
    assert st['nacc'] == 0 and st['ntot'] == 0


def test_resume_mid_thermalization_continues_not_restart(tmp_path):
    # Stopping mid-thermalization must resume the REMAINING thermalization, not redo all
    # of it (the biggest "lost work" case: ~n_therm trajectories at L=8 = ~45 min).
    p = str(tmp_path / "g2.npz")
    _write_ckpt(p, n_therm_done=np.int64(30), nacc=np.int64(0), ntot=np.int64(0))
    st = drv._load_checkpoint(p, seed=5, g=2.0, shape=(2, 16, 4, 4), n_therm=100)
    assert st['n_therm_done'] == 30 and st['therm_left'] == 70 and st['n_done'] == 0


def test_resume_post_therm_with_measurements(tmp_path):
    p = str(tmp_path / "g2.npz")
    _write_ckpt(p, tet_m2_history=np.zeros(5), n_therm_done=np.int64(100),
                nacc=np.int64(480), ntot=np.int64(500))
    st = drv._load_checkpoint(p, seed=5, g=2.0, shape=(2, 16, 4, 4), n_therm=100)
    assert st['n_done'] == 5 and st['therm_left'] == 0
    assert st['nacc'] == 480 and st['ntot'] == 500        # cumulative accept restored


def test_resume_old_npz_without_therm_field_assumes_thermalized(tmp_path):
    # Backward compat: an old checkpoint (pre-n_therm_done) is a post-thermalization
    # measurement run, so resume must NOT re-thermalize it.
    p = str(tmp_path / "g2.npz")
    _write_ckpt(p, tet_m2_history=np.zeros(3))            # no n_therm_done / nacc / ntot
    st = drv._load_checkpoint(p, seed=5, g=2.0, shape=(2, 16, 4, 4), n_therm=100)
    assert st['therm_left'] == 0 and st['n_done'] == 3


def test_stop_start_continues_and_preserves_acceptance(tmp_path):
    # End-to-end stop/start on Metal (L=2): run to completion, then (a) re-invoking with
    # the same n_meas is a NO-OP that must NOT clobber acceptance_rate to 0 (review C2),
    # and (b) extending n_meas must CONTINUE the chain (n_done grows), not restart.
    L, msq = 2, 0.04
    coeffs, _ = drv.build_coeffs_mlx(L, 2.0, msq, 12, seed=5)
    path = str(tmp_path / "g2.0000.npz")
    kw = dict(g=2.0, L=L, msq=msq, coeffs=coeffs, R=2, eps=0.05, n_md=4, n_therm=3,
              seed=5, mlx_solver='refined', checkpoint_every=2)

    s1 = drv.run_coupling_mlx(path=path, n_meas=4, **kw)
    d1 = np.load(path)
    assert int(len(np.asarray(d1['tet_m2_history']))) == 4
    acc1 = float(d1['acceptance_rate'])
    assert 0.0 < acc1 <= 1.0                              # a real rate, not the 0.0 clobber
    assert int(d1['n_therm_done']) == 3                   # thermalization progress persisted

    # (a) no-op resume: same n_meas → nothing runs → acceptance_rate must be unchanged
    drv.run_coupling_mlx(path=path, n_meas=4, **kw)
    d2 = np.load(path)
    assert float(d2['acceptance_rate']) == acc1
    assert int(len(np.asarray(d2['tet_m2_history']))) == 4

    # (b) extend: n_meas=7 → chain continues to 7 measured (no re-thermalization)
    s3 = drv.run_coupling_mlx(path=path, n_meas=7, **kw)
    d3 = np.load(path)
    assert int(len(np.asarray(d3['tet_m2_history']))) == 7
    assert s3['n'] == 7
