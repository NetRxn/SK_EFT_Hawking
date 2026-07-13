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


# --- heatbath-quality pre-flight gate (m->0 rational-approx adequacy) -------------------------
# The eo heatbath's Zolotarev r_{-1/2} fit degrades as m->0 (kappa=lam/m^2); n_poles=14 gives
# ~15% error at m=0.05 -> an UNCORRECTABLE sampled-weight bias. build_coeffs_mlx auto-bumps
# n_poles until the UNSIGNED max relerr <= tol, fail-closed at a cap. kappa is volume-flat, so
# L=2 exercises the same stiffness as L=8 instantly.

def test_build_coeffs_mlx_meets_heatbath_quality_gate():
    import src.vestigial.hs_rhmc_mlx as me
    L, g, msq = 2, 8.0, 0.05 ** 2
    coeffs, lam = drv.build_coeffs_mlx(L, g, msq, n_poles=14, seed=5, hb_relerr_tol=1e-3)
    relerr = me.zolotarev_max_relerr(coeffs['a0'], coeffs['alphas'], coeffs['betas'],
                                     msq, lam + msq, power=-0.5)
    assert relerr <= 1e-3                                  # returned coeffs MEET the gate


def test_build_coeffs_mlx_autobumps_more_poles_for_tighter_tol():
    # Tighter quality tol -> more poles (auto-bump), independent of absolute kappa.
    L, g, msq = 2, 8.0, 0.05 ** 2
    c_loose, _ = drv.build_coeffs_mlx(L, g, msq, 14, seed=5, hb_relerr_tol=5e-1)
    c_tight, _ = drv.build_coeffs_mlx(L, g, msq, 14, seed=5, hb_relerr_tol=1e-4)
    assert len(np.asarray(c_tight['betas'])) > len(np.asarray(c_loose['betas']))


def test_build_coeffs_mlx_fails_closed_when_cap_cannot_meet_tol():
    # An unreachable tol must RAISE (fail-closed), never silently return a biased heatbath.
    L, g, msq = 2, 8.0, 0.05 ** 2
    with pytest.raises(ValueError, match="Zolotarev|heatbath"):
        drv.build_coeffs_mlx(L, g, msq, 14, seed=5, hb_relerr_tol=1e-14, n_poles_cap=22)


def test_chrono_is_the_default_with_an_opt_out():
    # Perf audit 2026-07-13: chrono warm-starting is Creutz-certified (fast reversibility
    # + solution-equivalence + slow chain gates in test_hs_rhmc_mlx) and measured 1.43x
    # on MD at m=0.05 — it must be ON by default, with --no-chrono as the exactly-
    # reversible escape hatch for strict-reversibility studies.
    ap = drv.build_parser()
    assert ap.parse_args(['--mass', '0.05']).chrono is True
    assert ap.parse_args(['--mass', '0.05', '--no-chrono']).chrono is False
    assert ap.parse_args(['--mass', '0.05', '--chrono']).chrono is True   # explicit on


def test_build_hasenbusch_coeffs_gates_both_rationals():
    # Both PF rationals (heavy @ mu^2, ratio Mobius) must meet the unsigned-relerr gate,
    # with the balanced default split mu^2 = sqrt(m^2*lam) and shifts CG-safe in (a,b).
    import mlx.core as mx
    import src.vestigial.hs_rhmc_mlx as me
    L, g, msq = 2, 8.0, 0.05 ** 2
    hb, rc, musq, lam = drv.build_hasenbusch_coeffs_mlx(L, g, msq, 14, seed=5)
    assert msq < musq < lam                                     # balanced split in range
    assert me.zolotarev_max_relerr(hb['a0'], hb['alphas'], hb['betas'],
                                   musq, lam + musq, power=-0.5) <= 1e-3
    assert me.eo_ratio_sqrt_max_relerr(rc, lam) <= 1e-3
    assert np.all((np.asarray(rc['e']) > msq) & (np.asarray(rc['e']) < musq))


def test_hasenbusch_is_opt_in_with_working_defaults():
    ap = drv.build_parser()
    a = ap.parse_args(['--mass', '0.05'])
    assert a.hasenbusch is False and a.hb_n_inner == 4 and a.mu_sq is None
    assert ap.parse_args(['--mass', '0.05', '--hasenbusch']).hasenbusch is True
