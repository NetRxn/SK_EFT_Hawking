"""Analysis defaults: no double thermalization-cut.

The run driver (`run_rhmc_gpu_production.py`, both mlx and torch paths) discards its
`--n-therm` trajectories and saves MEASUREMENT-ONLY history, recording `n_therm_done` in
the npz. The analysis must therefore NOT re-apply a thermalization cut by default, or it
silently drops that many measurement samples (with the driver's n_therm=150 and the old
analysis default 150, a 400-sample run was analyzed on 250).
"""
import scripts.analyze_rhmc_vestigial as az


def test_effective_therm_no_double_cut_on_post_thermalized_data():
    # already-thermalized data (n_therm_done present) + no user override → cut 0
    assert az.effective_therm(None, data_is_post_thermalized=True) == 0
    # legacy full-chain data (no n_therm_done) keeps the historical 150-trajectory cut
    assert az.effective_therm(None, data_is_post_thermalized=False) == 150
    # an explicit user --therm always wins, either way
    assert az.effective_therm(50, data_is_post_thermalized=True) == 50
    assert az.effective_therm(50, data_is_post_thermalized=False) == 50
    assert az.effective_therm(0, data_is_post_thermalized=False) == 0
