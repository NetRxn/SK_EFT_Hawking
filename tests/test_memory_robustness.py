"""Conditional common-channel fixture, independent of formal proof acceptance."""
import numpy as np
import pytest
from src.core.formulas import memory_binary_robustness_reference as fixture
from src.core.formulas import memory_process_reference


def test_tight_observed_bound():
    r = fixture(.5, .1, .1, 0, d0=.02, d1=.02, allowance0=.0200000000000001, allowance1=.0200000000000001)
    np.testing.assert_allclose(r['trace_distances'], [.1, .1])
    assert r['observed_separation'] == pytest.approx(.24)
    assert r['observed_bound'] == pytest.approx(.24)


@pytest.mark.parametrize('q, expected', [(0, .2), (.25, .1), (.5, 0)])
def test_channel_contraction_and_erasure(q, expected):
    r = fixture(.5, .1, .1, q)
    assert r['separation'] == pytest.approx(expected, abs=1e-15)
    for rho in r['outputs']:
        assert np.trace(rho) == pytest.approx(1)
        assert np.linalg.eigvalsh(rho).min() >= 0


def test_conservative_allowances_and_cap():
    r = fixture(.5, .4, .4, 0, d0=.0999999999999999, d1=.0999999999999999, allowance0=.2, allowance1=.2)
    assert r['observed_bound'] == 1
    assert r['observed_separation'] == pytest.approx(1)


def test_retained_memory_exceeds_conditional_memoryless_threshold():
    # Common post-continuation bit-flip evaluated on actual final joint states.
    x = np.array([[0, 1], [1, 0]])
    flip = np.kron(x, np.eye(2))
    effect = np.diag([0, 0, 1, 1])
    probabilities = []
    for history in (0, 1):
        rho = memory_process_reference(history)['final']
        out = .9*rho + .1*flip @ rho @ flip.T
        probabilities.append(np.trace(effect @ out).real)
    separation = probabilities[1]-probabilities[0]
    assert separation == pytest.approx(.8)
    lower_observed_signal = separation-.01-.01
    threshold = .05+.05+.01+.01
    assert lower_observed_signal == pytest.approx(.78)
    assert threshold == pytest.approx(.12)
    assert lower_observed_signal > threshold
    # This comparison assumes eps bounds and common continuation, not confidence.


def test_different_channels_are_not_a_common_channel_witness():
    rho = np.diag([1., 0.])
    x = np.array([[0, 1], [1, 0]])
    effect = np.diag([0, 1])
    assert np.trace(effect @ rho) == 0
    assert np.trace(effect @ x @ rho @ x.T) == 1
    # Equal inputs separate under different channels; valid common one cannot.
    assert fixture(0, 0, 0, .25)['separation'] == 0


@pytest.mark.parametrize('args, kwargs', [
    ((.5,.6,0,0), {}), ((.5,0,.6,0), {}), ((.5,0,0,.6), {}),
    ((np.nan,0,0,0), {}), ((.5,0,0,0), {'d0':-.1}),
    ((0,0,0,0), {'d0':.1}), ((1,0,0,0), {'d1':.1}),
    ((.5,0,0,0), {'d0':.1, 'allowance0':.05}),
    ((.5,0,0,0), {'allowance1':np.inf})])
def test_invalid_inputs_are_rejected(args, kwargs):
    with pytest.raises(ValueError):
        fixture(*args, **kwargs)


def test_zero_allowances_use_matrix_probabilities_exactly():
    r = fixture(.5, .1, .1, .25)
    np.testing.assert_array_equal(r['observed'], r['probabilities'])
    np.testing.assert_array_equal(r['actual_errors'], [0, 0])


def test_sub_ulp_boundary_excursion_rejected():
    with pytest.raises(ValueError, match="lie in"):
        fixture(1, 0, 0, 0, d1=1e-100)


def test_rounding_cannot_enlarge_declared_allowance():
    with pytest.raises(ValueError, match="allowance"):
        fixture(.5, .1, .1, 0, d0=.02, d1=.02)
