"""Joint-trajectory checks; floating-point execution is not a certified witness."""
import numpy as np
import pytest

from src.core.formulas import (
    memory_partial_interaction, memory_partial_interaction_reference,
    memory_process_reference, memory_swap,
)


def test_reset_sensitive_interior():
    result = memory_partial_interaction_reference(.5, .25)
    np.testing.assert_array_equal(result["reset_trace_distances"], [0, 1/8])
    assert result["retained_separation"] == 5/16
    assert result["control_separation"] == 1/16
    assert result["criterion_margin"] == 3/16
    h = result["histories"][1]
    np.testing.assert_array_equal(h["after_reset"], np.diag([3/8, 1/2, 1/8, 0]))
    np.testing.assert_array_equal(h["control_input"], np.diag([7/8, 0, 1/8, 0]))
    assert memory_partial_interaction_reference(.5, 0)["retained_separation"] == 1/4
    assert memory_partial_interaction_reference(.5, 1)["retained_separation"] == 1/2


@pytest.mark.parametrize("t", [0., .031, .25, .5, .79, 1.])
@pytest.mark.parametrize("p", [0., .13, .25, .8, 1.])
def test_trajectory_identities_and_physical_bounds(t, p):
    result = memory_partial_interaction_reference(t, p)
    r, a, b = p*(1-t), t*t+p*(1-t)**2, p*(1-t)**2
    np.testing.assert_allclose(result["reset_trace_distances"], [0, r], atol=1e-15, rtol=0)
    assert result["retained_separation"] == pytest.approx(a, abs=1e-15, rel=0)
    assert result["control_separation"] == pytest.approx(b, abs=1e-15, rel=0)
    assert result["retained_control_difference"] == pytest.approx(t*t, abs=1e-15, rel=0)
    assert result["criterion_margin"] == pytest.approx(t*(t-p*(1-t)), abs=1e-15, rel=0)
    assert result["control_separation"] <= result["memoryless_bound"]+1e-15
    for h in result["histories"]:
        for key in ("initial", "after_interaction", "after_reset", "control_input",
                    "retained_final", "control_final", "reset_system_state"):
            rho = h[key]
            np.testing.assert_allclose(rho, rho.conj().T, atol=1e-15, rtol=0)
            assert np.trace(rho) == pytest.approx(1, abs=1e-15, rel=0)
            assert np.linalg.eigvalsh(rho).min() >= -1e-15
        for key in ("retained_probabilities", "control_probabilities"):
            assert np.all(h[key] >= 0) and np.all(h[key] <= 1)
            assert h[key].sum() == pytest.approx(1)
    np.testing.assert_array_equal(result["histories"][0]["retained_probabilities"], [1, 0])


def test_full_exchange_matches_existing_model():
    for p in (0., .2, 1.):
        result = memory_partial_interaction_reference(1, p)
        for b, h in enumerate(result["histories"]):
            for control, key in ((False, "retained_final"), (True, "control_final")):
                expected = memory_process_reference(b, failure_probability=p,
                                                    reset_environment=control)
                np.testing.assert_array_equal(h[key], expected["final"])


def test_comparison_boundary_and_inconclusive_region():
    assert memory_partial_interaction_reference(.5, 1)["criterion_margin"] == 0
    assert memory_partial_interaction_reference(.25, 1)["criterion_margin"] < 0
    assert memory_partial_interaction_reference(.5, .5)["criterion_margin"] > 0
    # With no interaction the surviving signal is entirely system reset leakage.
    result = memory_partial_interaction_reference(0, .5)
    assert result["retained_separation"] == result["control_separation"] == .5
    assert result["criterion_margin"] == 0


def test_correlated_complex_state_matches_normalized_kraus_map():
    ket = np.array([1, 2j, 3, -1j], dtype=complex)/np.sqrt(15)
    rho = np.outer(ket, ket.conj())
    original = rho.copy()
    t = .37
    swap = np.eye(4)[[0, 2, 1, 3]]
    kraus = [np.sqrt(1-t)*np.eye(4), np.sqrt(t)*swap]
    expected = sum(k @ rho @ k.conj().T for k in kraus)
    actual = memory_partial_interaction(rho, t)
    np.testing.assert_allclose(actual, expected, atol=1e-15, rtol=0)
    np.testing.assert_allclose(sum(k.conj().T @ k for k in kraus), np.eye(4), atol=1e-15, rtol=0)
    assert np.linalg.eigvalsh(actual).min() >= -1e-15
    np.testing.assert_array_equal(rho, original)
    np.testing.assert_array_equal(memory_partial_interaction(rho, 0), rho)
    np.testing.assert_array_equal(memory_partial_interaction(rho, 1), memory_swap(rho))
    # A mixed channel generally does not preserve purity as a unitary would.
    assert np.trace(actual @ actual).real < .99


@pytest.mark.parametrize("bad", [-.1, 1.1, np.nan, np.inf, -np.inf])
def test_invalid_parameters(bad):
    with pytest.raises(ValueError):
        memory_partial_interaction(np.diag([1, 0, 0, 0]), bad)
    for t, p in ((bad, .5), (.5, bad)):
        with pytest.raises(ValueError):
            memory_partial_interaction_reference(t, p)


@pytest.mark.parametrize("bad", [np.eye(2)/2, np.eye(4), np.diag([1.1, -.1, 0, 0]),
                                 np.full((4, 4), np.nan)])
def test_invalid_joint_state(bad):
    with pytest.raises(ValueError):
        memory_partial_interaction(bad, .5)
