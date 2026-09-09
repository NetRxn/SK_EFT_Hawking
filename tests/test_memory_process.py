"""Semantic tests of the finite CPU memory model; no Lean-equivalence claim."""
import numpy as np
import pytest

from src.core.formulas import (
    memory_process_reference, memory_reset_system, memory_swap,
    memory_system_probabilities,
)


@pytest.mark.parametrize("history", [0, 1])
def test_history_returns_and_reset_both_erases(history):
    result = memory_process_reference(history)
    np.testing.assert_array_equal(result["probabilities"], [1-history, history])
    np.testing.assert_array_equal(
        memory_system_probabilities(result["after_reset"]), [1, 0])
    control = memory_process_reference(history, reset_environment=True)
    np.testing.assert_array_equal(control["probabilities"], [1, 0])
    for key in ("initial", "after_swap", "after_reset", "final"):
        rho = result[key]
        assert np.trace(rho) == 1
        assert np.linalg.eigvalsh(rho).min() >= 0


def test_correlated_reset_preserves_environment_and_discards_coherence():
    # Entangled state with complex coherence and unequal E populations.
    ket = np.array([np.sqrt(.25), 0, 0, 1j*np.sqrt(.75)])
    rho = np.outer(ket, ket.conj())
    original = rho.copy()
    reset = memory_reset_system(rho)
    np.testing.assert_allclose(reset, np.diag([.25, .75, 0, 0]), atol=1e-15)
    np.testing.assert_array_equal(rho, original)
    # The retained E populations return to S under the common continuation.
    np.testing.assert_allclose(memory_system_probabilities(memory_swap(reset)), [.25, .75])


def test_reset_preserves_environment_off_diagonal_state():
    ket = np.array([0, 0, 1, 1j])/np.sqrt(2)
    rho = np.outer(ket, ket.conj())
    expected = np.zeros((4, 4), complex)
    expected[:2, :2] = [[.5, -.5j], [.5j, .5]]
    np.testing.assert_allclose(memory_reset_system(rho), expected, atol=1e-15)


def test_swap_factor_order_on_asymmetric_basis_state():
    rho = np.diag([0, 1, 0, 0])  # |0,1>
    np.testing.assert_array_equal(memory_swap(rho), np.diag([0, 0, 1, 0]))
    np.testing.assert_array_equal(memory_swap(memory_swap(rho)), rho)


def test_deterministic_imperfect_reset_on_entangled_input():
    rho = np.array([[.5, 0, 0, .5], [0, 0, 0, 0],
                    [0, 0, 0, 0], [.5, 0, 0, .5]])
    imperfect = memory_reset_system(rho, .2)
    expected = np.array([[.5, 0, 0, .1], [0, .4, 0, 0],
                         [0, 0, 0, 0], [.1, 0, 0, .1]])
    np.testing.assert_allclose(imperfect, expected)
    np.testing.assert_allclose(memory_system_probabilities(imperfect), [.9, .1])
    np.testing.assert_array_equal(memory_reset_system(rho, 1), rho)
    assert np.linalg.eigvalsh(imperfect).min() >= -1e-15


@pytest.mark.parametrize("state", [np.eye(2)/2, np.eye(4),
    np.diag([1.1, -.1, 0, 0]), np.full((4,4), np.nan),
    np.array([[1, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]])])
def test_invalid_states_rejected(state):
    for operation in (memory_swap, memory_reset_system, memory_system_probabilities):
        with pytest.raises(ValueError):
            operation(state)


@pytest.mark.parametrize("probability", [-.1, 1.1, np.nan, np.inf])
def test_invalid_reset_probability(probability):
    with pytest.raises(ValueError):
        memory_process_reference(0, failure_probability=probability)


def test_invalid_history():
    with pytest.raises(ValueError):
        memory_process_reference(2)
