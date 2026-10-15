"""Scientific regression checks for the E1 gain and cavity-lifetime figures."""

import numpy as np
import pytest

from src.core.constants import POLARITON_PLATFORMS
from src.core.formulas import stimulated_hawking_gain, stimulated_hawking_snr
from src.core.visualizations import (
    fig_polariton_regime_map,
    fig_stimulated_hawking_spectrum,
)


def test_gain_curve_and_half_gain_share_effective_frequency_coordinate():
    fig = fig_stimulated_hawking_spectrum()
    curve = next(trace for trace in fig.data if trace.name == 'Saturated-greybody gain')
    x, gain = np.asarray(curve.x), np.asarray(curve.y)
    # Direct Bose occupation, independent of the figure's sampling helper.
    np.testing.assert_allclose(gain, 1 / np.expm1(2 * np.pi * x), rtol=1e-13)
    assert np.all(np.diff(gain) < 0)
    crossing = next(trace for trace in fig.data if trace.name == 'Half gain')
    assert crossing.x[0] == pytest.approx(np.log(3) / (2 * np.pi))
    assert crossing.y[0] == pytest.approx(0.5)
    # This location is independent of the adopted surface-gravity scale.
    for kappa in (1.0, POLARITON_PLATFORMS['Paris_long']['kappa']):
        omega = crossing.x[0] * kappa
        assert stimulated_hawking_gain(omega, kappa) == pytest.approx(0.5)
        assert stimulated_hawking_snr(omega, kappa, 100) == pytest.approx(5)
    assert fig.layout.xaxis.title.text == 'ω / κ<sub>eff</sub>'
    text = ' '.join(a.text for a in fig.layout.annotations)
    assert 'Ideal shot-noise model' in text
    assert 'Lower edge unspecified' in text
    assert 'adopted working band' in text
    assert 'optimal' not in text.lower()
    assert 'Burkhard' not in text


def test_regime_map_preserves_measured_and_projected_positions_and_criterion():
    fig = fig_polariton_regime_map()
    expected = {
        'Standard (measured)': ('Paris_standard', 8.0, 1.25e11 / 7e10),
        'Long (projected)': ('Paris_long', 100.0, 1e10 / 7e10),
        'Ultralong (projected)': ('Paris_ultralong', 300.0, 3.33e9 / 7e10),
    }
    for label, (key, lifetime, ratio) in expected.items():
        trace = next(t for t in fig.data if t.name == label)
        assert trace.x[0] == pytest.approx(lifetime)
        assert trace.y[0] == pytest.approx(ratio)
        params = POLARITON_PLATFORMS[key]
        assert trace.y[0] == pytest.approx(params['Gamma_pol'] / params['kappa'])
    crossing = next(t for t in fig.data if t.name == 'Weak-dissipation criterion crossing')
    assert crossing.x[0] == pytest.approx(1000 / 7)
    assert crossing.y[0] == 0.1
    # Standard and long miss the criterion; the ultralong projection meets it.
    assert expected['Standard (measured)'][2] > expected['Long (projected)'][2] > 0.1
    assert expected['Ultralong (projected)'][2] < 0.1
    text = ' '.join(a.text for a in fig.layout.annotations)
    assert 'qualitative decay scales' in text
    assert 'projected cavities are not measurements' in text
    assert 'Tier' not in str(fig.to_plotly_json())


def test_fixed_positive_greybody_low_frequency_gain_diverges():
    # Pin the corrected documentation with the actual expression and asymptote.
    ratios = np.array([1e-3, 1e-4, 1e-5])
    gains = np.array([stimulated_hawking_gain(x, 1.0, 0.4) for x in ratios])
    assert np.all(np.diff(gains) > 0)
    np.testing.assert_allclose(gains * 2 * np.pi * ratios / 0.4, 1, atol=0.004)
    assert gains[-1] > 1000
