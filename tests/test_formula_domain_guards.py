"""A non-physical sound speed must be an ERROR, not a physically meaningful answer.

⚠️ `horizon_damping_rate` returned `0.0` for `c_s <= 0`. Zero damping is not a
sentinel — it is a *reading*: it flows into `δ_diss = Γ_H/κ = 0` and every
downstream consumer sees "dissipationless system". `conformal_kinematic_viscosity`
had no guard at all.

Both live in the module that exists BECAUSE an open-coded copy of
`horizon_damping_rate` dropped the velocity² and produced a quantity in [s·m⁻²]
labelled [s⁻¹] — wrong by eleven orders of magnitude, silently. A silent sentinel
is that same failure mode with a friendlier value.

⚠️ Neither function had ANY test before this file, so the round-3 review could
observe that reverting both guards left 162 tests green. That is the gap this
closes, in both directions.
"""
from __future__ import annotations

import math

import pytest

from src.core.formulas import conformal_kinematic_viscosity, horizon_damping_rate


class TestHorizonDampingRateRejectsNonPhysicalSoundSpeed:
    @pytest.mark.parametrize("c_s", [0.0, -1.0, -4.4e5])
    def test_non_positive_sound_speed_raises(self, c_s):
        with pytest.raises(ValueError, match="c_s"):
            horizon_damping_rate(1e-6, 2e-6, 1e3, c_s)

    def test_the_error_names_the_reading_it_prevents(self):
        """The message has to say why 0.0 was wrong, or the next author restores it."""
        with pytest.raises(ValueError, match="dissipationless"):
            horizon_damping_rate(1e-6, 2e-6, 1e3, 0.0)

    def test_a_physical_sound_speed_still_computes(self):
        """The silent direction — a function that always raised would pass above."""
        got = horizon_damping_rate(1e-6, 2e-6, 1e3, 4.4e5)
        assert math.isclose(got, 3e-6 * (1e3 / 4.4e5) ** 2, rel_tol=1e-12)
        assert got > 0

    def test_it_scales_as_the_inverse_square_of_c_s(self):
        """Γ_H = (γ₁+γ₂)(κ/c_s)²: doubling c_s must quarter the rate. This is the
        velocity² whose omission caused the eleven-order error."""
        a = horizon_damping_rate(1e-6, 2e-6, 1e3, 4.4e5)
        b = horizon_damping_rate(1e-6, 2e-6, 1e3, 8.8e5)
        assert math.isclose(a / b, 4.0, rel_tol=1e-12)


class TestConformalKinematicViscosityRejectsNonPhysicalSoundSpeed:
    @pytest.mark.parametrize("c_s", [0.0, -1.0])
    def test_non_positive_sound_speed_raises(self, c_s):
        with pytest.raises(ValueError, match="c_s"):
            conformal_kinematic_viscosity(1e-13, c_s)

    def test_a_physical_sound_speed_still_computes(self):
        got = conformal_kinematic_viscosity(1e-13, 4.4e5)
        assert math.isclose(got, 2.0 * 1e-13 * 4.4e5 ** 2, rel_tol=1e-12)

    def test_it_scales_quadratically_in_c_s(self):
        """ν = 2·(η/sT)·c_s². The Lean side asserts the same law
        (`DiracFluidSK.kinematicViscosity_scales_quadratically`); this is the
        Python half of that pair."""
        a = conformal_kinematic_viscosity(1e-13, 4.4e5)
        b = conformal_kinematic_viscosity(1e-13, 2 * 4.4e5)
        assert math.isclose(b / a, 4.0, rel_tol=1e-12)
