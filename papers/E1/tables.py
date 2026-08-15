"""Table and scalar specs for the E1 bundle (Paris-LKB polariton device).

Every device parameter E1 quotes — sound speed, healing length, both horizon
steepnesses, both Fresnel-like dispersion ratios, both Hawking temperatures and
the mean-field noise temperature — was a hand-typed ``\\SI{...}`` literal in the
draft, repeated at four to six sites each (abstract, §2, §3, §5, the Fig.~2
caption, §7). The device-parameter table on the old lines 118--130 was a
hand-written ``tabular``. Nothing bound any of them to
``src/core/constants.py``, so a change to the platform record would have left
the manuscript quoting the superseded numbers with no gate noticing:
``numerical_literals`` only counts literals against a frozen ceiling and
``bundle_tables_use_pipeline`` reads the ``\\input{tables/}`` form, which E1 did
not use.

Each entry renders to ``papers/E1/tables/<id>.tex``. Scalars are one-line
snippets the draft pulls in as ``\\input{tables/<id>.tex}\\unskip``; the table
renders a complete ``tabular`` the draft wraps in its own ``center`` envelope.

Regenerate after any change to constants or formulas, or to this spec:

    uv run python scripts/render_paper_tables.py --paper E1

Provenance of every value below:

* ``POLARITON_PLATFORMS['Paris_standard']`` in ``src/core/constants.py`` — the
  Falque et al.\\ 2025 §IV.1 measured record (``c_s``, ``xi``, ``kappa``).
* ``FALQUE_STEEP_HORIZON_KAPPA`` — the steep-horizon reach, same source.
* ``formulas.polariton_hawking_temperature`` — ``T_H = hbar*kappa/(2*pi*k_B)``.
* ``POLARITON_MASS`` — the mean-field noise floor ``T_noise = m* c_s^2 / k_B``.

⚠️ The downstream healing length (4.0 um) is NOT here. It has no record in
``constants.py``; binding it to a Python re-derivation would assert a freshness
relation that does not exist. It stays an inline literal until it is entered as
a provenanced parameter.

⚠️ Every value line is emitted without a trailing unit so the draft keeps
control of ``siunitx`` formatting; call sites read
``\\SI{\\input{tables/<id>.tex}\\unskip}{<unit>}``.
"""

from __future__ import annotations

import math

from scripts.paper_tables import Col

from src.core.constants import (
    FALQUE_STEEP_HORIZON_KAPPA,
    HBAR,
    K_B,
    POLARITON_MASS,
    POLARITON_PLATFORMS,
)
from src.core.formulas import (
    polariton_hawking_temperature,
    stimulated_hawking_gain,
    stimulated_hawking_snr,
)

_LKB = POLARITON_PLATFORMS['Paris_standard']

_C_S = _LKB['c_s']                       # m/s
_XI = _LKB['xi']                         # m
_KAPPA_SMOOTH = _LKB['kappa']            # s^-1
_KAPPA_STEEP = FALQUE_STEEP_HORIZON_KAPPA  # s^-1

#: The weak-dissipation cut the manuscript declares, Gamma_pol < r * kappa.
#: Held equal to the ``tier1_valid`` cut in ``src/core/constants.py`` so the
#: manuscript and the platform classifier cannot disagree; the test
#: ``tests/test_e1_tables.py`` pins that equality.
_WEAK_DISSIPATION_RATIO = 0.1


def _dispersion_ratio(kappa: float) -> float:
    """``D = xi * kappa / c_s`` — the draft's dimensionless dispersion ratio."""
    return _XI * kappa / _C_S


def _delta_disp(kappa: float) -> float:
    """``delta_disp = -pi D^2 / 6`` — the leading dispersive correction.

    This single expression is the manuscript's ONLY dispersive coefficient.
    It fixes ``c_1 = pi/6`` in the ``kappa_eff = kappa (1 - c_1 D^2)`` form,
    so ``kappa_eff/kappa = 1 + delta_disp``. ``formulas.dispersive_hawking_
    correction`` hardcodes ``c_1 = 1.0`` instead, which is a factor 1.9 away;
    that inconsistency is filed as a finding rather than silently adopted
    here, and this module deliberately does not call it.
    """
    return -math.pi * _dispersion_ratio(kappa) ** 2 / 6.0


def _kappa_tex(kappa: float) -> str:
    """``7e10`` -> ``7\\times 10^{10}``, the form the draft's math mode wants."""
    exponent = 0
    mantissa = float(kappa)
    while mantissa >= 10.0:
        mantissa /= 10.0
        exponent += 1
    mantissa_s = f'{mantissa:.1f}'.rstrip('0').rstrip('.')
    return rf'{mantissa_s}\times 10^{{{exponent}}}'


def _device_rows():
    return [
        {'config': 'Smooth horizon (baseline)',
         'kappa': f'${_kappa_tex(_KAPPA_SMOOTH)}$',
         'D': f'{_dispersion_ratio(_KAPPA_SMOOTH):.2f}'},
        {'config': 'Steep horizon (reach)',
         'kappa': f'${_kappa_tex(_KAPPA_STEEP)}$',
         'D': f'{_dispersion_ratio(_KAPPA_STEEP):.2f}'},
    ]


TABLES = {
    'lkb_device_params': {
        'description': 'E1 §2: the two Paris-LKB horizon configurations reported '
                       'by the primary source, with the dispersion ratio '
                       'D = xi*kappa/c_s derived rather than quoted',
        'rows': _device_rows,
        'columns': [
            Col('config', r'Configuration', align='l'),
            Col('kappa', r'$\kappa$ ($\SI{}{\per\second}$)'),
            Col('D', r'$D = \xi\kappa/c_s$'),
        ],
    },
}

SCALARS = {
    'lkb_c_s_um_per_ps': {
        'description': 'E1 abstract + §2: sound speed of the Paris-LKB fluid, in um/ps '
                       '(m/s * 1e6 um/m / 1e12 ps/s = m/s / 1e6).',
        'value': lambda: f'{_C_S / 1e6:.2f}',
    },
    'lkb_xi_um': {
        'description': 'E1 abstract + §2: upstream healing length, in um.',
        'value': lambda: f'{_XI * 1e6:.1f}',
    },
    'lkb_kappa_smooth': {
        'description': 'E1 abstract, §2, §5 and the Fig. 2 caption: smooth-horizon '
                       'surface gravity, in s^-1, in math-mode scientific form.',
        'value': lambda: _kappa_tex(_KAPPA_SMOOTH),
    },
    'lkb_kappa_steep': {
        'description': 'E1 abstract and §2: steep-horizon surface gravity, in s^-1, '
                       'in math-mode scientific form.',
        'value': lambda: _kappa_tex(_KAPPA_STEEP),
    },
    'lkb_D_smooth': {
        'description': 'E1 abstract, §2 and the Fig. 2 caption: dispersion ratio '
                       'D = xi*kappa/c_s at the smooth horizon.',
        'value': lambda: f'{_dispersion_ratio(_KAPPA_SMOOTH):.2f}',
    },
    'lkb_D_steep': {
        'description': 'E1 abstract and §2: dispersion ratio at the steep horizon.',
        'value': lambda: f'{_dispersion_ratio(_KAPPA_STEEP):.2f}',
    },
    'lkb_T_H_smooth_mK': {
        'description': 'E1 abstract and §5: Hawking temperature at the smooth '
                       'horizon, in mK, from formulas.polariton_hawking_temperature.',
        'value': lambda: f'{polariton_hawking_temperature(_KAPPA_SMOOTH) * 1e3:.0f}',
    },
    'lkb_T_H_steep_mK': {
        'description': 'E1 abstract and §5: Hawking temperature at the steep '
                       'horizon, in mK.',
        'value': lambda: f'{polariton_hawking_temperature(_KAPPA_STEEP) * 1e3:.0f}',
    },
    'lkb_T_noise_K': {
        'description': 'E1 §5: mean-field noise floor T_noise = m* c_s^2 / k_B, in K.',
        'value': lambda: f'{POLARITON_MASS * _C_S ** 2 / K_B:.2f}',
    },

    # ── Weak-dissipation criterion (§III of the 2026-08-15 redraft) ───────
    # The redraft's spine. Every one of these is derived from the platform
    # records, never typed: the as-built cavity's ratio is the paper's
    # headline and the required lifetime is what it asks the LKB team for.
    'lkb_Gamma_pol_standard': {
        'description': 'E1 §3: as-built Paris-LKB polariton decay rate, s^-1, '
                       'math-mode scientific form. 1/tau_cav at Falque tau = 8 ps.',
        'value': lambda: _kappa_tex(_LKB['Gamma_pol']),
    },
    'lkb_tau_cav_ps_standard': {
        'description': 'E1 §3: as-built Paris-LKB cavity lifetime, in ps '
                       "(Falque 2025 actual; hbar*gamma ~ 80 ueV, Appendix B.1).",
        'value': lambda: f"{_LKB['tau_cav'] * 1e12:.0f}",
    },
    'lkb_ratio_standard': {
        'description': 'E1 §3 and the Fig. 2 caption: Gamma_pol/kappa at the '
                       'as-built cavity and the smooth horizon. The paper headline.',
        'value': lambda: f"{_LKB['Gamma_pol_over_kappa']:.2f}",
    },
    'lkb_ratio_long': {
        'description': 'E1 §3: Gamma_pol/kappa for the PROJECTED 100 ps cavity.',
        'value': lambda: f"{POLARITON_PLATFORMS['Paris_long']['Gamma_pol_over_kappa']:.2f}",
    },
    'lkb_ratio_ultralong': {
        'description': 'E1 §3: Gamma_pol/kappa for the PROJECTED 300 ps cavity.',
        'value': lambda: f"{POLARITON_PLATFORMS['Paris_ultralong']['Gamma_pol_over_kappa']:.3f}",
    },
    'lkb_tau_required_ps': {
        'description': 'E1 §3 and §6 — THE ASK: the cavity lifetime at which '
                       'Gamma_pol = 0.1*kappa at the smooth horizon, in ps. '
                       'tau = 1/(0.1*kappa).',
        'value': lambda: f'{1e12 / (_WEAK_DISSIPATION_RATIO * _KAPPA_SMOOTH):.0f}',
    },
    'lkb_weak_dissipation_ratio': {
        'description': 'E1 §3: the weak-dissipation criterion Gamma_pol < r*kappa; '
                       'r as declared, matching the constants.py tier1_valid cut.',
        'value': lambda: f'{_WEAK_DISSIPATION_RATIO:g}',
    },
    # The attenuation exponent over ONE healing length is exactly the product
    # of the paper's two dimensionless parameters:
    #   Gamma_pol * xi / c_s == (Gamma_pol/kappa) * (xi kappa / c_s) == ratio * D
    # so §3 spends only quantities §2 already derived, and no new length scale
    # is introduced (in particular no un-provenanced propagation distance).
    'lkb_atten_per_xi_standard': {
        'description': 'E1 §3: exp(Gamma_pol xi / c_s) = exp(ratio*D), the '
                       'occupation-recovery factor per healing length of '
                       'propagation, at the as-built cavity.',
        'value': lambda: (
            f"{math.exp(_LKB['Gamma_pol_over_kappa'] * _dispersion_ratio(_KAPPA_SMOOTH)):.1f}"
        ),
    },
    'lkb_atten_per_xi_required': {
        'description': 'E1 §3: the same recovery factor per healing length at '
                       'the weak-dissipation boundary Gamma_pol = 0.1 kappa.',
        'value': lambda: (
            f'{math.exp(_WEAK_DISSIPATION_RATIO * _dispersion_ratio(_KAPPA_SMOOTH)):.2f}'
        ),
    },
    'penn_ratio_vs_steep': {
        'description': 'E1 §3: Penn TMD nanocavity Gamma_LP over the MOST GENEROUS '
                       'polariton-family kappa (Falque steep), matching the Lean '
                       'theorem polariton_tier1_fails_tmds.',
        'value': lambda: (
            f"{POLARITON_PLATFORMS['Penn_TMD_MoSe2']['Gamma_pol'] / _KAPPA_STEEP:.1f}"
        ),
    },

    # ── Dispersive correction, used consistently (§II, §IV) ───────────────
    # delta_disp = -pi D^2 / 6 fixes the dispersive coefficient at c_1 = pi/6.
    # kappa_eff/kappa = 1 + delta_disp is the SAME correction, so the gain
    # threshold in absolute kappa units is 0.175 * that ratio. Deriving both
    # from one expression is what stops the two drifting apart.
    'lkb_delta_disp_smooth': {
        'description': 'E1 §2: leading dispersive correction -pi D^2/6 at the '
                       'smooth horizon (signed).',
        'value': lambda: f'{_delta_disp(_KAPPA_SMOOTH):.2f}',
    },
    'lkb_delta_disp_steep': {
        'description': 'E1 §2: leading dispersive correction at the steep horizon '
                       '(signed).',
        'value': lambda: f'{_delta_disp(_KAPPA_STEEP):.2f}',
    },
    'lkb_kappa_eff_ratio_smooth': {
        'description': 'E1 §4: kappa_eff/kappa = 1 + delta_disp at the smooth horizon.',
        'value': lambda: f'{1.0 + _delta_disp(_KAPPA_SMOOTH):.2f}',
    },
    'lkb_gain_threshold': {
        'description': 'E1 §4: ln(3)/(2 pi) — the omega/kappa_eff at which the '
                       'Gamma=1 gain reaches 1/2. Exact, device-independent.',
        'value': lambda: f'{math.log(3.0) / (2.0 * math.pi):.3f}',
    },
    'lkb_gain_threshold_absolute': {
        'description': 'E1 §4: the same crossing expressed in absolute kappa units, '
                       'ln(3)/(2 pi) * (1 + delta_disp) at the smooth horizon.',
        'value': lambda: (
            f'{math.log(3.0) / (2.0 * math.pi) * (1.0 + _delta_disp(_KAPPA_SMOOTH)):.3f}'
        ),
    },

    # ── Gain spectrum (§IV) ───────────────────────────────────────────────
    # Consumed from the canonical formulas.stimulated_hawking_gain / _snr so
    # the manuscript cannot drift from the pipeline. The argument is
    # omega/kappa_eff, which is what the exponent actually contains; the
    # translation to absolute kappa is lkb_gain_threshold_absolute above.
    'lkb_gain_at_0p1': {
        'description': 'E1 §4 and the Fig. 1 caption: G at omega = 0.1 kappa_eff, '
                       'greybody-saturated.',
        'value': lambda: f'{stimulated_hawking_gain(0.1, 1.0):.2f}',
    },
    'lkb_gain_at_0p3': {
        'description': 'E1 §4: G at omega = 0.3 kappa_eff, greybody-saturated.',
        'value': lambda: f'{stimulated_hawking_gain(0.3, 1.0):.2f}',
    },
    'lkb_gain_at_1': {
        'description': 'E1 §4: G at omega = kappa_eff, greybody-saturated. Two '
                       'significant figures, matching its neighbours (the prior '
                       'draft rounded this one to 0.002 and its neighbours to two).',
        'value': lambda: f'{stimulated_hawking_gain(1.0, 1.0):.4f}',
    },
    'lkb_snr_at_0p1': {
        'description': 'E1 §4: single-shot SNR at omega = 0.1 kappa_eff with '
                       '100 probe photons per mode.',
        'value': lambda: f'{stimulated_hawking_snr(0.1, 1.0, 100, 1):.0f}',
    },

    # ── The primary source's own normalization (§II) ──────────────────────
    # Falque et al. Eq. (9) uses exp(omega / 2 pi kappa), i.e. k_B T = h kappa,
    # and quote "T^HR = 3 K" for the smooth horizon. That is (2 pi)^2 times the
    # standard k_B T_H = hbar kappa / 2 pi this Letter uses. The manuscript
    # reconciles the two explicitly, so the number is generated, not typed.
    'lkb_T_H_falque_norm_K': {
        'description': 'E1 §2: the smooth-horizon temperature under the primary '
                       "source's normalization k_B T = h kappa, in K. Falque et al. "
                       'print "3 K" for this configuration.',
        'value': lambda: f'{2.0 * math.pi * HBAR * _KAPPA_SMOOTH / K_B:.1f}',
    },
    'lkb_norm_ratio': {
        'description': 'E1 §2: (2 pi)^2, the ratio between the primary source\'s '
                       'normalization and the standard one.',
        'value': lambda: f'{(2.0 * math.pi) ** 2:.0f}',
    },
}
