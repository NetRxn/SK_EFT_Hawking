"""Row-generator functions for paper table autogen (Phase 5v).

Each source function returns a list of dicts ready for render. Values in
the dicts are pre-formatted strings (each physics quantity chooses its
natural precision); the rendering engine just handles column layout.

Sources grow as new data shapes are needed. Papers reference these from
their `tables.py` specs:

    from scripts.paper_tables.sources import platform_rows
    TABLES = {'tab1': {'rows': lambda: platform_rows(['Steinhauer', 'Heidelberg']), ...}}
"""

from __future__ import annotations


# Platform → BECParameters factory. Defined at module scope so papers
# can discover available platforms without importing all physics code.
_PLATFORM_FACTORIES = {
    'Steinhauer': 'steinhauer_Rb87',
    'Heidelberg': 'heidelberg_K39',
    'Trento':     'trento_spin_sonic',
}


def _format_sci(x: float, precision: int = 1) -> str:
    """LaTeX-friendly scientific notation for small values."""
    if x == 0:
        return '0'
    mantissa_exp = f'{x:.{precision}e}'
    mantissa, exp = mantissa_exp.split('e')
    exp_int = int(exp)
    return f'${mantissa} \\times 10^{{{exp_int}}}$'


def platform_rows(platforms: list[str]) -> list[dict]:
    """Per-parameter rows × per-platform columns for BEC analog Hawking
    experiments. One row per physics quantity; cells are formatted
    strings ready for LaTeX.

    Rows: c_s, ξ, κ, T_H, δ_diss
    Columns: (parameter, unit, <platform>, ...)

    Example: platform_rows(['Steinhauer', 'Heidelberg', 'Trento']) →
        [
          {'parameter': 'Speed of sound $c_s$', 'unit': 'mm/s',
           'Steinhauer': '0.55', 'Heidelberg': '3.92', 'Trento': '2.18'},
          {'parameter': 'Healing length $\\xi$', 'unit': '$\\mu$m',
           'Steinhauer': '1.33', 'Heidelberg': '0.42', 'Trento': '1.26'},
          ...
        ]
    """
    import src.core.transonic_background as tb
    from src.core.formulas import beliaev_transport_coefficients

    # Build per-platform BECParameters + TransonicBackground
    backgrounds: dict[str, tuple] = {}
    for p in platforms:
        factory_name = _PLATFORM_FACTORIES.get(p)
        if factory_name is None:
            raise ValueError(
                f"Unknown platform {p!r}. Known: "
                f"{sorted(_PLATFORM_FACTORIES)}. Register in "
                f"scripts/paper_tables/sources.py._PLATFORM_FACTORIES."
            )
        factory = getattr(tb, factory_name)
        params = factory()
        bg = tb.solve_transonic_background(params)
        backgrounds[p] = (params, bg)

    rows: list[dict] = []

    # c_s (mm/s)
    row = {'parameter': 'Speed of sound $c_s$', 'unit': 'mm/s'}
    for p in platforms:
        params, _bg = backgrounds[p]
        row[p] = f'{params.sound_speed_upstream * 1000:.2f}'
    rows.append(row)

    # ξ (μm)
    row = {'parameter': 'Healing length $\\xi$', 'unit': '$\\mu$m'}
    for p in platforms:
        params, _bg = backgrounds[p]
        row[p] = f'{params.healing_length * 1e6:.2f}'
    rows.append(row)

    # κ (s⁻¹)
    row = {'parameter': 'Surface gravity $\\kappa$', 'unit': 's$^{-1}$'}
    for p in platforms:
        _params, bg = backgrounds[p]
        row[p] = f'{bg.surface_gravity:.1f}'
    rows.append(row)

    # T_H (nK)
    row = {'parameter': 'Hawking temperature $T_H$', 'unit': 'nK'}
    for p in platforms:
        _params, bg = backgrounds[p]
        row[p] = f'{bg.hawking_temp * 1e9:.3f}'
    rows.append(row)

    # δ_diss (dimensionless, scientific notation)
    row = {'parameter': 'Dissipative correction $\\delta_{\\mathrm{diss}}$ (Beliaev, $T{=}0$)',
           'unit': '(dimensionless)'}
    for p in platforms:
        params, bg = backgrounds[p]
        xi = params.healing_length
        tc = beliaev_transport_coefficients(
            n_1D=params.density_upstream,
            a_s=params.scattering_length,
            kappa=bg.surface_gravity,
            c_s=params.sound_speed_upstream,
            xi=xi,
        )
        delta_diss = tb.compute_dissipative_correction(
            bg, params, tc['gamma_1'], tc['gamma_2'],
        )['delta_diss']
        row[p] = _format_sci(delta_diss, precision=1)
    rows.append(row)

    return rows
