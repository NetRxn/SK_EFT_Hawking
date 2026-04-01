"""
Parameter Provenance Registry

Structured citation metadata for every experimental parameter in the project.
Each entry traces a parameter value to a specific published source (paper,
table/figure, page), with two-phase verification:

  - llm_verified: LLM read the primary source and extracted the value + excerpt
  - human_verified: Human confirmed via the provenance dashboard

Work continues past llm_verified. Paper SUBMISSION gates on human_verified.

Confidence tiers (in order of decreasing reliability):
  MEASURED    — directly reported in a published paper with error bars
  EXTRACTED   — extracted from a published figure/plot (less precise)
  DERIVED     — computed from MEASURED values using known formulas
  PROJECTED   — estimated for an experiment that hasn't been performed
  THEORETICAL — from a theoretical paper, not experimentally validated

See also: src/core/citations.py for the canonical bibliography (CITATION_REGISTRY).
"""

import numpy as np

# ════════════════════════════════════════════════════════════════════
# Parameter Provenance Registry
# ════════════════════════════════════════════════════════════════════

PARAMETER_PROVENANCE = {

    # ── Fundamental constants ──────────────────────────────────────

    'HBAR': {
        'value': 1.054571817e-34,
        'unit': 'J·s',
        'tier': 'MEASURED',
        'source': 'CODATA 2018',
        'detail': 'Exact value in SI 2019 redefinition',
        'doi': None,  # CODATA is a database, not a single paper
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Exact by definition in SI 2019.',
    },
    'K_B': {
        'value': 1.380649e-23,
        'unit': 'J/K',
        'tier': 'MEASURED',
        'source': 'CODATA 2018',
        'detail': 'Exact value in SI 2019 redefinition',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Exact by definition in SI 2019.',
    },
    'A_BOHR': {
        'value': 5.29177210903e-11,
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'CODATA 2018',
        'detail': 'Bohr radius, NIST SP 961',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },

    # ── Rb-87 atomic properties ────────────────────────────────────

    'Rb87.mass': {
        'value': 1.443160648e-25,
        'unit': 'kg',
        'tier': 'MEASURED',
        'source': 'NIST Atomic Weights and Isotopic Compositions',
        'detail': 'Atomic mass 86.909180531 u × 1.66053906660e-27 kg/u',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Rb87.a_s': {
        'value': 5.77e-9,
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'van Kempen et al., PRL 88, 093201 (2002)',
        'detail': 'Table I, |F=2,mF=2> + |F=2,mF=2> channel, a = 109.1(1) a_0',
        'doi': '10.1103/PhysRevLett.88.093201',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Deep research cites 100.4 a_0 as "standard Rb-87 value" — '
                 'this may be a different scattering channel or source. '
                 '109 a_0 is the |2,2>+|2,2> triplet from van Kempen 2002. '
                 'CONFLICT UNRESOLVED — needs primary source verification of both claims.',
    },

    # ── K-39 atomic properties ─────────────────────────────────────

    'K39.mass': {
        'value': 6.470076e-26,
        'unit': 'kg',
        'tier': 'MEASURED',
        'source': 'NIST Atomic Weights and Isotopic Compositions',
        'detail': 'Atomic mass 38.96370668 u',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'K39.a_s': {
        'value': 50e-9,
        'unit': 'm',
        'tier': 'PROJECTED',
        'source': 'Falke et al., PRA 78, 012503 (2008)',
        'detail': 'Feshbach resonance near 402 G allows tuning 0-200 a_0. '
                  '50 nm chosen as representative mid-range value.',
        'doi': '10.1103/PhysRevA.78.012503',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Tunable parameter, not a fixed measurement. 50 nm is a '
                 'design choice for projections, not a published value.',
    },

    # ── Na-23 atomic properties ────────────────────────────────────

    'Na23.mass': {
        'value': 3.8175458e-26,
        'unit': 'kg',
        'tier': 'MEASURED',
        'source': 'NIST Atomic Weights and Isotopic Compositions',
        'detail': 'Atomic mass 22.9897692820 u',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Na23.a_s': {
        'value': 2.75e-9,
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Cited as ~52 a_0, triplet s-wave. Source paper not identified.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Standard Na-23 scattering length. Source paper needs identification.',
    },

    # ── Steinhauer experimental parameters ─────────────────────────

    'Steinhauer.density_upstream': {
        'value': 5e7,
        'unit': 'm^-1',
        'tier': 'EXTRACTED',
        'source': 'Wang et al., PRA 96, 023616 (2017)',
        'detail': 'Fig. 2 density profile. n_1D is position-dependent: '
                  'peak ~120 μm⁻¹, horizon region ~40-60 μm⁻¹. '
                  '5e7 m⁻¹ = 50 μm⁻¹ chosen as approximate horizon-region value.',
        'doi': '10.1103/PhysRevA.96.023616',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Position-dependent quantity — value depends on WHERE in the BEC. '
                 'This is an approximation. Real analysis should use the full profile.',
    },
    'Steinhauer.velocity_upstream': {
        'value': 0.85e-3,
        'unit': 'm/s',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'No published table with this exact value found. '
                  'Likely estimated from Mach ~ 0.74 assumption and solver c_s, '
                  'making it potentially circular if c_s is wrong.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Possibly circular derivation — if c_s is wrong (which it is), '
                 'this velocity estimate is also wrong.',
    },
    'Steinhauer.omega_perp': {
        'value': None,  # UNRESOLVED — code uses 2π×500, deep research says 2π×123
        'unit': 'rad/s',
        'tier': 'MEASURED',
        'source': 'UNRESOLVED — CONFLICTING SOURCES',
        'detail': 'Code currently uses 2π × 500 Hz (NO SOURCE FOUND). '
                  'Deep research cites Wang et al., PRA 96, 023616 (2017), '
                  'Table I: ω_⊥ = 2π × 123 Hz for the 2014 apparatus. '
                  'The 2019 Nature experiment may use a different trap configuration. '
                  'Neither 500 Hz nor 123 Hz has been verified against the primary source.',
        'doi': '10.1103/PhysRevA.96.023616',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'CRITICAL: This is the root cause of the 4.4× g₁D error. '
                 '500 Hz → c_s = 1.15 mm/s, κ = 21.9 (wrong). '
                 '123 Hz → c_s = 0.55 mm/s, κ ≈ 290 (matches published T_H). '
                 'The 500 Hz value has NO published source and may have been '
                 'hallucinated by an LLM in an early coding session.',
    },

    # ── Heidelberg projected parameters ────────────────────────────

    'Heidelberg.density_upstream': {
        'value': 3e7,
        'unit': 'm^-1',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Heidelberg (Oberthaler group) has published analog COSMOLOGY '
                  '(Viermann et al., Nature 611, 260, 2022), NOT analog Hawking radiation. '
                  'No transonic flow or sonic horizon experiment exists. '
                  'This density is a projection for a hypothetical Hawking experiment.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'PROJECTED: No Heidelberg Hawking experiment exists.',
    },
    'Heidelberg.velocity_upstream': {
        'value': 3.0e-3,
        'unit': 'm/s',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Projected value for hypothetical Hawking experiment.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'PROJECTED: No Heidelberg Hawking experiment exists.',
    },
    'Heidelberg.omega_perp': {
        'value': 2 * np.pi * 500,
        'unit': 'rad/s',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Projected value. No published source for this trap frequency '
                  'in a Hawking radiation context.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'PROJECTED: Same unsourced 500 Hz as Steinhauer. '
                 'Heidelberg uses 2D geometry for cosmology experiments — '
                 'different confinement than 1D BEC.',
    },

    # ── Trento projected parameters ────────────────────────────────

    'Trento.density_upstream': {
        'value': 1e8,
        'unit': 'm^-1',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Trento (Carusotto/Ferrari group) proposed spin-sonic Hawking '
                  'in Berti et al., Comptes Rendus Physique 25 (2025). '
                  'Paper uses dimensionless parameters only — no experimental density published.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'PROJECTED: Spin-sonic horizon is a theoretical proposal, not realized.',
    },
    'Trento.velocity_upstream': {
        'value': 1.6e-3,
        'unit': 'm/s',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Projected value for hypothetical spin-sonic experiment.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'PROJECTED: No Trento Hawking experiment exists.',
    },
    'Trento.omega_perp': {
        'value': 2 * np.pi * 500,
        'unit': 'rad/s',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Projected value. Same unsourced 500 Hz as other platforms.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'PROJECTED: Same unsourced 500 Hz. Trento uses two-component Na-23 '
                 'with spin degrees of freedom — trap parameters would differ from '
                 'single-component BEC.',
    },

    # ── Polariton platform parameters ──────────────────────────────

    'POLARITON_MASS': {
        'value': 7.0e-35,
        'unit': 'kg',
        'tier': 'MEASURED',
        'source': 'Falque et al., PRL 135, 023401 (2025)',
        'detail': 'Effective polariton mass, typical GaAs microcavity.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Paris_long.c_s': {
        'value': 1.0e6,
        'unit': 'm/s',
        'tier': 'EXTRACTED',
        'source': 'Jacquet et al., Eur. Phys. J. D 76, 152 (2022)',
        'detail': 'Typical Bogoliubov sound speed ~1 μm/ps in polariton condensate.',
        'doi': '10.1140/epjd/s10053-022-00477-5',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Same c_s used for all 3 Paris cavity configurations.',
    },
    'Paris_long.xi': {
        'value': 2.0e-6,
        'unit': 'm',
        'tier': 'EXTRACTED',
        'source': 'Jacquet et al., Eur. Phys. J. D 76, 152 (2022)',
        'detail': 'Healing length ~2 μm, typical for polariton condensate.',
        'doi': '10.1140/epjd/s10053-022-00477-5',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Paris_long.kappa': {
        'value': 5.0e10,
        'unit': 's^-1',
        'tier': 'PROJECTED',
        'source': 'Falque et al., PRL 135, 023401 (2025)',
        'detail': 'SLM-controlled horizon, projected surface gravity ~0.05 THz.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Falque demonstrated polariton horizons but did not report κ directly. '
                 'This is an order-of-magnitude estimate.',
    },
    'Paris_long.tau_cav': {
        'value': 100e-12,
        'unit': 's',
        'tier': 'MEASURED',
        'source': 'Falque et al., PRL 135, 023401 (2025)',
        'detail': 'Long-lifetime cavity, τ = 100 ps.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Paris_long.Gamma_pol': {
        'value': 1.0e10,
        'unit': 's^-1',
        'tier': 'DERIVED',
        'source': 'Derived: 1/tau_cav',
        'detail': 'Γ_pol = 1/τ_cav = 1/(100 ps) = 10^10 s⁻¹.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Derived from tau_cav, not independently measured.',
    },
    'Paris_long.gamma_phonon_dim': {
        'value': 1e-4,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'NEEDS IDENTIFICATION',
        'detail': 'Dimensionless phonon damping, subdominant to cavity decay. '
                  'Order-of-magnitude estimate.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Estimated, not measured or published.',
    },
    # Paris_ultralong and Paris_standard share c_s, xi, kappa, gamma_phonon_dim
    # with Paris_long. Only tau_cav and Gamma_pol differ.
    'Paris_ultralong.tau_cav': {
        'value': 300e-12,
        'unit': 's',
        'tier': 'MEASURED',
        'source': 'Falque et al., PRL 135, 023401 (2025)',
        'detail': 'Ultra-long-lifetime cavity, τ = 300 ps.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Paris_ultralong.Gamma_pol': {
        'value': 3.33e9,
        'unit': 's^-1',
        'tier': 'DERIVED',
        'source': 'Derived: 1/tau_cav',
        'detail': 'Γ_pol = 1/(300 ps) ≈ 3.33×10⁹ s⁻¹.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Paris_standard.tau_cav': {
        'value': 3e-12,
        'unit': 's',
        'tier': 'MEASURED',
        'source': 'Typical GaAs microcavity',
        'detail': 'Standard cavity lifetime ~3 ps.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Standard value, not from a specific paper.',
    },
    'Paris_standard.Gamma_pol': {
        'value': 3.33e11,
        'unit': 's^-1',
        'tier': 'DERIVED',
        'source': 'Derived: 1/tau_cav',
        'detail': 'Γ_pol = 1/(3 ps) ≈ 3.33×10¹¹ s⁻¹.',
        'doi': None,
        'llm_verified_date': None,
        'llm_verified_notes': None,
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
}


# ════════════════════════════════════════════════════════════════════
# Helper functions for the provenance registry
# ════════════════════════════════════════════════════════════════════

def get_unverified_params(level='llm'):
    """Return list of parameter keys that are not yet verified at the given level.

    Args:
        level: 'llm' or 'human'
    """
    date_field = f'{level}_verified_date'
    return [k for k, v in PARAMETER_PROVENANCE.items()
            if v.get(date_field) is None]


def get_conflicts():
    """Return list of parameter keys with value=None (unresolved conflicts)."""
    return [k for k, v in PARAMETER_PROVENANCE.items()
            if v['value'] is None]


def get_params_by_tier(tier):
    """Return list of parameter keys with the given confidence tier."""
    return [k for k, v in PARAMETER_PROVENANCE.items()
            if v['tier'] == tier]


def get_params_for_paper(paper_num):
    """Return parameter keys relevant to a specific paper.

    Maps paper numbers to the platforms/atoms they reference.
    """
    # Papers 1-4 use all 3 BEC platforms
    # Paper 5-6 use ADW model params (not in provenance — model choices)
    # Paper 7 uses lattice framework (not experimental params)
    bec_params = [k for k in PARAMETER_PROVENANCE
                  if any(k.startswith(p) for p in
                         ['Steinhauer', 'Heidelberg', 'Trento', 'Rb87', 'K39', 'Na23'])]
    polariton_params = [k for k in PARAMETER_PROVENANCE
                        if k.startswith('Paris') or k == 'POLARITON_MASS']

    paper_map = {
        1: bec_params,
        2: bec_params,
        3: bec_params,  # gauge erasure references BEC context
        4: bec_params,
        5: [],  # ADW — model params, not experimental
        6: [],  # vestigial — MC model
        7: [],  # chirality — lattice framework
    }
    return paper_map.get(paper_num, bec_params + polariton_params)


def summary():
    """Print provenance registry summary."""
    total = len(PARAMETER_PROVENANCE)
    llm = total - len(get_unverified_params('llm'))
    human = total - len(get_unverified_params('human'))
    conflicts = len(get_conflicts())
    tiers = {}
    for v in PARAMETER_PROVENANCE.values():
        tiers[v['tier']] = tiers.get(v['tier'], 0) + 1

    print(f"Parameter Provenance Registry: {total} parameters")
    print(f"  LLM-verified:   {llm}/{total}")
    print(f"  Human-verified: {human}/{total}")
    print(f"  Conflicts:      {conflicts}")
    print(f"  Tiers: {tiers}")
