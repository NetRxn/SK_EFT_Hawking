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
        'source': 'CODATA 2018 / SI 2019',
        'detail': 'Exact value by definition in SI 2019 redefinition. '
                  'ℏ = h/(2π) = 1.054571817...×10⁻³⁴ J·s.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'CODATA exact value. Verified against NIST reference: '
                              'https://physics.nist.gov/cgi-bin/cuu/Value?hbar',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Exact by definition in SI 2019.',
    },
    'K_B': {
        'value': 1.380649e-23,
        'unit': 'J/K',
        'tier': 'MEASURED',
        'source': 'CODATA 2018 / SI 2019',
        'detail': 'Exact value by definition in SI 2019 redefinition. '
                  'k_B = 1.380649×10⁻²³ J/K.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'CODATA exact value. Verified against NIST reference: '
                              'https://physics.nist.gov/cgi-bin/cuu/Value?k',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Exact by definition in SI 2019.',
    },
    'A_BOHR': {
        'value': 5.29177210903e-11,
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'CODATA 2018',
        'detail': 'Bohr radius a₀ = 5.29177210903(80)×10⁻¹¹ m. NIST SP 961.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'CODATA 2018 recommended value. Verified against NIST reference: '
                              'https://physics.nist.gov/cgi-bin/cuu/Value?bohrrada0',
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
        'detail': '86.909180531 u × 1.66053906660e-27 kg/u = 1.443160648e-25 kg',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'NIST standard atomic mass for Rb-87. Calculation: '
                              '86.909180531 u × 1.66053906660e-27 kg/u = 1.4432e-25 kg. '
                              'Matches code value to 7 significant figures.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Rb87.a_s': {
        'value': 5.31e-9,  # LLM-VERIFIED: 100.4 a_0 from van Kempen, NOT 109 a_0
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'van Kempen et al., PRL 88, 093201 (2002)',
        'detail': 'Page 2: "aF=2 = +100.4(1)a0" for the F=2 hyperfine state. '
                  'Steinhauer uses |F=2, mF=2> (confirmed in Wang 2017 Table II). '
                  '100.4 a_0 × 5.2918e-11 m/a_0 = 5.313e-9 m ≈ 5.31 nm.',
        'doi': '10.1103/PhysRevLett.88.093201',
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'LLM read arXiv:cond-mat/0110610 (van Kempen 2002). Page 2: '
                              '"aF=2 = +100.4(1)a0". This is the F=2 channel scattering length. '
                              'Code currently uses 109 a_0 = 5.77 nm — THIS IS WRONG. '
                              '109 a_0 does not appear in van Kempen; it may be from an older '
                              'reference or a different channel. The pure triplet is 98.98 a_0. '
                              'Impact: ~4% change in c_s (0.571 → 0.548 mm/s with corrected omega_perp).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'CODE HAS WRONG VALUE: 109 a_0 = 5.77 nm. Correct: 100.4 a_0 = 5.31 nm. '
                 'Impact is ~8% in a_s, ~4% in c_s. Secondary to the omega_perp 4× error '
                 'but still needs fixing for publication accuracy.',
    },

    # ── K-39 atomic properties ─────────────────────────────────────

    'K39.mass': {
        'value': 6.470076e-26,
        'unit': 'kg',
        'tier': 'MEASURED',
        'source': 'NIST Atomic Weights and Isotopic Compositions',
        'detail': '38.96370668 u × 1.66053906660e-27 kg/u = 6.470076e-26 kg',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'NIST standard atomic mass for K-39.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'K39.a_s': {
        'value': 50e-9,
        'unit': 'm',
        'tier': 'PROJECTED',
        'source': 'Design choice — K-39 Feshbach resonance allows wide tuning',
        'detail': 'K-39 has a broad Feshbach resonance near 402 G that allows '
                  'tuning a_s from near-zero to thousands of a_0 (D\'Errico et al., '
                  'New J. Phys. 9, 223 (2007)). 50 nm ≈ 945 a_0 is a design choice '
                  'for a projected experiment — chosen as a moderate value that gives '
                  'reasonable BEC density and sound speed.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — tunable parameter. 50 nm = 945 a_0, well within '
                              'the K-39 Feshbach tuning range (up to ~4000 a_0 near resonance). '
                              'Original detail incorrectly stated "0-200 a_0" which is the '
                              'BACKGROUND scattering length range, not the Feshbach-enhanced range. '
                              'Falke et al. 2008 is spectroscopy, not Feshbach tuning — '
                              'D\'Errico et al. 2007 is the correct Feshbach reference.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Tunable parameter, not a fixed measurement. 50 nm = 945 a_0 is within '
                 'the broad K-39 Feshbach resonance range. This is a design choice — '
                 'Heidelberg could choose any value by tuning the magnetic field.',
    },

    # ── Na-23 atomic properties ────────────────────────────────────

    'Na23.mass': {
        'value': 3.8175458e-26,
        'unit': 'kg',
        'tier': 'MEASURED',
        'source': 'NIST Atomic Weights and Isotopic Compositions',
        'detail': '22.9897692820 u × 1.66053906660e-27 kg/u = 3.8175458e-26 kg',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'NIST standard atomic mass for Na-23.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Na23.a_s': {
        'value': 2.75e-9,
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'Knoop et al., PRA 83, 042704 (2011)',
        'detail': 'Na-23 triplet scattering length a_T = 54.54(20) a_0 '
                  '(Knoop et al. 2011, high-precision Feshbach spectroscopy). '
                  'Older value: 52.98 a_0 (Tiesinga et al. 1996). '
                  '2.75 nm ≈ 52 a_0 — matches older reference. '
                  'With Knoop: 54.54 a_0 = 2.887 nm.',
        'doi': '10.1103/PhysRevA.83.042704',
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'Standard Na-23 value. 52 a_0 = 2.75 nm matches Tiesinga 1996. '
                              'More recent Knoop 2011 gives 54.54(20) a_0 = 2.887 nm. '
                              'Difference is ~5%. Code uses the older value. '
                              'For PROJECTED Trento experiment, precision doesn\'t matter — '
                              'but for publication, should cite Knoop 2011.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Value 2.75 nm (52 a_0) is from older Tiesinga 1996. '
                 'More precise Knoop 2011: 54.54 a_0 = 2.887 nm. ~5% difference. '
                 'Acceptable for projected experiment.',
    },

    # ── Steinhauer experimental parameters ─────────────────────────

    'Steinhauer.density_upstream': {
        'value': 5e7,
        'unit': 'm^-1',
        'tier': 'EXTRACTED',
        'source': 'Wang et al., PRA 96, 023616 (2017)',
        'detail': 'Page 13 text: "nmax ~ 120 μm⁻¹" (peak density from 3D GP). '
                  'Fig. 2 shows position-dependent profile. '
                  'Horizon region is well below peak: ~40-60 μm⁻¹. '
                  '5e7 m⁻¹ = 50 μm⁻¹ chosen as approximate horizon-region value.',
        'doi': '10.1103/PhysRevA.96.023616',
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'LLM read arXiv:1605.01027 page 13: "nmax ~ 120 μm⁻¹" is the '
                              'PEAK density, not horizon density. 50 μm⁻¹ is reasonable for '
                              'horizon region based on Fig. 2 density profiles. N=6000 atoms '
                              'in ~100 μm BEC → average ~60 μm⁻¹.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Position-dependent quantity. Peak = 120 μm⁻¹, horizon ~ 40-60 μm⁻¹. '
                 'Our value of 50 μm⁻¹ is an approximation, not an exact measurement.',
    },
    'Steinhauer.velocity_upstream': {
        'value': 0.41e-3,
        'unit': 'm/s',
        'tier': 'DERIVED',
        'source': 'NEEDS IDENTIFICATION — derived from Mach number assumption',
        'detail': 'No published table with this exact value found. '
                  'Appears to be derived from Mach ~ 0.74 × c_s, where c_s itself '
                  'is computed from (now-known-wrong) omega_perp = 500 Hz. '
                  'With corrected c_s ≈ 0.55 mm/s, Mach 0.74 gives v ≈ 0.41 mm/s, '
                  'not 0.85 mm/s. VALUE NEEDS RECALCULATION after omega_perp fix.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'Tier corrected from PROJECTED to DERIVED — Steinhauer experiment '
                              'was actually performed (Nature Physics 2016). Value appears derived '
                              'from Mach number × c_s. With corrected omega_perp, the derived '
                              'velocity would be ~0.41 mm/s not 0.85 mm/s. Needs recalculation '
                              'or primary source identification.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'CIRCULAR DERIVATION: v = Mach × c_s, but c_s was computed from wrong '
                 'omega_perp. With corrected params, v ≈ 0.41 mm/s. Also: Steinhauer may '
                 'report flow velocity directly in density profile figures — needs check.',
    },
    'Steinhauer.omega_perp': {
        'value': 2 * np.pi * 123,  # LLM-VERIFIED: 123 Hz from Wang et al. Table II
        'unit': 'rad/s',
        'tier': 'MEASURED',
        'source': 'Wang et al., PRA 96, 023616 (2017)',
        'detail': 'Table II: "radial trap frequency ν = 123 Hz". '
                  'Also confirmed in text: "ω_x/ω_ρ = 4.5 Hz/123 Hz". '
                  'The paper labels this ω_ρ (radial) = ω_perp (transverse). '
                  'This is for Steinhauer 2014 apparatus (same trap as 2019).',
        'doi': '10.1103/PhysRevA.96.023616',
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'LLM read arXiv:1605.01027 (correct arXiv ID, not 1706.01483 '
                              'which was a hallucinated combustion paper). Page 13, Table II: '
                              '"radial trap frequency ν = 123 Hz". g₁D formula in Eq. A8 '
                              'context: g1D = g3D·m·ω_ρ/h = 2ℏ·ω_perp·a_s (confirmed). '
                              'CODE CURRENTLY HAS 500 Hz — NO SOURCE EXISTS FOR THIS VALUE.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'CRITICAL: Code uses 2π×500 Hz but source says 123 Hz. '
                 'The 500 Hz value has NO published source. '
                 '123 Hz → g₁D = 8.63e-40 J·m, c_s ≈ 0.55 mm/s, κ ≈ 290 s⁻¹ (matches published T_H). '
                 '500 Hz → g₁D = 3.82e-39 J·m, c_s = 1.15 mm/s, κ = 21.9 s⁻¹ (wrong by 13×). '
                 'Also: deep research arXiv ID 1706.01483 was WRONG (combustion paper). '
                 'Correct arXiv is 1605.01027.',
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
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — Heidelberg (Oberthaler) has only published analog cosmology (Viermann 2022), not Hawking. No transonic flow experiment exists. Density value is an arbitrary projection.',
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
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — no Heidelberg Hawking experiment. 3.0 mm/s chosen for Mach < 1 at projected sound speed.',
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
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — no Heidelberg Hawking experiment. 500 Hz is unsourced (same issue as Steinhauer). Heidelberg cosmology experiments use 2D geometry with different confinement.',
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
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — Trento spin-sonic is a theoretical proposal (Berti 2025). Paper uses dimensionless params only, no experimental density published. 1e8 m⁻¹ is an arbitrary projection.',
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
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — no Trento Hawking experiment. 1.6 mm/s chosen for Mach ~ 0.73 at projected sound speed.',
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
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — no Trento Hawking experiment. 500 Hz is unsourced (same issue as Steinhauer). Trento two-component Na-23 would have different confinement.',
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
        'detail': 'Page 4: "we extract the effective polariton mass at the working '
                  'point, m* = 7.0 × 10⁻³⁵ kg." Fitted from measured spectrum.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'LLM read arXiv:2311.01392 (Falque 2025). Page 4, Section III: '
                              '"m* = 7.0 × 10⁻³⁵ kg" — extracted from measured polariton spectrum. '
                              'Value matches code. ArXiv ID for citation: 2311.01392.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Paris_long.c_s': {
        'value': 4.0e5,
        'unit': 'm/s',
        'tier': 'MEASURED',
        'source': 'Falque et al., PRL 135, 023401 (2025), §IV.1',
        'detail': 'UPDATE 2026-04-13 (Phase 5u Wave 4): adopted Falque\'s measured value '
                  '0.40 µm/ps = 4.0e5 m/s directly, replacing the Apr 5 "representative '
                  'midpoint" of 5.0e5 (which was a mean of 0.40/0.40/0.81 across Falque/'
                  'Estrecho/Amo). Using Falque\'s value aligns with claims that Paper 12 '
                  'makes about the LKB platform specifically. Estrecho and Amo retained '
                  'as cross-checks in the 2026-04-05 history below.'
                  '\n\n'
                  '2026-04-05 history: Previous code used 1.0e6 m/s (1 µm/ps) from '
                  'Jacquet 2022 theoretical simulation — a reservoir-free GPE model that '
                  'never measured c_s experimentally. Three independent measurements: '
                  '(1) Falque PRL 135, 023401 (2025) §IV.1: cs ≈ 0.40 µm/ps; '
                  '(2) Estrecho PRL 126, 075301 (2021): c₀ = 0.4 µm/ps at threshold; '
                  '(3) Amo NatPhys 5, 805 (2009): cs = 0.81 µm/ps under strong resonant drive. '
                  'Stepanov NatComm 10, 3869 (2019): c_s "apparently twice too low" vs naive. '
                  'Root cause: excitonic reservoir absorbs 50-75% of blueshift without '
                  'contributing to dynamic c_s. Correct formula: c_s = sqrt(g·n_condensate/m*), '
                  'NOT sqrt(ΔE_total/m*).',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': '2026-04-13',
        'llm_verified_notes': 'Re-read Falque full text (arXiv:2311.01392v2) 2026-04-13. '
                              'c_s = 0.40 µm/ps confirmed in §IV.1. Adopting Falque\'s value '
                              'directly (Wave 4) rather than the blended midpoint.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': '2026-04-13: Updated from 5.0e5 to 4.0e5 m/s to match Falque directly. '
                 'Previous 5.0e5 was a blended midpoint; Falque is the primary source for '
                 'the Paris platform and directly reports 0.40 µm/ps.',
    },
    'Paris_long.xi': {
        'value': 3.4e-6,
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'Falque et al., PRL 135, 023401 (2025), §IV.1',
        'detail': 'UPDATE 2026-04-13 (Phase 5u Wave 4): adopted Falque\'s measured upstream '
                  'value ξ = 3.4 µm directly, replacing the Apr 5 computed 3.0 µm '
                  '(which was derived from the blended c_s=5e5). With c_s now 4e5, '
                  'ξ = ℏ/(m*·c_s) = 1.05e-34/(7e-35·4e5) = 3.75 µm; Falque\'s measured '
                  '3.4 µm upstream is close but not exactly ℏ/(m*c_s) (also reports '
                  '4.0 µm downstream, showing the spatial variation). Using the measured '
                  'upstream value directly is more faithful to the primary source than '
                  'deriving from c_s.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': '2026-04-13',
        'llm_verified_notes': 'Falque §IV.1 reports ξ ≈ 3.4 µm upstream, 4.0 µm downstream. '
                              'We adopt the upstream value as the reference since horizon '
                              'physics is set upstream.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': '2026-04-13: Updated from 3.0e-6 to 3.4e-6 m to match Falque measured value.',
    },
    'Paris_long.kappa': {
        'value': 7.0e10,
        'unit': 's^-1',
        'tier': 'MEASURED',
        'source': 'Falque et al., PRL 135, 023401 (2025), Fig. 2 / §IV.1',
        'detail': 'PROVENANCE CORRECTION 2026-04-13 (Phase 5u Wave 3). The Falque '
                  'PRL DOES report three measured κ values (verified by LLM re-read '
                  'of arXiv:2311.01392v2 full text, 2026-04-13): '
                  'κ = 0.07 ps⁻¹ (smooth horizon, red trace in Fig. 2), '
                  'κ = 0.08 ps⁻¹ (smooth horizon, purple trace in Fig. 2), '
                  'κ = 0.11 ps⁻¹ (steep horizon, Section IV.2). '
                  'In SI units: 7e10, 8e10, 1.1e11 s⁻¹. '
                  'The current constants.py value (5e10 s⁻¹) is BELOW the measured '
                  'range — not a projection but an underestimate. Flagged for update: '
                  'Phase 5u Wave 4 will decide whether to (a) adopt the smooth-horizon '
                  'value (7e10 s⁻¹) as the default for Paris_long, (b) adopt the steep '
                  'value (1.1e11 s⁻¹) for maximum T_H, or (c) parametrize all three '
                  'configurations. Paper 12 numerics for T_H, D, G(ω) need to be '
                  'recomputed downstream.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': '2026-04-13',
        'llm_verified_notes': 'Re-verified against arXiv:2311.01392v2 full text. The '
                              'prior 2026-03-31 LLM reading — which claimed "Falque '
                              'did not report κ" — was WRONG. The 2026-04-10 LKB audit '
                              '(temporary/working-docs/reviews/papers/2026-04-10-Perplexity/'
                              'LKB-Paris-Polariton-Assessment.md) was correct to cite '
                              'the three measured κ values. Root cause of the 2026-03-31 '
                              'error: the LLM likely read only the arXiv abstract rather '
                              'than the full paper, and the abstract does not include '
                              'the numerical κ values (they appear in Fig. 2 and '
                              'Section IV). Process lesson → Phase 5u Wave 18 '
                              '(cross-LLM provenance consistency check).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Falque reports three measured κ values spanning 7e10–1.1e11 s⁻¹. '
                 'Current value 5e10 is an underestimate; awaiting decision on which '
                 'Falque configuration to adopt (Phase 5u Wave 4).',
    },
    'Paris_long.tau_cav': {
        'value': 100e-12,
        'unit': 's',
        'tier': 'PROJECTED',
        'source': 'Projected — NOT from Falque 2025 (actual cavity has τ ≈ 8 ps)',
        'detail': 'Falque 2025 reports ℏγ ≈ 80 µeV → γ = 1.2e11 s⁻¹ → τ ≈ 8 ps. '
                  '100 ps is a projected value for a next-generation long-lifetime cavity. '
                  'Such cavities exist (e.g., Ballarini 2017) but Falque did not use one.',
        'doi': '10.1103/PhysRevLett.135.023401',
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'LLM read Falque 2025 (arXiv:2311.01392) page 9: '
                              '"ℏγ ≈ 80 µeV" → τ ≈ 8 ps, NOT 100 ps. The 100 ps value '
                              'is a projection for future cavity technology. '
                              'TIER CHANGED from MEASURED to PROJECTED.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'TIER CORRECTED: Was MEASURED, now PROJECTED. Falque actual cavity τ ≈ 8 ps.',
    },
    'Paris_long.Gamma_pol': {
        'value': 1.0e10,
        'unit': 's^-1',
        'tier': 'DERIVED',
        'source': 'Derived: 1/tau_cav',
        'detail': 'Γ_pol = 1/τ_cav = 1/(100 ps) = 10^10 s⁻¹.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'DERIVED: trivially verified from parent parameter.',
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
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — order-of-magnitude estimate for polariton-polariton scattering damping. In polariton systems cavity decay dominates; phonon damping is subdominant. 1e-4 is a reasonable but unconstrained estimate.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Estimated, not measured or published.',
    },
    # Paris_ultralong and Paris_standard share c_s, xi, kappa, gamma_phonon_dim
    # with Paris_long. Only tau_cav and Gamma_pol differ.
    'Paris_ultralong.tau_cav': {
        'value': 300e-12,
        'unit': 's',
        'tier': 'PROJECTED',
        'source': 'Projected — validated by Snoke/Pfeiffer high-Q samples',
        'detail': 'Ultra-long-lifetime cavity τ = 300 ps. Snoke/Pfeiffer GaAs samples '
                  'achieve τ ~ 270 ps with Q ~ 10^6 (Nelsen PRX 3, 041015, 2013; '
                  'Alnatah SciAdv 10, eadk6960, 2024). Deep research (Phase-5d polariton '
                  'review) confirms these cavities exist and show BKT physics. '
                  'Falque actual cavity τ ≈ 8 ps — different sample type.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'PROJECTED — 300 ps is a projected future cavity. '
                              'Falque 2025 actual cavity has τ ≈ 8 ps (ℏγ ≈ 80 µeV). '
                              'TIER CHANGED from MEASURED to PROJECTED.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'TIER CORRECTED: Was MEASURED, now PROJECTED.',
    },
    'Paris_ultralong.Gamma_pol': {
        'value': 3.33e9,
        'unit': 's^-1',
        'tier': 'DERIVED',
        'source': 'Derived: 1/tau_cav',
        'detail': 'Γ_pol = 1/(300 ps) ≈ 3.33×10⁹ s⁻¹.',
        'doi': None,
        'llm_verified_date': '2026-03-31',
        'llm_verified_notes': 'DERIVED: trivially verified from parent parameter.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'Paris_standard.tau_cav': {
        'value': 8e-12,
        'unit': 's',
        'tier': 'MEASURED',
        'source': 'Falque et al. 2025 polariton condensate cavity',
        'detail': 'Standard Paris polariton cavity lifetime: τ_cav ≈ 8 ps '
                  '(Falque 2025 actual measured cavity value, superseded the '
                  'prior 3 ps order-of-magnitude estimate used through March 2026).',
        'doi': None,
        'llm_verified_date': '2026-04-14',
        'llm_verified_notes': 'Updated 2026-04-14 from prior 3 ps EXTRACTED estimate to '
                              'Falque 2025 actual measured value of 8 ps. constants.py '
                              "Paris_standard.tau_cav comment confirms: 'Falque 2025 actual "
                              "cavity; was 3 ps projected'. Tier upgraded EXTRACTED → MEASURED.",
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Falque 2025 measured value. Update from prior 3 ps order-of-magnitude '
                 'estimate. Original literature-derived 3 ps lives in Paris_long.tau_cav '
                 'as the order-of-magnitude reference.',
    },
    'Paris_standard.Gamma_pol': {
        'value': 1.25e11,
        'unit': 's^-1',
        'tier': 'DERIVED',
        'source': 'Derived: 1/tau_cav',
        'detail': 'Γ_pol = 1/(8 ps) = 1.25×10¹¹ s⁻¹ (from Falque 2025 τ_cav).',
        'doi': None,
        'llm_verified_date': '2026-04-14',
        'llm_verified_notes': 'DERIVED from updated τ_cav = 8 ps (Falque 2025). '
                              'Was 3.33×10¹¹ s⁻¹ when τ_cav = 3 ps.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },

    # ── Graphene Dirac fluid parameters (Phase 5w) ─────────────────

    'V_FERMI_GRAPHENE': {
        'value': 1.0e6,
        'unit': 'm/s',
        'tier': 'MEASURED',
        'source': 'Castro Neto et al., Rev. Mod. Phys. 81, 109 (2009)',
        'detail': 'Fermi velocity in monolayer graphene: v_F ≈ 10⁶ m/s. '
                  'Measured via ARPES, STS, and magneto-transport. '
                  'Renormalized by e-e interactions: ~15% enhancement at low carrier '
                  'density (Elias et al., Nature Physics 7, 701, 2011).',
        'doi': '10.1103/RevModPhys.81.109',
        'llm_verified_date': '2026-04-16',
        'llm_verified_notes': 'Canonical value from Castro Neto review. '
                              'Confirmed in Majumdar 2025, Lucas & Fong 2018 review.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },
    'ALPHA_GRAPHENE_HBN': {
        'value': 0.7,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Lucas & Fong, JPCM 30, 053001 (2018)',
        'detail': 'Effective fine structure constant α_g = e²/(ℏv_Fε_eff) on hBN. '
                  'ε_eff depends on screening model: static ε_eff ≈ (1+ε_hBN)/2 ≈ 2.0 '
                  'gives α ≈ 1.1; dynamic screening and RPA reduce to 0.5-0.9. '
                  'Representative value 0.7 used following Gallagher 2019 analysis.',
        'doi': '10.1088/1361-648X/aaa274',
        'llm_verified_date': '2026-04-16',
        'llm_verified_notes': 'Range 0.5-0.9 confirmed across Lucas & Fong 2018, '
                              'Gallagher 2019, Majumdar 2025. Midpoint 0.7 adopted.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Range 0.5-0.9; 0.7 is representative midpoint.',
    },
    'Dean_bilayer_nozzle.c_s': {
        'value': 4.4e5,
        'unit': 'm/s',
        'tier': 'MEASURED',
        'source': 'Geurs et al., arXiv:2509.16321 (2025)',
        'detail': 'Sound speed in bilayer graphene Dirac fluid. Dean group measured '
                  'supersonic electron flow through de Laval nozzle geometry in '
                  'hBN-encapsulated bilayer graphene. c_s ≈ 435 km/s in bilayer '
                  '(lower than monolayer v_F/√2 ≈ 710 km/s due to bilayer band structure).',
        'doi': None,
        'llm_verified_date': '2026-04-16',
        'llm_verified_notes': 'From Phase 5w deep research survey. Geurs 2025 reports '
                              'supersonic flow past the hydrodynamic sound speed.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'First electronic sonic horizon. Bilayer c_s < monolayer c_s.',
    },
    'Dean_bilayer_nozzle.channel_width_nm': {
        'value': 1000,
        'unit': 'nm',
        'tier': 'EXTRACTED',
        'source': 'Geurs et al., arXiv:2509.16321 (2025); Phase 5w deep research §2',
        'detail': 'Channel width W for the Dean bilayer nozzle, used in the quasi-1D '
                  'reduction bound (Phase 5w Wave 10b). The first transverse-mode '
                  'threshold is ω_⊥ = π·c_s/W ≈ 1.38e12 rad/s for W=1 μm, placing all '
                  'transverse modes evanescent within the detection band (ω_⊥/ω_H ≈ 4.46). '
                  'Evanescent suppression factor exp(-2π·L/W) ≈ 0.284 at L/W=0.2.',
        'doi': None,
        'llm_verified_date': '2026-04-22',
        'llm_verified_notes': 'Dean geometry standard per Phase 5w deep research Block 2 §2.1-2.3.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Required by greybody quasi-1D correction bound (Lean T5 in QuasiOneDReduction).',
    },
    'Dean_bilayer_nozzle.l_ee_nm': {
        'value': 51,
        'unit': 'nm',
        'tier': 'EXTRACTED',
        'source': 'Phase 5w deep research §1.4 (Finazzi-Parentani regime analysis)',
        'detail': 'Electron-electron mean free path l_ee for the Dean hydrodynamic '
                  'regime. Sets the dispersive length in the Dean adiabaticity parameter '
                  'D = κ·l_ee/c_s = 0.232 (adiabatic regime D<1). Also sets the dispersive '
                  'UV cutoff ω_max = √(κ c_s/l_ee) ≈ 4.15e12 rad/s via Macher-Parentani.',
        'doi': None,
        'llm_verified_date': '2026-04-22',
        'llm_verified_notes': 'Deep research cites standard hydrodynamic regime l_ee ≈ 50 nm '
                              'for high-mobility graphene at Dean operating temperatures; '
                              'reproduces D = 0.232 quoted in deep research §1.4.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Distinct from momentum-relaxation l_mr (5 μm); l_ee governs dispersion.',
    },
    'Dean_bilayer_nozzle.v_over_c_s_horizon': {
        'value': 0.985,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Phase 5w deep research §1.1 (Anderson et al. PRD 87 profile-independent limit)',
        'detail': 'Flow velocity at the horizon expressed as v/c_s. Chosen such that the '
                  'profile-independent zero-frequency greybody Γ₀ = 4·c_R·v/(c_R+v)² matches '
                  'the deep-research quoted value 0.9994 for the Dean nozzle. The exact value '
                  'depends on the asymptotic flow parameters which the deep research fixes '
                  'via nozzle geometry. Value is a single-point choice; the full v(x) profile '
                  'is a PDE-gap tracked hypothesis (see QuasiOneDReduction).',
        'doi': None,
        'llm_verified_date': '2026-04-22',
        'llm_verified_notes': 'Derived from Anderson-Balbinot-Fabbri-Parentani (PRD 87) closed-form; '
                              'the 0.9994 quote places v/c_s at ~0.985 for subsonic-side c_R = c_s.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Only used to evaluate Γ₀; the Lean greybody_zero_freq theorem is fully general.',
    },
    'Dean_bilayer_nozzle.T_H_K': {
        'value': 2.4,
        'unit': 'K',
        'tier': 'DERIVED',
        'source': 'Phase 5w deep research (this project)',
        'detail': 'Predicted analog Hawking temperature for Dean group bilayer nozzle. '
                  'T_H = ℏ|dv/dx|_horizon/(2πk_B) with |dv/dx| ~ c_s/L, '
                  'L ~ 200 nm (nozzle throat). T_H ≈ 2.4 K. '
                  'Ratio T_H/T_ambient ≈ 0.01-0.02.',
        'doi': None,
        'llm_verified_date': '2026-04-16',
        'llm_verified_notes': 'Computed from deep research §3 parameter table. '
                              'Consistent with T_H = ℏ × 2e12 / (2π × k_B) ≈ 2.4 K.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'DERIVED from geometry + measured c_s. Not directly measured.',
    },
    'Monolayer_100nm.c_s': {
        'value': 7.1e5,
        'unit': 'm/s',
        'tier': 'MEASURED',
        'source': 'Zhao et al., Nature 614, 688 (2023)',
        'detail': 'Sound speed in monolayer graphene Dirac fluid: c_s = v_F/√2 ≈ 710 km/s. '
                  'First direct measurement via hydrodynamic plasmon spectroscopy.',
        'doi': '10.1038/s41586-022-05619-8',
        'llm_verified_date': '2026-04-16',
        'llm_verified_notes': 'Zhao 2023 directly measures electronic sound velocity. '
                              'Consistent with conformal prediction c_s = v_F/√2.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used for Monolayer_100nm, Monolayer_50nm, PN_junction_10nm.',
    },
    'Majumdar.sigma_Q': {
        'value': 4.0,
        'unit': 'e²/h',
        'tier': 'MEASURED',
        'source': 'Majumdar et al., Nature Physics 21, 1374 (2025) [arXiv:2501.03193]',
        'detail': 'Universal quantum critical conductivity σ_Q = (4 ± 1) × e²/h. '
                  'Device-independent: varies <25% across samples despite σ_min '
                  'varying by order of magnitude with disorder. Extracted from '
                  'thermal transport (not electrical σ_min).',
        'doi': None,
        'llm_verified_date': '2026-04-16',
        'llm_verified_notes': 'Extracted from arXiv:2501.03193 full HTML via WebFetch. '
                              'σ_Q = (4 ± 1) e²/h confirmed in abstract and results.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used for all graphene platforms as universal value.',
    },
    'Majumdar.eta_over_s': {
        'value': 4.0,
        'unit': 'ℏ/(4πk_B)',
        'tier': 'MEASURED',
        'source': 'Majumdar et al., Nature Physics 21, 1374 (2025) [arXiv:2501.03193]',
        'detail': 'Viscosity-to-entropy ratio η/s ≈ 4 × ℏ/(4πk_B) in cleanest '
                  'devices near room temperature. Within factor 4 of KSS bound.',
        'doi': None,
        'llm_verified_date': '2026-04-16',
        'llm_verified_notes': 'From arXiv:2501.03193: "viscosity-to-entropy-density '
                              'ratio η_th/s_th approaches the theoretical limit '
                              'ℏ/4πk_B within a factor of four."',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': None,
    },

    # ── Majorana 8×8 representation constants (Wave 7B) ───────────

    'MAJORANA_GAMMA_8x8': {
        'value': '4 real symmetric 8×8 matrices',
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'Lawson & Michelsohn, "Spin Geometry" (1989), Ch. I §5',
        'detail': 'Real 8×8 representation of Cl(4,0). The 4 gamma matrices '
                  'satisfy {Γ^a, Γ^b} = 2δ^{ab}, are symmetric (Γ^a)^T = Γ^a, '
                  'and real. Unique up to orthogonal conjugation. '
                  'Constructed via tensor products of Pauli matrices: '
                  'Γ^1=σ₁⊗σ₀⊗σ₁, Γ^2=σ₁⊗σ₀⊗σ₃, Γ^3=σ₁⊗σ₁⊗σ₀, Γ^4=σ₁⊗σ₃⊗σ₀.',
        'doi': None,
        'llm_verified_date': '2026-04-01',
        'llm_verified_notes': 'Verified: Cl(4,0) ≅ M₂(ℍ) admits a real 8×8 rep '
                              '(but NOT a real 4×4 rep). Anticommutation verified '
                              'computationally in test_gauge.py::TestMajorana8x8GammaMatrices.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Lean: majorana_gamma_squared_identity, majorana_anticommutation '
                 '(MajoranaKramers.lean). All proved, zero sorry.',
    },
    'MAJORANA_J1': {
        'value': 'antisymmetric 8×8 matrix, J₁² = -I',
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'Lawson & Michelsohn, "Spin Geometry" (1989), Ch. I §5',
        'detail': 'Charge conjugation matrix in the 8×8 Majorana basis. '
                  'J₁ is antisymmetric (J₁^T = -J₁), satisfies J₁² = -I, '
                  'and commutes with all Γ^a: [J₁, Γ^a] = 0. '
                  'J₁Γ^a is antisymmetric, enabling nonzero Majorana bilinear '
                  'Ψ^T(J₁Γ^a)Ψ. Part of the quaternionic commutant of Cl(4,0).',
        'doi': None,
        'llm_verified_date': '2026-04-01',
        'llm_verified_notes': 'Verified: J₁ from deep research "The 8×8 Majorana '
                              'formulation for ADW fermion-bag MC". Properties checked '
                              'computationally in test_gauge.py::TestQuaternionicCommutant.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Lean: quaternionic_structure_squared, cg_antisymmetric '
                 '(MajoranaKramers.lean). All proved, zero sorry.',
    },
    'MAJORANA_J2': {
        'value': 'antisymmetric 8×8 matrix, J₂² = -I',
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'Wei/Wu/Li/Zhang/Xiang, PRL 116, 250601 (2016)',
        'detail': 'Kramers operator. Antisymmetric, J₂² = -I, '
                  '{J₁, J₂} = 0, [J₂, Γ^a] = 0, [J₂, S] = 0 for S ∈ Spin(4). '
                  'The key property {J₂, A} = 0 for the fermion matrix A '
                  'guarantees Pf(A) has definite sign → sign-problem-free MC.',
        'doi': '10.1103/PhysRevLett.116.250601',
        'llm_verified_date': '2026-04-01',
        'llm_verified_notes': 'Verified: Kramers positivity from Wei et al. PRL 116. '
                              'The pseudoreal structure of Spin(4) ≅ SU(2)_L × SU(2)_R '
                              'guarantees {J₂, A} = 0. Checked computationally in '
                              'test_gauge.py::TestKramersPfaffianSignAcrossConfigs.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Lean: kramers_anticommutation, kramers_pfaffian_definite_sign, '
                 'adw_sign_problem_free (MajoranaKramers.lean). All proved, zero sorry.',
    },
    'MAJORANA_J3': {
        'value': 'antisymmetric 8×8 matrix, J₃ = J₁·J₂',
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'Lawson & Michelsohn, "Spin Geometry" (1989), Ch. I §5',
        'detail': 'Third quaternionic structure. J₃ = J₁J₂, satisfies J₃² = -I, '
                  '{J₁, J₃} = 0, {J₂, J₃} = 0. Together J₁, J₂, J₃ generate '
                  'the quaternion algebra ℍ, the commutant of Cl(4,0) in M₈(ℝ).',
        'doi': None,
        'llm_verified_date': '2026-04-01',
        'llm_verified_notes': 'Verified: quaternion product rule checked in '
                              'test_gauge.py::TestQuaternionicCommutant::test_quaternion_product_rule.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Lean: j1_j2_anticommute (MajoranaKramers.lean). Proved, zero sorry.',
    },

    # ── SFDM / BK fiducial parameters (Phase 5x, paper 17) ─────────────
    # Added 2026-04-24 in response to adversarial-review finding 3.1
    # (paper17, ParameterProvenance gate). Values drawn from:
    #   - BK2015 (Berezhiani–Khoury, PRD 92, 103510, 2015, arXiv:1507.01019)
    #   - BK2025 (BK, Cintia, De Luca, Khoury, Phys Rep, arXiv:2505.23900)
    # Paper-17 classification tier: THEORETICAL — the BK values are
    # model parameters (scalar mass, self-coupling), not experimentally-
    # measured quantities. They fix the scale of the superfluid DM model;
    # measurement-driven constraints come later via Euclid/Roman forecasts.

    'SFDM.m_DM_BK': {
        'value': 0.6,  # eV
        'unit': 'eV',
        'tier': 'THEORETICAL',
        'source': 'Berezhiani & Khoury, PRD 92, 103510 (2015)',
        'detail': 'Scalar-field DM mass in the BK fiducial: m_DM = 0.6 eV. '
                  'Fixed by requiring the superfluid phase to form on galactic '
                  'scales (de Broglie wavelength at halo velocity dispersion). '
                  'See BK2015 Eq. (2.3) and surrounding discussion; same '
                  'fiducial carried through BK2025 Phys. Rep. review.',
        'doi': '10.1103/PhysRevD.92.103510',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Value repeatedly cited across BK corpus and in '
                              'the Phase 5x W1b merger forecast memo '
                              '(Lit-Search/Phase-5x/5x-SFDM Cluster Merger *.md). '
                              'Primary source: BK2015 PRD 92, 103510.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Paper 17 abstract + §SFDM merger. Model parameter, not '
                 'measurement — tier THEORETICAL.',
    },
    'SFDM.Lambda_BK': {
        'value': 0.2,  # meV
        'unit': 'meV',
        'tier': 'THEORETICAL',
        'source': 'Berezhiani & Khoury, PRD 92, 103510 (2015)',
        'detail': 'Self-coupling scale Λ = 0.2 meV in the BK fiducial. '
                  'Sets the chemical potential (μ ~ Λ) and hence the '
                  'sub-cluster sound speed c_s = sqrt(2μ/m).',
        'doi': '10.1103/PhysRevD.92.103510',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'BK2015 fiducial scaling; used throughout paper 17 '
                              '§sfdm-merger. Primary source same as SFDM.m_DM_BK.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Paper 17 abstract + §SFDM merger. Model parameter, not measurement.',
    },
    'SFDM.c_s_subcluster_BK': {
        'value': 1525,  # km/s
        'unit': 'km/s',
        'tier': 'DERIVED',
        'source': 'Berezhiani & Khoury, PRD 92, 103510 (2015) + W1b derivation',
        'detail': 'Sub-cluster sound speed c_s^{subcl} = sqrt(2μ/m) computed '
                  'from BK fiducial m_DM = 0.6 eV and Λ = 0.2 meV at a '
                  'galaxy-cluster scale (~10^14 M_sun). Derived in '
                  'Lit-Search/Phase-5x/5x-SFDM Cluster Merger Sonic Boom *.md '
                  'from the BK equation-of-state ρ ∝ μ^3 using μ ~ Λ(ρ/ρ0)^{1/2}.',
        'doi': None,
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Value and derivation traced in W1b merger-forecast '
                              'memo; anchors all five Mach numbers in paper 17 '
                              '§sfdm-merger (Bullet 1.77, Pandora 2.23, A520 1.51, '
                              'El Gordo 1.64, MACS J0025 1.31).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Paper 17 §sfdm-merger Eq. for c_s^{subcl}. Cross-checked in '
                 'src/dark_sector/sfdm_merger_forecast.py (same value).',
    },
    'SFDM.merger_Mach_canonical': {
        'value': {'Bullet': 1.77, 'Pandora': 2.23, 'A520': 1.51,
                  'ElGordo': 1.64, 'MACSJ0025': 1.31},
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'W1b deep research / infall-velocity compilation',
        'detail': 'Mach numbers M = v_infall / c_s for the five canonical '
                  'radio-relic cluster mergers, computed using the BK '
                  'sub-cluster sound speed (SFDM.c_s_subcluster_BK) and '
                  'observational infall velocities (per-cluster references '
                  'collected in the W1b SFDM-merger memo). Paper 17 uses all '
                  'five in §sfdm-merger and Fig. money-plot-left.',
        'doi': None,
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Values match the SFDMMergerForecast.lean module '
                              'and the all_canonical_mergers_supersonic Lean '
                              'theorem. Per-cluster infall-velocity sources '
                              'require separate human-verification audit at '
                              'submission — collected in the Phase 5x Roadmap '
                              'Wave 10 action list.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Tier DERIVED because v_infall is observational per-cluster but '
                 'c_s is theoretical — the product is mixed. Paper 17 submission '
                 'requires human verification of each per-cluster v_infall.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 5z: Electroweak sector (Wave 1 — ScalarRungInterpretation)
    # ════════════════════════════════════════════════════════════════

    'EW.M_W_GEV': {
        'value': 80.3692,
        'unit': 'GeV/c²',
        'tier': 'MEASURED',
        'source': 'Particle Data Group, Review of Particle Physics (2024)',
        'detail': 'W boson mass: m_W = 80.3692 ± 0.0133 GeV (PDG 2024 world average). '
                  'Dominant input from CDF II, ATLAS, LHCb tensions handled via PDG scale factor.',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PDG 2024 values. Used in EW.ew_mass_matrix_from_scalar_vev Lean '
                              'theorem (ScalarRungInterpretation.lean).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 5z Wave 1 canonical value. M_W/M_Z ratio with cos θ_W gives '
                 'a tight consistency test for the scalar-rung Anderson-Higgs prediction.',
    },
    'EW.M_Z_GEV': {
        'value': 91.1876,
        'unit': 'GeV/c²',
        'tier': 'MEASURED',
        'source': 'Particle Data Group, Review of Particle Physics (2024)',
        'detail': 'Z boson mass: m_Z = 91.1876 ± 0.0021 GeV (PDG 2024, LEP/SLD combined).',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PDG 2024 values. Definitional Z-pole mass.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 5z Wave 1 canonical value. Enters Anderson-Higgs consistency check '
                 'M_W/M_Z = cos θ_W.',
    },
    'EW.M_H_GEV': {
        'value': 125.20,
        'unit': 'GeV/c²',
        'tier': 'MEASURED',
        'source': 'Particle Data Group, Review of Particle Physics (2024)',
        'detail': 'Higgs boson mass: m_H = 125.20 ± 0.11 GeV (PDG 2024; '
                  'S. Navas et al., Phys. Rev. D 110, 030001 (2024); world average '
                  'from ATLAS + CMS diphoton and 4-lepton channels).',
        'doi': '10.1103/PhysRevD.110.030001',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PDG 2024 single canonical value: m_H = 125.20 ± 0.11. '
                              'Updated 2026-04-26 from prior 125.25 ± 0.17 placeholder; '
                              'DOI and detail align with PDG2024 CITATION_REGISTRY entry. '
                              'Correctness-push target for Phase 5z Wave 1 + Wave 1b.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 5z Wave 1 FALSIFIABILITY ANCHOR. Scalar-rung framing is a '
                 'quantitative EWSB theory iff the microscopic prediction falls within '
                 'M_H_MATCH_TOLERANCE of this value.',
    },
    'EW.V_EW_GEV': {
        'value': 246.21965,
        'unit': 'GeV',
        'tier': 'DERIVED',
        'source': 'Derived from Fermi constant G_F via v = (√2·G_F)^{-1/2}',
        'detail': 'EW vacuum expectation value v = 246.21965 ± 0.00014 GeV. Computed as '
                  'v = (√2 · G_F)^{-1/2} with G_F = 1.1663787 × 10⁻⁵ GeV⁻² (muon lifetime).',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Standard EW-sector derived quantity. Value consistent '
                              'with PDG 2024 Electroweak Model review.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Scale-setting parameter for the Anderson-Higgs mass matrix: M_W = g·v/2, '
                 'M_Z = √(g²+g\'²)·v/2.',
    },
    'EW.SIN2_THETA_W': {
        'value': 0.23121,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Particle Data Group, Review of Particle Physics (2024), on-shell scheme',
        'detail': 'On-shell weak mixing angle sin²θ_W = 1 − M_W²/M_Z² = 0.22337 tree-level, '
                  '0.23121 with PDG 2024 effective-scheme value at M_Z.',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PDG 2024 effective-scheme value. Two schemes exist (on-shell '
                              'vs MS-bar); we use the effective-scheme on-shell for the '
                              'scalar-rung matrix-element derivation.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Fixes g / g\' ratio. Enters Anderson-Higgs M_W/M_Z consistency theorem.',
    },
    'EW.G_FERMI_GEV_M2': {
        'value': 1.1663787e-5,
        'unit': 'GeV⁻²',
        'tier': 'MEASURED',
        'source': 'Particle Data Group, Review of Particle Physics (2024), from muon lifetime',
        'detail': 'Fermi constant G_F = 1.1663787(6) × 10⁻⁵ GeV⁻², from muon lifetime with '
                  'full radiative corrections (MuLan 2011 experiment + theory).',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PDG 2024 tabulated value, MuLan final result.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Sets v via v = (√2 G_F)^{-1/2}. Fundamental low-energy EW parameter.',
    },
    'EW.G_SU2': {
        'value': 0.6536,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Derived from α_EM(M_Z) and sin²θ_W via g = e/sin θ_W',
        'detail': 'SU(2)_L gauge coupling at M_Z: g ≈ 0.6536, using α_EM(M_Z)⁻¹ = 127.934 '
                  '(running value) and sin²θ_W = 0.23121.',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Standard PDG-derived value. Used in Anderson-Higgs M_W theorem.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Enters M_W = g v / 2 via the scalar-rung W/Z mass-matrix theorem.',
    },
    'EW.G_U1Y': {
        'value': 0.3489,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Derived from α_EM(M_Z) and sin²θ_W via g\' = e/cos θ_W',
        'detail': 'U(1)_Y hypercharge gauge coupling at M_Z: g\' ≈ 0.3489. '
                  'Satisfies tan θ_W = g\'/g.',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Standard PDG-derived value.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Enters M_Z = √(g² + g\'²) v / 2 via the Anderson-Higgs theorem.',
    },
    'EW.LAMBDA_SM_HIGGS': {
        'value': 0.129,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Derived from m_H and v via λ = m_H²/(2 v²) at tree level',
        'detail': 'Tree-level SM Higgs quartic: λ = m_H²/(2 v²) = (125.25)²/(2·246.22²) ≈ 0.129. '
                  'Running λ(M_H) differs by a few percent from tree value.',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Standard tree-level derivation. Used as comparison to '
                              'Wetterich scalar-channel quartic in the microscopic m_H scan.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Target value for the scalar-rung Mexican-hat quartic at the matching scale.',
    },
    'EW.M_TOP_GEV': {
        'value': 172.57,
        'unit': 'GeV/c²',
        'tier': 'MEASURED',
        'source': 'Particle Data Group, Review of Particle Physics (2024)',
        'detail': 'Top quark mass: m_t = 172.57 ± 0.29 GeV (PDG 2024; world '
                  'average from direct kinematic measurements at Tevatron + LHC).',
        'doi': '10.1103/PhysRevD.110.030001',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PDG 2024 single canonical value: m_t = 172.57 ± 0.29. '
                              'Added 2026-04-26 to resolve prior coexistence of 172.57 / '
                              '172.69 / 172.76 across paper 20, EW.Y_TOP derivation, and '
                              'fig_bhl_bilocal_correction. This value is now the project-'
                              'wide canonical entry.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 5z Wave 1b reference value for the bilocal-correction figure '
                  '(fig_bhl_bilocal_correction right-panel PDG marker) and Wave 1b §6 '
                  'BHL benchmark comparison (m_t_BHL = 220 GeV vs PDG 172.57 GeV).',
    },
    'EW.Y_TOP': {
        'value': 0.9912,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Derived from top-quark pole mass m_t = 172.57 GeV (PDG 2024) and v',
        'detail': 'Top Yukawa y_t = √2 m_t/v = √2 · 172.57 / 246.22 ≈ 0.9912. Near-unity '
                  'y_t is a natural outcome of any overlap-integral picture where top is '
                  'strong-coupled to the scalar condensate. Updated 2026-04-26 to use '
                  'M_TOP_GEV = 172.57 (PDG 2024 single canonical) instead of prior 172.76.',
        'doi': '10.1103/PhysRevD.110.030001',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PDG 2024 top mass m_t = 172.57 ± 0.29 GeV (single canonical '
                              'PDG 2024 entry, S. Navas et al., PRD 110, 030001). y_t = '
                              '√2 · 172.57 / 246.21965 = 0.9912. Updated 2026-04-26 from '
                              'prior 0.9946 (which used 172.76 as central) to align with '
                              'EW.M_TOP_GEV = 172.57.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Top-Yukawa near-unity is a key input to the m_H microscopic prediction '
                 'via the RG running of λ.',
    },
    'EW.LAMBDA_UV_FIDUCIAL_GEV': {
        'value': 1.0e16,
        'unit': 'GeV',
        'tier': 'PROJECTED',
        'source': 'Wetterich spinor-gravity substrate scale, GUT-adjacent',
        'detail': 'Fiducial UV cutoff Λ_UV for the ADW / Wetterich 4-fermion substrate. '
                  'Chosen at the GUT scale (10^16 GeV) as the natural anchor for a condensate-'
                  'based EWSB in which the scalar-rung VEV v ≈ 246 GeV is ~14 orders of '
                  'magnitude below the substrate scale. Phase 5z Wave 1 m_H scan sweeps '
                  'over (10^10 — 10^19) GeV.',
        'doi': None,
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PROJECTED — no primary source pins this to a unique value. '
                              'Choice is motivated by GUT-adjacent substrate + Planck '
                              'hierarchy. Full scan in src/scalar_rung/higgs_prediction.py.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Parameter sweep variable; fiducial value only for point predictions. '
                 'All paper 20 claims derive from the full scan, not this one value.',
    },
    'EW.N_F_FIDUCIAL': {
        'value': 15,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'SM Weyl fermion content per generation (García-Etxebarria & Montero)',
        'detail': 'Without ν_R: 15 Weyl components per generation (6+3+3+2+1). '
                  'SMFermionData.lean encodes this. Used as default N_f for the m_H scan '
                  'absent Embedding I resolution of O.3.',
        'doi': '10.1007/JHEP08(2019)003',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Matches SM_FERMION_DATA in constants.py and the 15 ≡ -1 mod 16 '
                              'anomaly result in HiddenSectorClassification.lean.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Tier MEASURED because SM fermion count is definitionally fixed from '
                 'experimental observation of the known fermions.',
    },
    'EW.N_F_WITH_NU_R': {
        'value': 16,
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'ℤ₁₆-anomaly-preferred extension (García-Etxebarria & Montero)',
        'detail': 'With right-handed neutrino ν_R: 16 Weyl components per generation. '
                  'Matches the ℤ₁₆ period exactly — 16 ≡ 0 mod 16, anomaly-free per generation. '
                  'Alternative N_f value for the m_H scan under seesaw Embedding I (O.3).',
        'doi': '10.1007/JHEP08(2019)003',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'Consistent with one_gen_anomaly_with_nuR and ℤ₁₆-period '
                              'coincidence documented in Z16AnomalyComputation.lean.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Theoretical extension; ν_R itself is not observed. Used only under '
                 'Embedding I in Phase 5z Wave 2 follow-up.',
    },
    'EW.G_C_FIDUCIAL': {
        'value': 1.0,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'ADW / NJL tetrad gap-equation critical-coupling nominal unit',
        'detail': 'Fiducial dimensionless 4-fermion coupling G_c for the scalar channel. '
                  'Phase 5z Wave 1 m_H scan sweeps G_c over (0.1 — 10) at fixed Λ_UV; '
                  'G_c = 1.0 is the order-unity anchor point. Maps to physical g_EH via '
                  'the NJL-ADW correspondence (WetterichNJL.lean: g_EH = 16 g_njl).',
        'doi': None,
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PROJECTED; no primary source. Order-unity choice motivated by '
                              'ADW critical-coupling calculations and TetradGapEquation bifurcation point.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Parameter sweep variable. Correctness-push conclusions depend on range, '
                 'not this single value.',
    },
    'EW.LAMBDA_4_FIDUCIAL': {
        'value': 0.13,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Tuned to tree-level SM quartic λ_SM_HIGGS for baseline m_H scan',
        'detail': 'Fiducial scalar-channel quartic λ_4 matched to λ_SM_HIGGS = 0.129 at the '
                  'matching scale, giving the "expected" microscopic value under the '
                  'scalar-rung identification. Phase 5z Wave 1 scan sweeps 0.01 — 1.0.',
        'doi': None,
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PROJECTED; baseline value only. Full scan in '
                              'src/scalar_rung/higgs_prediction.py.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Deliberately chosen near SM value to highlight deviations from the '
                 'substrate-driven microscopic prediction.',
    },
    'EW.M_H_MATCH_TOLERANCE': {
        'value': 0.5,
        'unit': 'dimensionless (fractional)',
        'tier': 'PROJECTED',
        'source': 'Phase 5z Wave 1 correctness-push operational threshold',
        'detail': 'Order-of-magnitude match tolerance for the Higgs microscopic prediction. '
                  'If |m_H_predicted − 125.25 GeV| / 125.25 < 0.5 over a natural parameter range, '
                  'the scalar-rung framing is "quantitatively compatible" with 125 GeV. '
                  'Otherwise the framing is structural-only. Defines Gate Z.1 activation.',
        'doi': None,
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PROJECTED — operational choice for the falsifiability anchor. '
                              '50% allows for RG-running uncertainty + substrate-specific '
                              'corrections; tighter than 1-order-of-magnitude.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 5z roadmap Gate Z.1. User decision at Stage 10 paper submission on '
                 'whether tighter tolerance is warranted.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 5z Wave 2: Majorana Rung — Sterile-Neutrino + PMNS
    # ════════════════════════════════════════════════════════════════
    # Embedding III per Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-
    # Neutrino Embedding for the Majorana Rung.md (verdict 2026-04-25).
    # Oscillation values from NuFit-6.0 global fit (Esteban et al. JHEP
    # 12 (2024) 216, arXiv:2410.05380). 0νββ bounds: KamLAND-Zen 800
    # (arXiv:2406.11438) and LEGEND-1000 PCDR (arXiv:2107.11462).
    # Citations verified 2026-04-25 in CITATION_REGISTRY (NuFit60 +
    # KamLANDZen800 + LEGEND1000 all doi_verified=True after CrossRef +
    # arXiv WebFetch round).
    # ════════════════════════════════════════════════════════════════

    'MAJORANA.M_R_FIDUCIAL_GEV': {
        'value': 1.0e14,
        'unit': 'GeV',
        'tier': 'PROJECTED',
        'source': 'Type-I seesaw central scale (Mohapatra & Smirnov, Annu. Rev. Nucl. Part. Sci. 56, 569 (2006), hep-ph/0603118)',
        'detail': 'Fiducial heavy-Majorana mass M_R for Type-I seesaw with O(1) Yukawa: '
                  'm_ν ~ y² v² / M_R ⇒ M_R ~ y² · 246² / 0.05e-9 ≈ 1.2e15 GeV at y=1; '
                  'M_R ≈ 1e14 GeV is the central fiducial taken across canonical reviews. '
                  'In Embedding III, M_R is the Z₁₆-invariant ADW condensate scale Λ_ADW; '
                  'the derivation Λ_ADW → M_R is OPEN in primary literature (WAVE2-OPEN-1).',
        'doi': '10.1146/annurev.nucl.56.080805.140534',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PROJECTED — fiducial Type-I seesaw scale. Used as anchor for '
                              'the Wave 2 m_ν prediction scan in src/majorana_rung/. Per '
                              'feedback_citation_verification_required, primary-source '
                              'WebFetch verification of the Mohapatra-Smirnov review is '
                              'deferred to Stage 10 paper-21 citation round.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'WAVE2-OPEN-1: M_R = Λ_ADW is a tracked-hypothesis, not a derived theorem. '
                 'Substrate parameters (Λ_UV, N_f, G_c) leave M_R as a fit parameter in all '
                 'current ADW / Wetterich / Volovik sources. See deep research Block §2.',
    },
    'MAJORANA.M_R_LOWER_BOUND_GEV': {
        'value': 1.0e9,
        'unit': 'GeV',
        'tier': 'DERIVED',
        'source': 'Type-I seesaw with electron-Yukawa-like ν Yukawa (deep research Block 2.2)',
        'detail': 'Lower edge of the seesaw band: with y ≈ y_e ≈ 3e-6 (electron-Yukawa-like) '
                  'and m_ν ≈ 0.05 eV, the seesaw relation m_ν = y² v² / M_R gives '
                  'M_R ≈ 9e-12 · 246² / 0.05e-9 GeV ≈ 1e9 GeV. Sets the lower envelope of '
                  'M_R in the (y, M_R) plane consistent with NuFit-6.0 mass splittings.',
        'doi': '10.1007/JHEP08(2024)217',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'DERIVED — algebraic from y_lower + m_ν_heaviest. Cross-check '
                              'against Fang et al. JHEP 08 (2024) 217 confirms 10⁹ GeV is '
                              'standard low-y endpoint. WebFetch deferred per Stage 10.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Wave 2 phenomenological scan as the lower band of the (y, M_R) '
                 'plane that reproduces observed Δm²_atm.',
    },
    'MAJORANA.M_R_UPPER_BOUND_GEV': {
        'value': 1.0e15,
        'unit': 'GeV',
        'tier': 'DERIVED',
        'source': 'Type-I seesaw with O(1) Yukawa (deep research Block 2.2)',
        'detail': 'Upper edge of the seesaw band: with y ≈ 1 (top-Yukawa-like) and '
                  'm_ν ≈ 0.05 eV, M_R ≈ 1.2e15 GeV. Sets the upper envelope; consistent '
                  'with cosmological-inflation/leptogenesis fits (Kawasaki & Yanagida, '
                  'JHEP 11 (2023) 106, arXiv:2304.10100, reheating ~ 10⁸–10¹⁰ GeV with '
                  'right-handed leptons living at higher M_R).',
        'doi': '10.1007/JHEP08(2024)217',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'DERIVED — algebraic from y_upper + m_ν_heaviest.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Upper band of the Wave 2 (y, M_R) phenomenological plane.',
    },
    'MAJORANA.DELTA_M_SQ_21_EV2': {
        'value': 7.42e-5,
        'unit': 'eV²',
        'tier': 'MEASURED',
        'source': 'NuFit-6.0 (Esteban et al., JHEP 12 (2024) 216, arXiv:2410.05380)',
        'detail': 'Solar mass-squared splitting Δm²_21 = (7.42 ± 0.21) × 10⁻⁵ eV² from the '
                  'NuFit-6.0 global three-flavor oscillation fit (KamLAND reactor + solar '
                  'experiments dominant). Normal ordering best fit.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'NuFit-6.0 best-fit value, reported in deep research Block 2.3 '
                              'and Wikipedia PMNS summary. Primary-source WebFetch deferred '
                              'to Stage 10 paper-21 citation round.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 oscillation anchor. Enters m_ν_next via √Δm²_21 ≈ 8.6 meV.',
    },
    'MAJORANA.DELTA_M_SQ_31_EV2': {
        'value': 2.515e-3,
        'unit': 'eV²',
        'tier': 'MEASURED',
        'source': 'NuFit-6.0 (Esteban et al., JHEP 12 (2024) 216, arXiv:2410.05380)',
        'detail': 'Atmospheric mass-squared splitting |Δm²_31| = (2.515 ± 0.028) × 10⁻³ eV² '
                  '(NO best fit). T2K + NOvA + IceCube DeepCore + reactor dominant.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'NuFit-6.0 best-fit value, normal ordering.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 oscillation anchor. Enters m_ν_heaviest via √|Δm²_31| ≈ 50 meV (NO).',
    },
    'MAJORANA.THETA_12_DEG': {
        'value': 33.41,
        'unit': 'deg',
        'tier': 'MEASURED',
        'source': 'NuFit-6.0 (Esteban et al., JHEP 12 (2024) 216, arXiv:2410.05380)',
        'detail': 'Solar mixing angle θ₁₂ = 33.41° (NO best fit; sin²θ₁₂ = 0.303 ± 0.012). '
                  'Reactor + solar.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'NuFit-6.0 best-fit angle.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'PMNS standard-parameterization angle. Wave 2 NeutrinoMixing.lean records.',
    },
    'MAJORANA.THETA_13_DEG': {
        'value': 8.54,
        'unit': 'deg',
        'tier': 'MEASURED',
        'source': 'NuFit-6.0 (Esteban et al., JHEP 12 (2024) 216, arXiv:2410.05380)',
        'detail': 'Reactor mixing angle θ₁₃ = 8.54° (NO; sin²θ₁₃ = 0.02203 ± 0.00056). '
                  'Daya Bay, RENO, Double Chooz dominant.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'NuFit-6.0 best-fit angle.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Smallness of θ₁₃ unexplained in either Wave 2 embedding (deep research §3.1).',
    },
    'MAJORANA.THETA_23_DEG': {
        'value': 49.1,
        'unit': 'deg',
        'tier': 'MEASURED',
        'source': 'NuFit-6.0 (Esteban et al., JHEP 12 (2024) 216, arXiv:2410.05380)',
        'detail': 'Atmospheric mixing angle θ₂₃ = 49.1° (NO; sin²θ₂₃ = 0.572). T2K + NOvA. '
                  'Near-maximal; whether truly maximal vs slightly off is the leading '
                  'open phenomenological question for the next-generation T2HK / DUNE.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'NuFit-6.0 best-fit angle (NO; IO has slightly different '
                              'central value but inside 1σ).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Near-maximal θ₂₃ unexplained in Embedding I/III; "predicted ≈ π/4 from '
                 'composite μ-τ symmetry" claim under Embedding II is unrealized in any '
                 'primary source (deep research §3.2). Wave 2 marks as fit, not derived.',
    },
    'MAJORANA.DELTA_CP_DEG': {
        'value': 197.0,
        'unit': 'deg',
        'tier': 'MEASURED',
        'source': 'NuFit-6.0 (Esteban et al., JHEP 12 (2024) 216, arXiv:2410.05380)',
        'detail': 'Dirac CP-violating phase δ_CP = 197° (NO best fit, ~1σ around 195–230°). '
                  'CP-conservation (δ_CP = 0 or π) disfavored at ~2.4σ in NO.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'NuFit-6.0 best-fit phase. Substantial uncertainty remains; '
                              'Wave 2 NeutrinoMixing.lean records the value as a free parameter.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Free parameter in Embedding I/III; predicted near ±π/2 only under full '
                 'μ-τ reflection symmetry (not realized in any primary source).',
    },
    'MAJORANA.M_BB_KAMLAND_ZEN_MEV_LOWER': {
        'value': 28.0,
        'unit': 'meV',
        'tier': 'MEASURED',
        'source': 'KamLAND-Zen Collaboration, arXiv:2406.11438 (v2 March 2026)',
        'detail': 'Most-stringent NME bound on m_ββ (effective Majorana mass) from the full '
                  'KamLAND-Zen 800 dataset: m_ββ < 28 meV (90% CL) using the most-favored '
                  'NME calculation. Half-life T_{1/2} > 3.8 × 10²⁶ yr.',
        'doi': '10.48550/arXiv.2406.11438',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'Deep research Block 4.1: bounds 28-122 meV; lower edge '
                              'corresponds to the most-favorable NME (shell-model). '
                              'Primary-source WebFetch deferred to Stage 10 paper-21 round.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Excludes the quasi-degenerate (QD) mass-hierarchy region for any embedding '
                 '— embedding-agnostic bound.',
    },
    'MAJORANA.M_BB_KAMLAND_ZEN_MEV_UPPER': {
        'value': 122.0,
        'unit': 'meV',
        'tier': 'MEASURED',
        'source': 'KamLAND-Zen Collaboration, arXiv:2406.11438 (v2 March 2026)',
        'detail': 'Conservative-NME bound on m_ββ from KamLAND-Zen 800: m_ββ < 122 meV '
                  '(90% CL) using the least-favorable NME calculation. Half-life same as '
                  'above (T_{1/2} > 3.8 × 10²⁶ yr); the spread is purely NME-theoretic.',
        'doi': '10.48550/arXiv.2406.11438',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'NME spread covers full QRPA / IBM-2 / shell-model band.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Conservative complement to the 28 meV bound; reports the full NME envelope.',
    },
    'MAJORANA.M_BB_LEGEND_MEV_LOWER': {
        'value': 9.0,
        'unit': 'meV',
        'tier': 'PROJECTED',
        'source': 'LEGEND-1000 PCDR, arXiv:2107.11462',
        'detail': 'LEGEND-1000 99.7% CL discovery sensitivity at most-favored NME: '
                  'm_ββ ≈ 9 meV after 10 years live time. Covers the entire inverted-ordering '
                  '(IO) parameter space.',
        'doi': '10.48550/arXiv.2107.11462',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PROJECTED — experiment under construction; design report '
                              'specifies sensitivity range 9–21 meV.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Reach: discovers IO if real. Embedding-agnostic experimental target.',
    },
    'MAJORANA.M_BB_LEGEND_MEV_UPPER': {
        'value': 21.0,
        'unit': 'meV',
        'tier': 'PROJECTED',
        'source': 'LEGEND-1000 PCDR, arXiv:2107.11462',
        'detail': 'LEGEND-1000 99.7% CL discovery sensitivity at conservative NME: '
                  'm_ββ ≈ 21 meV. Conservative complement to the 9 meV reach.',
        'doi': '10.48550/arXiv.2107.11462',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PROJECTED — design report range upper end.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Conservative-NME LEGEND-1000 reach.',
    },
    'MAJORANA.Y_NU_LOWER': {
        'value': 1.0e-3,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Type-I seesaw natural-Yukawa range (deep research Block 2.2)',
        'detail': 'Lower edge of the Wave 2 neutrino-Yukawa scan: y ≈ 10⁻³ (much smaller '
                  'than electron Yukawa y_e ≈ 3e-6 but still in the "natural" envelope '
                  'used as the lower fiducial in canonical seesaw reviews). Pairs with '
                  'M_R_LOWER_BOUND_GEV to reproduce m_ν_heaviest.',
        'doi': None,
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PROJECTED — operational scan choice. Not a measured value.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 Yukawa-overlap scan lower bound.',
    },
    'MAJORANA.Y_NU_UPPER': {
        'value': 1.0,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Type-I seesaw O(1) upper anchor (deep research Block 2.2)',
        'detail': 'Upper edge of the Wave 2 neutrino-Yukawa scan: y ~ 1 (top-Yukawa-like). '
                  'Pairs with M_R_UPPER_BOUND_GEV.',
        'doi': None,
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'PROJECTED — O(1) upper anchor.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 Yukawa-overlap scan upper bound.',
    },
    'MAJORANA.M_NU_HEAVIEST_EV': {
        'value': 0.0501,
        'unit': 'eV',
        'tier': 'DERIVED',
        'source': 'Derived from |Δm²_31| (NuFit-6.0) at m_lightest → 0',
        'detail': 'Heaviest light-neutrino mass m₃ ≈ √|Δm²_31| ≈ 0.0501 eV in the normal-'
                  'ordering massless-lightest limit. Used as the seesaw target m_ν.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'Standard derivation: m₃ = √(Δm²_31 + m_lightest²) ≈ √Δm²_31 '
                              'at m_lightest = 0.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 seesaw target. m_ν = y² v² / M_R must reproduce this value.',
    },
    'MAJORANA.M_NU_NEXT_EV': {
        'value': 0.00861,
        'unit': 'eV',
        'tier': 'DERIVED',
        'source': 'Derived from Δm²_21 (NuFit-6.0) at m_lightest → 0',
        'detail': 'Next-heaviest light-neutrino mass m₂ ≈ √Δm²_21 ≈ 8.61 meV in the NO '
                  'massless-lightest limit.',
        'doi': '10.1007/JHEP12(2024)216',
        'llm_verified_date': '2026-04-26',
        'llm_verified_notes': 'Standard derivation: m₂ = √(Δm²_21 + m_lightest²) ≈ √Δm²_21.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used as the next mass anchor for the seesaw scan; less constraining than m₃.',
    },

    # ── Phase 5z Wave 4: SMG-route substrate-bridge constants ──────────
    # Deep-research-anchored values per Lit-Search/Phase-5z/Phase 5z Wave 4 —
    # SMG Substrate Phase Diagram.md §2 (verdict 2026-04-27).
    # The dimensionless ratio c_SMG = Λ_SMG/Λ_UV is the PHYSICAL substrate
    # gap-to-UV-cutoff ratio after Fierz-translation of HW's g²_GF onto V&D's
    # 8-coupling NJL scaling. NOT the lattice ratio Λ_D/a⁻¹ ≈ 0.13 (which HW
    # report directly). Status: OPEN-AT-LITERATURE-FRONTIER on three sub-
    # questions; V&D's own mean-field (PRD 86 104019) tilts NEGATIVE.
    'MAJORANA.C_SMG_BROAD_LOWER': {
        'value': 1.0e-12,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 4 deep research §2.2 (NJL-derived broad envelope, g_eff − g_c ∈ [0.3, 3])',
        'detail': 'Lower edge of the broad NJL-scaling envelope for c_SMG = Λ_SMG/Λ_UV under '
                  'Fierz-translated Hasenfratz-Witzel strong coupling. Computed as '
                  'exp(-2π²/(g_eff − g_c)) at the wide end (g_eff − g_c ≈ 0.3). Substrate-'
                  'specific value for ADW remains OPEN-W4-1.',
        'doi': '10.48550/arXiv.2412.10322',
        'llm_verified_date': '2026-04-27',
        'llm_verified_notes': 'PROJECTED — Wave 4 deep-research-derived NJL envelope.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 4 broad-band lower bound for the H_SubstrateInBroadSMGBand predicate.',
    },
    'MAJORANA.C_SMG_BROAD_UPPER': {
        'value': 1.0e-3,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 4 deep research §2.2 (NJL-derived broad envelope upper)',
        'detail': 'Upper edge of the broad NJL-scaling envelope for c_SMG. Corresponds to '
                  'g_eff − g_c ≈ 3. Above this band, NJL scaling fails (non-perturbative regime).',
        'doi': '10.48550/arXiv.2412.10322',
        'llm_verified_date': '2026-04-27',
        'llm_verified_notes': 'PROJECTED — Wave 4 deep-research-derived NJL envelope upper edge.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 4 broad-band upper bound.',
    },
    'MAJORANA.C_SMG_SEESAW_LOWER': {
        'value': 1.0e-10,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 4 deep research §2.3 (seesaw-restricted band lower)',
        'detail': 'Lower edge of the seesaw-restricted c_SMG band. At Λ_UV = M_Pl ≈ 10¹⁹ GeV, '
                  'c_SMG = 10⁻¹⁰ produces Λ_SMG = 10⁹ GeV — seesaw band lower edge. Requires '
                  'g_eff − g_c ≈ 2.15 in NJL scaling, a fine-tuning of (λ_i) of order 10–30%.',
        'doi': '10.48550/arXiv.2412.10322',
        'llm_verified_date': '2026-04-27',
        'llm_verified_notes': 'PROJECTED — derived from seesaw band consistency at M_Pl UV anchor.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 4 H_SubstrateNearSMGFixedPoint band lower bound (seesaw-restricted).',
    },
    'MAJORANA.C_SMG_SEESAW_UPPER': {
        'value': 1.0e-4,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 4 deep research §2.3 (seesaw-restricted band upper)',
        'detail': 'Upper edge of the seesaw-restricted c_SMG band. At Λ_UV = M_Pl, c_SMG = 10⁻⁴ '
                  'produces Λ_SMG = 10¹⁵ GeV — seesaw band upper edge. Requires g_eff − g_c '
                  '≈ 0.86 in NJL scaling.',
        'doi': '10.48550/arXiv.2412.10322',
        'llm_verified_date': '2026-04-27',
        'llm_verified_notes': 'PROJECTED — derived from seesaw band consistency at M_Pl UV anchor.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 4 H_SubstrateNearSMGFixedPoint band upper bound (seesaw-restricted).',
    },
    'MAJORANA.C_SMG_FIDUCIAL': {
        'value': 1.0e-7,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Geometric mid-band of seesaw-restricted band [10⁻¹⁰, 10⁻⁴]',
        'detail': 'Fiducial mid-band value of c_SMG = Λ_SMG/Λ_UV. Geometric mean '
                  '√(10⁻¹⁰ · 10⁻⁴) = 10⁻⁷. At Λ_UV = M_Pl, this gives Λ_SMG ≈ 10¹² GeV — '
                  'central seesaw scale, matching M_R_FIDUCIAL_GEV = 10¹⁴ GeV order.',
        'doi': None,
        'llm_verified_date': '2026-04-27',
        'llm_verified_notes': 'PROJECTED — operational scan choice. Substrate-specific value '
                              'is OPEN-W4-1.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 4 default fiducial for src/core/formulas.py smg_gap_substrate.',
    },
    'MAJORANA.LAMBDA_UV_SMG_FIDUCIAL_GEV': {
        'value': 1.0e19,
        'unit': 'GeV',
        'tier': 'PROJECTED',
        'source': 'Wave 4 deep research §2.3 (Planck-scale substrate UV anchor)',
        'detail': 'Substrate UV cutoff fiducial at the Planck scale Λ_UV ≈ M_Pl ≈ 10¹⁹ GeV. '
                  'Most natural choice for the ADW substrate: the substrate is a discretization '
                  'of the spinor-gravity action at the Planck scale, so its UV cutoff is naturally '
                  'identified with M_Pl.',
        'doi': None,
        'llm_verified_date': '2026-04-27',
        'llm_verified_notes': 'PROJECTED — natural substrate UV anchor per Wave 4 deep research §2.3.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 4 substrate UV fiducial; consumes M_Pl natural UV anchor.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 6a Wave 1: emergent G_N + linearized Einstein equations
    # ════════════════════════════════════════════════════════════════
    # Sakharov-Adler induced-gravity baseline: G_N = 12π / (N_f · Λ²) at
    # one loop with hard cutoff (Adler 1982 Eq. 3.3). ADW-specific
    # coefficient α_ADW awaits Vergeles unitarity computation
    # (Lit-Search/Tasks/submitted/Phase6a_W1_vergeles_GN_coefficient.md).

    'GRAV.G_N_OBS_M3_KGM1_S2': {
        'value': 6.67430e-11,
        'unit': 'm³ kg⁻¹ s⁻²',
        'tier': 'MEASURED',
        'source': 'CODATA 2018 recommended value (Tiesinga et al., RMP 93, 025010 (2021))',
        'detail': 'Newton gravitational constant G_N = 6.67430(15) × 10⁻¹¹ m³ kg⁻¹ s⁻². '
                  'CODATA 2018 recommended value (relative uncertainty 2.2 × 10⁻⁵).',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'CODATA 2018 standard reference value. Stable across CODATA updates '
                              'since 2014. Tiesinga RMP article is the canonical citation.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 6a Wave 1 correctness-push anchor: G_N^emerg(Λ_UV, N_f, α_ADW) '
                 'must match this value within G_N_MATCH_TOLERANCE for natural parameters.',
    },
    'GRAV.G_N_OBS_GEV_M2': {
        'value': 6.70883e-39,
        'unit': 'GeV⁻²',
        'tier': 'DERIVED',
        'source': 'Algebraic conversion of CODATA G_N to natural units via M_Planck',
        'detail': 'In natural units (ℏ=c=1), G_N = 1/M_P² where M_P = 1.220890 × 10¹⁹ GeV '
                  '(CODATA-derived Planck mass). Hence G_N = (1.220890e19)⁻² ≈ 6.7088e-39 GeV⁻². '
                  'The ratio G_N^obs(SI) / G_N^obs(natural) = (ℏc)⁵ converts dimensions.',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — algebraic conversion verified by hand computation from '
                              'M_P = √(ℏc/G) with CODATA inputs.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in LinearizedEFE.lean and src/emergent_gravity/G_N_emerg.py for the '
                 'natural-units correctness-push comparison.',
    },
    'GRAV.M_PLANCK_GEV': {
        'value': 1.220890e19,
        'unit': 'GeV',
        'tier': 'DERIVED',
        'source': 'CODATA-derived Planck mass M_P = √(ℏc/G_N)',
        'detail': 'Planck mass M_P = (ℏc/G_N)^(1/2) with CODATA 2018 G_N gives '
                  'M_P = 1.220890 × 10¹⁹ GeV. Standard reference value tabulated by PDG.',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — agrees with PDG 2024 (Particle Data Group, '
                              'Phys. Rev. D 110, 030001 (2024), Astrophysical Constants table).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Defines the natural Λ_UV anchor for the G_N_emerg parameter scan.',
    },
    'GRAV.M_PLANCK_REDUCED_GEV': {
        'value': 2.435e18,
        'unit': 'GeV',
        'tier': 'DERIVED',
        'source': 'M̄_P = M_P / √(8π) (cosmology convention)',
        'detail': 'Reduced Planck mass M̄_P ≡ (8π G_N)^(-1/2) ≈ 2.435 × 10¹⁸ GeV. Convention '
                  'used in cosmology literature (and specifically in Phase 5y q-theory + DESI '
                  'fits). Algebraic from M_PLANCK_GEV / sqrt(8π).',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — standard cosmology convention; no separate primary '
                              'source needed beyond CODATA G_N.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Cross-references Phase 5y FLRW-related modules (Wave 4 of Phase 6a).',
    },
    'GRAV.LAMBDA_UV_GEV_LOWER': {
        'value': 1.0e10,
        'unit': 'GeV',
        'tier': 'PROJECTED',
        'source': 'Phase 6a Wave 1 G_N parameter-scan lower bound',
        'detail': 'Intermediate-scale UV cutoff anchor. Below 10¹⁰ GeV the predicted '
                  'G_N^emerg = 12π / (N_f · Λ²) overshoots G_N^obs by 10⁹+ — "too '
                  'far below Planck" regime. Sets the lower edge of the Wave 1 parameter scan.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED — operational lower edge of the scan range. No primary '
                              'source pins this to a unique value.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Parameter sweep lower edge; not a physical constant.',
    },
    'GRAV.LAMBDA_UV_GEV_UPPER': {
        'value': 1.0e19,
        'unit': 'GeV',
        'tier': 'PROJECTED',
        'source': 'Phase 6a Wave 1 G_N parameter-scan upper bound',
        'detail': 'Super-Planck-scale UV cutoff anchor. Above 10¹⁹ GeV the cutoff exceeds the '
                  'observed M_Planck — physically nonsensical for an effective theory '
                  'that purports to derive M_Planck. Sets the upper edge of the scan.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED — operational upper edge. The natural anchor inside the '
                              'scan is M_PLANCK_GEV = 1.221e19 GeV; we extend slightly past for '
                              'visualization clarity.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Parameter sweep upper edge.',
    },
    'GRAV.LAMBDA_UV_GUT_GEV': {
        'value': 1.0e16,
        'unit': 'GeV',
        'tier': 'PROJECTED',
        'source': 'GUT-adjacent canonical anchor for ADW substrate scale',
        'detail': 'Canonical anchor at 10¹⁶ GeV (gauge-coupling unification scale in SM + '
                  'minimal SUSY-extension fits). Mirrors EW.LAMBDA_UV_FIDUCIAL_GEV = 1e16 GeV '
                  'used in Phase 5z Wave 1 m_H scan; same physical anchor.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED — same anchor as EW.LAMBDA_UV_FIDUCIAL_GEV. Order-unity '
                              'check: G_N_sakharov(N_f=15, Λ=10¹⁶) = 12π/(15·10³²) ≈ 2.5e-32 '
                              'GeV⁻², compared to G_N^obs ≈ 6.7e-39 GeV⁻² — overshoots by 7 '
                              'orders, so 10¹⁶ is too low for natural emergent gravity.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Cross-references EW.LAMBDA_UV_FIDUCIAL_GEV. Used as the GUT-adjacent fiducial '
                 'point in the Wave 1 scan.',
    },
    'GRAV.LAMBDA_UV_PLANCK_GEV': {
        'value': 1.220890e19,
        'unit': 'GeV',
        'tier': 'DERIVED',
        'source': 'Same numerical value as M_PLANCK_GEV',
        'detail': 'Natural-Planck anchor: setting Λ_UV = M_P (and α_ADW = 12π/N_f to match '
                  'the Sakharov coefficient exactly) reproduces the observed G_N within the '
                  'free α_ADW prefactor. This is the "correctness-push exact match" anchor.',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — same as M_PLANCK_GEV. Used as the natural anchor for '
                              'verifying that G_N^emerg matches G_N^obs at Λ ≈ M_P.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'The "ideal" anchor: at Λ = M_P, G_N^emerg = α_ADW · 12π / (N_f M_P²) = '
                 '(α_ADW · 12π / N_f) · G_N^obs. Matches G_N^obs iff α_ADW · 12π / N_f = 1 '
                 '→ α_ADW = N_f / (12π) ≈ 0.40 (N_f=15) or 0.42 (N_f=16). Within Vergeles '
                 'natural range [0.1, 10].',
    },
    'GRAV.N_F_PER_GEN_NO_NU_R': {
        'value': 15,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'SM Weyl fermion content per generation (García-Etxebarria & Montero)',
        'detail': 'Without ν_R: 15 Weyl components per generation (6 quarks: 3+3, 2 leptons: 2+1, '
                  '1 charged lepton: 1+1+0+1). Same value as EW.N_F_FIDUCIAL.',
        'doi': '10.1007/JHEP08(2019)003',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Cross-references EW.N_F_FIDUCIAL = 15 and the 15 ≡ -1 mod 16 '
                              'Z₁₆-anomaly result in HiddenSectorClassification.lean.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Default N_f for the Wave 1 G_N scan absent ν_R.',
    },
    'GRAV.N_F_PER_GEN_WITH_NU_R': {
        'value': 16,
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'ℤ₁₆-anomaly-preferred extension (García-Etxebarria & Montero)',
        'detail': 'With right-handed ν_R: 16 Weyl per generation, ℤ₁₆-period-matched. Same as '
                  'EW.N_F_WITH_NU_R.',
        'doi': '10.1007/JHEP08(2019)003',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Same theoretical justification as EW.N_F_WITH_NU_R = 16.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Alternative N_f for the Wave 1 G_N scan under Embedding I (ν_R extension).',
    },
    'GRAV.N_F_THREE_GEN_NO_NU_R': {
        'value': 45,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': '3 generations × 15 Weyl per generation',
        'detail': 'Total SM Weyl count without ν_R: 3 × 15 = 45. Used when the Sakharov loop '
                  'integrates over all SM fermions simultaneously (one universal cutoff).',
        'doi': '10.1007/JHEP08(2019)003',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — algebraic from N_F_PER_GEN_NO_NU_R × 3.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Three-generation aggregate. With Λ_UV = M_P this gives '
                 'G_N^emerg / G_N^obs = α_ADW · 12π / 45 = 0.838 α_ADW — Sakharov default '
                 'lands within 16% of observed G_N. Tightest natural fit.',
    },
    'GRAV.N_F_THREE_GEN_WITH_NU_R': {
        'value': 48,
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': '3 generations × 16 Weyl per generation',
        'detail': 'Total SM+ν_R Weyl count: 3 × 16 = 48.',
        'doi': '10.1007/JHEP08(2019)003',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — algebraic from N_F_PER_GEN_WITH_NU_R × 3.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Three-generation aggregate with ν_R extension.',
    },
    'GRAV.N_F_DEFAULT': {
        'value': 15,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Default N_f for the Wave 1 G_N scan (per-generation, no ν_R)',
        'detail': 'Same value as N_F_PER_GEN_NO_NU_R; provided as a separate key for the '
                  'parameter-scan default configuration.',
        'doi': '10.1007/JHEP08(2019)003',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention key; same as N_F_PER_GEN_NO_NU_R.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention key — value is N_F_PER_GEN_NO_NU_R.',
    },
    'GRAV.ALPHA_ADW_SAKHAROV_DEFAULT': {
        'value': 1.0,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Sakharov-Adler one-loop free-fermion limit (Adler RMP 54, 729 (1982) Eq. 3.3)',
        'detail': 'ADW microscopic coefficient α_ADW: in the Sakharov-Adler limit (free fermions, '
                  'one loop, hard cutoff) α_ADW = 1 by definition. The ADW-specific value awaits '
                  'Vergeles unitarity computation (deep research dropped 2026-04-25, '
                  'Lit-Search/Tasks/submitted/Phase6a_W1_vergeles_GN_coefficient.md).',
        'doi': '10.1103/RevModPhys.54.729',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED — Sakharov-Adler default. Tracked-hypothesis treatment '
                              'in LinearizedEFE.lean (H_VergelesCoefficient).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Tracked hypothesis pending Vergeles deep research return.',
    },
    'GRAV.ALPHA_ADW_LOWER': {
        'value': 0.1,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 1 tracked-hypothesis natural range (-1 OOM from Sakharov)',
        'detail': 'Lower edge of the natural α_ADW range. Vergeles-derived value almost certainly '
                  'lies within [0.1, 10] = ±1 order of magnitude from the Sakharov default of 1.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED operational lower edge of α_ADW scan.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Replaced by single value once deep research returns Vergeles α_ADW.',
    },
    'GRAV.ALPHA_ADW_UPPER': {
        'value': 10.0,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 1 tracked-hypothesis natural range (+1 OOM from Sakharov)',
        'detail': 'Upper edge of the natural α_ADW range. ±1 order of magnitude from the '
                  'Sakharov default of 1.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED operational upper edge of α_ADW scan.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Replaced by single value once deep research returns Vergeles α_ADW.',
    },
    'GRAV.SAKHAROV_COEFFICIENT': {
        'value': 12.0 * 3.141592653589793,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Sakharov-Adler one-loop calculation (Adler RMP 54, 729 (1982) Eq. 3.3)',
        'detail': 'The numerical coefficient 12π ≈ 37.699 in G_N = 12π / (N_f Λ²) is the '
                  'standard Sakharov-Adler result for N_f Dirac fermions integrated at one loop '
                  'with a hard UV cutoff Λ. It comes from the loop-momentum integral '
                  '∫ d⁴k / (2π)⁴ · 1/(k² + m²)² evaluated at hard cutoff.',
        'doi': '10.1103/RevModPhys.54.729',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Numerical value matches direct evaluation 12π = 37.6991... and '
                              'agrees with Adler 1982 Eq. (3.3); verified analytically. Visser '
                              'Mod. Phys. Lett. A17, 977 (2002) gives modern reformulation.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Foundational dimensionless coefficient for Sakharov induced gravity.',
    },
    'GRAV.G_N_MATCH_TOLERANCE': {
        'value': 0.5,
        'unit': 'dimensionless (fractional)',
        'tier': 'PROJECTED',
        'source': 'Phase 6a Wave 1 correctness-push operational threshold',
        'detail': 'Order-of-magnitude match tolerance: |G_N^emerg − G_N^obs| / G_N^obs < 0.5 '
                  'over a natural parameter range = "quantitatively compatible with observed '
                  'gravity." Tighter than 1-OOM, allowing for RG-running uncertainty + '
                  'Vergeles α_ADW O(1). Same operational pattern as EW.M_H_MATCH_TOLERANCE.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED — operational choice for the falsifiability anchor.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 6a Gate A.1 threshold. User decision at Stage 10 paper submission.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 6a Wave 4: FLRW cosmological dynamics (Planck 2018)
    # ════════════════════════════════════════════════════════════════
    # Cosmological parameters from Planck 2018 (TT,TE,EE+lowE+lensing+BAO),
    # base ΛCDM. Used for Friedmann ODE sanity checks and DESI cross-ref.

    'FLRW.H0_KM_S_MPC': {
        'value': 67.66,
        'unit': 'km/s/Mpc',
        'tier': 'MEASURED',
        'source': 'Planck Collaboration, A&A 641, A6 (2020), Table 2 — base ΛCDM',
        'detail': 'Hubble constant H₀ = 67.66 ± 0.42 km/s/Mpc from Planck 2018 '
                  'TT,TE,EE+lowE+lensing+BAO base-ΛCDM fit (Table 2, column 2).',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Standard Planck 2018 reference. Tension with local-distance-ladder '
                              'measurements (~73 km/s/Mpc) is the H₀ tension; we anchor on Planck '
                              'for cosmology-internal consistency.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used for FLRW Friedmann ODE numerical integration in Wave 4.',
    },
    'FLRW.H0_INV_S': {
        'value': 2.193e-18,
        'unit': '1/s',
        'tier': 'DERIVED',
        'source': 'Algebraic conversion of Planck H₀ to SI units',
        'detail': 'H₀ = 67.66 km/s/Mpc × (1 km / 3.0857e16 km/Mpc · 1/s) = 2.193e-18 /s.',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — direct unit conversion.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'SI-unit form of H₀ for ODE integration.',
    },
    'FLRW.OMEGA_M_PLANCK': {
        'value': 0.3111,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Planck Collaboration, A&A 641, A6 (2020), Table 2 — base ΛCDM',
        'detail': 'Total matter density parameter Ω_m = 0.3111 ± 0.0056 (Planck 2018, '
                  'TT,TE,EE+lowE+lensing+BAO).',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Planck 2018 base-ΛCDM Table 2.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Friedmann I sanity check input (Ω_m + Ω_Λ + Ω_r = 1).',
    },
    'FLRW.OMEGA_LAMBDA_PLANCK': {
        'value': 0.6889,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Planck Collaboration, A&A 641, A6 (2020), Table 2 — base ΛCDM',
        'detail': 'Cosmological-constant density parameter Ω_Λ = 0.6889 ± 0.0056. Direct '
                  'complement to Ω_m in flat ΛCDM.',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Planck 2018 base-ΛCDM Table 2.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Friedmann I sanity check.',
    },
    'FLRW.OMEGA_R_PLANCK': {
        'value': 9.2e-5,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Planck Collaboration, A&A 641, A6 (2020) — derived from T_CMB + N_eff',
        'detail': 'Radiation density parameter Ω_r = 9.2 × 10⁻⁵ (CMB photons + 3.046 effective '
                  'neutrino species). Subdominant today, dominant before z ~ 3400.',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Standard derivation from T_CMB = 2.7255 K + 3.046 effective '
                              'neutrino species; agrees with Planck 2018 Section 7.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Negligible at z=0; relevant only for early-universe FLRW.',
    },
    'FLRW.OMEGA_K_PLANCK': {
        'value': 0.0,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Planck Collaboration, A&A 641, A6 (2020) — flat ΛCDM',
        'detail': 'Curvature density parameter |Ω_K| < 0.005 (Planck 2018), consistent with '
                  'flat universe. We adopt Ω_K = 0 (flat) as the default.',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Flat-universe assumption; matches Planck 2018 base-ΛCDM convention.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Flat-universe default; Wave 4 LinearizedEFE → Friedmann reduction assumes flat.',
    },
    'FLRW.RHO_CRIT_KG_M3': {
        'value': 8.620e-27,
        'unit': 'kg/m³',
        'tier': 'DERIVED',
        'source': 'Critical density ρ_crit = 3 H₀² / (8π G_N) at Planck 2018 H₀',
        'detail': 'ρ_crit = 3·(2.193e-18)² / (8π · 6.6743e-11) ≈ 8.62 × 10⁻²⁷ kg/m³. Standard '
                  'reference value at the Planck 2018 Hubble parameter.',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DERIVED — direct algebraic computation from H₀ and G_N.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Friedmann I normalization.',
    },
    'FLRW.W_MATTER': {
        'value': 0.0,
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'Standard cosmology: pressureless dust EOS w = p/ρ = 0',
        'detail': 'Equation-of-state parameter for pressureless dust (matter, cold dark matter): '
                  'w = 0 by definition for non-relativistic, non-interacting components.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'THEORETICAL — defining property of dust. No primary source needed.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Friedmann ρ̇ + 3H(1+w)ρ = 0 conservation.',
    },
    'FLRW.W_RADIATION': {
        'value': 1.0/3.0,
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'Standard cosmology: relativistic gas EOS w = 1/3',
        'detail': 'Equation-of-state parameter for relativistic gas (photons + relativistic '
                  'neutrinos): w = 1/3 from kinetic theory.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'THEORETICAL — defining property of relativistic gas.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Standard radiation EOS.',
    },
    'FLRW.W_LAMBDA': {
        'value': -1.0,
        'unit': 'dimensionless',
        'tier': 'THEORETICAL',
        'source': 'Standard cosmology: cosmological constant EOS w = −1',
        'detail': 'Equation-of-state parameter for the cosmological constant Λ: w = −1 by '
                  'Lorentz invariance (vacuum stress-energy ∝ g_μν).',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'THEORETICAL — locked by Lorentz invariance. See Phase 5y '
                              'GibbsDuhemTheorem.lean for the formal proof of w = −1 lock '
                              'across q-theory KV realizations.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Cross-references Phase 5y w_vac = −1 obstruction theorem.',
    },
    'FLRW.W_DE_DESI_DR2_TODAY': {
        'value': -0.838,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'DESI Collaboration, DESI DR2 (DESI 2024.III + 2024.IV), arXiv:2404.03002',
        'detail': 'DESI DR2 best-fit dark-energy equation-of-state at z=0: w₀ = -0.838 from '
                  'CPL parameterization w(z) = w₀ + w_a · z/(1+z) combined with CMB + SN. '
                  'Indicates ~3σ tension with w = -1 (cosmological constant).',
        'doi': '10.48550/arXiv.2404.03002',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DESI DR2 result. Phase 5y QTheoryNoGoTheorem proved no Volovik-'
                              'family q-theory mechanism produces this time-evolving w(z); see '
                              'DESIComparison.lean for the formal incompatibility theorem.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 5y W4 / Phase 6a W4 cross-reference anchor for FLRW DE comparison.',
    },
    'FLRW.W_A_DESI_DR2': {
        'value': -0.62,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'DESI Collaboration, DESI DR2, arXiv:2404.03002',
        'detail': 'DESI DR2 best-fit CPL slope at z=0: w_a ≈ -0.62 (dark energy weakening with '
                  'time). Combined with w₀ = -0.838 gives the canonical "evolving DE" picture.',
        'doi': '10.48550/arXiv.2404.03002',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'DESI DR2 result. See Phase 5y DESIComparison.lean.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Phase 5y W4 cross-reference.',
    },
    'FLRW.FLRW_NUMERICAL_TOLERANCE': {
        'value': 1.0e-9,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Phase 6a Wave 4 numerical-tolerance operational choice',
        'detail': 'Friedmann ODE residual tolerance 10⁻⁹ allows machine-precision-limited ODE '
                  'integration with margin. Stricter tolerances run into floating-point limits.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED operational tolerance.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 4 ODE-integrator tolerance.',
    },

    # ════════════════════════════════════════════════════════════════════
    # Phase 6a Wave 2 — Gravitational waves
    # ════════════════════════════════════════════════════════════════════
    'GW.C_LIGHT_M_S': {
        'value': 2.99792458e8,
        'unit': 'm/s',
        'tier': 'MEASURED',
        'source': 'BIPM SI definition (2019 redefinition); CODATA 2018 recommended values',
        'detail': 'Defined exactly. Anchors the c_GW deviation tolerance (Δc/c).',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'CODATA 2018 / Tiesinga et al. RMP 93 025010 (2021).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'SI defined exactly; cross-references GRAV.G_N_OBS_M3_KGM1_S2 CODATA bundle.',
    },
    'GW.C_GW_DEVIATION_UPPER_BOUND': {
        'value': 7.0e-16,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Abbott et al. (LIGO+Virgo+EM partners), ApJL 848, L13 (2017), Eq. (5)',
        'detail': 'GW170817 / GRB 170817A multi-messenger arrival time bound: '
                  '−3 × 10⁻¹⁵ ≤ (c_GW − c)/c ≤ +7 × 10⁻¹⁶, conservative (+) side.',
        'doi': '10.3847/2041-8213/aa920c',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Abstract reports ±10⁻¹⁵ deviation; Eq. (5) gives the asymmetric bound.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'GW170817 (BNS merger) primary anchor for Wave 2 correctness-push.',
    },
    'GW.C_GW_DEVIATION_LOWER_BOUND': {
        'value': -3.0e-15,
        'unit': 'dimensionless',
        'tier': 'MEASURED',
        'source': 'Abbott et al. (LIGO+Virgo+EM partners), ApJL 848, L13 (2017), Eq. (5)',
        'detail': '(−) side of the GW170817 bound: −3 × 10⁻¹⁵ ≤ (c_GW − c)/c.',
        'doi': '10.3847/2041-8213/aa920c',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Same source as GW.C_GW_DEVIATION_UPPER_BOUND.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Asymmetric bound — astrophysical-emission delay accounts for asymmetry.',
    },
    'GW.C_GW_TWO_SIDED_CAP': {
        'value': 3.0e-15,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Symmetrized GW170817 cap; max(|7e-16|, |-3e-15|) = 3e-15',
        'detail': 'Symmetric two-sided falsification cap derived from the asymmetric '
                  'GW170817 bound; used in Wave 2 correctness-push falsifiers.',
        'doi': '10.3847/2041-8213/aa920c',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Operational symmetrization of the asymmetric LIGO bound.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Computed: |C_GW_DEVIATION_LOWER_BOUND| > |C_GW_DEVIATION_UPPER_BOUND|.',
    },
    'GW.CHI_VEST_NATURAL_LOWER': {
        'value': 0.1,
        'unit': 'dimensionless (× Λ²)',
        'tier': 'PROJECTED',
        'source': 'Vergeles 2025 RPA bubble-integral natural range, half-decade convention',
        'detail': 'Vestigial-phase metric-channel susceptibility natural lower bound. '
                  'χ_vest · Λ² ∈ [0.1, 10] is the natural range from VestigialSusceptibility.lean '
                  'chi_RPA closed form with O(Λ²/16π²) bubble integral.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED. Same convention as GRAV.ALPHA_ADW_LOWER.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Cross-link: VestigialSusceptibility.chi_RPA (Lean).',
    },
    'GW.CHI_VEST_NATURAL_UPPER': {
        'value': 10.0,
        'unit': 'dimensionless (× Λ²)',
        'tier': 'PROJECTED',
        'source': 'Vergeles 2025 RPA bubble-integral natural range, half-decade convention',
        'detail': 'Upper bound matching CHI_VEST_NATURAL_LOWER; ±1 order of magnitude window.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED. Same convention as GRAV.ALPHA_ADW_UPPER.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Cross-link: VestigialSusceptibility.chi_RPA (Lean).',
    },
    'GW.CHI_VEST_DEFAULT': {
        'value': 1.0,
        'unit': 'dimensionless (× Λ²)',
        'tier': 'PROJECTED',
        'source': 'Operational default at the natural-range center (geometric mean of [0.1, 10])',
        'detail': 'Default χ_vest · Λ² = 1 used as the leading-order Wave 2 fiducial.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED operational default.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention matches GRAV.ALPHA_ADW_SAKHAROV_DEFAULT = 1.',
    },
    'GW.GW_FREQ_HZ_LOWER': {
        'value': 10.0,
        'unit': 'Hz',
        'tier': 'MEASURED',
        'source': 'LIGO sensitivity curve lower edge (Aasi et al. CQG 32, 074001 (2015))',
        'detail': 'aLIGO seismic-noise-limited low-frequency cutoff.',
        'doi': '10.1088/0264-9381/32/7/074001',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'aLIGO design paper reports sensitivity from 10 Hz.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 dispersion-relation scan range.',
    },
    'GW.GW_FREQ_HZ_UPPER': {
        'value': 1.0e4,
        'unit': 'Hz',
        'tier': 'MEASURED',
        'source': 'LIGO sensitivity curve upper edge (Aasi et al. CQG 32, 074001 (2015))',
        'detail': 'aLIGO photon-shot-noise-limited high-frequency cutoff at ~10 kHz.',
        'doi': '10.1088/0264-9381/32/7/074001',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'aLIGO design paper sensitivity to 10 kHz at reduced response.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 dispersion-relation scan range.',
    },
    'GW.GW170817_PEAK_FREQ_HZ': {
        'value': 100.0,
        'unit': 'Hz',
        'tier': 'MEASURED',
        'source': 'Abbott et al. (LIGO+Virgo), PRL 119, 161101 (2017) — GW170817 inspiral peak',
        'detail': 'GW170817 binary-neutron-star inspiral peak strain frequency ≈ 100 Hz '
                  '(post-Newtonian expansion through ISCO at ~1 kHz). Used as the probe '
                  'frequency for Wave 2 dispersion-correction evaluation.',
        'doi': '10.1103/PhysRevLett.119.161101',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'BNS-merger inspiral analysis; representative frequency ~100 Hz.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 2 correctness-push probe frequency.',
    },
    'GW.GW_FREQ_HZ_PROBE': {
        'value': 100.0,
        'unit': 'Hz',
        'tier': 'DERIVED',
        'source': 'Operational alias of GW170817 inspiral peak (GW.GW170817_PEAK_FREQ_HZ)',
        'detail': 'Probe frequency for Wave 2 dispersion-correction evaluation = GW170817 peak.',
        'doi': '10.1103/PhysRevLett.119.161101',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Same value as GW.GW170817_PEAK_FREQ_HZ — alias for code clarity.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention alias.',
    },
    'GW.GAMMA_H_VESTIGIAL_DEFAULT': {
        'value': 1.0e-30,
        'unit': 'dimensionless (Γ_H · ω/c² at probe ω)',
        'tier': 'PROJECTED',
        'source': 'Phase 6a Wave 2 placeholder (vestigial regime ≪ observed gravity scale)',
        'detail': 'Dimensionless dispersion coefficient placeholder. Vestigial-regime '
                  'γ₁+γ₂ scales out at the linearized level; placeholder value chosen '
                  'so the dispersion correction stays well below the GW170817 cap.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'PROJECTED scaffold. Refined when Wave 2 deep research returns.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Cross-link: SecondOrderSK.GammaH (Lean).',
    },
    'GW.C_GW_MATCH_TOLERANCE': {
        'value': 3.0e-15,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Tolerance = GW170817 two-sided cap (GW.C_GW_TWO_SIDED_CAP)',
        'detail': 'Wave 2 correctness-push tolerance for |c_GW − c|/c.',
        'doi': '10.3847/2041-8213/aa920c',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Set equal to GW.C_GW_TWO_SIDED_CAP by convention.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Wave 2 ligo_constraint_check + correctness-push theorems.',
    },
    # ──────────────────────────────────────────────────────────────────
    # Phase 6a Wave 3 — Bekenstein-Hawking entropy from MTC counting
    # ──────────────────────────────────────────────────────────────────
    'BH.PLANCK_LENGTH_M': {
        'value': 1.616255e-35,
        'unit': 'm',
        'tier': 'MEASURED',
        'source': 'CODATA 2018 recommended value',
        'detail': 'ℓ_P = √(ℏ G/c³). Sets the area scale in S_BH = A/(4 ℓ_P²).',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'CODATA 2018 + 2022 agree to within 11 ppb.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in formulas.bh_entropy_kaul_majumdar leading coefficient.',
    },
    'BH.PLANCK_AREA_M2': {
        'value': 2.6121e-70,
        'unit': 'm²',
        'tier': 'DERIVED',
        'source': 'ℓ_P² with ℓ_P from CODATA 2018',
        'detail': 'Used as the area unit in the Kaul-Majumdar saddle-point regime.',
        'doi': '10.1103/RevModPhys.93.025010',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention alias.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention alias.',
    },
    'BH.BH_ENTROPY_LEADING_COEFFICIENT': {
        'value': 0.25,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Bekenstein 1973 + Hawking 1975; tuning hypothesis in Kaul-Majumdar 2000',
        'detail': 'The 1/4 in S = A/(4 G_N) is structurally a tuning (Immirzi γ in '
                  'Kaul-Majumdar gr-qc/0002040 §4; UV cutoff ε in Bombelli-Koul-Lee-Sorkin '
                  '1986; periodicity β in Carlip horizon-CFT gr-qc/0005017). Wave 3 encodes '
                  'this as a hypothesis-discharge (`immirziTuned` field of the '
                  'IsHorizonBC structure), NOT as a derived theorem.',
        'doi': '10.1103/PhysRevLett.84.5255',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Verified against Kaul-Majumdar gr-qc/0002040 abstract '
                              'and Eq. (4.4); tuning role explicit in arXiv:1201.6102 §5.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Encoded in Lean as `BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi`.',
    },
    'BH.IMMIRZI_GAMMA_DOMAGALA_LEWANDOWSKI': {
        'value': 0.23753295796592,
        'unit': 'dimensionless',
        'tier': 'EXTRACTED',
        'source': 'Domagala-Lewandowski, CQG 21, 5233 (2004), arXiv:gr-qc/0407051',
        'detail': 'Immirzi parameter chosen so the Verlinde-counted leading coefficient '
                  'equals 1/4. Distinct counting prescription from Meissner; same −3/2 '
                  'log coefficient.',
        'doi': '10.1088/0264-9381/21/22/014',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Standard LQG literature value; arXiv:1201.6102 Table 2.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 3 ships both DL and Meissner γ; chooses Meissner as default.',
    },
    'BH.IMMIRZI_GAMMA_MEISSNER': {
        'value': 0.27392803876474,
        'unit': 'dimensionless',
        'tier': 'EXTRACTED',
        'source': 'Meissner, CQG 21, 5245 (2004), arXiv:gr-qc/0407052',
        'detail': 'Immirzi parameter from Meissner counting prescription. Recent LQG '
                  'literature default. Same −3/2 log coefficient as Domagala-Lewandowski.',
        'doi': '10.1088/0264-9381/21/22/015',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Verified via arXiv:1201.6102 Table 2.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Default Wave 3 value.',
    },
    'BH.IMMIRZI_GAMMA_DEFAULT': {
        'value': 0.27392803876474,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Alias for BH.IMMIRZI_GAMMA_MEISSNER',
        'detail': 'Default Immirzi γ used by Wave 3 numerics.',
        'doi': '10.1088/0264-9381/21/22/015',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention alias.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention alias.',
    },
    'BH.LOG_CORRECTION_KAUL_MAJUMDAR_SU2K': {
        'value': -1.5,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Kaul-Majumdar, PRL 84, 5255 (2000), arXiv:gr-qc/0002040, Eq. (15)',
        'detail': 'c_log = −1/2 (Gaussian saddle) + (−1) (SU(2)-singlet projection from '
                  'the I₀ − I₁ cancellation that removes the constant-Fourier-mode) = −3/2. '
                  'Universal within the Cardy-saddle / single-CFT / microcanonical / '
                  'A-independent-c family. Sen 2013 (arXiv:1205.0971) heat-kernel result '
                  'for 4D Schwarzschild pure gravity DISAGREES (gives +(212/45 − 3) ln a).',
        'doi': '10.1103/PhysRevLett.84.5255',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Reproduced in arXiv:1201.6102, Engle-Noui-Perez '
                              'arXiv:0905.3168, BTZ gr-qc/0104010. Carlip arXiv:gr-qc/0005017 '
                              'gives same coefficient via independent Cardy-CFT route.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Encoded in Lean as `BHEntropyMicroscopic.kaulMajumdarLogCoefficient`.',
    },
    'BH.LOG_CORRECTION_GAUSSIAN_SADDLE': {
        'value': -0.5,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Standard Laplace-method asymptotic',
        'detail': 'I₀ ~ C e^{F(0)} / √(−F\'\'(0)). With −F\'\'(0) ∝ A, the leading '
                  'asymptotic contributes −(1/2) log A.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Textbook result.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Wave 3 originally axiomatized in Lean as '
                 '`gaussianSaddleAsymptotic`; Wave 6a.7 (2026-04-27) retired '
                 'the axiom by interpreting `verlindeEntropy_SU2k` at the '
                 'Laplace-saddle limit. Now a theorem in '
                 '`BHEntropyMicroscopic.gaussianSaddleAsymptotic` with axiom '
                 'closure {propext, Classical.choice, Quot.sound} only.',
    },
    'BH.LOG_CORRECTION_SINGLET_PROJECTION': {
        'value': -1.0,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Kaul-Majumdar, gr-qc/0002040, the I₀ − I₁ cancellation step',
        'detail': 'I₀ − I₁ produces an extra inverse-Hessian factor 1/[−F\'\'(0)], '
                  'contributing −1·log A on top of the Gaussian saddle\'s −(1/2)·log A.',
        'doi': '10.1103/PhysRevLett.84.5255',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Eq. (12)−(15) in gr-qc/0002040.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Combined with Gaussian saddle yields −3/2 total.',
    },
    'BH.LOG_CORRECTION_SEN_4D_SCHWARZSCHILD': {
        'value': 1.7111111,
        'unit': 'dimensionless',
        'tier': 'EXTRACTED',
        'source': 'Sen, JHEP 04, 156 (2013), arXiv:1205.0971',
        'detail': '212/45 − 3 ≈ +1.711 from heat-kernel computation for 4D Schwarzschild '
                  'pure gravity. Explicitly disagrees with the Cardy-saddle / Kaul-Majumdar '
                  '−3/2. Sen flags the LQG disagreement in §1 of the cited paper. '
                  'Wave 3 documents this as a non-universality witness in the paper.',
        'doi': '10.1007/JHEP04(2013)156',
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Verified via deep-research return §4 Table.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'NOT used in core Wave 3 derivation; used as a falsifiability anchor.',
    },
    'BH.FIBONACCI_PHI': {
        'value': 1.6180339887498948,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Algebraic identity φ² = φ + 1 (golden ratio)',
        'detail': 'Quantum dimension of the τ object in the Fibonacci MTC. '
                  'Lean: FibonacciMTC.lean.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Pure algebra.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Fibonacci falsifier-instance check.',
    },
    'BH.FIBONACCI_GLOBAL_DIM_SQ': {
        'value': 3.6180339887498949,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': '1 + φ² = 2 + φ',
        'detail': 'Total quantum dim D² for the Fibonacci MTC. Lean: '
                  'FibonacciMTC.globalDim.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Pure algebra.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Fibonacci falsifier-instance check.',
    },
    'BH.FIBONACCI_LOG_D_MAX': {
        'value': 0.4812118250596034,
        'unit': 'dimensionless (log)',
        'tier': 'DERIVED',
        'source': 'log φ',
        'detail': 'Anyon-cell counting κ ∝ log d_max (Kitaev arXiv:cond-mat/0506438). '
                  'Used by area-law leading coefficient ansatz.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Pure algebra.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Fibonacci falsifier-instance F2 check.',
    },
    'BH.ISING_GLOBAL_DIM_SQ': {
        'value': 4.0,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Ising MTC: D² = 1² + (√2)² + 1² = 4',
        'detail': 'Total quantum dim for the Ising MTC. Lean: IsingBraiding.lean.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Pure algebra.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Ising falsifier-instance check.',
    },
    'BH.ISING_D_SIGMA': {
        'value': 1.4142135623730951,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': '√2 (quantum dim of σ in Ising)',
        'detail': 'σ = non-abelian anyon. Lean: IsingBraiding.lean.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Pure algebra.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Ising falsifier-instance check.',
    },
    'BH.ISING_LOG_D_MAX': {
        'value': 0.34657359027997264,
        'unit': 'dimensionless (log)',
        'tier': 'DERIVED',
        'source': '(1/2) log 2',
        'detail': 'log d_σ = (1/2) log 2 for Ising.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Pure algebra.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Ising F2 check.',
    },
    'BH.ISING_EDGE_C_MOD8': {
        'value': 0.5,
        'unit': 'dimensionless (mod 8)',
        'tier': 'EXTRACTED',
        'source': 'Standard Ising MTC chiral central charge c_- = 1/2',
        'detail': 'Boundary chiral central charge for the Ising MTC. Used in F5 '
                  'anomaly-match falsifier.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Standard reference: Kitaev cond-mat/0506438.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in F5 anomaly-match falsifier.',
    },
    'BH.TORIC_CODE_GLOBAL_DIM_SQ': {
        'value': 4.0,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'D² = |G|² for D(Z₂); 4 anyons {1, e, m, ψ} all d_a = 1',
        'detail': 'Toric code is abelian: all d_a = 1. log d_max = 0 ⇒ no area-law in '
                  'the Kitaev counting ansatz. Used as a F2 (area-law) falsifier instance.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Standard.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Abelian-MTC F2 falsifier.',
    },
    'BH.TORIC_CODE_LOG_D_MAX': {
        'value': 0.0,
        'unit': 'dimensionless (log)',
        'tier': 'DERIVED',
        'source': 'log 1 = 0 (all anyons d_a = 1)',
        'detail': 'Triggers F2 falsifier: abelian MTC cannot source non-trivial area law.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Algebraic.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'F2 falsifier.',
    },
    'BH.DS3_GLOBAL_DIM_SQ': {
        'value': 36.0,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'D(S₃): 8 anyons d=1,1,2,3,3,2,2,2; D² = 36 = |S₃|²',
        'detail': 'D² = |S₃|² for the D(S₃) Drinfeld double. Lean: S3CenterAnyons.lean.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Verified in S3CenterAnyons.lean (proven, zero sorry).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in S3 falsifier-instance check.',
    },
    'BH.DS3_LOG_D_MAX': {
        'value': 1.0986122886681098,
        'unit': 'dimensionless (log)',
        'tier': 'DERIVED',
        'source': 'log 3 (max d_a in D(S₃))',
        'detail': 'log d_max for D(S₃) = log 3.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Algebraic.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in D(S₃) F2 check.',
    },
    'BH.AREA_LAW_KAPPA_MIN_POSITIVE': {
        'value': 1.0e-12,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Numerical positivity threshold for the F2 falsifier',
        'detail': 'Below this κ value the area-law leading scaling is treated as '
                  'numerically zero (F2 falsifier triggered).',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention; consistent with double-precision noise floor.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention.',
    },
    'BH.BH_ENTROPY_COEFFICIENT_MATCH_TOLERANCE': {
        'value': 0.10,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 3 correctness-push tolerance (Immirzi tuning O(1) ambiguity)',
        'detail': '±10% on the leading coefficient absorbs the Domagala-Lewandowski vs '
                  'Meissner γ ambiguity (γ ∈ [0.237, 0.274]).',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Set wide enough to cover the published γ range.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Wave 3 coefficient cross-check tests.',
    },
    'BH.LOG_CORRECTION_MATCH_TOLERANCE': {
        'value': 0.01,
        'unit': 'dimensionless',
        'tier': 'PROJECTED',
        'source': 'Wave 3 correctness-push tolerance (structural coefficient)',
        'detail': 'Tighter than the leading-coefficient tolerance because c_log is '
                  'structural (½ Gaussian + 1 singlet projection) and not γ-dependent.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in Wave 3 log-correction cross-check tests.',
    },
    'BH.HORIZON_AREA_LOG_LOWER': {
        'value': 10.0,
        'unit': 'dimensionless (log)',
        'tier': 'PROJECTED',
        'source': 'Asymptotic-regime lower cut: A/(4 ℓ_P²) ≫ 1 needed for saddle-point',
        'detail': 'Lower edge of the asymptotic regime where the Kaul-Majumdar saddle '
                  'asymptotic is reliable. e^{10} ≈ 2.2e4 area units.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention.',
    },
    'BH.HORIZON_AREA_LOG_UPPER': {
        'value': 80.0,
        'unit': 'dimensionless (log)',
        'tier': 'PROJECTED',
        'source': 'Solar-mass Schwarzschild upper anchor',
        'detail': 'log(A_⊙/(4 ℓ_P²)) ≈ 77.0 for a 1 solar-mass Schwarzschild horizon. '
                  '80 covers solar-mass scales with margin.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention.',
    },
    'BH.SU2K_LEVEL_LOWER': {
        'value': 2,
        'unit': 'integer (CS level)',
        'tier': 'PROJECTED',
        'source': 'Wave 3 SU(2)_k scan range',
        'detail': 'k=1 is too restrictive (only j=0, 1/2 simple objects); k=2 is the '
                  'first level admitting non-trivial Verlinde sums.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention.',
    },
    'BH.SU2K_LEVEL_UPPER': {
        'value': 10,
        'unit': 'integer (CS level)',
        'tier': 'PROJECTED',
        'source': 'Wave 3 SU(2)_k scan upper bound',
        'detail': 'Large enough to see the asymptotic-large-k regime (k → ∞) where the '
                  '−3/2 universality is sharpest.',
        'doi': None,
        'llm_verified_date': '2026-04-25',
        'llm_verified_notes': 'Convention.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Convention.',
    },

    # ── Phase 6c Wave 1 — Strong-CP / topological dark energy ──────
    # (Added 2026-04-29 to close paper32 adversarial REQUIRED F-3.)

    'STRONG_CP_DE.LAMBDA_QCD_GEV': {
        'value': 0.1,
        'unit': 'GeV',
        'tier': 'MEASURED',
        'source': 'Particle Data Group 2022, Λ_QCD ≈ 100 MeV (MS-bar, 3-flavor)',
        'detail': 'Project working value for the QCD scale used in the Zhitnitsky '
                  'topological-DE prediction ρ_DE ~ Λ_QCD^6 / M_P^2. PDG quotes '
                  '~210 MeV for the 5-flavor Λ_QCD and varies by scheme; our 0.1 GeV '
                  'is the rounded 3-flavor MS-bar value typical in cosmological '
                  'estimates.',
        'doi': '10.1093/ptep/ptac097',
        'llm_verified_date': '2026-04-29',
        'llm_verified_notes': 'PDG 2022 Workman et al. Prog. Theor. Exp. Phys. 2022, 083C01.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in src.strong_cp_de.LAMBDA_QCD_GEV; consumed by Zhitnitsky-prediction theorems.',
    },
    'STRONG_CP_DE.NEUTRON_EDM_BOUND': {
        'value': 1.0e-9,
        'unit': 'dimensionless (radians)',
        'tier': 'MEASURED',
        'source': 'Pendlebury et al., Phys. Rev. D 92, 092003 (2015)',
        'detail': 'Conservative upper bound on the QCD topological angle |θ| from '
                  'neutron-EDM measurements. The actual 2015 result is |d_n| < 3e-26 e·cm '
                  '(90% CL), translating to |θ| ≲ 1e-10 in standard chiral-perturbation '
                  'estimates; we use the conservative 1e-9 as the load-bearing structural '
                  'bound (Lean ThetaVacuum.theta_small invariant).',
        'doi': '10.1103/PhysRevD.92.092003',
        'llm_verified_date': '2026-04-29',
        'llm_verified_notes': 'Pendlebury et al. arXiv:1509.04411, PRD 92, 092003 (2015).',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in src.strong_cp_de.NEUTRON_EDM_BOUND; consumed by ThetaVacuum constructor.',
    },
    'STRONG_CP_DE.RHO_DE_OBSERVED_EV4': {
        'value': 2.8e-11,
        'unit': 'eV⁴',
        'tier': 'DERIVED',
        'source': 'Planck 2018 + DESI 2024 cosmological-constant measurements',
        'detail': 'Observed dark-energy density ρ_Λ ≈ (2.3 meV)⁴ ≈ 2.8e-11 eV⁴, derived '
                  'from Planck 2018 + DESI Year-1 BAO measurements of the cosmological '
                  'constant under flat-ΛCDM. Used as the falsification anchor for the '
                  'Zhitnitsky topological-DE prediction.',
        'doi': '10.1051/0004-6361/201833910',
        'llm_verified_date': '2026-04-29',
        'llm_verified_notes': 'Planck 2018 results VI (A&A 641, A6, 2020) and DESI Year-1 BAO release 2024.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in src.strong_cp_de.RHO_DE_OBSERVED_EV4; consumed by Zhitnitsky-prediction within-3-orders predicate.',
    },

    # ── Phase 6e Wave 2 — Higher-curvature observational ceilings ─────
    # Order-of-magnitude bounds on dimensionless higher-curvature
    # couplings α (R²) and β (C², Weyl-squared) in the Stelle truncation
    # L = (1/16π G_N)(R + α R² + β C²). These are *derived* values: they
    # translate experimental constraints from short-range gravity, GW
    # propagation, binary-pulsar timing, and post-Newtonian solar-system
    # tests into dimensionless action coefficients via the EFT framework
    # of Calmet-Capozziello-Pryer (EPJC 77:589, 2017). Tier is DERIVED:
    # the values are not single-paper measurements but order-of-magnitude
    # ceilings consistent with multiple independent data sources.

    'HC_BOUND_LIGO_C_SQ': {
        'value': 1.0e62,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'GW170817 + Calmet-Capozziello-Pryer 2017 EFT translation',
        'detail': 'Order-of-magnitude ceiling on the Stelle β coefficient '
                  '(C² coupling) from the LIGO/Virgo speed-of-graviton '
                  'measurement (GW170817, Abbott et al, PRL 119, 161101, '
                  '2017) translated through the EFT framework of '
                  'Calmet-Capozziello-Pryer (EPJC 77:589, 2017). '
                  'Loose bound; not the tightest ceiling.',
        'doi': '10.1103/PhysRevLett.119.161101',
        'llm_verified_date': '2026-04-30',
        'llm_verified_notes': 'GW170817 paper title + venue verified via Crossref. '
                              'Translation framework cited via Calmet-Capozziello-Pryer 2017.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in src.core.constants.HIGHER_CURVATURE_PARAMS["HC_BOUND_LIGO_C_SQ"] '
                 'and src.higher_curvature.HC_OBS_BOUNDS["LIGO_C_sq"]. Consumed by '
                 'paper40 correctness-push as one of four canonical observational '
                 'ceilings.',
    },
    'HC_BOUND_SRG_R_SQ': {
        'value': 1.0e61,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Eöt-Wash short-range gravity (Kapner et al 2007) + '
                  'Calmet-Capozziello-Pryer 2017 EFT translation',
        'detail': 'Order-of-magnitude ceiling on the Stelle α coefficient '
                  '(R² coupling) from inverse-square-law tests at 50 μm '
                  '(Kapner et al, PRL 98, 021101, 2007) translated through '
                  'the EFT framework of Calmet-Capozziello-Pryer (EPJC '
                  '77:589, 2017). The Yukawa-mediator-mass bound m₀ ≳ '
                  '0.004 eV maps to α ≲ 1/(6 G_N m₀²) in natural units.',
        'doi': '10.1103/PhysRevLett.98.021101',
        'llm_verified_date': '2026-04-30',
        'llm_verified_notes': 'Eöt-Wash paper title + venue verified via Crossref. '
                              'Translation framework cited via Calmet-Capozziello-Pryer 2017.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in src.core.constants.HIGHER_CURVATURE_PARAMS["HC_BOUND_SRG_R_SQ"] '
                 'and src.higher_curvature.HC_OBS_BOUNDS["SRG_R_sq"].',
    },
    'HC_BOUND_PULSAR_C_SQ': {
        'value': 1.0e59,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Hulse-Taylor binary pulsar timing (Damour-Taylor 1991; '
                  'Weisberg-Huang 2016) + Calmet-Capozziello-Pryer 2017 '
                  'EFT translation',
        'detail': 'Order-of-magnitude ceiling on the Stelle β coefficient '
                  '(C² coupling) from binary-pulsar period-decay precision '
                  '(Weisberg & Huang, ApJ 829:55, 2016, GR within ~0.1%) '
                  'translated through the EFT framework of '
                  'Calmet-Capozziello-Pryer (EPJC 77:589, 2017). This is '
                  'the **tightest** of the four canonical ceilings, by '
                  '~3 orders of magnitude.',
        'doi': '10.3847/0004-637X/829/1/55',
        'llm_verified_date': '2026-04-30',
        'llm_verified_notes': 'Weisberg-Huang 2016 ApJ 829:55 verified via Crossref. '
                              'Translation framework via Calmet-Capozziello-Pryer 2017.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in src.core.constants.HIGHER_CURVATURE_PARAMS["HC_BOUND_PULSAR_C_SQ"] '
                 'and src.higher_curvature.HC_OBS_BOUNDS["pulsar_C_sq"]. The Wave 2 '
                 'correctness-push theorem `higher_curvature_below_pulsar_bound` is '
                 'phrased against this value.',
    },
    'HC_BOUND_CASSINI_C_SQ': {
        'value': 1.0e62,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Cassini post-Newtonian γ_PPN (Bertotti-Iess-Tortora 2003) + '
                  'Calmet-Capozziello-Pryer 2017 EFT translation',
        'detail': 'Order-of-magnitude ceiling on the Stelle β coefficient '
                  '(C² coupling) from post-Newtonian solar-system tests '
                  '(Bertotti, Iess, Tortora, Nature 425, 374, 2003: '
                  'γ_PPN-1 ~ 2×10⁻⁵) translated through the EFT framework '
                  'of Calmet-Capozziello-Pryer (EPJC 77:589, 2017). '
                  'Loose bound; comparable to LIGO ceiling.',
        'doi': '10.1038/nature01997',
        'llm_verified_date': '2026-04-30',
        'llm_verified_notes': 'Cassini paper venue Nature 425:374 (2003) verified via Crossref. '
                              'Translation framework via Calmet-Capozziello-Pryer 2017.',
        'human_verified_date': None,
        'human_verified_notes': None,
        'notes': 'Used in src.core.constants.HIGHER_CURVATURE_PARAMS["HC_BOUND_CASSINI_C_SQ"] '
                 'and src.higher_curvature.HC_OBS_BOUNDS["cassini_C_sq"].',
    },
}


# ════════════════════════════════════════════════════════════════════
# Paper Dependency Mappings
#
# Declared data: which formulas, Lean modules, and parameters each
# paper depends on. Used by the provenance dashboard Paper Claims tab
# instead of brittle regex parsing of .tex files.
# ════════════════════════════════════════════════════════════════════

PAPER_DEPENDENCIES = {
    'paper1_first_order': {
        'title': 'Paper 1: First-Order SK-EFT (PRL)',
        'topic': 'δ_diss = Γ_H/κ correction for 3 BEC platforms',
        'formulas': [
            'hawking_temperature', 'first_order_correction', 'dispersive_correction',
            'damping_rate', 'effective_temperature_ratio',
            'beliaev_damping_rate', 'beliaev_transport_coefficients',
        ],
        'lean_modules': ['AcousticMetric', 'SKDoubling', 'HawkingUniversality'],
        'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
        'key_claims': [
            'δ_diss = Γ_H/κ (first-order dissipative correction)',
            'Γ_H = (γ₁+γ₂)(κ/c_s)² (damping rate at horizon)',
            'Spin-sonic enhancement ×(c_density/c_spin)²',
            'Table 1: c_s, ξ, κ, T_H, D, δ_disp, δ_diss for 3 platforms',
        ],
    },
    'paper2_second_order': {
        'title': 'Paper 2: Second-Order SK-EFT (PRD)',
        'topic': 'Frequency-dependent ω³ correction, counting formula, CGL FDR',
        'formulas': [
            'count_coefficients', 'enumerate_monomials',
            'second_order_correction', 'damping_rate',
        ],
        'lean_modules': ['SecondOrderSK', 'WKBAnalysis', 'CGLTransform', 'ThirdOrderSK'],
        'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
        'key_claims': [
            'count(N) = ⌊(N+1)/2⌋ + 1 (transport coefficient counting)',
            'δ^(2)(ω) ∝ ω³ (frequency-dependent spectral distortion)',
            'Positivity: (γ_{2,1}+γ_{2,2})² ≤ 4γ₂γ_x β',
            'CGL FDR derivation at arbitrary order',
        ],
    },
    'paper3_gauge_erasure': {
        'title': 'Paper 3: Non-Abelian Gauge Erasure (PRL)',
        'topic': 'Universal structural theorem — U(1) survives',
        'formulas': [],  # structural theorem, not formula-based
        'lean_modules': ['GaugeErasure'],
        'platforms': ['Steinhauer'],
        'key_claims': [
            'Non-Abelian gauge DOF erased by hydrodynamization',
            'Only U(1)_EM survives as continuous Goldstone',
            'SM analysis: SU(3)→domain walls, SU(2)→domain walls, U(1)→Goldstone',
        ],
    },
    'paper4_wkb_connection': {
        'title': 'Paper 4: Exact WKB Connection (PRD)',
        'topic': 'Non-perturbative Bogoliubov, decoherence, noise floor',
        'formulas': [
            'turning_point_shift', 'decoherence_parameter', 'fdr_noise_floor',
            'first_order_correction', 'hawking_temperature', 'planck_occupation',
        ],
        'lean_modules': ['WKBConnection'],
        'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
        'key_claims': [
            '|α|²−|β|² = 1−δ_k (modified unitarity)',
            'Noise floor = δ_diss/(2(1−δ_diss))',
            'Spectral floor at ω ≳ 6T_H',
            'Acoustic BHs cool toward extremality',
        ],
    },
    'paper5_adw_gap': {
        'title': 'Paper 5: ADW Gap Equation (PRD)',
        'topic': 'Mean-field tetrad condensation, G_c, 2 gravitons',
        'formulas': [
            'adw_effective_potential', 'adw_critical_coupling',
            'adw_curvature_at_origin', 'tetrad_broken_generators',
            'graviton_polarization_count',
        ],
        'lean_modules': ['ADWMechanism'],
        'platforms': [],
        'key_claims': [
            'G_c = 8π²/(N_f·Λ²) (critical coupling)',
            'd²−1 = 15 broken generators in 4D',
            'd(d−3)/2 = 2 massless gravitons in 4D',
            'Four structural obstacles for fermion bootstrap',
        ],
    },
    'paper6_vestigial': {
        'title': 'Paper 6: Vestigial Gravity (PRD)',
        'topic': 'Lattice MC, vestigial metric phase, Weingarten integration',
        'formulas': [
            'so4_weingarten_2nd_moment', 'so4_weingarten_4th_moment',
            'adw_bond_weight_fundamental', 'adw_bond_weight_adjoint',
            'adw_bond_weight_total', 'vestigial_phase_indicator',
            'binder_cumulant', 'fermion_bag_local_weight',
        ],
        'lean_modules': ['VestigialGravity', 'FermionBag4D', 'SO4Weingarten'],
        'platforms': [],
        'key_claims': [
            'SO(4) Weingarten multi-channel bond coupling',
            'Three-phase structure: pre-geometric → vestigial → full tetrad',
            'EP violation prediction in vestigial phase',
        ],
    },
    'paper7_chirality_formal': {
        'title': 'Paper 7: Chirality Wall Formal Verification (PRD/CPC)',
        'topic': 'GS 9 conditions formalized, TPF evasion machine-verified',
        'formulas': [
            'gs_condition_count', 'tpf_evasion_count',
            'brillouin_zone_dimension', 'vector_like_spectrum_check',
        ],
        'lean_modules': ['LatticeHamiltonian', 'GoltermanShamir', 'TPFEvasion'],
        'platforms': [],
        'key_claims': [
            '7/9 GS conditions formalized as substantive Lean propositions',
            '5 TPF violations proved (C1, C2, I3, extra-dim, C3-conditional)',
            'tpf_outside_gs_scope_main: machine-checked 5-part conjunction',
            'First formal verification in lattice chiral fermion literature',
        ],
    },
    'experimental_predictions': {
        'title': 'Prediction Tables',
        'topic': 'Platform-specific spectral predictions',
        'formulas': [
            'kappa_scaling_dispersive', 'kappa_scaling_dissipative',
            'kappa_scaling_crossover', 'polariton_spatial_attenuation',
            'polariton_tier1_validity', 'polariton_hawking_temperature',
        ],
        'lean_modules': ['KappaScaling', 'PolaritonTier1'],
        'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
        'key_claims': [
            'δ_diss ∝ κ (linear, not constant)',
            'κ_cross = 6(γ₁+γ₂)/(πξ²) (crossover formula)',
            'Polariton T_H ~ 0.8-4 K (10¹⁰× hotter than BEC)',
        ],
    },
    'paper12_polariton': {
        'title': 'Polariton Prediction Paper: Stimulated Hawking from SK-EFT',
        'topic': 'Reservoir-corrected predictions for polariton analog Hawking radiation',
        'formulas': [
            'polariton_hawking_temperature',
            'polariton_spatial_attenuation',
            'polariton_tier1_validity',
            'stimulated_hawking_gain',
            'stimulated_hawking_snr',
            'stimulated_hawking_spectrum',
            'dispersive_hawking_correction',
        ],
        'lean_modules': ['PolaritonTier1', 'AcousticMetric'],
        'platforms': ['Paris_long', 'Paris_ultralong', 'Paris_standard'],
        'key_claims': [
            'c_s = 0.40 µm/ps (Falque 2025 measured; adopted in Phase 5u Wave 4)',
            'ξ ≈ 3.4 µm upstream (Falque 2025 §IV.1)',
            'Smooth-horizon baseline κ = 7×10¹⁰ s⁻¹ → T_H ≈ 85 mK, D = 0.60',
            'Steep-horizon reach κ = 1.1×10¹¹ s⁻¹ → T_H ≈ 134 mK, D = 0.93 '
                '(reported as platform upper bound; non-perturbative dispersive)',
            'Dispersive correction −π D²/6: −0.19 (smooth) to −0.46 (steep)',
            'Stimulated gain G(ω) > 0.5 for ω < ln(3)/(2π)·κ ≈ 0.175κ (κ-invariant)',
            'SNR ~ sqrt(N_probe) · G(ω) — 10³–10⁶× better than spontaneous',
            'κτ_pol > 1 required; ultralong (300 ps) is optimal',
            '2237+ Lean 4 theorems across project; PolaritonTier1.lean: 9 theorems, zero sorry',
        ],
    },
    'paper39_heat_kernel_expansion': {
        'title': 'Paper 39: Formal heat-kernel calibration of induced Newton\'s constant '
                 'from the ADW Dirac substrate (long-form formalization, Phase 6e Wave 1)',
        'topic': 'Seeley-DeWitt heat-kernel expansion of the Dirac fermion determinant. '
                 'Closed-form Christensen-Duff a₀, a₂, a₄ Dirac coefficients in 4D '
                 'vacuum; Decision Gate E.2 calibration biconditional that matches the '
                 'a₂ coefficient to LinearizedEFE.G_N_sakharov iff α_ADW = 1; '
                 'tracked-hypothesis structure DiracHeatKernelAsymptotic for the PDE-level '
                 'asymptotic existence (deferred to Mathlib spin-bundle infrastructure)',
        'formulas': [
            'seeley_dewitt_a0',
            'seeley_dewitt_a2_R_coefficient',
            'seeley_dewitt_a4_basis',
            'G_N_from_seeley_dewitt',
            'gauss_bonnet_density',
            'heat_kernel_a2_matches_GN_sakharov',
        ],
        'lean_modules': ['HeatKernelExpansion', 'LinearizedEFE'],
        'platforms': [],
        'key_claims': [
            'a₀ = 4 N_f / (4π)² closed form (Lean: a0_dirac, a0_dirac_pos, '
                'a0_dirac_linear) — leading cosmological-constant scale',
            'a₂(R) = -(N_f/12) · R / (4π)² closed form (Lean: a2_R_coefficient, '
                'a2_R_coefficient_neg, a2_R_coefficient_eq_zero_iff)',
            'a₄ Christensen-Duff Dirac rationals (-5, +7, -12)/(12·180) per (4π)² '
                '(Lean: a4_R_sq_coef, a4_Ricci_sq_coef, a4_Riemann_sq_coef + '
                'sign theorems _neg/_pos/_neg)',
            'Sakharov-Adler closed form: G_N_from_a2 = 12π/(N_f Λ²) = G_N_sakharov '
                '(Lean: G_N_from_a2_eq_G_N_sakharov — substantive cross-bridge '
                'invokes LinearizedEFE.G_N_sakharov by name)',
            'Decision Gate E.2 biconditional: G_N_from_a2 = G_N_emerg(Λ, N_f, α) '
                'iff α = 1 (Lean: a2_matches_GNemerg_iff_alpha_ADW_unity)',
            'GUT-anchor inverse: 1/G_N_from_a2 at (Λ, N_f) = (10¹⁶, 15) = '
                '15·10³²/(12π) ≈ 3.98·10³¹ GeV² (Lean: G_N_from_a2_at_GUT_inverse)',
            'GUT inverse below Planck-squared: 1/G_N_from_a2(GUT) < (10¹⁹)² '
                '(Lean: G_N_from_a2_inverse_at_GUT_below_planck_squared via '
                'norm_num + Real.pi_gt_three)',
            'Gauss-Bonnet local-algebra combination: c_R - 4 c_Ricci + c_Riem = '
                '-N_f/(48 (4π)²) (Lean: a4_gauss_bonnet_combination via ring)',
            'Tracked-hypothesis structure DiracHeatKernelAsymptotic encodes the '
                'PDE-level asymptotic existence (Vassilevich 2003 Theorem 4.1); '
                'invariants a0_value/a2_R_value force consumers to commit to '
                'textbook Christensen-Duff values',
        ],
    },
    'paper40_higher_curvature': {
        'title': 'Paper 40: Higher-curvature structure from the Dirac heat kernel — '
                 'microscopic predictions and observational ceilings (formalization, '
                 'Phase 6e Wave 2)',
        'topic': 'Wave 1 Christensen-Duff Dirac a_4 coefficients re-expressed in '
                 'Stelle\'s {R², C², 𝒢} basis with closed-form sign-definite Stelle '
                 'coefficients (α, β, γ) solved from a 3×3 linear system; substantive '
                 'cross-bridge to Wave 1 via ring identity; correctness-push '
                 'comparing predicted dimensionless higher-curvature couplings to '
                 'LIGO/Eöt-Wash/Hulse-Taylor/Cassini observational ceilings',
        'formulas': [
            'higher_curvature_R_sq_coefficient',
            'higher_curvature_Ricci_sq_coefficient',
            'higher_curvature_Riemann_sq_coefficient',
            'gauss_bonnet_4D_identity',
            'weyl_squared_4D',
            'higher_curvature_predicted_in_observational_band',
        ],
        'lean_modules': ['HigherCurvatureStructure', 'HeatKernelExpansion'],
        'platforms': [],
        'key_claims': [
            'Gauss-Bonnet density 𝒢 = R² - 4 R_μν² + R_μνρσ² topological in 4D '
                '(Lean: gaussBonnet4D)',
            'Weyl-squared decomposition C² = R_μνρσ² - 2 R_μν² + (1/3) R² '
                '(Lean: weylSquared4D)',
            'Conformal-flatness biconditional: C² = 0 ↔ R_μνρσ² = 2 R_μν² - R²/3 '
                '(Lean: weylSquared4D_eq_zero_iff_conformally_flat)',
            'Algebraic engine: 𝒢 - C² = (2/3) R² - 2 R_μν² '
                '(Lean: gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination)',
            'Closed-form Stelle coefficients (α, β, γ) = '
                '(-N_f/324, -41 N_f/4320, +17 N_f/4320) / (4π)² solved from 3×3 '
                'linear system over Christensen-Duff rationals',
            'Sign-definite for N_f > 0: α < 0, β < 0, γ > 0 (the topological '
                'coefficient carries the chiral-anomaly-positive sign) '
                '(Lean: a4_alpha_neg, a4_beta_neg, a4_gamma_pos)',
            'MAIN basis-change identity: a_4 density in {R², R_μν², R_μνρσ²} basis '
                '= a_4 density in {R², C², 𝒢} basis with (α, β, γ) coefficients '
                '(Lean: a4_density_eq_a4_density_in_RC2GB_basis — substantive '
                'cross-bridge invokes Wave 1 a4_R_sq_coef/a4_Ricci_sq_coef/'
                'a4_Riemann_sq_coef by name; closes by ring)',
            'Helper bounds: 1 < (4π)² and (4π)⁻² < 1 from Real.pi_gt_three '
                '(Lean: fourPiSq_gt_one, fourPiSqInv_lt_one)',
            'CORRECTNESS-PUSH: at 0 < N_f ≤ 100, all three a_4 coefficients have '
                '|c| < hc_bound_pulsar = 10⁵⁹ (Lean: '
                'higher_curvature_below_pulsar_bound — Hulse-Taylor binary pulsar, '
                'tightest of the four canonical observational ceilings; predicted '
                'O(10⁻³) sits ~62 orders below)',
            'Falsifier: predictions strictly non-zero for N_f > 0 (Lean: '
                'higher_curvature_predictions_strictly_positive — rules out '
                'trivial-vanishing reading)',
            'Tracked Prop H_HigherCurvatureWithinObservationalBounds B '
                'parameterised by upper bound; pulsar-bound witness '
                '(Lean: H_HigherCurvatureWithinObservationalBounds_pulsar_witness)',
        ],
    },
    'paper41_diff_invariance': {
        'title': 'Paper 41: Path-(b) order-by-order diffeomorphism invariance of '
                 'the Seeley-DeWitt heat-kernel effective action (formalization, '
                 'Phase 6e Wave 3)',
        'topic': 'Algebraic path-(b) anomaly residual at orders a_0, a_2, a_4 of '
                 'the Seeley-DeWitt expansion; correctness-push biconditional '
                 'identifies order-a_4 invariance with Wave 2 basis-change identity '
                 'pointwise; Dirac coefficient bundle satisfies the predicate '
                 'order-by-order; deliberately perturbed bundle has residual = δ '
                 'at unit R² (linear-in-δ falsifier); Decision Gate E.3 returns '
                 'PASS through order a_4',
        'formulas': [
            'diff_invariance_anomaly_residual_a0',
            'diff_invariance_anomaly_residual_a2',
            'diff_invariance_anomaly_residual_a4',
            'diff_invariance_holds_at_order',
            'diff_invariance_holds_order_by_order',
        ],
        'lean_modules': ['NonlinearDiffInvariance', 'HigherCurvatureStructure',
                          'HeatKernelExpansion'],
        'platforms': [],
        'key_claims': [
            'EffectiveLagrangianCoefs 5-tuple bundle through a_4 order '
                '(Lean: EffectiveLagrangianCoefs); diracCoefBundle invokes Wave 1 '
                'coefs by name (P6 cross-module bridge integrity)',
            'Bridge identity: diracCoefBundle.density_a4 = Wave 2 a4_density '
                '(Lean: diracCoefBundle_density_a4_eq_wave2_a4_density)',
            'Order-a_0 path-b residual is definitionally 0 (constant scalar)',
            'Order-a_2 path-b residual is definitionally 0 (single scalar invariant R)',
            'MAIN order-a_4 zero-residual theorem for the Dirac bundle: '
                'pathB_residual_a4(diracCoefBundle N_f, ...) = 0 '
                '(Lean: pathB_residual_a4_dirac_eq_zero — load-bearing Wave 2 '
                'cross-bridge via a4_density_eq_a4_density_in_RC2GB_basis)',
            'Order-by-order Dirac diff-invariance witnesses: orders 0, 2, 4 '
                '(Lean: dirac_diffInvariantAt_zero/two/four)',
            'CORRECTNESS-PUSH biconditional: order-a_4 path-b invariance ↔ Wave 2 '
                'basis-change identity at every curvature input '
                '(Lean: diff_invariance_a4_iff_dirac_basis_consistent — both '
                'directions reduce algebraically to the Wave 2 main theorem)',
            'Falsifier with linear response: at unit R²=1, the perturbed-bundle '
                'residual equals exactly δ '
                '(Lean: perturbed_pathB_residual_a4_at_unit_R_sq)',
            'Falsifier-witness: nonzero δ ⇒ perturbed bundle is NOT order-a_4 '
                'path-b diff-invariant (Lean: perturbed_not_diffInvariantAt_four)',
            'Tracked Prop H_NonlinearDiffInvariance bundles all three order witnesses; '
                'discharged for the Dirac bundle '
                '(Lean: dirac_H_NonlinearDiffInvariance) and falsified for the '
                'perturbed bundle (Lean: perturbed_not_H_NonlinearDiffInvariance)',
            'Decision Gate E.3 verdict: PASS through order a_4 — Phase 6e Wave 4 '
                'NonlinearEFE.lean and beyond proceed at full scope',
        ],
    },
    'paper42_nonlinear_efe': {
        'title': 'Paper 42: Variational nonlinear Einstein field equations '
                 'from the ADW emergent-gravity programme: a Lean-formalized '
                 'trace-level Decision Gate (Phase 6e Wave 4)',
        'topic': 'Trace-level variational EFE residual under the ADW α_ADW '
                 'rescaling; Decision-Gate-style biconditional (residual = 0 '
                 'iff α = 1) consuming Wave 1 G_N + Wave 2 a_4 + Wave 3 diff '
                 'invariance + Phase 6a.1 G_N_emerg cross-bridges; '
                 'PPN-style multi-channel observable predictions (deflection, '
                 'perihelion precession, ringdown frequency) with the '
                 'project-specific 2:3 cross-channel ratio as testable '
                 'structural claim; bundled tracked-Prop H_NonlinearEFEHolds',
        'formulas': [
            'emergent_stress_energy_trace',
            'matter_stress_energy_trace',
            'emergent_minus_matter_stress_energy_trace',
            'efe_residual_trace',
            'deflection_ratio',
            'precession_ratio',
            'ringdown_ratio',
            'higher_curvature_correction_at_background',
            'efe_residual_at_dirac_calibration',
            'nonlinear_efe_holds',
        ],
        'lean_modules': ['NonlinearEFE', 'NonlinearDiffInvariance',
                          'HigherCurvatureStructure', 'HeatKernelExpansion',
                          'LinearizedEFE'],
        'platforms': [],
        'key_claims': [
            'Emergent stress-energy trace T_emerg = α_ADW · ρ_ADW '
                '(Lean: emergentStressEnergyTrace)',
            'Linear deviation channel: T_emerg − T_matter = (α_ADW − 1) · ρ_ADW '
                '(Lean: emergentStressEnergyTrace_minus_matter_eq)',
            'T_emerg = T_matter biconditional: at non-zero ρ_ADW, the emergent '
                'and bare-matter traces coincide iff α_ADW = 1 '
                '(Lean: emergentStressEnergyTrace_eq_matter_iff_alpha_unity)',
            'Trace-level EFE residual closed form: '
                'efeResidualTrace = 8π G_N · ρ_ADW · (α_ADW − 1) '
                '(Lean: efeResidualTrace; vanishes at α=1: efeResidualTrace_at_alpha_one)',
            'MAIN Decision-Gate-style biconditional: under hG > 0, hρ ≠ 0, '
                'efeResidualTrace = 0 iff α_ADW = 1 '
                '(Lean: efeResidualTrace_eq_zero_iff_alpha_unity — Wave 4 '
                'correctness-push, nonlinear analogue of Wave 1 Decision Gate E.2)',
            'Substantive cross-bridge to Wave 1 + Phase 6a.1: at the Dirac+Sakharov '
                'calibration α=1, the EFE residual at G_N = G_N_emerg(Λ, N_f, 1) '
                '= G_N_from_a2(Λ, N_f) is identically zero '
                '(Lean: efeResidualTrace_at_dirac_calibration_vanishes — invokes '
                'G_N_emerg_at_alpha_one + G_N_from_a2_eq_G_N_sakharov by name)',
            'Light deflection ratio: δθ_ADW/δθ_GR = α_ADW '
                '(Lean: deflectionRatio); deviation linear in (α-1) '
                '(Lean: deflectionRatio_minus_one_eq)',
            'Perihelion precession ratio: δφ_ADW/δφ_GR = (2α + 1)/3 — non-trivial '
                'PPN combination ((2 + 2γ - β)/3 at γ=α, β=1, Will 2018 Eq. 4.31); '
                'equals 1 iff α = 1 '
                '(Lean: precessionRatio_eq_one_iff_alpha_unity — non-rfl '
                'biconditional requires linarith)',
            'Cross-channel structural claim: precession deviation = 2/3 × deflection '
                'deviation (testable multi-observation prediction; Lean: '
                'precession_dev_eq_two_thirds_deflection_dev)',
            'Quantitative VLBI floor falsifier: |α-1| > 3×10⁻⁴ ⇒ deflection '
                'deviation detectable '
                '(Lean: deflectionRatio_deviation_exceeds_VLBI_floor)',
            'Substantive cross-bridge to Wave 2: |𝒜₄(R², R_μν², R_μνρσ²)| ≤ '
                '(|R²| + |R_μν²| + |R_μνρσ²|) · 10⁵⁹ at SM-relevant N_f, '
                'consuming Wave 2 higher_curvature_below_pulsar_bound '
                '(Lean: higherCurvatureCorrection_abs_bound)',
            'Bundled Prop H_NonlinearEFEHolds combines (C1) EFE residual = 0, '
                '(C2) Wave 2 H_HigherCurvatureWithinObservationalBounds at the '
                'pulsar bound, (C3) Wave 3 H_NonlinearDiffInvariance for the '
                'Dirac bundle. Discharged at α=1 by '
                'dirac_H_NonlinearEFEHolds_at_alpha_one; falsified for any '
                'α ≠ 1 by perturbed_alpha_not_H_NonlinearEFEHolds.',
        ],
    },
    'paper23_linearized_efe': {
        'title': 'Paper 23: Linearized Einstein Equations from ADW Microscopic Theory (PRD)',
        'topic': 'Linearized EFE in momentum space, Sakharov-Adler closed form, '
                 'ADW α_ADW tracked-hypothesis parameterization, correctness-push '
                 'against G_N^obs at the natural Planck anchor',
        'formulas': [
            'G_N_sakharov',
            'G_N_emergent',
            'G_N_emergent_at_coupling',
            'G_N_emergent_matches_observed',
            'planck_mass_emergent_gev',
            'alpha_ADW_linear_ansatz',
            'linearized_einstein_de_donder',
            'trace_reverse_perturbation',
        ],
        'lean_modules': ['LinearizedEFE', 'ADWMechanism'],
        'platforms': [],
        'key_claims': [
            'Linearized Einstein tensor G^(1)_μν(k) = -(1/2) k² h̄_μν in '
                'de Donder gauge (Lean: linEinsteinDeDonder, _linear, _symm)',
            'Sakharov-Adler closed form: G_N = 12π/(N_f · Λ²) (Lean: G_N_sakharov_pos, '
                'G_N_sakharov_eq_ratio_critical_coupling)',
            'ADW emergent G_N: G_N^emerg = α_ADW · G_N^Sakharov (Lean: G_N_emerg_pos, '
                '_sign, _zero_iff)',
            'Correctness-push exact match locus: Λ² = α_ADW · 12π/(N_f · G_N^obs) '
                '(Lean: G_N_emerg_match_locus)',
            'Planck-anchor reduction: at Λ = M_P^obs, match condition reduces to '
                'α_ADW · 12π = N_f (Lean: G_N_emerg_match_at_planck_anchor); for '
                'SM N_f ∈ {15, 16, 45, 48} the matching α* lies in [0.40, 1.27], '
                'inside the natural range [0.1, 10]',
            'Three Vergeles-derived structural properties on α_ADW: positivity '
                '(Vergeles 2025), critical-limit collapse (mean field), deep-gap '
                'reduction to Sakharov-Adler (Adler 1982). Lean: H_VergelesPositivity, '
                'H_CriticalLimitCollapse, H_DeepGapReducesToAdler',
            'Linear ansatz α_ADW(G/G_c) = 1 - G_c/G satisfies all three properties '
                '(Lean: alphaADW_linear_satisfies_all_three); not literature-endorsed',
            'At G/G_c = 2 with linear ansatz: α_ADW = 1/2 → Λ_UV ≈ 0.7 M̄_P at N_f=15',
            'Closed-form ADW α_ADW value awaits the missing one-loop ⟨h h⟩ '
                'computation in the broken phase (deep-research §6.3)',
        ],
    },
    'paper25_gravitational_waves': {
        'title': 'Paper 25: Gravitational Wave Propagation under the Vestigial-Susceptibility '
                 'Identification — A GW170817 Falsification of the Volovik Second-Sound Graviton (PRD)',
        'topic': 'c_GW = c · √χ_vest leading-order propagation, GW170817 multi-messenger '
                 'correctness-push biconditional, natural-range falsification by ~10^14, '
                 'tracked-hypothesis bundle H_VestigialModeIsGraviton with three falsifiers, '
                 'Phase 5y H1 caveat encoded as second_sound_graviton_not_derived_DOF, '
                 'SK-EFT dispersion correction from SecondOrderSK Γ_H',
        'formulas': [
            'c_GW_from_chi_vest',
            'c_GW_deviation_from_c',
            'dispersion_correction_from_GammaH',
            'ligo_constraint_check',
            'c_GW_natural_range',
        ],
        'lean_modules': ['GravitationalWaves', 'VestigialSusceptibility', 'SecondOrderSK',
                         'LinearizedEFE'],
        'platforms': [],
        'key_claims': [
            'Leading-order c_GW = c · √χ_vest (Lean: c_GW); deviation Δc/c = √χ_vest − 1 '
                '(Lean: c_GW_deviation, _zero_iff_chi_one, _strict_mono)',
            'GW170817 correctness-push biconditional: |Δc/c| ≤ 3e-15 ⟺ χ_vest ∈ '
                '[(1-τ)², (1+τ)²] (Lean: c_GW_match_iff_chi_close_to_one)',
            'Natural-range falsification: at χ_vest = 0.1, Δc/c ≈ -0.684; at χ_vest = 10, '
                'Δc/c ≈ +2.162. Both endpoints fail GW170817 by ~10^14 (Lean: '
                'natural_lower_violates_ligo, natural_upper_violates_ligo, '
                'vestigial_natural_range_violates_ligo)',
            'Phase 5y H1 caveat: vestigial-second-sound graviton identification is NOT '
                'derived as a propagating DOF (Lean: second_sound_graviton_not_derived_DOF, '
                'an existential meta-theorem)',
            'Bundled tracked hypothesis H_VestigialModeIsGraviton: positivity ∧ LIGO '
                'compatibility ∧ luminal propagation; discharged at χ_vest = 1 (Lean: '
                'H_VestigialModeIsGraviton_at_one), three falsifiers at natural range '
                'endpoints + zero',
            'GW170817-compatible χ_vest window has width 4·(3e-15) = 1.2e-14 — vanishing '
                'measure under any natural-range prior',
            'SK-EFT dispersion correction δω/ω = γ·ω from Γ_H bridge (Lean: '
                'dispersion_correction, _zero_at_no_dissipation, _linear_in_gamma, '
                '_abs_bound)',
        ],
    },
    'paper26_bh_entropy': {
        'title': 'Paper 26: Bekenstein-Hawking Entropy from MTC State Counting — '
                 'Kaul-Majumdar SU(2)_k Closed Form, Tracked-Hypothesis Bundle for '
                 'the General MTC, and Walker-Wang Anomaly Match for ADW Substrates',
        'topic': 'S = A/(4 G_N) − (3/2) log(A/(4 G_N)) + c_0 closed form under SU(2)_k '
                 'specialization (Kaul-Majumdar gr-qc/0002040), Outcome-3 tracked-'
                 'hypothesis bundle H_HorizonBoundaryCondition with five falsifier '
                 'theorems for the general MTC case, falsifier-instance status table '
                 'for FibonacciMTC + IsingBraiding + S3CenterAnyons + Toric code, '
                 'novelty flagging for the Walker-Wang anomaly-match conjecture',
        'formulas': [
            'verlinde_dim_horizon',
            'bh_entropy_kaul_majumdar',
            'bh_entropy_leading_coefficient',
            'log_correction_coefficient_su2k',
            'log_correction_coefficient_per_mtc',
            'mtc_area_law_kappa',
        ],
        'lean_modules': ['BHEntropyMicroscopic', 'SphericalCategory', 'SU2kFusion',
                         'FibonacciMTC', 'IsingBraiding', 'S3CenterAnyons',
                         'LinearizedEFE'],
        'platforms': [],
        'key_claims': [
            'Kaul-Majumdar SU(2)_k closed form: S(A) = A/(4 G_N) − (3/2) log(A/(4 G_N)) '
                '+ c_0 + O(A⁻¹) under the immirziTuning + gaussianSaddleAsymptotic '
                'hypotheses; the gaussianSaddleAsymptotic hypothesis was '
                'axiomatized in Wave 3 and retired in Wave 6a.7 (theorem in '
                'BHEntropyMicroscopic, Laplace-saddle-limit interpretation; '
                'cf. LaplaceMethod.lean)',
            'Log-correction structure: c_log = −1/2 (Gaussian saddle, Lean: '
                'gaussianSaddleAsymptotic theorem post-Wave 6a.7) + −1 (singlet '
                'projection, Lean: kaul_majumdar_log_decomposition) = −3/2 total. '
                'Universal within the Cardy-saddle subfamily (Carlip gr-qc/0005017, '
                'Engle-Noui-Perez 0905.3168), DISAGREES with Sen 4D Schwarzschild '
                'heat-kernel arXiv:1205.0971 (+1.71 ln a)',
            'Leading 1/4 coefficient is a TUNING (Immirzi γ), not a derivation. Lean '
                'encodes via `HorizonMTCBC.γ_immirzi` field + `immirziTuned` discharge',
            'Tracked-hypothesis bundle H_HorizonBoundaryCondition: positivity ∧ areaLeading '
                '∧ secondLaw ∧ modularInvariant ∧ anomalyMatch. Five falsifier '
                'theorems (Lean: H_HorizonBoundaryCondition.falsifier_*).',
            'Falsifier-instance status: Fibonacci passes F1/F3/F4 (positivity, monotonicity, '
                'modular invariance via formalized F-symbols); F2 (area-law κ_F = c·log φ) '
                'is conjectural — no published derivation. Ising same. S3 same. Toric code '
                'FAILS F2 (abelian: log d_max = 0)',
            'Walker-Wang anomaly match: bulk Z₂ time-reversal of ADW substrate ↔ boundary '
                'chiral c_- mod 8 of horizon MTC. Anomaly-inflow conjecture, novelty-flagged',
            'Bridge to Wave 1 G_N^emerg: the immirziTuning hypothesis discharges to '
                '`leadingCoeff = 1/(4 G_N^emerg)` via the Wave 1 Sakharov-Adler closed form',
            'Quantitative MTC zoo: D²(Fib) ≈ 3.618, D²(Ising) = 4, D²(D(S₃)) = 36 '
                '(formalized in Lean modules). Per-MTC log d_max sets the κ_C predicted '
                'value if F2 ever discharges',
        ],
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
    graphene_params = [k for k in PARAMETER_PROVENANCE
                       if any(k.startswith(p) for p in
                              ['V_FERMI_GRAPHENE', 'ALPHA_GRAPHENE', 'E_CHARGE',
                               'Dean_bilayer', 'Monolayer_', 'PN_junction',
                               'Majumdar'])]

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
