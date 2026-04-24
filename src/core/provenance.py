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
        'value': 125.25,
        'unit': 'GeV/c²',
        'tier': 'MEASURED',
        'source': 'Particle Data Group, Review of Particle Physics (2024)',
        'detail': 'Higgs boson mass: m_H = 125.25 ± 0.17 GeV (PDG 2024 world average from '
                  'ATLAS + CMS diphoton and 4-lepton channels).',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PDG 2024 world average. Correctness-push target for Phase 5z '
                              'Wave 1 HiggsMassFromCondensate predicate.',
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
    'EW.Y_TOP': {
        'value': 0.9946,
        'unit': 'dimensionless',
        'tier': 'DERIVED',
        'source': 'Derived from top-quark pole mass m_t = 172.76 GeV and v',
        'detail': 'Top Yukawa y_t = √2 m_t/v = √2 · 172.76 / 246.22 ≈ 0.9946. Near-unity '
                  'y_t is a natural outcome of any overlap-integral picture where top is '
                  'strong-coupled to the scalar condensate.',
        'doi': '10.1093/ptep/ptae163',
        'llm_verified_date': '2026-04-24',
        'llm_verified_notes': 'PDG 2024 top mass m_t = 172.69 ± 0.30 GeV (pole-mass combination). '
                              'Using 172.76 as central for Yukawa — well within PDG uncertainty.',
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
