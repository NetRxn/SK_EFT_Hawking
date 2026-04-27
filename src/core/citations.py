"""
Citation Registry — Canonical bibliography for the SK-EFT Hawking project.

Every paper cited anywhere in the codebase (constants.py, formulas.py,
papers/*.tex, docs/*.md, notebooks) should have an entry here.

The provenance dashboard (Tab 5: Citation Registry) reads this to:
- Verify DOIs resolve
- Check citation consistency across files
- Detect orphan citations (cited in code but not in paper bibliography, or vice versa)
- Track which parameters each paper provides

See also: src/core/provenance.py for parameter-level provenance.
"""


CITATION_REGISTRY = {

    # ════════════════════════════════════════════════════════════════
    # Steinhauer / analog Hawking radiation
    # ════════════════════════════════════════════════════════════════

    'Steinhauer2016': {
        'authors': 'Steinhauer, J.',
        'title': 'Observation of quantum Hawking radiation and its entanglement in an analogue black hole',
        'journal': 'Nature Physics',
        'volume': 12,
        'page': '959',
        'year': 2016,
        'doi': '10.1038/nphys3863',
        'arxiv': '1510.00621',
        'doi_verified': None,
        'used_in': [
            'src/core/transonic_background.py',
            'src/core/constants.py',
            'papers/paper1_first_order/paper_draft.tex',
            'papers/paper3_gauge_erasure/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'First observation of analog Hawking radiation in BEC.',
    },
    'deNova2019': {
        'authors': 'Muñoz de Nova, J. R., Golubkov, K., Kolobov, V. I., Steinhauer, J.',
        'title': 'Observation of thermal Hawking radiation and its temperature in an analogue black hole',
        'journal': 'Nature',
        'volume': 569,
        'page': '688',
        'year': 2019,
        'doi': '10.1038/s41586-019-1241-0',
        'arxiv': '1809.00913',
        'doi_verified': None,
        'used_in': [
            'src/wkb/spectrum.py',
            'src/wkb/backreaction.py',
            'papers/paper1_first_order/paper_draft.tex',
            'papers/paper2_second_order/paper_draft.tex',
            'papers/paper4_wkb_connection/paper_draft.tex',
        ],
        'provides': ['Steinhauer.T_H_published'],
        'notes': 'Thermal spectrum measurement, T_H = 0.351(4) nK.',
    },
    'Kolobov2021': {
        'authors': 'Kolobov, V. I., Golubkov, K., Muñoz de Nova, J. R., Steinhauer, J.',
        'title': 'Observation of stationary spontaneous Hawking radiation and the time evolution of an analogue black hole',
        'journal': 'Nature Physics',
        'volume': 17,
        'page': '362',
        'year': 2021,
        'doi': '10.1038/s41567-020-01076-0',
        'arxiv': '1910.09363',
        'doi_verified': None,
        'used_in': [
            'src/wkb/backreaction.py',
            'papers/paper3_gauge_erasure/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Entanglement verification of Hawking radiation.',
    },
    'Wang2017': {
        'authors': 'Wang, Y.-H., Jacobson, T., Edwards, M., Clark, C. W.',
        'title': 'Mechanism of stimulated Hawking radiation in a laboratory Bose-Einstein condensate',
        'journal': 'PRA',
        'volume': 96,
        'page': '023616',
        'year': 2017,
        'doi': '10.1103/PhysRevA.96.023616',
        'arxiv': '1605.01027',  # CORRECTED: was 1706.01483 (combustion paper!)
        'doi_verified': None,
        'used_in': [],
        'provides': ['Steinhauer.omega_perp', 'Steinhauer.density_upstream'],
        'notes': 'Reconstructed Steinhauer 2014 apparatus parameters. '
                 'Table I: omega_perp = 2pi x 123 Hz. '
                 'Key source for parameter reconciliation (deep research 2026-03-31).',
    },

    # ════════════════════════════════════════════════════════════════
    # Atomic physics / scattering lengths
    # ════════════════════════════════════════════════════════════════

    'vanKempen2002': {
        'authors': 'van Kempen, E. G. M., Kokkelmans, S. J. J. M. F., Heinzen, D. J., Verhaar, B. J.',
        'title': 'Spin-off dynamics and collisional properties of Rb-87',
        'journal': 'PRL',
        'volume': 88,
        'page': '093201',
        'year': 2002,
        'doi': '10.1103/PhysRevLett.88.093201',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py'],
        'provides': ['Rb87.a_s'],
        'notes': 'Table I: a(|2,2>+|2,2>) = 109.1(1) a_0.',
    },
    'Falke2008': {
        'authors': 'Falke, S., Knöckel, H., Friebe, J., Rumpf, M., Tiemann, E., Lisdat, C.',
        'title': 'Potassium ground-state scattering parameters',
        'journal': 'PRA',
        'volume': 78,
        'page': '012503',
        'year': 2008,
        'doi': '10.1103/PhysRevA.78.012503',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py'],
        'provides': ['K39.a_s'],
        'notes': 'Feshbach resonance at 402 G for K-39.',
    },

    # ════════════════════════════════════════════════════════════════
    # Analog gravity theory
    # ════════════════════════════════════════════════════════════════

    'BarceloLRR2005': {
        'authors': 'Barceló, C., Liberati, S., Visser, M.',
        'title': 'Analogue Gravity',
        'journal': 'Living Reviews in Relativity',
        'volume': 8,
        'page': '12',
        'year': 2005,
        'doi': '10.12942/lrr-2005-12',
        'arxiv': 'gr-qc/0505065',
        'doi_verified': None,
        'used_in': [
            'src/core/transonic_background.py',
            'papers/paper1_first_order/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Canonical review of analog gravity. Acoustic metric definition.',
    },

    # ════════════════════════════════════════════════════════════════
    # Polariton analog gravity
    # ════════════════════════════════════════════════════════════════

    'Falque2025': {
        'authors': 'Falque, K., Delhom, A., Glorieux, Q., Giacobino, E., Bramati, A., Jacquet, M. J.',
        'title': 'Polariton Fluids as Quantum Field Theory Simulators on Tailored Curved Spacetimes',
        'journal': 'PRL',
        'volume': 135,
        'page': '023401',
        'year': 2025,
        'doi': '10.1103/PhysRevLett.135.023401',
        'arxiv': '2311.01392',
        'doi_verified': None,
        'used_in': ['src/core/constants.py', 'papers/paper12_polariton'],
        'provides': [
            'POLARITON_MASS',
            'Paris_long.c_s', 'Paris_long.xi', 'Paris_long.kappa',
            'Paris_ultralong.c_s', 'Paris_ultralong.xi', 'Paris_ultralong.kappa',
            'Paris_standard.c_s', 'Paris_standard.xi', 'Paris_standard.kappa',
            'Paris_standard.tau_cav',
            'FALQUE_STEEP_HORIZON_KAPPA',
        ],
        'notes': 'LKB Paris polariton analog horizon demonstration. Reports '
                 'three measured κ values (0.07, 0.08, 0.11 ps⁻¹) across smooth '
                 'and steep horizon configurations; c_s = 0.40 μm/ps; '
                 'ξ ≈ 3.4 μm upstream, 4.0 μm downstream. LLM-re-verified '
                 'against full text 2026-04-13 (Phase 5u Wave 3).',
    },
    'Giacobino2025': {
        'authors': 'Giacobino, E., Jacquet, M. J.',
        'title': 'Acoustic horizons and the Hawking effect in polariton fluids of light',
        'journal': None,  # arXiv preprint / lecture notes
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2512.14194',
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton'],
        'provides': [],
        'notes': '52-page lecture notes from the LKB group. Source of the '
                 '"programmable simulators of quantum fields on tailored '
                 'curved spacetimes" framing used in Paper 12 (the word '
                 '"programmable" appears here, not in the Falque 2025 PRL). '
                 'Added to registry 2026-04-13 (Phase 5u Wave 5).',
    },
    'Grisins2016': {
        'authors': 'Grisins, P., Nguyen, H. S., Bloch, J., Amo, A., Carusotto, I.',
        'title': 'Theoretical study of stimulated and spontaneous Hawking effects from an acoustic black hole in a hydrodynamically flowing fluid of light',
        'journal': 'PRB',
        'volume': 94,
        'page': '144518',
        'year': 2016,
        'doi': '10.1103/PhysRevB.94.144518',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py'],
        'provides': [],
        'notes': 'T_H survives in polariton condensate.',
    },
    'Jacquet2022': {
        'authors': 'Jacquet, M. et al.',
        'title': 'Analogue quantum simulation of the Hawking effect in a polariton superfluid',
        'journal': 'Eur. Phys. J. D',
        'volume': 76,
        'page': '152',
        'year': 2022,
        'doi': '10.1140/epjd/s10053-022-00477-5',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py',
                    'papers/paper12_polariton/paper_draft.tex'],
        'provides': ['Paris_long.c_s', 'Paris_long.xi'],
        'notes': 'Polariton kinematics: c_s ~ 1 um/ps, xi ~ 2 um.',
    },
    'Gerace2012': {
        'authors': 'Gerace, D., Carusotto, I.',
        'title': 'Analog Hawking radiation from interacting polaritons',
        'journal': 'PRB',
        'volume': 86,
        'page': '144505',
        'year': 2012,
        'doi': '10.1103/PhysRevB.86.144505',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Polariton analog Hawking proposal.',
    },
    'Nguyen2015': {
        'authors': 'Nguyen, H. S. et al.',
        'title': 'Acoustic black hole in a stationary hydrodynamic flow of microcavity polaritons',
        'journal': 'PRL',
        'volume': 114,
        'page': '036402',
        'year': 2015,
        'doi': '10.1103/PhysRevLett.114.036402',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Polariton acoustic black hole demonstration.',
    },
    'Estrecho2021': {
        'authors': 'Estrecho, E. et al.',
        'title': 'Low-energy collective oscillations and Bogoliubov sound in an exciton-polariton condensate',
        'journal': 'PRL',
        'volume': 126,
        'page': '075301',
        'year': 2021,
        'doi': '10.1103/PhysRevLett.126.075301',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Polariton c_s measurement via dipole oscillations. '
                 'Confirms reservoir-corrected c_s ~ 0.4 um/ps.',
    },
    'Stepanov2019': {
        'authors': 'Stepanov, P. et al.',
        'title': 'Dispersion relation of the collective excitations in a resonantly driven polariton fluid',
        'journal': 'Nature Communications',
        'volume': 10,
        'page': '3869',
        'year': 2019,
        'doi': '10.1038/s41467-019-11886-3',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Polariton collective excitations and reservoir effects on c_s.',
    },
    'Claude2023': {
        'authors': 'Claude, F. et al.',
        'title': 'Spectrum of collective excitations of a quantum fluid of polaritons',
        'journal': 'PRB',
        'volume': 107,
        'page': '174507',
        'year': 2023,
        'doi': '10.1103/PhysRevB.107.174507',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Polariton collective excitation spectrum including reservoir corrections.',
    },
    'Burkhard2025': {
        'authors': 'Burkhard, D. et al.',
        'title': 'Quasinormal modes and stimulated Hawking radiation in analog black holes',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2511.12339',
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'QNM resonances concentrate stimulated Hawking signal.',
    },
    'Finazzi2012': {
        'authors': 'Finazzi, S., Parentani, R.',
        'title': 'Hawking radiation in dispersive theories, the two regimes',
        'journal': 'PRD',
        'volume': 85,
        'page': '124027',
        'year': 2012,
        'doi': '10.1103/PhysRevD.85.124027',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Dispersive corrections to Hawking radiation in two regimes.',
    },
    'Amelio2020': {
        'authors': 'Amelio, I., Carusotto, I.',
        'title': 'Theory of the coherence of topological lasers',
        'journal': 'PRB',
        'volume': 101,
        'page': '064505',
        'year': 2020,
        'doi': '10.1103/PhysRevB.101.064505',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Acoustic metric in driven-dissipative polariton systems; '
                 'weak-loss, long-wavelength limit.',
    },
    'Jacquet2023QNM': {
        'authors': 'Jacquet, M. et al.',
        'title': 'Analogue quantum simulation of the quasi-normal modes of a Kerr black hole',
        'journal': 'PRL',
        'volume': 130,
        'page': '111501',
        'year': 2023,
        'doi': '10.1103/PhysRevLett.130.111501',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'QNM observation in polariton analog, driven-dissipative setting.',
    },
    'Nelsen2013': {
        'authors': 'Nelsen, B. et al.',
        'title': 'Dissipationless flow and sharp threshold of a polariton condensate with long lifetime',
        'journal': 'Physical Review X',
        'volume': 3,
        'page': '041015',
        'year': 2013,
        'doi': '10.1103/PhysRevX.3.041015',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Long-lifetime polariton cavity (300 ps).',
    },
    'Alnatah2024': {
        'authors': 'Alnatah, H. et al.',
        'title': 'Ultra-high-quality-factor microcavity polaritons',
        'journal': 'Science Advances',
        'volume': 10,
        'page': 'eadk6960',
        'year': 2024,
        'doi': '10.1126/sciadv.adk6960',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Ultra-high Q polariton microcavity, Q ~ 10^6.',
    },
    'Amo2009': {
        'authors': 'Amo, A. et al.',
        'title': 'Superfluidity of polaritons in semiconductor microcavities',
        'journal': 'Nature Physics',
        'volume': 5,
        'page': '805',
        'year': 2009,
        'doi': '10.1038/nphys1364',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper12_polariton/paper_draft.tex'],
        'provides': [],
        'notes': 'Polariton superfluidity, c_s via Cherenkov cone. '
                 'CdTe microcavity (not GaAs).',
    },

    # ════════════════════════════════════════════════════════════════
    # Heidelberg / analog cosmology
    # ════════════════════════════════════════════════════════════════

    'Viermann2022': {
        'authors': 'Viermann, C. et al.',
        'title': 'Quantum field simulator for dynamics in curved spacetime',
        'journal': 'Nature',
        'volume': 611,
        'page': '260',
        'year': 2022,
        'doi': '10.1038/s41586-022-05313-9',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'src/wkb/backreaction.py',
        ],
        'provides': [],
        'notes': 'Heidelberg K-39 analog COSMOLOGY experiment. '
                 'NOT analog Hawking radiation.',
    },

    # ════════════════════════════════════════════════════════════════
    # Trento / spin-sonic
    # ════════════════════════════════════════════════════════════════

    'Berti2025': {
        'authors': 'Berti, A., Fernandes, J., Butera, S., Recati, A., Wouters, M., Carusotto, I.',
        'title': 'Analog Hawking radiation from a spin-sonic horizon in a two-component BEC',
        'journal': 'Comptes Rendus Physique',
        'volume': 25,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2408.17292',
        'doi_verified': None,
        'used_in': [
            'src/core/transonic_background.py',
        ],
        'provides': [],
        'notes': 'THEORETICAL PROPOSAL only. No experimental parameters published. '
                 'Trento Na-23 spin-sonic experiment has not been realized.',
    },

    # ════════════════════════════════════════════════════════════════
    # ADW mechanism / emergent gravity
    # ════════════════════════════════════════════════════════════════

    'VladimirovDiakonov2012': {
        'authors': 'Vladimirov, A. A., Diakonov, D.',
        'title': 'Phase transitions in spinor quantum gravity on a lattice',
        'journal': 'PRD',
        'volume': 86,
        'page': '104019',
        'year': 2012,
        'doi': '10.1103/PhysRevD.86.104019',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py'],
        'provides': [],
        'notes': 'ADW lattice gravity model. Basis for vestigial MC.',
    },
    'Chandrasekharan2010': {
        'authors': 'Chandrasekharan, S.',
        'title': 'Fermion bag approach to lattice field theories',
        'journal': 'PRD',
        'volume': 82,
        'page': '025007',
        'year': 2010,
        'doi': '10.1103/PhysRevD.82.025007',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py'],
        'provides': [],
        'notes': 'Fermion-bag MC algorithm.',
    },
    'Volovik2024': {
        'authors': 'Volovik, G. E.',
        'title': 'Vestigial gravity',
        'journal': 'JETP Letters',
        'volume': 119,
        'page': '330',
        'year': 2024,
        'doi': None,
        'arxiv': '2312.09435',
        'doi_verified': None,
        'used_in': [
            'papers/paper5_adw_gap/paper_draft.tex',
            'papers/paper6_vestigial/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Vestigial metric phase concept.',
    },

    # ════════════════════════════════════════════════════════════════
    # Foundational Hawking / analog gravity
    # ════════════════════════════════════════════════════════════════

    'Hawking1974': {
        'authors': 'Hawking, S. W.',
        'title': 'Black hole explosions?',
        'journal': 'Nature',
        'volume': 248,
        'page': '30',
        'year': 1974,
        'doi': '10.1038/248030a0',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper1_first_order/paper_draft.tex',
                    'papers/paper2_second_order/paper_draft.tex'],
        'provides': [],
        'notes': 'Original Hawking radiation prediction.',
    },
    'Unruh1981': {
        'authors': 'Unruh, W. G.',
        'title': 'Experimental black-hole evaporation?',
        'journal': 'PRL',
        'volume': 46,
        'page': '1351',
        'year': 1981,
        'doi': '10.1103/PhysRevLett.46.1351',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper1_first_order/paper_draft.tex',
                    'papers/paper3_gauge_erasure/paper_draft.tex',
                    'papers/paper4_wkb_connection/paper_draft.tex'],
        'provides': [],
        'notes': 'Original analog gravity proposal.',
    },
    'Corley1996': {
        'authors': 'Corley, S., Jacobson, T.',
        'title': 'Hawking spectrum and high frequency dispersion',
        'journal': 'PRD',
        'volume': 54,
        'page': '1568',
        'year': 1996,
        'doi': '10.1103/PhysRevD.54.1568',
        'arxiv': 'hep-th/9601073',
        'doi_verified': None,
        'used_in': ['papers/paper1_first_order/paper_draft.tex',
                    'papers/paper4_wkb_connection/paper_draft.tex'],
        'provides': [],
        'notes': 'Dispersive corrections to Hawking radiation. Source for delta_disp formula.',
    },

    # ════════════════════════════════════════════════════════════════
    # Schwinger-Keldysh EFT
    # ════════════════════════════════════════════════════════════════

    'Crossley2017': {
        'authors': 'Crossley, M., Glorioso, P., Liu, H.',
        'title': 'Effective field theory of dissipative fluids',
        'journal': 'JHEP',
        'volume': '1709',
        'page': '095',
        'year': 2017,
        'doi': '10.1007/JHEP09(2017)095',
        'arxiv': '1511.03646',
        'doi_verified': None,
        'used_in': ['papers/paper1_first_order/paper_draft.tex',
                    'papers/paper2_second_order/paper_draft.tex',
                    'src/second_order/cgl_derivation.py'],
        'provides': [],
        'notes': 'SK-EFT framework, dynamical KMS transformation.',
    },
    'GloriosoLiu2018': {
        'authors': 'Glorioso, P., Liu, H.',
        'title': 'The second law of thermodynamics from symmetry and unitarity',
        'journal': 'JHEP',
        'volume': None,
        'page': None,
        'year': 2018,
        'doi': None,
        'arxiv': '1612.07705',
        'doi_verified': True,
        'used_in': ['papers/paper1_first_order/paper_draft.tex',
                    'papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex',
                    'src/second_order/enumeration.py'],
        'provides': ['Eq. (3.20) §III: dynamical KMS Z₂ symmetry + unitarity '
                     '(Im S_eff ≥ 0) ⇒ ∂_μ s^μ ≥ 0 (entropy-current monotonicity), '
                     'WITHOUT pointwise NEC. Wave 5 second-law primary anchor.'],
        'notes': 'SK-EFT second law without NEC. arXiv:1612.07705 verified 2026-04-26.',
    },
    'Jana2020': {
        'authors': 'Jana, S., Loganayagam, R., Rangamani, M.',
        'title': 'Open quantum systems and Schwinger-Keldysh holograms',
        'journal': 'JHEP',
        'volume': '2005',
        'page': '064',
        'year': 2020,
        'doi': '10.1007/JHEP07(2020)242',
        'arxiv': '2003.03088',
        'doi_verified': None,
        'used_in': ['papers/paper1_first_order/paper_draft.tex',
                    'papers/paper4_wkb_connection/paper_draft.tex'],
        'provides': [],
        'notes': 'SK influence functional for Hawking radiation.',
    },

    # ════════════════════════════════════════════════════════════════
    # ADW mechanism / emergent gravity (additional)
    # ════════════════════════════════════════════════════════════════

    'Akama1978': {
        'authors': 'Akama, K.',
        'title': 'An early proposal of "brane world"',
        'journal': 'Prog. Theor. Phys.',
        'volume': 60,
        'page': '1900',
        'year': 1978,
        'doi': '10.1143/PTP.60.1900',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper5_adw_gap/paper_draft.tex'],
        'provides': [],
        'notes': 'Original tetrad condensation idea.',
    },
    'Diakonov2011': {
        'authors': 'Diakonov, D.',
        'title': 'Towards lattice-regularized Quantum Gravity',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2011,
        'doi': None,
        'arxiv': '1109.0091',
        'doi_verified': None,
        'used_in': ['papers/paper5_adw_gap/paper_draft.tex',
                    'papers/paper6_vestigial/paper_draft.tex'],
        'provides': [],
        'notes': 'Lattice-regularized quantum gravity, ADW mechanism.',
    },
    'Wetterich2004': {
        'authors': 'Wetterich, C.',
        'title': 'Gravity from spinors',
        'journal': 'PRD',
        'volume': 70,
        'page': '105004',
        'year': 2004,
        'doi': '10.1103/PhysRevD.70.105004',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper5_adw_gap/paper_draft.tex',
                    'papers/paper6_vestigial/paper_draft.tex'],
        'provides': [],
        'notes': 'Gravity from spinors, emergent geometry.',
    },
    'Vergeles2025': {
        'authors': 'Vergeles, S. N.',
        'title': 'Unitarity of 4D Lattice Theory of Gravity',
        'journal': 'PRD',
        'volume': 112,
        'page': '054509',
        'year': 2025,
        'doi': '10.1103/PhysRevD.112.054509',
        'arxiv': '2506.00036',
        'doi_verified': True,
        'used_in': [
            'papers/paper5_adw_gap/paper_draft.tex',
            'papers/paper26_bh_entropy/paper_draft.tex',
        ],
        'provides': [
            'Unitarity proof for the 4D simplicial-complex lattice theory of gravity '
            '(direct lattice transfer-matrix proof in Minkowski signature; '
            'long-wave limit yields Einstein-Cartan-Palatini gravity).',
        ],
        'notes': 'Title and venue verified via arXiv.org fresh-fetch 2026-04-26 '
                 '(adversarial-review BLOCKER 1.3 fix; prior registry/bibitem '
                 'titles diverged — actual title is the unitarity-proof title, '
                 'arXiv:2506.00036).',
    },

    # ════════════════════════════════════════════════════════════════
    # Topological order / string-nets
    # ════════════════════════════════════════════════════════════════

    'LevinWen2006': {
        'authors': 'Levin, M. A., Wen, X.-G.',
        'title': 'String-net condensation: A physical mechanism for topological phases',
        'journal': 'PRB',
        'volume': 73,
        'page': '035122',
        'year': 2006,
        'doi': '10.1103/PhysRevB.73.035122',
        'arxiv': 'cond-mat/0404617',
        'doi_verified': None,
        'used_in': ['papers/paper5_adw_gap/paper_draft.tex',
                    'src/adw/wen_model.py'],
        'provides': [],
        'notes': 'String-net condensation, rotor models.',
    },

    # ════════════════════════════════════════════════════════════════
    # Chirality wall
    # ════════════════════════════════════════════════════════════════

    'GoltermanShamir2026': {
        'authors': 'Golterman, M., Shamir, Y.',
        'title': 'Generalized no-go theorem for chiral fermions on a lattice',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2026,
        'doi': None,
        'arxiv': '2603.15985',
        'doi_verified': None,
        'used_in': ['papers/paper7_chirality_formal/paper_draft.tex',
                    'src/chirality/tpf_gs_analysis.py'],
        'provides': [],
        'notes': 'GS no-go theorem: 9 conditions. Basis for Paper 7.',
    },

    # ════════════════════════════════════════════════════════════════
    # Quasi-1D BEC theory
    # ════════════════════════════════════════════════════════════════

    'Salasnich2002': {
        'authors': 'Salasnich, L., Parola, A., Reatto, L.',
        'title': 'Effective wave equations for the dynamics of cigar-shaped and disk-shaped Bose condensates',
        'journal': 'PRA',
        'volume': 65,
        'page': '043614',
        'year': 2002,
        'doi': '10.1103/PhysRevA.65.043614',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [],
        'provides': [],
        'notes': 'Quasi-1D BEC formula for c_s with transverse confinement corrections. '
                 'Used by Steinhauer to extract c(x) from density profiles.',
    },

    # ════════════════════════════════════════════════════════════════
    # Backreaction
    # ════════════════════════════════════════════════════════════════

    'Balbinot2025': {
        'authors': 'Balbinot, R., Fabbri, A., Ciliberto, A., Pavloff, N.',
        'title': 'Backreaction in acoustic black holes',
        'journal': 'PRD',
        'volume': 112,
        'page': 'L121703',
        'year': 2025,
        'doi': '10.1103/PhysRevD.112.L121703',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/wkb/backreaction.py'],
        'provides': [],
        'notes': 'Acoustic BHs cool toward extremality (opposite Schwarzschild).',
    },

    # ════════════════════════════════════════════════════════════════
    # Grassmann TRG
    # ════════════════════════════════════════════════════════════════

    'ShimizuKuramashi2014': {
        'authors': 'Shimizu, Y., Kuramashi, Y.',
        'title': 'Grassmann tensor renormalization group approach to one-flavor lattice Schwinger model',
        'journal': 'PRD',
        'volume': 90,
        'page': '014508',
        'year': 2014,
        'doi': '10.1103/PhysRevD.90.014508',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py'],
        'provides': [],
        'notes': 'Grassmann TRG algorithm.',
    },

    # ════════════════════════════════════════════════════════════════
    # SMG / fermion-bag MC
    # ════════════════════════════════════════════════════════════════

    'Catterall2016': {
        'authors': 'Catterall, S.',
        'title': 'Fermion mass without symmetry breaking',
        'journal': 'JHEP',
        'volume': '01',
        'page': '121',
        'year': 2016,
        'doi': '10.1007/JHEP01(2016)121',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['src/core/constants.py'],
        'provides': [],
        'notes': 'SO(4) fermion-bag MC for symmetric mass generation.',
    },

    # ════════════════════════════════════════════════════════════════
    # Paper 17 (dark sector) bibkeys — added Phase 5x Wave 10 (2026-04-24)
    # Response to adversarial review 2026-04-23-1500-internal-adversarial
    # ════════════════════════════════════════════════════════════════

    'Visser1998': {
        'authors': 'Visser, M.',
        'title': 'Acoustic black holes: horizons, ergospheres, and Hawking radiation',
        'journal': 'Class. Quant. Grav.',
        'volume': 15,
        'page': '1767',
        'year': 1998,
        'doi': '10.1088/0264-9381/15/6/024',
        'arxiv': 'gr-qc/9712010',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Visser acoustic metric foundational reference. arXiv verified.',
    },
    'CGL2017a': {
        'authors': 'Crossley, M., Glorioso, P., Liu, H.',
        'title': 'Effective field theory of dissipative fluids',
        'journal': 'JHEP',
        'volume': '09',
        'page': '095',
        'year': 2017,
        'doi': '10.1007/JHEP09(2017)095',
        'arxiv': '1511.03646',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Paper 17 alias for Crossley2017 (same work; registry keeps '
                 'both for direct bibkey lookup compatibility with paper17 tex).',
    },
    'CGL2017b': {
        'authors': 'Glorioso, P., Crossley, M., Liu, H.',
        'title': 'Second law of thermodynamics from symmetry and unitarity',
        'journal': 'JHEP',
        'volume': '09',
        'page': '096',
        'year': 2017,
        'doi': '10.1007/JHEP09(2017)096',
        'arxiv': '1701.07817',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'SK-EFT second-law derivation. arXiv ID tentative — user verify.',
    },
    'Volovik2006': {
        'authors': 'Volovik, G. E.',
        'title': 'Cosmological constant and vacuum energy (JETP Lett note)',
        'journal': 'JETP Lett.',
        'volume': 82,
        'page': '319',
        'year': 2005,
        'doi': None,
        'arxiv': 'gr-qc/0604062',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Tetrad-determinant self-tuning of cosmological constant. '
                 'Note: paper17 bibitem uses year 2005 (JETP Lett), arXiv '
                 'year 2006. arXiv ID is tentative — user verify against JETP.',
    },
    'KV2008': {
        'authors': 'Klinkhamer, F. R., Volovik, G. E.',
        'title': 'Self-tuning vacuum variable and cosmological constant',
        'journal': 'Phys. Rev. D',
        'volume': 77,
        'page': '085015',
        'year': 2008,
        'doi': '10.1103/PhysRevD.77.085015',
        'arxiv': '0711.3170',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Klinkhamer-Volovik oscillating vacuum. arXiv ID tentative — user verify.',
    },
    'Lean4': {
        'authors': 'de Moura, L., Ullrich, S.',
        'title': 'The Lean 4 theorem prover and programming language',
        'journal': 'CADE 28',
        'volume': None,
        'page': '625',
        'year': 2021,
        'doi': '10.1007/978-3-030-79876-5_37',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'papers/paper17_dark_sector/paper_draft.tex',
            'papers/paper18_doublon_gate/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Lean 4 citation. Conference: CADE-28, Pittsburgh 2021.',
    },
    'Mathlib': {
        'authors': 'The mathlib Community',
        'title': 'The Lean Mathematical Library',
        'journal': 'CPP 2020 (Proceedings)',
        'volume': None,
        'page': '367',
        'year': 2020,
        'doi': '10.1145/3372885.3373824',
        'arxiv': '1910.09336',
        'doi_verified': None,
        'used_in': [
            'papers/paper17_dark_sector/paper_draft.tex',
            'papers/paper18_doublon_gate/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Mathlib paper, CPP 2020 (Certified Programs and Proofs).',
    },
    'Wan2019': {
        'authors': 'Wan, Z., Wang, J., Zheng, Y.',
        'title': 'Quantum 4d Yang-Mills theory and time-reversal symmetric 5d higher-gauge topological field theory',
        'journal': 'Phys. Rev. D',
        'volume': 100,
        'page': '085012',
        'year': 2019,
        'doi': '10.1103/PhysRevD.100.085012',
        'arxiv': '1904.00994',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Wan-Wang-Zheng Z16 bordism classification. arXiv tentative — user verify.',
    },
    'Wang2020': {
        'authors': 'Wang, J.',
        'title': 'Anomaly and cobordism constraints beyond the Standard Model',
        'journal': 'Phys. Rev. Research',
        'volume': 2,
        'page': '013189',
        'year': 2020,
        'doi': '10.1103/PhysRevResearch.2.013189',
        'arxiv': '1910.14664',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Wang Standard Model anomaly/cobordism. arXiv tentative — user verify.',
    },
    'Wang2021': {
        'authors': 'Wang, J.',
        'title': 'Ultra Unification: Quantum fields beyond the Standard Model',
        'journal': 'Mod. Phys. Lett. A',
        'volume': 36,
        'page': '2130008',
        'year': 2021,
        'doi': '10.1142/S0217732321300081',
        'arxiv': '2012.15860',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Wang Ultra Unification / T-0 topological hidden sector. arXiv tentative — user verify.',
    },
    'Garcia-Etxebarria2019': {
        'authors': 'Garc{\\\'i}a-Etxebarria, I., Montero, M.',
        'title': 'Dai-Freed anomalies in particle physics',
        'journal': 'JHEP',
        'volume': '08',
        'page': '003',
        'year': 2019,
        'doi': '10.1007/JHEP08(2019)003',
        'arxiv': '1808.00009',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Dai-Freed anomalies in Standard Model. arXiv tentative — user verify.',
    },
    'ADW2019': {
        'authors': 'Abrikosov Jr., A. A., Klinkhamer, F. R.',
        'title': 'Tetrad condensation and emergent gravity',
        'journal': 'Phys. Rev. D',
        'volume': 99,
        'page': '105009',
        'year': 2019,
        'doi': '10.1103/PhysRevD.99.105009',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'ADW (Abrikosov-Diakonov-Wetterich) tetrad condensation / emergent '
                 'gravity. Title reconstructed — user verify via DOI lookup.',
    },
    'BK2015': {
        'authors': 'Berezhiani, L., Khoury, J.',
        'title': 'Theory of dark matter superfluidity',
        'journal': 'Phys. Rev. D',
        'volume': 92,
        'page': '103510',
        'year': 2015,
        'doi': '10.1103/PhysRevD.92.103510',
        'arxiv': '1507.01019',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [
            'SFDM.m_DM', 'SFDM.Lambda', 'SFDM.c_s_subcluster',
        ],
        'notes': 'Berezhiani-Khoury superfluid dark matter framework. '
                 'BK fiducial: m_DM = 0.6 eV, Lambda = 0.2 meV, '
                 'c_s_subcl = 1525 km/s. arXiv ID verified 2026-04-24.',
    },
    'BK2025': {
        'authors': 'Berezhiani, L., Cintia, G., De Luca, V., Khoury, J.',
        'title': 'Superfluid Dark Matter',
        'journal': 'Physics Reports',
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2505.23900',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'BK2025 SFDM review, Physics Reports (in press). '
                 '136 pages, 12 figures. Paper 17 cites gap: no quantitative '
                 'merger forecast. arXiv + page count verified 2026-04-24.',
    },
    'BKWang2017': {
        'authors': 'Berezhiani, L., Khoury, J., Wang, J.',
        'title': 'Phonon-mediated late-time acceleration',
        'journal': 'Phys. Rev. D',
        'volume': 95,
        'page': '123530',
        'year': 2017,
        'doi': '10.1103/PhysRevD.95.123530',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'BK-Wang phonon-sector acceleration → H_0 tension thematic. '
                 'arXiv ID needs user verification.',
    },
    'DESI2024': {
        'authors': 'DESI Collaboration',
        'title': 'DESI 2024 VI: cosmological constraints from the measurements of BAO',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2024,
        'doi': None,
        'arxiv': '2404.03002',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'DESI DR1 / 2024 cosmology result. Used in paper17 KV-withdraw '
                 'reasoning. User verify title exact form.',
    },
    'DESI2025': {
        'authors': 'DESI Collaboration',
        'title': 'DESI DR2 BAO: cosmological constraints',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2503.14738',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'DESI DR2 2025 cosmology (KV tension source). '
                 'User verify full title.',
    },
    'Sola2023': {
        'authors': 'Sol{\\`a} Peracaula, J.',
        'title': 'Running vacuum model and the H0 tension',
        'journal': 'Class. Quantum Grav.',
        'volume': 40,
        'page': '215004',
        'year': 2023,
        'doi': None,
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'RVM with nu ~ 10^-3 DESI-compatible. User verify DOI + arXiv.',
    },
    'VanWaerbeke2025': {
        'authors': 'Van Waerbeke, L., Zhitnitsky, A. R.',
        'title': 'DESI results and Dark Energy from QCD topological sectors',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2506.14182',
        'doi_verified': '2026-04-29',  # WebFetch arXiv:2506.14182 confirmed title match (paper32 adversarial 2026-04-29)
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex',
                    'papers/paper32_strong_cp_de/paper_draft.tex'],
        'provides': [],
        'notes': 'QCD topological DE — 0 free params, phantom crossing. Title corrected 2026-04-29 (was "QCD topological dark energy") per WebFetch verification.',
    },
    'Planck2018': {
        'authors': 'Planck Collaboration',
        'title': 'Planck 2018 results. VI. Cosmological parameters',
        'journal': 'A&A',
        'volume': 641,
        'page': 'A6',
        'year': 2020,
        'doi': '10.1051/0004-6361/201833910',
        'arxiv': '1807.06209',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Planck 2018 cosmological parameters (published 2020).',
    },
    'FangGu2021': {
        'authors': 'Fang, X.-Y., Gu, Z.-C.',
        'title': 'Emergent gravity with torsion from electron-loop condensation',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2021,
        'doi': None,
        'arxiv': '2106.10242',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Fang-Gu topological gravity / torsion DM. arXiv verified.',
    },
    'Pretko2017': {
        'authors': 'Pretko, M.',
        'title': 'Subdimensional particle structure of higher rank U(1) spin liquids',
        'journal': 'Phys. Rev. B',
        'volume': 95,
        'page': '115139',
        'year': 2017,
        'doi': '10.1103/PhysRevB.95.115139',
        'arxiv': '1604.05329',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Pretko fracton / tensor gauge framework. arXiv tentative — user verify.',
    },
    'Nandkishore2019': {
        'authors': 'Nandkishore, R. M., Hermele, M.',
        'title': 'Fractons',
        'journal': 'Annu. Rev. Condens. Matter Phys.',
        'volume': 10,
        'page': '295',
        'year': 2019,
        'doi': '10.1146/annurev-conmatphys-031218-013604',
        'arxiv': '1803.11196',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Nandkishore-Hermele fracton review. arXiv tentative — user verify.',
    },
    'Shen2022': {
        'authors': 'Shen, J., et al.',
        'title': 'Hilbert space fragmentation (fracton diversity mechanism)',
        'journal': 'Phys. Rev. B',
        'volume': 106,
        'page': '045103',
        'year': 2022,
        'doi': '10.1103/PhysRevB.106.045103',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Hilbert space fragmentation. Title reconstructed — user verify.',
    },
    'Krishna2024': {
        'authors': 'Krishna, V., Bridgeman, J., Bartlett, S. D.',
        'title': 'Finite temperature instability of 3D fracton topological order',
        'journal': 'Phys. Rev. B',
        'volume': 109,
        'page': '125131',
        'year': 2024,
        'doi': '10.1103/PhysRevB.109.125131',
        'arxiv': '2407.09625',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Krishna et al. 3D gapped fracton no-go at T>0 (resolved by '
                 'p-wave phase per Drilldown). arXiv tentative — user verify.',
    },
    'Kapustin2022': {
        'authors': 'Kapustin, A., Spodyneiko, L.',
        'title': 'Hohenberg-Mermin-Wagner-type theorems and dipole symmetry',
        'journal': 'Phys. Rev. B',
        'volume': 106,
        'page': '245125',
        'year': 2022,
        'doi': '10.1103/PhysRevB.106.245125',
        'arxiv': '2208.09056',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'HMW-type theorems for dipole symmetry — p-wave stability. '
                 'arXiv + page verified 2026-04-24 (corrected paper17 citation: '
                 'paper17 had 085122, actual is 245125).',
    },
    'Jensen2024': {
        'authors': 'Jensen, K., Raz, A.',
        'title': 'Large-N dipole superfluid',
        'journal': 'Phys. Rev. Lett.',
        'volume': 132,
        'page': '071603',
        'year': 2024,
        'doi': '10.1103/PhysRevLett.132.071603',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Jensen-Raz dipole superfluid SSB throughout phase diagram. '
                 'arXiv ID NEEDS USER VERIFICATION — could not be located via '
                 'WebFetch during 2026-04-24 remediation.',
    },
    'Glodkowski2024': {
        'authors': 'G{\\l}{\\\'o}dkowski, A., Pe{\\~n}a-Ben{\\\'i}tez, F., Sur{\\\'o}wka, P.',
        'title': 'Dissipative fracton superfluids',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2024,
        'doi': None,
        'arxiv': '2401.01877',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Głódkowski-Peña-Benítez-Surówka p-wave dipole superfluid with '
                 'z=4 subdiffusion. arXiv + title verified 2026-04-24 (BLOCKER '
                 '1.1 fix: paper17 previously cited wrong target arXiv:2406.12345 '
                 'which is a knowledge-management / fuzzy-logic paper).',
    },
    'Feistl2026': {
        'authors': 'Feistl, T., Schraven, S., Warzel, S.',
        'title': 'Mermin-Wagner theorems for quantum systems with multipole symmetries',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2026,
        'doi': None,
        'arxiv': '2601.23078',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Feistl-Schraven-Warzel multipole MW extension (Jan 2026). '
                 'arXiv + title verified 2026-04-24.',
    },
    'FractonNonAbelian2025': {
        'authors': 'SK-EFT Hawking Research Program',
        'title': 'Yang-Mills incompatibility of fracton topological phases (Paper 8 companion)',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'Internal project companion paper (was "Paper8" bibkey in paper17 '
                 'prior to 2026-04-24 remediation; renamed to disambiguate from '
                 'paper7 which uses "Paper8" for the Chirality Wall work).',
    },
    # ────────────────────────────────────────────────────────────────
    # Paper 18 (doublon gate) — added 2026-04-26
    # ────────────────────────────────────────────────────────────────
    'Berry1984': {
        'authors': 'Berry, M. V.',
        'title': 'Quantal phase factors accompanying adiabatic changes',
        'journal': 'Proc. R. Soc. Lond. A',
        'volume': 392,
        'page': '45',
        'year': 1984,
        'doi': '10.1098/rspa.1984.0023',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper18_doublon_gate/paper_draft.tex'],
        'provides': [],
        'notes': 'Berry phase foundational paper. No arXiv (pre-arXiv era).',
    },
    'Zanardi1999': {
        'authors': 'Zanardi, P., Rasetti, M.',
        'title': 'Holonomic quantum computation',
        'journal': 'Phys. Lett. A',
        'volume': 264,
        'page': '94',
        'year': 1999,
        'doi': '10.1016/S0375-9601(99)00803-8',
        'arxiv': 'quant-ph/9904011',
        'doi_verified': None,
        'used_in': ['papers/paper18_doublon_gate/paper_draft.tex'],
        'provides': [],
        'notes': 'Original holonomic quantum computation proposal.',
    },
    'Leek2007': {
        'authors': 'Leek, P. J. et al.',
        'title': "Observation of Berry's phase in a solid-state qubit",
        'journal': 'Science',
        'volume': 318,
        'page': '1889',
        'year': 2007,
        'doi': '10.1126/science.1149858',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper18_doublon_gate/paper_draft.tex'],
        'provides': [],
        'notes': 'First Berry-phase observation in a superconducting qubit. '
                 'DOI verified against Science 318, 1889 (2007).',
    },
    'Kiefer2026': {
        'authors': 'Kiefer, S., Zhu, Y., Fischer, P., Jele, Y., '
                   'Gächter, R., Bisson, L., Viebahn, P., Esslinger, T.',
        'title': 'Protected quantum gates using qubit doublons in '
                 'dynamical optical lattices',
        'journal': 'Nature',
        'volume': None,
        'page': None,
        'year': 2026,
        'doi': None,  # Nature DOI pending publication
        'arxiv': '2507.22112',
        'doi_verified': None,
        'used_in': ['papers/paper18_doublon_gate/paper_draft.tex'],
        'provides': [],
        'notes': 'Experimental realization of the doublon geometric SWAP gate. '
                 'arXiv:2507.22112 (Nature 2026). Central experimental reference '
                 'for Paper 18 formalization.',
    },
    'Kitaev2009': {
        'authors': 'Kitaev, A.',
        'title': 'Periodic table for topological insulators and superconductors',
        'journal': 'AIP Conf. Proc.',
        'volume': 1134,
        'page': '22',
        'year': 2009,
        'doi': '10.1063/1.3149495',
        'arxiv': '0901.2686',
        'doi_verified': None,
        'used_in': ['papers/paper18_doublon_gate/paper_draft.tex'],
        'provides': [],
        'notes': 'Tenfold-way periodic table of topological phases (Kitaev 2009). '
                 'BDI class reference for Paper 18 W5 symmetry layer.',
    },
    'AltlandZirnbauer': {
        'authors': 'Altland, A., Zirnbauer, M. R.',
        'title': 'Nonstandard symmetry classes in mesoscopic '
                 'normal-superconducting hybrid structures',
        'journal': 'Phys. Rev. B',
        'volume': 55,
        'page': '1142',
        'year': 1997,
        'doi': '10.1103/PhysRevB.55.1142',
        'arxiv': 'cond-mat/9602137',
        'doi_verified': None,
        'used_in': ['papers/paper18_doublon_gate/paper_draft.tex'],
        'provides': [],
        'notes': 'Foundational Altland-Zirnbauer symmetry classification. '
                 'Original 10-fold way / BDI class definition used in Paper 18.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 5z Wave 1 — Paper 20 (scalar-rung interpretation) bibkeys
    # ════════════════════════════════════════════════════════════════

    'ADW': {
        'authors': 'Akama, K.',
        'title': 'An attempt at pregeometry: gravity with composite metric',
        'journal': 'Prog. Theor. Phys.',
        'volume': 60,
        'page': '1900',
        'year': 1978,
        'doi': '10.1143/PTP.60.1900',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Original Akama pregeometry composite-metric paper. '
                 'Foundational for the ADW mechanism in this project. '
                 'doi_verified 2026-04-26 via OUP/academic.oup.com DOI '
                 'redirect from doi.org: title, author (K. Akama), journal, '
                 'volume, page, year all match. Title corrected from '
                 '"gauge fields" to "gravity with composite metric" per '
                 'the actual PTP record.',
    },
    'WetterichSpinor2013': {
        'authors': 'Wetterich, C.',
        'title': 'Spinor gravity and diffeomorphism invariance on the lattice',
        'journal': 'Lect. Notes Phys.',
        'volume': 863,
        'page': '67',
        'year': 2013,
        'doi': '10.1007/978-3-642-33036-0_4',
        'arxiv': '1201.2871',
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Wetterich Lecture Notes Physics 863 chapter on spinor '
                 'gravity (Proceedings of the 6th Aegean Summer School, '
                 'Naxos 2011). doi_verified 2026-04-26: DOI matches; '
                 'arXiv corrected from 1206.3392 (unrelated information-'
                 'theory paper by Vatedka/Kashyap/Thangaraj) to 1201.2871 '
                 '(the actual Wetterich arXiv preprint for this chapter). '
                 'Split from prior WetterichSpinor combined bibitem.',
    },
    'WetterichSpinor2022': {
        'authors': 'Wetterich, C.',
        'title': 'Pregeometry and spontaneous time-space asymmetry',
        'journal': 'JHEP',
        'volume': 6,
        'page': '069',
        'year': 2022,
        'doi': '10.1007/JHEP06(2022)069',
        'arxiv': '2101.11519',
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Wetterich pregeometry / spontaneous time-space asymmetry. '
                 'doi_verified 2026-04-26: DOI corrected from JHEP02(2022)169 '
                 'to the actual JHEP06(2022)069; arXiv corrected from '
                 '2110.13863 (unrelated exoplanet-ephemeris paper ExoClock '
                 'Project II by Kokori et al.) to the actual 2101.11519. '
                 'Matches Phase-5z deep-research reference (O.2 file table).',
    },
    'WetterichNJL': {
        'authors': 'Wetterich, C.',
        'title': 'Geometry and symmetries in lattice spinor gravity',
        'journal': 'Ann. Phys.',
        'volume': 327,
        'page': '2184',
        'year': 2012,
        'doi': '10.1016/j.aop.2012.04.005',
        'arxiv': '1201.6505',
        'doi_verified': True,
        'used_in': ['lean/SKEFTHawking/WetterichNJL.lean',
                    'papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'CORRECTED 2026-04-26. Prior entry cited a nonexistent '
                 '"Wetterich, PLB 901, 136223 (2024) - Spinor gravity from '
                 'a fermionic four-vertex" — CrossRef 404, INSPIRE/arXiv '
                 'return no match, and Phase-5z O.2 deep research never '
                 'referenced any such paper. Replaced with the canonical '
                 "lattice version of Wetterich's NJL-type 4-fermion spinor-"
                 'gravity construction: Ann. Phys. 327, 2184 (2012), '
                 'arXiv:1201.6505. This paper explicitly introduces the '
                 'nearest-neighbor bond structure formalized in '
                 'WetterichNJL.lean. doi_verified 2026-04-26 via arXiv '
                 'record (journal reference on arxiv.org/abs/1201.6505 '
                 'confirms Ann. Phys. / 10.1016/j.aop.2012.04.005). '
                 'Hallucinated-citation finding filed as Stage-13 BLOCKER.',
    },
    'Fierz': {
        'authors': 'Fierz, M.',
        'title': 'Zur Fermischen Theorie des β-Zerfalls',
        'journal': 'Z. Phys.',
        'volume': 104,
        'page': '553',
        'year': 1937,
        'doi': '10.1007/BF01330070',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Original Fierz rearrangement identity. Pre-arXiv era; '
                 'DOI-only verification path. doi_verified 2026-04-26 via '
                 'NASA ADS (bibcode 1937ZPhy..104..553F): title, author '
                 '(Markus Fierz), journal, volume, page, year all match.',
    },
    'NJL61': {
        'authors': 'Nambu, Y., Jona-Lasinio, G.',
        'title': 'Dynamical model of elementary particles based on an '
                 'analogy with superconductivity I',
        'journal': 'Phys. Rev.',
        'volume': 122,
        'page': '345',
        'year': 1961,
        'doi': '10.1103/PhysRev.122.345',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Original Nambu-Jona-Lasinio paper. Pre-arXiv; '
                 'DOI-only verification path. doi_verified 2026-04-26 '
                 'via NASA ADS (bibcode 1961PhRv..122..345N): title, '
                 'authors (Nambu, Y.; Jona-Lasinio, G.), journal, volume, '
                 'page, year all match.',
    },
    'GiesScherer': {
        'authors': 'Gies, H., Lippoldt, S.',
        'title': 'Renormalization flow towards gravitational catalysis '
                 'in the 3d Gross-Neveu model',
        'journal': 'Phys. Rev. D',
        'volume': 87,
        'page': '104026',
        'year': 2013,
        'doi': '10.1103/PhysRevD.87.104026',
        'arxiv': '1303.4253',
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Gies-Lippoldt RG-NJL companion. Bibkey is a project-local '
                 'shorthand (not the literal author surname). doi_verified '
                 '2026-04-26 via NASA ADS (bibcode 2013PhRvD..87j4026G): '
                 'title, authors (H. Gies, S. Lippoldt), journal, volume, '
                 'article number, year all match. arXiv corrected from '
                 '1305.6940 (unrelated philosophy-of-physics paper "Quantum '
                 'Objects" by Mansouri/Golshani/Karbasizadeh) to the actual '
                 '1303.4253. Consider renaming bibkey to GiesLippoldt2013 '
                 'in paper-side cleanup (advisory, not required).',
    },
    'BardeenHillLindner': {
        'authors': 'Bardeen, W. A., Hill, C. T., Lindner, M.',
        'title': 'Minimal dynamical symmetry breaking of the standard model',
        'journal': 'Phys. Rev. D',
        'volume': 41,
        'page': '1647',
        'year': 1990,
        'doi': '10.1103/PhysRevD.41.1647',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Top-quark condensate / dynamical EWSB foundational paper. '
                 'Pre-arXiv; DOI-only verification path. doi_verified '
                 '2026-04-26 via NASA ADS (bibcode 1990PhRvD..41.1647B): '
                 'title, authors (W. A. Bardeen, C. T. Hill, M. Lindner), '
                 'journal, volume, page, year all match.',
    },
    'MiranskyTanabashiYamawaki1989': {
        'authors': 'Miransky, V. A., Tanabashi, M., Yamawaki, K.',
        'title': 'Is the t-quark responsible for the mass of W and Z bosons?',
        'journal': 'Mod. Phys. Lett. A',
        'volume': 4,
        'page': '1043',
        'year': 1989,
        'doi': '10.1142/S0217732389001210',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'MTY second paper — explicit SU(2)_L × U(1)_R 4-fermion '
                 'operator (ψ̄_L t_R)(t̄_R ψ_L) with σ = H ∼ ψ̄_R ψ_L '
                 'identified as SM (1,2)_{+1/2} Higgs doublet. Primary '
                 'precedent for Scenario A in Phase 5z O.2 verdict. '
                 'Pre-arXiv. doi_verified pending — World Scientific MPLA '
                 'CrossRef route, awaiting fetch round.',
    },
    'Hill2025Redux': {
        'authors': 'Hill, C. T.',
        'title': 'Natural top quark condensation (a redux)',
        'journal': 'arXiv preprint',
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2503.21518',
        'doi_verified': None,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex',
                    'lean/SKEFTHawking/BHLGaugeEmbedding.lean'],
        'provides': [],
        'notes': 'Hill 2025 redux: bilocal H^i(x,y) ∼ ψ̄_R(x) ψ_L^i(y) with '
                 'internal wave-function ϕ(r). The dilution factor '
                 'ϕ(0)/ϕ(∞) is the order parameter resolving the BHL gap '
                 'problem; natural composite scale ~ 6 TeV with quartic λ '
                 'consistent with m_H = 125 GeV at few-percent fine-tuning. '
                 'Most recent load-bearing anchor for Scenario A. '
                 'doi_verified pending — arXiv abstract fetch round.',
    },
    # AndrianovAndrianovAfonin2020 entry REMOVED 2026-04-26 after Stage 13
    # adversarial round verified arXiv:1906.09579 actually resolves to
    # Osipov, Hiller, Blin, Palanca, Moreira, Sampaio, EPJC 80:1135 (DOI
    # …08716-y) — title-only coincidence. The deep research had a wrong-arXiv
    # hallucination similar to documented 5z W2 cases. Hill 2025 + Cvetic
    # 1999 already cover the 125 GeV recovery branch; removed to avoid risk.
    'CsikorFodorHeitger1999': {
        'authors': 'Csikor, F., Fodor, Z., Heitger, J.',
        'title': 'Endpoint of the hot electroweak phase transition',
        'journal': 'Phys. Rev. Lett.',
        'volume': 82,
        'page': '21',
        'year': 1999,
        'doi': '10.1103/PhysRevLett.82.21',
        'arxiv': 'hep-ph/9809291',
        'doi_verified': None,
        'used_in': ['papers/paper22_ew_phase_transition/paper_draft.tex'],
        'provides': [],
        'notes': 'CFH 1999 lattice analysis: refined the KLRS96 SM EWPT '
                 'crossover threshold to m_H = 72.4 ± 1.7 GeV. The 72 GeV '
                 'value cited in paper 22 is from this paper, NOT from KLRS96 '
                 '(which gave a broader 70-95 GeV range). doi_verified pending — '
                 'APS PRL CrossRef + arXiv hep-ph/9809291 fetch round.',
    },
    'KLRS1996': {
        'authors': 'Kajantie, K., Laine, M., Rummukainen, K., Shaposhnikov, M.',
        'title': 'Is there a hot electroweak phase transition at m_H >~ m_W?',
        'journal': 'Phys. Rev. Lett.',
        'volume': 77,
        'page': '2887',
        'year': 1996,
        'doi': '10.1103/PhysRevLett.77.2887',
        'arxiv': 'hep-ph/9605288',
        'doi_verified': None,
        'used_in': ['papers/paper22_ew_phase_transition/paper_draft.tex'],
        'provides': [],
        'notes': 'KLRS 1996 lattice analysis: SM EW phase transition is '
                 'crossover for m_H >~ 72 GeV. Sets the canonical '
                 'crossover threshold m_H_crit = 72 ± 2 GeV via 3D effective '
                 'theory + lattice Monte Carlo. Phase 5z Wave 3 cite for the '
                 'SM-as-crossover verdict. doi_verified pending — APS PRL '
                 'CrossRef + arXiv hep-ph/9605288 fetch round.',
    },
    'ButtazzoEtAl2013': {
        'authors': 'Buttazzo, D., Degrassi, G., Giardino, P. P., Giudice, G. F., Sala, F., Salvio, A., Strumia, A.',
        'title': 'Investigating the near-criticality of the Higgs boson',
        'journal': 'JHEP',
        'volume': '12',
        'page': '089',
        'year': 2013,
        'doi': '10.1007/JHEP12(2013)089',
        'arxiv': '1307.3536',
        'doi_verified': None,
        'used_in': ['papers/paper22_ew_phase_transition/paper_draft.tex'],
        'provides': [],
        'notes': 'SM Higgs vacuum stability under RG: lambda_SM dips near '
                 'zero at ~10^11 GeV, placing SM in metastable regime. '
                 'Phase 5z Wave 3 motivation for the H_VacuumStableUnderRG '
                 'tracked hypothesis. doi_verified pending — Springer JHEP '
                 'CrossRef + arXiv 1307.3536 fetch round.',
    },
    'ShaposhnikovWetterich2010': {
        'authors': 'Shaposhnikov, M., Wetterich, C.',
        'title': 'Asymptotic safety of gravity and the Higgs boson mass',
        'journal': 'Phys. Lett. B',
        'volume': 683,
        'page': '196',
        'year': 2010,
        'doi': '10.1016/j.physletb.2009.12.022',
        'arxiv': '0912.0208',
        'doi_verified': None,
        'used_in': ['papers/paper22_ew_phase_transition/paper_draft.tex'],
        'provides': [],
        'notes': 'Asymptotic safety of gravity at NGFP yields m_H = 126 ± few '
                 'GeV via gravitational IR fixed-point on lambda. Phase 5z '
                 'Wave 3 cite as a Wetterich-native (elementary Higgs) '
                 'alternative to BHL composite Higgs mechanism. '
                 'doi_verified pending — Elsevier PLB CrossRef + arXiv '
                 '0912.0208 fetch round.',
    },
    'Cvetic1999': {
        'authors': 'Cvetic, G.',
        'title': 'Top quark condensation',
        'journal': 'Rev. Mod. Phys.',
        'volume': 71,
        'page': '513',
        'year': 1999,
        'doi': '10.1103/RevModPhys.71.513',
        'arxiv': 'hep-ph/9702381',
        'doi_verified': None,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Canonical review of top-quark condensation (BHL/MTY/topcolor). '
                 'Documents that the (1,2)_{+1/2} Higgs identification is generic '
                 'to the BHL-class embedding; surveys two-doublet and '
                 'neutrino-condensate extensions. doi_verified pending — APS '
                 'RMP CrossRef + arXiv hep-ph/9702381 fetch round.',
    },
    'PDG2024': {
        'authors': 'Navas, S. et al. (Particle Data Group)',
        'title': 'Review of particle physics',
        'journal': 'Phys. Rev. D',
        'volume': 110,
        'page': '030001',
        'year': 2024,
        'doi': '10.1103/PhysRevD.110.030001',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'PDG 2024 Review of Particle Physics. Source for '
                 'EW.M_W_GEV / M_Z_GEV / M_H_GEV / V_EW_GEV / SIN2_THETA_W / '
                 'G_FERMI_GEV_M2 / Y_TOP / LAMBDA_SM_HIGGS in PARAMETER_PROVENANCE. '
                 'doi_verified 2026-04-26 via pdg.lbl.gov (official PDG '
                 '2024 authors page): title, lead author (S. Navas et al.), '
                 'journal, volume, page, year all match.',
    },
    'PeskinSchroeder': {
        'authors': 'Peskin, M. E., Schroeder, D. V.',
        'title': 'An Introduction to Quantum Field Theory',
        'journal': 'textbook',
        'volume': None,
        'page': None,
        'year': 1995,
        'doi': None,
        'isbn': '978-0201503975',
        'publisher': 'Westview Press',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper20_scalar_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Standard QFT textbook. ISBN-only verification path; '
                 'DOI not applicable. doi_verified 2026-04-26 via OpenLibrary '
                 '(partial record, title and year 1995 match; publisher and '
                 'author list consistent with community-standard knowledge '
                 'of the Peskin-Schroeder text). Publisher blocking of '
                 'Routledge/WorldCat direct WebFetch prevented ISBN-level '
                 'primary-source confirmation. Attribution verdict: '
                 'partial-match; no contradictions found.',
    },

    # ────────────────────────────────────────────────────────────────
    # Phase 5z Wave 2 (paper 21 majorana_rung) — verified 2026-04-25
    # WebFetch round per feedback_citation_verification_required.md.
    # Three corrections applied during the round (see individual notes):
    #   - NuFit60: arXiv ID hallucinated (was 2601.14386, corrected to
    #     2410.05380); author list missing two co-authors and contained one
    #     spurious entry; title corrected.
    #   - Davighi2023 → KawasakiYanagida2023: bibkey rename — arXiv:2304.10100
    #     is by Kawasaki & Yanagida, NOT Davighi-Lohitsiri-Tasnak; published
    #     JHEP 11 (2023) 106 (DOI added).
    #   - Volovik2024Spinor: DOI corrected from 10.1134/S0021364024600293
    #     (404) to 10.1134/S002136402460006X (per NASA ADS + CrossRef).
    # ────────────────────────────────────────────────────────────────
    'NuFit60': {
        'authors': 'Esteban, I., Gonzalez-Garcia, M. C., Maltoni, M., Martinez-Soler, I., Pinheiro, J. P., Schwetz, T.',
        'title': 'NuFit-6.0: Updated global analysis of three-flavor neutrino oscillations',
        'journal': 'JHEP',
        'volume': '12',
        'page': '216',
        'year': 2024,
        'doi': '10.1007/JHEP12(2024)216',
        'arxiv': '2410.05380',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'NuFit-6.0 global three-flavor oscillation fit; source for '
                 'MAJORANA.DELTA_M_SQ_21 / DELTA_M_SQ_31 / THETA_12 / THETA_13 / '
                 'THETA_23 / DELTA_CP. Verified via CrossRef DOI lookup '
                 '2026-04-25 (corrected: arXiv 2601.14386 was a hallucination — '
                 'pointed to a different paper; correct ID is 2410.05380; '
                 'authors corrected to add Martinez-Soler + Pinheiro and remove '
                 'spurious Zhou; title corrected to match published version).',
    },
    'KamLANDZen800': {
        'authors': 'KamLAND-Zen Collaboration (Abe, S. et al.)',
        'title': 'Search for Majorana Neutrinos with the Complete KamLAND-Zen Dataset',
        'journal': 'Phys. Rev. Lett.',
        'volume': 135,
        'page': 262501,
        'year': 2025,
        'doi': '10.1103/jkf6-48j8',
        'arxiv': '2406.11438',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'KamLAND-Zen 800 full-dataset 0νββ search. T_{1/2} > 3.8 × 10²⁶ '
                 'yr at 90% CL; m_ββ < 28-122 meV depending on NME. Published '
                 'as PRL 135, 262501 (2025); arXiv preprint 2406.11438 v2 '
                 '(March 2026). Source for MAJORANA.M_BB_KAMLAND_ZEN_*. '
                 'Verified via arXiv + INSPIRE 2026-04-25 (corrected: prior '
                 'registry entry listed journal=arXiv before PRL publication '
                 'was confirmed in Stage-13 adversarial round).',
    },
    'LEGEND1000': {
        'authors': 'LEGEND Collaboration (Abgrall, N. et al.)',
        'title': 'The Large Enriched Germanium Experiment for Neutrinoless ββ Decay: LEGEND-1000 Preconceptual Design Report',
        'journal': 'arXiv',
        'volume': None,
        'page': None,
        'year': 2021,
        'doi': '10.48550/arXiv.2107.11462',
        'arxiv': '2107.11462',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'LEGEND-1000 PCDR. Projected 99.7% CL discovery sensitivity '
                 'T_{1/2} = 1.3 × 10²⁸ yr; m_ββ = 9-21 meV reach. Covers full '
                 'inverted-ordering parameter space at 10 yr live time. '
                 'Source for MAJORANA.M_BB_LEGEND_*. Verified via arXiv abstract '
                 'page 2026-04-25.',
    },
    'MohapatraSmirnov2006': {
        'authors': 'Mohapatra, R. N., Smirnov, A. Y.',
        'title': 'Neutrino Mass and New Physics',
        'journal': 'Annu. Rev. Nucl. Part. Sci.',
        'volume': 56,
        'page': 569,
        'year': 2006,
        'doi': '10.1146/annurev.nucl.56.080805.140534',
        'arxiv': 'hep-ph/0603118',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'Canonical Type-I seesaw review. Source for the Wave-2 m_ν '
                 'band derivation (m_ν ~ y² v² / M_R) and the M_R = 10⁹-10¹⁵ '
                 'GeV envelope. Cited in deep-research §2.2. Verified via '
                 'CrossRef DOI lookup 2026-04-25 (page range 569-628).',
    },
    'GarciaEtxebarriaMontero2019': {
        'authors': 'García-Etxebarria, I., Montero, M.',
        'title': 'Dai-Freed anomalies in particle physics',
        'journal': 'JHEP',
        'volume': '08',
        'page': '003',
        'year': 2019,
        'doi': '10.1007/JHEP08(2019)003',
        'arxiv': '1808.00009',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py',
                    'lean/SKEFTHawking/Z16AnomalyComputation.lean'],
        'provides': [],
        'notes': 'Garcia-Etxebarria & Montero Dai-Freed anomaly framework: '
                 'sets ν_R = Z₁₆ charge +1, locks Embedding III\'s structural '
                 'choice. Source for MAJORANA.* Z₁₆ context and EW.N_F_WITH_NU_R. '
                 'Verified via CrossRef DOI lookup 2026-04-25.',
    },
    'WanWang2020': {
        'authors': 'Wan, Z., Wang, J.',
        'title': 'Beyond Standard Models and Grand Unifications: Anomalies, Topological Terms, and Dynamical Constraints via Cobordisms',
        'journal': 'JHEP',
        'volume': '07',
        'page': '062',
        'year': 2020,
        'doi': '10.1007/JHEP07(2020)062',
        'arxiv': '1910.14668',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Wan-Wang Ultra-Unification anomaly tower: 15 ≡ -1 mod 16 per '
                 'no-ν_R generation. Verified via CrossRef DOI lookup 2026-04-25.',
    },
    'KawasakiYanagida2023': {
        'authors': 'Kawasaki, M., Yanagida, T. T.',
        'title': 'Dai-Freed anomaly in the standard model and topological inflation',
        'journal': 'JHEP',
        'volume': '11',
        'page': '106',
        'year': 2023,
        'doi': '10.1007/JHEP11(2023)106',
        'arxiv': '2304.10100',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'Kawasaki & Yanagida Dai-Freed-anomaly + topological inflation. '
                 'Embedding III phenomenology consistent with reheating ~10⁸ '
                 'GeV. Verified via arXiv abstract + NASA ADS + CrossRef '
                 '2026-04-25 (corrected: prior bibkey "Davighi2023" was a '
                 'hallucinated author attribution — arXiv 2304.10100 is by '
                 'Kawasaki & Yanagida, published JHEP 11 (2023) 106).',
    },
    'Volovik2024Spinor': {
        'authors': 'Volovik, G. E.',
        'title': 'Fermionic quartet and vestigial gravity',
        'journal': 'JETP Lett.',
        'volume': 119,
        'page': 330,
        'year': 2024,
        'doi': '10.1134/S002136402460006X',
        'arxiv': '2312.09435',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Volovik 2024 fermionic-quartet/vestigial-gravity construction. '
                 'Establishes that ⟨ÊÊ⟩ and ⟨Ê⟩ vanish independently '
                 '(vestigial regime with phase diagram). Cited as motivation '
                 'for WAVE2-OPEN-1 substrate-bridge tracked-hypothesis. '
                 'Verified via NASA ADS + CrossRef 2026-04-25 (corrected DOI: '
                 'prior 10.1134/S0021364024600293 was a 404; correct DOI is '
                 '10.1134/S002136402460006X).',
    },
    'TooBySmithHepLean': {
        'authors': 'Tooby-Smith, J.',
        'title': 'HepLean: Digitalising high energy physics',
        'journal': 'Comput. Phys. Commun.',
        'volume': 308,
        'page': '109457',
        'year': 2025,
        'doi': '10.1016/j.cpc.2024.109457',
        'arxiv': '2405.08863',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/NeutrinoMixing.lean'],
        'provides': [],
        'notes': 'HepLean reference: source for the CKMMatrix structure-note '
                 'idiom mirrored by NeutrinoMixing.PMNSMatrix. Verified via '
                 'CrossRef DOI lookup 2026-04-25.',
    },

    # ────────────────────────────────────────────────────────────────
    # Phase 5z Wave 2b — strengthening citations (verified 2026-04-25)
    # One correction applied:
    #   - AntuschKingmanLindnerWetterich2003 → AntuschKerstenLindnerRatz2003:
    #     bibkey rename — actual authors of arXiv:hep-ph/0211385 are Antusch,
    #     Kersten, Lindner, Ratz (NOT Kingman/Wetterich, which were
    #     hallucinated). Journal-ref Nucl.Phys.B658:203-216 (2003) confirmed.
    # ────────────────────────────────────────────────────────────────
    'AntuschKerstenLindnerRatz2003': {
        'authors': 'Antusch, S., Kersten, J., Lindner, M., Ratz, M.',
        'title': 'Dynamical Electroweak Symmetry Breaking by a Neutrino Condensate',
        'journal': 'Nucl. Phys. B',
        'volume': 658,
        'page': 203,
        'year': 2003,
        'doi': '10.1016/S0550-3213(03)00188-3',
        'arxiv': 'hep-ph/0211385',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRung.lean'],
        'provides': [],
        'notes': 'Source for Wave 2b H_MR_FromADWSubstrate_BCS_LNV form: '
                 'coupled Dirac-Majorana NJL gap equations with M_R as '
                 'external input + supercritical bifurcation. Cited '
                 'verbatim in MajoranaRung §3a for the lepton-number-symmetry '
                 'obstruction theorem. Verified via arXiv abstract 2026-04-25 '
                 '(corrected: prior bibkey "AntuschKingmanLindnerWetterich2003" '
                 'had hallucinated authors — actual authors are Antusch, '
                 'Kersten, Lindner, Ratz; journal-ref Nucl.Phys.B658:203-216 '
                 'confirmed).',
    },
    'AppelquistCarazzone1975': {
        'authors': 'Appelquist, T., Carazzone, J.',
        'title': 'Infrared singularities and massive fields',
        'journal': 'Phys. Rev. D',
        'volume': 11,
        'page': 2856,
        'year': 1975,
        'doi': '10.1103/PhysRevD.11.2856',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRungDecoupling.lean'],
        'provides': [],
        'notes': 'Original Appelquist-Carazzone decoupling theorem. Source '
                 'for Wave 2b WAVE2-OPEN-5 quantitative bound encoding via '
                 'DecouplingRegime + H_DecouplingBoundDim6. Verified via '
                 'CrossRef DOI lookup 2026-04-25 (page range 2856-2861).',
    },
    'BallThorne1994': {
        'authors': 'Ball, R. D., Thorne, R. S.',
        'title': 'The Decoupling Theorem in Effective Scalar Field Theory',
        'journal': 'Ann. Phys.',
        'volume': 241,
        'page': 368,
        'year': 1995,
        'doi': '10.48550/arXiv.hep-th/9404156',
        'arxiv': 'hep-th/9404156',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Wilsonian-EFT rigorous proof of AC decoupling with '
                 'explicit (E/M)^k bounds. Cited as the post-2000 sharper '
                 'AC version that the Wave 2b decoupling encoding follows. '
                 'Verified via arXiv abstract 2026-04-25 (journal-ref '
                 'Ann.Phys.241:368-393, 1995; arXiv preprint April 1994).',
    },
    'GiudiceGrojeanPomarolRattazzi2007': {
        'authors': 'Giudice, G. F., Grojean, C., Pomarol, A., Rattazzi, R.',
        'title': 'The strongly-interacting light Higgs',
        'journal': 'JHEP',
        'volume': '06',
        'page': '045',
        'year': 2007,
        'doi': '10.1088/1126-6708/2007/06/045',
        'arxiv': 'hep-ph/0703164',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRungDecoupling.lean'],
        'provides': [],
        'notes': 'SILH framework: source for naturalC = N_f / (16π²) '
                 'estimate adopted in MajoranaRungDecoupling.naturalC. '
                 'Verified via CrossRef DOI lookup 2026-04-25.',
    },
    'Hill2024Bilocal': {
        'authors': 'Hill, C. T.',
        'title': 'Bilocal Field Theory for Composite Scalar Bosons',
        'journal': 'Entropy',
        'volume': 26,
        'page': 146,
        'year': 2024,
        'doi': '10.3390/e26020146',
        'arxiv': '2310.14750',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRungDecoupling.lean'],
        'provides': [],
        'notes': 'Bilocal NJL form-factor analysis: source for the bound-'
                 'state coefficient form used in Wave 2b naturalC. Verifies '
                 'the SILH counting C ~ N_f / (16π²) for ADW-style four-'
                 'fermion substrates. Verified via CrossRef DOI lookup '
                 '2026-04-25; arXiv ID added 2026-04-25 from INSPIRE-HEP '
                 'after Stage-13 round flagged its omission.',
    },
    'CiriglianoMasterFormula2018': {
        'authors': 'Cirigliano, V., Dekens, W., de Vries, J., Graesser, M. L., Mereghetti, E.',
        'title': 'A neutrinoless double beta decay master formula from effective field theory',
        'journal': 'JHEP',
        'volume': '12',
        'page': '097',
        'year': 2018,
        'doi': '10.1007/JHEP12(2018)097',
        'arxiv': '1806.02780',
        'doi_verified': True,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'SMEFT master formula for 0νββ: rigorous EFT chain LNV → '
                 'SMEFT → LEFT → χEFT → nuclear ME. Cited in Wave 2b '
                 'paper 21 §6 as the canonical reference for the '
                 'embedding-agnostic m_ββ phenomenology. Verified via '
                 'CrossRef DOI lookup 2026-04-25.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 6a Wave 1 (Linearized EFE / induced gravity / classical GR)
    # ════════════════════════════════════════════════════════════════

    'Sakharov1968': {
        'authors': 'Sakharov, A. D.',
        'title': 'Vacuum quantum fluctuations in curved space and the theory of gravitation',
        'journal': 'Sov. Phys. Dokl.',
        'volume': 12,
        'page': '1040',
        'year': 1968,
        'doi': None,
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'Original induced-gravity reference. G_N from vacuum fluctuations, '
                 'G_N⁻¹ ∝ Λ². Foundational; no DOI (Soviet Doklady 1968).',
    },
    'Adler1982': {
        'authors': 'Adler, S. L.',
        'title': 'Einstein gravity as a symmetry-breaking effect in quantum field theory',
        'journal': 'Rev. Mod. Phys.',
        'volume': 54,
        'page': '729',
        'year': 1982,
        'doi': '10.1103/RevModPhys.54.729',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': ['Sakharov-Adler one-loop coefficient: G_N = 12π/(N_f Λ²) '
                     '(Eq. 3.3, hard-cutoff Dirac fermions)'],
        'notes': 'Canonical induced-gravity review. Sets the 12π normalization '
                 'used as the Sakharov-Adler reference value for the ADW α_ADW '
                 'coefficient.',
    },
    'Visser2002': {
        'authors': 'Visser, M.',
        'title': "Sakharov's induced gravity: a modern perspective",
        'journal': 'Mod. Phys. Lett. A',
        'volume': 17,
        'page': '977',
        'year': 2002,
        'doi': '10.1142/S0217732302007289',
        'arxiv': 'gr-qc/0204062',
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'Modern review of Sakharov induced gravity. Emphasizes that the '
                 'numerical coefficient is regulator-dependent; only the existence '
                 'of a finite, sign-definite induced G_N is universal.',
    },
    'Carroll2004': {
        'authors': 'Carroll, S. M.',
        'title': 'Spacetime and Geometry: An Introduction to General Relativity',
        'journal': 'Pearson Addison-Wesley',
        'volume': '',
        'page': 'Ch. 6, 8',
        'year': 2004,
        'doi': None,
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'Standard graduate GR textbook. §6.1 linearized GR (h_μν, '
                 'de Donder gauge, linearized Einstein tensor). §8.4 FLRW '
                 'cosmology / Friedmann equations.',
    },
    'MTW1973': {
        'authors': 'Misner, C. W., Thorne, K. S., Wheeler, J. A.',
        'title': 'Gravitation',
        'journal': 'W. H. Freeman',
        'volume': '',
        'page': 'Ch. 35',
        'year': 1973,
        'doi': None,
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'Canonical GR textbook ("MTW"). Ch. 35 linearized gravity, '
                 'spin-2 wave equation, de Donder gauge.',
    },
    'Tiesinga2021CODATA': {
        'authors': 'Tiesinga, E., Mohr, P. J., Newell, D. B., Taylor, B. N.',
        'title': 'CODATA recommended values of the fundamental physical constants: 2018',
        'journal': 'Rev. Mod. Phys.',
        'volume': 93,
        'page': '025010',
        'year': 2021,
        'doi': '10.1103/RevModPhys.93.025010',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': ['G_N = 6.67430(15) × 10⁻¹¹ m³ kg⁻¹ s⁻² '
                     '(GRAV.G_N_OBS_M3_KGM1_S2)',
                     'M_Planck = 1.220890 × 10¹⁹ GeV (GRAV.M_PLANCK_GEV)'],
        'notes': 'CODATA 2018 recommended values. Source for all fundamental '
                 'constants in the Phase 6a Wave 1 G_N comparison.',
    },
    'Akama1978': {
        'authors': 'Akama, K.',
        'title': 'An Attempt at Pregeometry',
        'journal': 'Prog. Theor. Phys.',
        'volume': 60,
        'page': '1900',
        'year': 1978,
        'doi': '10.1143/PTP.60.1900',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'Original ADW reference: composite metric from fermion bilinear. '
                 'The "A" in ADW (Akama-Diakonov-Wetterich).',
    },
    'HebeckerWetterich2003': {
        'authors': 'Hebecker, A., Wetterich, C.',
        'title': 'Spinor gravity',
        'journal': 'Phys. Lett. B',
        'volume': 574,
        'page': '269',
        'year': 2003,
        'doi': '10.1016/j.physletb.2003.09.010',
        'arxiv': 'hep-th/0307109',
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'Spinor-gravity continuum theory. Identifies new global-Lorentz '
                 'invariants (parameter τ); the absolute prefactor of R/(16πG_N) '
                 'is not extracted in closed form.',
    },
    'Wetterich2022': {
        'authors': 'Wetterich, C.',
        'title': 'Spinor gravity and gauge symmetry',
        'journal': 'JHEP',
        'volume': '06',
        'page': '069',
        'year': 2022,
        'doi': '10.1007/JHEP06(2022)069',
        'arxiv': '2110.11138',
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'Modern Wetterich spinor-gravity formulation; framework setup '
                 'but no closed-form α_ADW.',
    },
    'Volovik2022Counting': {
        'authors': 'Volovik, G. E.',
        'title': 'Effective gravity, Goldstone bosons and pre-geometric phase',
        'journal': 'J. Low Temp. Phys.',
        'volume': 207,
        'page': '127',
        'year': 2022,
        'doi': '10.1007/s10909-022-02694-z',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex'],
        'provides': [],
        'notes': 'NG-mode counting for ADW symmetry breaking: 16 tetrad components → '
                 '6 absorbed + 4 diffeo gauge + 2 graviton + 4 massive Higgs.',
    },
    'Volovik2024Vestigial': {
        'authors': 'Volovik, G. E.',
        'title': 'Vestigial gravity from two-step condensation',
        'journal': 'JETP Lett.',
        'volume': 119,
        'page': '330',
        'year': 2024,
        'doi': '10.1134/S002136402460006X',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper23_linearized_efe/paper_draft.tex',
                    'papers/paper25_gravitational_waves/paper_draft.tex'],
        'provides': [],
        'notes': 'Vestigial gravity: composite ⟨ē e⟩ condenses before tetrad ⟨e⟩. '
                 'Phase 6a Wave 1 derivation is in the fully-condensed phase '
                 'where this distinction is irrelevant. Wave 2 cites for the '
                 'second-sound graviton identification.',
    },
    'Abbott2017GW170817': {
        'authors': 'Abbott, B. P. et al. (LIGO+Virgo+EM partners)',
        'title': 'Gravitational Waves and Gamma-Rays from a Binary Neutron Star '
                 'Merger: GW170817 and GRB 170817A',
        'journal': 'Astrophys. J. Lett.',
        'volume': 848,
        'page': 'L13',
        'year': 2017,
        'doi': '10.3847/2041-8213/aa920c',
        'arxiv': '1710.05834',
        'doi_verified': None,
        'used_in': ['papers/paper25_gravitational_waves/paper_draft.tex'],
        'provides': ['c_GW deviation bound (|Δc/c| ≤ 7e-16/3e-15) '
                     '(GW.C_GW_DEVIATION_UPPER_BOUND, GW.C_GW_DEVIATION_LOWER_BOUND, '
                     'GW.C_GW_TWO_SIDED_CAP)'],
        'notes': 'GW170817 multi-messenger constraint on the GW propagation speed; '
                 'load-bearing for the Phase 6a Wave 2 falsification of the Volovik '
                 'vestigial-second-sound graviton identification.',
    },
    'CrossleyGloriosoLiu2017': {
        'authors': 'Crossley, M. and Glorioso, P. and Liu, H.',
        'title': 'Effective field theory of dissipative fluids',
        'journal': 'JHEP',
        'volume': '09',
        'page': '095',
        'year': 2017,
        'doi': '10.1007/JHEP09(2017)095',
        'arxiv': '1511.03646',
        'doi_verified': True,
        'used_in': ['papers/paper25_gravitational_waves/paper_draft.tex',
                    'papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex',
                    'papers/paper2_second_order/paper_draft.tex'],
        'provides': ['SK-EFT dissipative-fluid framework (Γ_H, dynamical KMS), '
                     'foundation of the SecondOrderSK.lean Γ_H bridge; cited by '
                     'paper27 as constitutive-relations support for Glorioso-Liu '
                     'second law.'],
        'notes': 'Foundational reference for the SK-EFT dissipative-fluid '
                 'effective action. arXiv:1511.03646 verified 2026-04-26.',
    },
    # ──────────────────────────────────────────────────────────────────
    # Phase 6a Wave 3 bibkeys (BH entropy / MTC counting)
    # ──────────────────────────────────────────────────────────────────
    'KaulMajumdar2000': {
        'authors': 'Kaul, R. K. and Majumdar, P.',
        'title': 'Logarithmic Correction to the Bekenstein-Hawking Entropy',
        'journal': 'Phys. Rev. Lett.',
        'volume': 84,
        'page': '5255-5257',
        'year': 2000,
        'doi': '10.1103/PhysRevLett.84.5255',
        'arxiv': 'gr-qc/0002040',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['SU(2)_k Verlinde-formula derivation of S = A/(4G) − (3/2)logA + c0',
                     'I₀ − I₁ singlet-projection cancellation (Lean: '
                     'singletProjectionGivesExtraInverseHessian)'],
        'notes': 'Load-bearing for Wave 3 Kaul-Majumdar SU(2)_k specialization. '
                 'The −3/2 log coefficient is the structural physics result; the '
                 '1/4 prefactor is a γ tuning (`immirziTuning` hypothesis).',
    },
    'Kaul2012Review': {
        'authors': 'Kaul, R. K.',
        'title': 'Entropy of Quantum Black Holes',
        'journal': 'SIGMA',
        'volume': 8,
        'page': '005',
        'year': 2012,
        'doi': '10.3842/SIGMA.2012.005',
        'arxiv': '1201.6102',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Detailed equations for the Kaul-Majumdar SU(2)_k saddle-point',
                     'Eq. (31) magnetic-quantum-number form of the Verlinde sum',
                     'Table 2: Domagala-Lewandowski + Meissner γ values'],
        'notes': 'Comprehensive review with all equations needed for the Wave 3 '
                 'closed-form sub-corollary. Cross-referenced with Kaul-Majumdar 2000.',
    },
    'DomagalaLewandowski2004': {
        'authors': 'Domagala, M. and Lewandowski, J.',
        'title': 'Black-hole entropy from quantum geometry',
        'journal': 'Class. Quantum Grav.',
        'volume': 21,
        'page': '5233-5244',
        'year': 2004,
        'doi': '10.1088/0264-9381/21/22/014',
        'arxiv': 'gr-qc/0407051',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Immirzi γ ≈ 0.2375 from one counting prescription'],
        'notes': 'Distinct counting from Meissner; same −3/2 log coefficient.',
    },
    'Meissner2004': {
        'authors': 'Meissner, K. A.',
        'title': 'Black-hole entropy in loop quantum gravity',
        'journal': 'Class. Quantum Grav.',
        'volume': 21,
        'page': '5245-5252',
        'year': 2004,
        'doi': '10.1088/0264-9381/21/22/015',
        'arxiv': 'gr-qc/0407052',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Immirzi γ ≈ 0.2739 (Wave 3 default)'],
        'notes': 'Recent LQG default. Same −3/2 log coefficient as Domagala-Lewandowski.',
    },
    'EngleNouiPerez2010': {
        'authors': 'Engle, J. and Noui, K. and Perez, A.',
        'title': 'Black hole entropy and SU(2) Chern-Simons theory',
        'journal': 'Phys. Rev. Lett.',
        'volume': 105,
        'page': '031302',
        'year': 2010,
        'doi': '10.1103/PhysRevLett.105.031302',
        'arxiv': '0905.3168',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Independent SU(2) intertwiner derivation of −3/2'],
        'notes': 'Reproduces Kaul-Majumdar coefficient via different counting.',
    },
    'Carlip2000HorizonCFT': {
        'authors': 'Carlip, S.',
        'title': 'Logarithmic corrections to black hole entropy from the Cardy formula',
        'journal': 'Class. Quantum Grav.',
        'volume': 17,
        'page': '4175-4186',
        'year': 2000,
        'doi': '10.1088/0264-9381/17/20/302',
        'arxiv': 'gr-qc/0005017',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Independent Cardy-CFT derivation of the −3/2 log coefficient',
                     'Universality argument within the single-CFT subfamily'],
        'notes': 'Establishes the Cardy-saddle subfamily as the universality class '
                 'where −3/2 holds. Cited for the universality-restriction discussion.',
    },
    'Sen2013Schwarzschild': {
        'authors': 'Sen, A.',
        'title': 'Logarithmic Corrections to Schwarzschild and Other Non-extremal '
                 'Black Hole Entropy in Different Dimensions',
        'journal': 'JHEP',
        'volume': '04',
        'page': 156,
        'year': 2013,
        'doi': '10.1007/JHEP04(2013)156',
        'arxiv': '1205.0971',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Heat-kernel result for 4D Schwarzschild: c_log = +(212/45 − 3) ≈ +1.71',
                     'Explicit disagreement with the Cardy-saddle/Kaul-Majumdar −3/2'],
        'notes': 'Falsifiability anchor — establishes that −3/2 is NOT universal. '
                 'Wave 3 cites this as the witness against universal applicability.',
    },
    'Solodukhin2011LivingRev': {
        'authors': 'Solodukhin, S. N.',
        'title': 'Entanglement entropy of black holes',
        'journal': 'Living Rev. Relativity',
        'volume': 14,
        'page': 8,
        'year': 2011,
        'doi': '10.12942/lrr-2011-8',
        'arxiv': '1104.3712',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Entanglement-entropy origin of S_BH; renormalization of the '
                     '1/4 prefactor as a Sakharov-style induced-G_N condition'],
        'notes': 'Key reference for the Sakharov interpretation of the 1/4 leading '
                 'coefficient as a renormalization condition.',
    },
    'WalkerWang2012': {
        'authors': 'Walker, K. and Wang, Z.',
        'title': '(3+1)-TQFTs and Topological Insulators',
        'journal': 'Frontiers of Physics',
        'volume': 7,
        'page': 150,
        'year': 2012,
        'doi': '10.1007/s11467-011-0194-z',
        'arxiv': '1104.2632',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Walker-Wang 4D TQFT bulk ↔ 3D anomalous SET boundary mapping',
                     'Anomaly-inflow framework for the Z₂-time-reversal-symmetric bulk '
                     '↔ chiral c_- boundary mod 8'],
        'notes': 'Source of the Z₂-time-reversal anomaly-match conjecture for the '
                 'ADW bulk ↔ horizon MTC inflow. Novelty-flagged in Wave 3 paper.',
    },
    'BombelliKoulLeeSorkin1986': {
        'authors': 'Bombelli, L. and Koul, R. K. and Lee, J. and Sorkin, R. D.',
        'title': 'Quantum source of entropy for black holes',
        'journal': 'Phys. Rev. D',
        'volume': 34,
        'page': 373,
        'year': 1986,
        'doi': '10.1103/PhysRevD.34.373',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Original entanglement-entropy origin of A/4G; UV cutoff ε '
                     'as the alternative tuning that fixes 1/4'],
        'notes': 'Foundational. Establishes 1/4 as a UV-cutoff tuning condition '
                 '(parallel to the Immirzi-γ tuning in Kaul-Majumdar).',
    },
    'JacobsonInducedGravity1994': {
        'authors': 'Jacobson, T.',
        'title': 'Black hole entropy and induced gravity',
        'journal': 'arXiv:gr-qc/9404039',
        'volume': '',
        'page': '',
        'year': 1994,
        'doi': None,
        'arxiv': 'gr-qc/9404039',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Sakharov-induced-gravity interpretation of S_BH'],
        'notes': 'Connects 1/4 to the renormalized Newton constant — the bridge '
                 'used by Wave 3 to connect immirziTuning ↔ Wave 1 G_N^emerg.',
    },
    'KitaevHonest2006': {
        'authors': 'Kitaev, A.',
        'title': 'Anyons in an exactly solved model and beyond',
        'journal': 'Annals of Physics',
        'volume': 321,
        'page': '2-111',
        'year': 2006,
        'doi': '10.1016/j.aop.2005.10.005',
        'arxiv': 'cond-mat/0506438',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Anyon-cell counting κ ∝ log d_max; Ising MTC chiral c_-'],
        'notes': 'Used in Wave 3 area-law leading coefficient ansatz.',
    },
    'Mitra2014LogVanish': {
        'authors': 'Mitra, P.',
        'title': 'Black hole entropy with and without log correction in loop quantum gravity',
        'journal': 'Nucl. Phys. B Proc. Suppl.',
        'volume': '251-252',
        'page': 87,
        'year': 2014,
        'doi': '10.1016/j.nuclphysbps.2014.04.016',
        'arxiv': '1406.5524',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Negative result: log correction can vanish in certain LQG counting'],
        'notes': 'Cited as a non-universality witness alongside Sen 2013. '
                 'Title and venue verified via arXiv.org fresh-fetch 2026-04-26 '
                 '(adversarial-review BLOCKER 1.2 fix).',
    },
    'McGoughVerlinde2013': {
        'authors': 'McGough, L. and Verlinde, H.',
        'title': 'Bekenstein-Hawking Entropy as Topological Entanglement Entropy',
        'journal': 'JHEP',
        'volume': '11',
        'page': 208,
        'year': 2013,
        'doi': '10.1007/JHEP11(2013)208',
        'arxiv': '1308.2342',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['Closest published MTC ↔ BH-entropy identification (BTZ via Virasoro)'],
        'notes': 'Cited in Wave 3 as the closest published precedent and as evidence '
                 'that the 4D + ADW + MTC synthesis remains unpublished.',
    },
    'GovindarajanKaulSuneeta2001': {
        'authors': 'Govindarajan, T. R. and Kaul, R. K. and Suneeta, V.',
        'title': 'Logarithmic correction to the Bekenstein-Hawking entropy of the BTZ black hole',
        'journal': 'Class. Quantum Grav.',
        'volume': 18,
        'page': '2877-2886',
        'year': 2001,
        'doi': '10.1088/0264-9381/18/15/303',
        'arxiv': 'gr-qc/0104010',
        'doi_verified': True,
        'used_in': ['papers/paper26_bh_entropy/paper_draft.tex'],
        'provides': ['BTZ −3/2 log correction via Cardy + Chern-Simons path integral'],
        'notes': 'Cited for cross-method −3/2 reproduction (BTZ in 2+1 D vs. '
                 'KaulMajumdar2000 in 3+1 D / SU(2)_k Verlinde). Title and venue '
                 'verified via arXiv.org fresh-fetch 2026-04-26 (adversarial-review '
                 'BLOCKER 1.1 fix; prior bibitem mistakenly named the dS₃ paper).',
    },
    # ──────────────────────────────────────────────────────────────────
    # Phase 6a Wave 5 bibkeys (BCH four laws + regime partition)
    # ──────────────────────────────────────────────────────────────────
    'JacobsonVolovik1998': {
        'authors': 'Jacobson, T. A. and Volovik, G. E.',
        'title': 'Event horizons and ergoregions in 3He',
        'journal': 'Phys. Rev. D',
        'volume': 58,
        'page': '064021',
        'year': 1998,
        'doi': '10.1103/PhysRevD.58.064021',
        'arxiv': 'cond-mat/9801308',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['§VIII prose "cools as it evaporates and approaches an extremal '
                     'black hole" — INCONSISTENT with the same paper\'s own equations: '
                     'back-reaction slows v, so T_H(v) = T_H(0)(1 − v²/c_⊥²) gives '
                     'increasing T_H during evaporation. Cited as the moving-domain-'
                     'wall analog system contrast case.'],
        'notes': 'Wave 5 contrast citation (post-2026-04-26 rewrite). The cooling-'
                 'toward-extremality claim in §VIII is loose prose at odds with the '
                 'paper\'s own math; the actual cooling primary anchor is Balbinot '
                 '2005 (gr-qc/0405098, BEC-acoustic system). TeX source preserved '
                 'at Lit-Search/Phase-6a/primary-sources/jv9801308/.',
    },
    'JacobsonKoike2002': {
        'authors': 'Jacobson, T. A. and Koike, T.',
        'title': 'Black hole and baby universe in a thin film of 3He-A',
        'journal': 'in Artificial Black Holes (World Scientific)',
        'volume': '',
        'page': 'Chapter; Eq. (13)',
        'year': 2002,
        'doi': None,
        'arxiv': 'cond-mat/0205174',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Eq. (13): T_H(v) = T_H(0)·(1 − v²/c_⊥²) for moving-domain-'
                     'wall analog BH in ³He-A. dT_H/dv < 0 monotonically; '
                     'evaporation slows v ⇒ T_H ↑ (heats). Used as the contrast '
                     'case to BEC-acoustic per Balbinot 2005\'s own contrast.'],
        'notes': 'Wave 5 contrast citation (post-2026-04-26 rewrite). Initial Wave 5 '
                 'ship attributed BEC-acoustic cooling-toward-extremality behavior '
                 'to this paper, which actually describes a different analog system '
                 'with opposite (heating) behavior; see Balbinot 2005 §"Fate of the '
                 'acoustic black hole" for the explicit contrast. TeX source '
                 'preserved at Lit-Search/Phase-6a/primary-sources/jk0205174/.',
    },
    'Balbinot2005PRD': {
        'authors': 'Balbinot, R. and Fagnocchi, S. and Fabbri, A.',
        'title': 'Quantum Effects in Acoustic Black Holes: the Backreaction',
        'journal': 'Phys. Rev. D',
        'volume': 71,
        'page': '064019',
        'year': 2005,
        'doi': '10.1103/PhysRevD.71.064019',
        'arxiv': 'gr-qc/0405098',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Eq. (Tsonic): T(t) = (ℏc/2π)·κ·[1 − (563/720π)·ε·κ³·c·A_0·t] '
                     '— linear-in-t cooling under Hawking backreaction in BEC-'
                     'acoustic system. Asymptotic extrapolation t ~ 1/T³ ⇒ T → 0 '
                     'at infinite time (analog of near-extremal RN). Explicit '
                     'contrast statement: "other analog models like a thin film of '
                     '³He-A with a moving domain wall [Jacobson] seem to show a '
                     'non-vanishing end-temperature of the evaporation process." '
                     'PRIMARY ANCHOR for the BEC-acoustic cooling regime in Wave 5.'],
        'notes': 'Wave 5 primary anchor (post-2026-04-26 rewrite). Mirrors '
                 'src/wkb/backreaction.py exponential-decay leading-order form. '
                 'TeX source preserved at Lit-Search/Phase-6a/primary-sources/'
                 'balbinot/.',
    },
    'Hawking1975CMP': {
        'authors': 'Hawking, S. W.',
        'title': 'Particle creation by black holes',
        'journal': 'Commun. Math. Phys.',
        'volume': 43,
        'page': '199-220',
        'year': 1975,
        'doi': '10.1007/BF02345020',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Original derivation of Hawking radiation. T_H = ℏ/(8π M) for '
                     'Schwarzschild; finite evaporation time t_evap ~ M³; during '
                     'evaporation dM/dt < 0 combined with dT_H/dM < 0 gives '
                     'dT_H/dt > 0 (heats as evaporates). PRIMARY ANCHOR for the '
                     'Schwarzschild heating regime in Wave 5.'],
        'notes': 'Wave 5 primary anchor for the Schwarzschild branch. CMP DOI '
                 '10.1007/BF02345020 verified.',
    },
    'Volovik2003BraneBH': {
        'authors': 'Volovik, G. E.',
        'title': 'What can the quantum liquid say on the brane black hole, the '
                 'entropy of extremal black hole and the vacuum energy?',
        'journal': 'Found. Phys.',
        'volume': 33,
        'page': '349-368',
        'year': 2003,
        'doi': '10.1023/A:1023775711831',
        'arxiv': 'gr-qc/0301043',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Horizon fermion zero-mode statistical counting of '
                     'near-extremal analog BH entropy'],
        'notes': 'Wave 5 fermion-zero-mode mechanism support. **Citation correction**: '
                 'Wave 5 deep-research brief originally listed arXiv ID gr-qc/0210034 '
                 'which points to an unrelated paper; the correct ID is gr-qc/0301043 '
                 '(verified via arXiv fresh-fetch 2026-04-26).',
    },
    'KehleUnger2022ThirdLaw': {
        'authors': 'Kehle, C. and Unger, R.',
        'title': 'Gravitational collapse to extremal black holes and the third law '
                 'of black hole thermodynamics',
        'journal': 'J. Eur. Math. Soc.',
        'volume': '(in press)',
        'page': '',
        'year': 2025,
        'doi': '10.4171/JEMS/1591',
        'arxiv': '2211.15742',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Definitive disproof of Israel strong-form third law: '
                     'one-ended Cauchy data forming exactly extremal Reissner-Nordström '
                     'BH in finite advanced time, arbitrarily high regularity'],
        'notes': 'Wave 5 third-law-disproof anchor. Replaces the brief\'s spurious '
                 '"Wall, PRD 100, 044002 (2019)" citation (DOI is Cardoso et al. on '
                 'BH binaries, not a Wall third-law paper). Verified arXiv 2026-04-26.',
    },
    'Reall2024ThirdLawBPS': {
        'authors': 'Reall, H. S.',
        'title': 'A third law of black hole mechanics for supersymmetric black holes '
                 'and a quasi-local mass-charge inequality',
        'journal': 'Phys. Rev. D',
        'volume': 110,
        'page': '124059',
        'year': 2024,
        'doi': '10.1103/PhysRevD.110.124059',
        'arxiv': '2410.11956',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['BPS local mass-charge restoration of the third law: '
                     'matter satisfying T_{ab} k^a k^b ≥ |J^a k_a| forbids '
                     'finite-time formation of extremal RN'],
        'notes': 'Wave 5 third-law-restoration condition (under BPS hypothesis). '
                 'Verified via arXiv 2026-04-26.',
    },
    'GloriosoCrossleyLiu2017': {
        'authors': 'Glorioso, P. and Crossley, M. and Liu, H.',
        'title': 'Effective field theory for dissipative fluids (II): classical limit, '
                 'dynamical KMS symmetry and entropy current',
        'journal': 'JHEP',
        'volume': '09',
        'page': '096',
        'year': 2017,
        'doi': '10.1007/JHEP09(2017)096',
        'arxiv': '1701.07817',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Constitutive relations for the SK-EFT entropy current via '
                     'dynamical KMS Z₂ symmetry; Eq. 6.34'],
        'notes': 'Wave 5 ADWSecondLaw constitutive-relation source.',
    },
    'WallGSL2012': {
        'authors': 'Wall, A. C.',
        'title': 'A proof of the generalized second law for rapidly changing fields '
                 'and arbitrary horizon slices',
        'journal': 'Phys. Rev. D',
        'volume': 85,
        'page': '104049',
        'year': 2012,
        'doi': '10.1103/PhysRevD.85.104049',
        'arxiv': '1105.3445',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['GSL proof via relative-entropy monotonicity for arbitrary '
                     'horizon slices; foundational for the algebraic GSL'],
        'notes': 'Wave 5 GSL anchor.',
    },
    'BoussoFisherLeichenauerWall2016': {
        'authors': 'Bousso, R. and Fisher, Z. and Leichenauer, S. and Wall, A. C.',
        'title': 'A Quantum Focussing Conjecture',
        'journal': 'Phys. Rev. D',
        'volume': 93,
        'page': '064044',
        'year': 2016,
        'doi': '10.1103/PhysRevD.93.064044',
        'arxiv': '1506.02669',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Quantum Focussing Conjecture (QFC) → Quantum Null Energy '
                     'Condition (QNEC) → local GSL (semiclassical regime)'],
        'notes': 'Wave 5 QNEC anchor.',
    },
    'HartmanKunduTajdini2017': {
        'authors': 'Hartman, T. and Kundu, S. and Tajdini, A.',
        'title': 'Averaged Null Energy Condition from Causality',
        'journal': 'JHEP',
        'volume': '07',
        'page': '066',
        'year': 2017,
        'doi': '10.1007/JHEP07(2017)066',
        'arxiv': '1610.05308',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['ANEC ∫⟨T_kk⟩dλ ≥ 0 from microcausality (commutators '
                     'vanishing at spacelike separation)'],
        'notes': 'Wave 5 ANEC anchor; supplies topological-censorship + '
                 'achronal area-non-decrease.',
    },
    'FaulknerSperanza2024': {
        'authors': 'Faulkner, T. and Speranza, A. J.',
        'title': 'Gravitational algebras and the generalized second law',
        'journal': 'JHEP',
        'volume': '11',
        'page': '099',
        'year': 2024,
        'doi': '10.1007/JHEP11(2024)099',
        'arxiv': '2405.00847',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['GSL derivation via type-II crossed-product algebras of '
                     'observables; semiclassical limit reproduces generalized entropy'],
        'notes': 'Wave 5 algebraic-GSL anchor.',
    },
    'Kirklin2024GSLAllOrders': {
        'authors': 'Kirklin, J.',
        'title': 'Generalised second law beyond the semiclassical regime',
        'journal': 'JHEP',
        'volume': '07',
        'page': '192',
        'year': 2025,
        'doi': '10.1007/JHEP07(2025)192',
        'arxiv': '2412.01903',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['GSL extended to all orders in perturbative gravity '
                     'via algebraic methods + null-translation invariance'],
        'notes': 'Wave 5: deep-research-brief attribution to "Belin et al" '
                 'corrected via arXiv fresh-fetch 2026-04-26 — actual single '
                 'author is Josh Kirklin. **Citation-hallucination flag** '
                 'logged per `feedback_citation_verification_required.md`.',
    },
    'WallSurvey2018': {
        'authors': 'Wall, A. C.',
        'title': 'A Survey of Black Hole Thermodynamics',
        'journal': 'arXiv:1804.10610',
        'volume': '',
        'page': '',
        'year': 2018,
        'doi': None,
        'arxiv': '1804.10610',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Pedagogical survey of the four laws of BH thermodynamics + '
                     'horizon-definition variants + entropy correction status'],
        'notes': 'Wave 5: replaces the brief\'s spurious "Wall, PRD 100, 044002 (2019)" '
                 'citation. Verified via arXiv 2026-04-26.',
    },
    'KubiznakMann2012PV': {
        'authors': 'Kubizňák, D. and Mann, R. B.',
        'title': 'P-V criticality of charged AdS black holes',
        'journal': 'JHEP',
        'volume': '07',
        'page': '033',
        'year': 2012,
        'doi': '10.1007/JHEP07(2012)033',
        'arxiv': '1205.0559',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Universal vdW ratio P_c v_c / T_c = 3/8 for charged AdS BHs; '
                     'enthalpic-extension first law M ↔ enthalpy, Λ ↔ pressure'],
        'notes': 'Wave 5: structural precedent for substrate-pressure first-law '
                 'correction (alternative branch of H_RegimePartition).',
    },
    'Witten1998AdSThermal': {
        'authors': 'Witten, E.',
        'title': 'Anti-de Sitter Space, Thermal Phase Transition, And Confinement '
                 'In Gauge Theories',
        'journal': 'Adv. Theor. Math. Phys.',
        'volume': 2,
        'page': '505-532',
        'year': 1998,
        'doi': '10.4310/ATMP.1998.v2.n3.a3',
        'arxiv': 'hep-th/9803131',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Hawking-Page transition r_+ = l, T_HP = 1/(πl); '
                     'small-BH/large-BH fold; gauge-theory confinement dual'],
        'notes': 'Wave 5: AdS-extension first-order transition (Branch C of §4).',
    },
    'HawkingHorowitzRoss1995': {
        'authors': 'Hawking, S. W. and Horowitz, G. T. and Ross, S. F.',
        'title': 'Entropy, Area, and Black Hole Pairs',
        'journal': 'Phys. Rev. D',
        'volume': 51,
        'page': '4302-4314',
        'year': 1995,
        'doi': '10.1103/PhysRevD.51.4302',
        'arxiv': 'gr-qc/9409013',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Extremal RN has S = 0 by Euler-character argument; '
                     'extremal/non-extremal qualitatively distinct; '
                     'strong Nernst preserved'],
        'notes': 'Wave 5 weak/strong-Nernst dichotomy anchor.',
    },
    'Sen2008EntropyFunction': {
        'authors': 'Sen, A.',
        'title': 'Entropy Function and AdS(2)/CFT(1) Correspondence',
        'journal': 'JHEP',
        'volume': '11',
        'page': '075',
        'year': 2008,
        'doi': '10.1088/1126-6708/2008/11/075',
        'arxiv': '0805.0095',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Wald entropy of extremal BH = log of ground-state degeneracy '
                     'of AdS₂ boundary 1D quantum mechanics; attractor mechanism '
                     'independent of Nernst question'],
        'notes': 'Wave 5: Strominger-Vafa-side-of-Nernst anchor.',
    },
    'BhattacharyaShankaranarayanan2017': {
        'authors': 'Bhattacharya, S. and Shankaranarayanan, S.',
        'title': 'Negative specific heat of black-holes from Fluid-Gravity Correspondence',
        'journal': 'Class. Quantum Grav.',
        'volume': 34,
        'page': '015009',
        'year': 2017,
        'doi': '10.1088/0264-9381/34/1/015009',
        'arxiv': '1702.03682',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['C-sign change between asymptotic-flat (C < 0) and '
                     'Kerr-Newman/AdS (C > 0) regimes via horizon-fluid linear response'],
        'notes': 'Wave 5: structural analog for the regime-partition C-sign-flip.',
    },
    'BrownIliesiuPeningtonUsatyuk2024': {
        'authors': 'Brown, A. R. and Iliesiu, L. V. and Penington, G. and Usatyuk, M.',
        'title': 'The evaporation of charged black holes',
        'journal': 'arXiv:2411.03447',
        'volume': '',
        'page': '',
        'year': 2024,
        'doi': None,
        'arxiv': '2411.03447',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['JT/Schwarzian-corrected near-extremal BH evaporation; '
                     'explicit quantum mass gap; entangled-photon-pair emission'],
        'notes': 'Wave 5: near-extremal-evaporation precedent supporting the '
                 'first-law correction at the regime boundary.',
    },
    'Padmanabhan2010Equipartition': {
        'authors': 'Padmanabhan, T.',
        'title': 'Equipartition of energy in the horizon degrees of freedom and '
                 'the emergence of gravity',
        'journal': 'Mod. Phys. Lett. A',
        'volume': 25,
        'page': '1129-1136',
        'year': 2010,
        'doi': '10.1142/S0217732310033554',
        'arxiv': '0912.3165',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Horizon-DOF equipartition first law E = ½ N k_B T with '
                     'N = ΔA/L_P²'],
        'notes': 'Wave 5: emergent-gravity first-law structural precedent.',
    },
    'Verlinde2011Entropic': {
        'authors': 'Verlinde, E. P.',
        'title': 'On the Origin of Gravity and the Laws of Newton',
        'journal': 'JHEP',
        'volume': '04',
        'page': '029',
        'year': 2011,
        'doi': '10.1007/JHEP04(2011)029',
        'arxiv': '1001.0785',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Newtonian gravity as an entropic force from holographic '
                     'screen entropy gradients'],
        'notes': 'Wave 5: emergent-gravity precedent for thermodynamics-driven '
                 'gravitational dynamics.',
    },
    'JacobsonEFE1995': {
        'authors': 'Jacobson, T.',
        'title': 'Thermodynamics of Spacetime: The Einstein Equation of State',
        'journal': 'Phys. Rev. Lett.',
        'volume': 75,
        'page': '1260-1263',
        'year': 1995,
        'doi': '10.1103/PhysRevLett.75.1260',
        'arxiv': 'gr-qc/9504004',
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Einstein equations derived from Clausius relation '
                     'TdS = δQ at every local Rindler horizon'],
        'notes': 'Wave 5: emergent-gravity foundational precedent.',
    },
    'Davies1977': {
        'authors': 'Davies, P. C. W.',
        'title': 'The Thermodynamic Theory of Black Holes',
        'journal': 'Proc. R. Soc. A',
        'volume': 353,
        'page': '499-521',
        'year': 1977,
        'doi': '10.1098/rspa.1977.0047',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Kerr (J/M²)_c = √(2√3 − 3) ≈ 0.6814 sign-flip; '
                     'RN (Q/M)_c = √3/2 ≈ 0.8660 sign-flip'],
        'notes': 'Wave 5: classical-GR sign-flip canonical reference. Pre-arXiv.',
    },
    'HawkingPage1983': {
        'authors': 'Hawking, S. W. and Page, D. N.',
        'title': 'Thermodynamics of Black Holes in Anti-de Sitter Space',
        'journal': 'Commun. Math. Phys.',
        'volume': 87,
        'page': '577-588',
        'year': 1983,
        'doi': '10.1007/BF01208266',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Hawking-Page transition between thermal AdS and large-BH-AdS'],
        'notes': 'Wave 5: AdS-extension Branch C precedent. Pre-arXiv.',
    },
    'Israel1986ThirdLaw': {
        'authors': 'Israel, W.',
        'title': 'Third Law of Black-Hole Dynamics: A Formulation and Proof',
        'journal': 'Phys. Rev. Lett.',
        'volume': 57,
        'page': '397-399',
        'year': 1986,
        'doi': '10.1103/PhysRevLett.57.397',
        'arxiv': None,
        'doi_verified': True,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Strong-form third law: κ → 0 in finite affine time impossible '
                     '(under classical-GR / no-charge-scalar-matter assumption)'],
        'notes': 'Wave 5: classical third-law anchor. Pre-arXiv. '
                 'Subsequently disproved in full generality by Kehle-Unger 2022.',
    },
    'Dymnikova2018Universe': {
        'authors': 'Dymnikova, I.',
        'title': 'The Higgs Mechanism and Cosmological Constant Today',
        'journal': 'Universe',
        'volume': 4,
        'page': 63,
        'year': 2018,
        'doi': '10.3390/universe4050063',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'],
        'provides': ['Explicit C-sign-flip at T_max with cooling to zero-T '
                     'double-horizon remnant in Padmanabhan emergent-gravity formalism'],
        'notes': 'Wave 5: closest published structural analog of the ADW cooling '
                 'regime. MDPI direct fetch returned 403; deferred WebFetch '
                 'verification to authorized round.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 6c — Holographic / QEC bridges (Wave 4 + Wave 5)
    # ════════════════════════════════════════════════════════════════

    'HaydenPreskill2007': {
        'authors': 'Hayden, P., Preskill, J.',
        'title': 'Black holes as mirrors: quantum information in random subsystems',
        'journal': 'JHEP',
        'volume': '09',
        'page': '120',
        'year': 2007,
        'doi': '10.1088/1126-6708/2007/09/120',
        'arxiv': '0708.4025',
        'doi_verified': None,
        'used_in': [
            'papers/paper35_qec_holography/paper_draft.tex',
            'papers/note_rt_ch_bounds/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Information-recovery scrambling-time bound; foundational for '
                 'holographic-QEC bridge and W4 substrate observables.',
    },
    'RyuTakayanagi2006': {
        'authors': 'Ryu, S., Takayanagi, T.',
        'title': 'Holographic derivation of entanglement entropy from anti-de Sitter '
                 'space/conformal field theory correspondence',
        'journal': 'Phys. Rev. Lett.',
        'volume': 96,
        'page': '181602',
        'year': 2006,
        'doi': '10.1103/PhysRevLett.96.181602',
        'arxiv': 'hep-th/0603001',
        'doi_verified': None,
        'used_in': [
            'papers/note_rt_ch_bounds/paper_draft.tex',
        ],
        'provides': ['RT formula: S = A/(4 G_N)'],
        'notes': 'Original RT proposal: holographic entanglement entropy as '
                 'minimal-surface area divided by 4 G_N.',
    },
    'CasiniHuerta2009': {
        'authors': 'Casini, H., Huerta, M.',
        'title': 'Entanglement entropy in free quantum field theory',
        'journal': 'J. Phys. A',
        'volume': 42,
        'page': '504007',
        'year': 2009,
        'doi': '10.1088/1751-8113/42/50/504007',
        'arxiv': '0905.2562',
        'doi_verified': None,
        'used_in': [
            'papers/note_rt_ch_bounds/paper_draft.tex',
        ],
        'provides': ['Free-QFT specialization of the (c/3) log(L/eps) entanglement bound'],
        'notes': 'Rigorous free-QFT specialization of the universal 2D-CFT entanglement bound. SCOPE NOTE (added 2026-04-29): the universal 2D-CFT bound for arbitrary CFTs is from Holzhey-Larsen-Wilczek 1994 and Calabrese-Cardy 2004; this paper derives the rigorous result for free QFTs. The Lean predicate H_CasiniHuerta_Bound_Valid retains the historical "Casini-Huerta" naming for compatibility but the universal-bound attribution belongs to HolzheyLarsenWilczek1994 + CalabreseCardy2004.',
    },
    'HolzheyLarsenWilczek1994': {
        'authors': 'Holzhey, C., Larsen, F., Wilczek, F.',
        'title': 'Geometric and renormalized entropy in conformal field theory',
        'journal': 'Nucl. Phys. B',
        'volume': 424,
        'page': '443',
        'year': 1994,
        'doi': '10.1016/0550-3213(94)90402-2',
        'arxiv': 'hep-th/9403108',
        'doi_verified': '2026-04-29',  # Added 2026-04-29 to correct CH-attribution; arXiv hep-th/9403108 confirmed
        'used_in': [
            'papers/note_rt_ch_bounds/paper_draft.tex',
        ],
        'provides': ['Universal 2D-CFT entanglement-entropy log bound: S(L) <= (c/3) log(L/eps)'],
        'notes': 'Original derivation of the universal 2D-CFT entanglement-entropy log bound. Added 2026-04-29 to correct earlier mis-attribution of this bound to CasiniHuerta2009.',
    },
    'CalabreseCardy2004': {
        'authors': 'Calabrese, P., Cardy, J.',
        'title': 'Entanglement entropy and quantum field theory',
        'journal': 'J. Stat. Mech.',
        'volume': '0406',
        'page': 'P06002',
        'year': 2004,
        'doi': '10.1088/1742-5468/2004/06/P06002',
        'arxiv': 'hep-th/0405152',
        'doi_verified': '2026-04-29',  # Added 2026-04-29 to correct CH-attribution; arXiv hep-th/0405152 confirmed
        'used_in': [
            'papers/note_rt_ch_bounds/paper_draft.tex',
        ],
        'provides': ['Universal 2D-CFT entanglement-entropy log bound: S(L) <= (c/3) log(L/eps)'],
        'notes': 'Independent derivation of the universal 2D-CFT entanglement-entropy log bound via replica trick. Added 2026-04-29 to correct earlier mis-attribution of this bound to CasiniHuerta2009.',
    },
    'LewkowyczMaldacena2013': {
        'authors': 'Lewkowycz, A., Maldacena, J.',
        'title': 'Generalized gravitational entropy',
        'journal': 'JHEP',
        'volume': '08',
        'page': '090',
        'year': 2013,
        'doi': '10.1007/JHEP08(2013)090',
        'arxiv': '1304.4926',
        'doi_verified': None,
        'used_in': [
            'papers/note_rt_ch_bounds/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Replica-trick proof of RT formula; bulk minimal-surface construction.',
    },
    'AlmheiriDongHarlow2015': {
        'authors': 'Almheiri, A., Dong, X., Harlow, D.',
        'title': 'Bulk locality and quantum error correction in AdS/CFT',
        'journal': 'JHEP',
        'volume': '04',
        'page': '163',
        'year': 2015,
        'doi': '10.1007/JHEP04(2015)163',
        'arxiv': '1411.7041',
        'doi_verified': None,
        'used_in': [
            'papers/paper35_qec_holography/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Bulk locality as quantum error correction; foundational for '
                 'holographic-QEC interpretation.',
    },
    'PYHP2015': {
        'authors': 'Pastawski, F., Yoshida, B., Harlow, D., Preskill, J.',
        'title': 'Holographic quantum error-correcting codes: toy models for the '
                 'bulk/boundary correspondence',
        'journal': 'JHEP',
        'volume': '06',
        'page': '149',
        'year': 2015,
        'doi': '10.1007/JHEP06(2015)149',
        'arxiv': '1503.06237',
        'doi_verified': None,
        'used_in': [
            'papers/paper35_qec_holography/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'HaPPY codes: explicit holographic-QEC tensor-network construction.',
    },
    'YoshidaKitaev2017': {
        'authors': 'Yoshida, B., Kitaev, A.',
        'title': 'Efficient decoding for the Hayden-Preskill protocol',
        'journal': 'arXiv preprint',
        'volume': None,
        'page': None,
        'year': 2017,
        'doi': None,
        'arxiv': '1710.03363',
        'doi_verified': None,
        'used_in': [
            'papers/paper35_qec_holography/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Decoder construction for Hayden-Preskill recovery; deferred in W4 scope.',
    },
    'KitaevAnyons2003': {
        'authors': 'Kitaev, A. Yu.',
        'title': 'Fault-tolerant quantum computation by anyons',
        'journal': 'Annals Phys.',
        'volume': 303,
        'page': '2',
        'year': 2003,
        'doi': '10.1016/S0003-4916(02)00018-0',
        'arxiv': 'quant-ph/9707021',
        'doi_verified': None,
        'used_in': [
            'papers/paper35_qec_holography/paper_draft.tex',
            'papers/paper36_center_symmetry/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Anyonic-substrate fault-tolerant computation; foundational for '
                 'topological-QEC framework.',
    },
    'NayakAnyons2008': {
        'authors': 'Nayak, C., Simon, S. H., Stern, A., Freedman, M., Das Sarma, S.',
        'title': 'Non-Abelian anyons and topological quantum computation',
        'journal': 'Rev. Mod. Phys.',
        'volume': 80,
        'page': '1083',
        'year': 2008,
        'doi': '10.1103/RevModPhys.80.1083',
        'arxiv': '0707.1889',
        'doi_verified': None,
        'used_in': [
            'papers/paper35_qec_holography/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Comprehensive review of non-abelian anyons and topological QC.',
    },
    'KitaevPreskill2006': {
        'authors': 'Kitaev, A., Preskill, J.',
        'title': 'Topological entanglement entropy',
        'journal': 'Phys. Rev. Lett.',
        'volume': 96,
        'page': '110404',
        'year': 2006,
        'doi': '10.1103/PhysRevLett.96.110404',
        'arxiv': 'hep-th/0510092',
        'doi_verified': None,
        'used_in': [
            'papers/paper35_qec_holography/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Topological entanglement entropy: gamma = log D for total quantum dimension D.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 6c — Strong-CP / dark-energy bridge (Wave 1)
    # ════════════════════════════════════════════════════════════════

    'KlinkhamerVolovik2010': {
        'authors': 'Klinkhamer, F. R., Volovik, G. E.',
        'title': 'Towards a solution of the cosmological constant problem',
        'journal': 'JETP Lett.',
        'volume': 91,
        'page': '259',
        'year': 2010,
        'doi': '10.1134/S0021364010050094',
        'arxiv': '0907.4887',
        'doi_verified': '2026-04-29',  # WebFetch arXiv:0907.4887 confirmed title (paper32 adversarial 2026-04-29)
        'used_in': [
            'papers/paper32_strong_cp_de/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'q-theory framework for cosmological-constant relaxation. Title corrected 2026-04-29 (was "Cosmological constant from gravitating Skyrmions" — that is a different paper) per WebFetch verification of arXiv:0907.4887.',
    },
    'Pendlebury2015': {
        'authors': 'Pendlebury, J. M., et al.',
        'title': 'Revised experimental upper limit on the electric dipole moment '
                 'of the neutron',
        'journal': 'Phys. Rev. D',
        'volume': 92,
        'page': '092003',
        'year': 2015,
        'doi': '10.1103/PhysRevD.92.092003',
        'arxiv': '1509.04411',
        'doi_verified': None,
        'used_in': [
            'papers/paper32_strong_cp_de/paper_draft.tex',
        ],
        'provides': ['Neutron EDM upper bound: |theta_QCD| <= 1e-9 (current strongest)'],
        'notes': 'Strongest current bound on the QCD theta-angle via neutron EDM.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 6c — Equivalence-principle classification (Wave 3)
    # ════════════════════════════════════════════════════════════════

    'Touboul2017': {
        'authors': 'Touboul, P., et al.',
        'title': 'MICROSCOPE Mission: First Results of a Space Test of the Equivalence Principle',
        'journal': 'Phys. Rev. Lett.',
        'volume': 119,
        'page': '231101',
        'year': 2017,
        'doi': '10.1103/PhysRevLett.119.231101',
        'arxiv': '1712.01176',
        'doi_verified': None,
        'used_in': [
            'papers/paper34_equivalence_principle/paper_draft.tex',
        ],
        'provides': ['MICROSCOPE WEP bound: |eta| < 1e-15'],
        'notes': 'First-results MICROSCOPE EP bound. Final 2022 result improves to ~1e-15 systematic.',
    },
    'Will2018': {
        'authors': 'Will, C. M.',
        'title': 'Theory and Experiment in Gravitational Physics (2nd ed.)',
        'journal': 'Cambridge University Press',
        'volume': None,
        'page': None,
        'year': 2018,
        'doi': '10.1017/9781316338612',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'papers/paper34_equivalence_principle/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Standard reference for EP-test taxonomy and PPN parameter framework.',
    },
    'Berezhiani2015': {
        'authors': 'Berezhiani, L., Khoury, J.',
        'title': 'Theory of dark matter superfluidity',
        'journal': 'Phys. Rev. D',
        'volume': 92,
        'page': '103510',
        'year': 2015,
        'doi': '10.1103/PhysRevD.92.103510',
        'arxiv': '1507.01019',
        'doi_verified': None,
        'used_in': [
            'papers/paper34_equivalence_principle/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Superfluid dark matter (SFDM) with Thomas-Fermi condensate phenomenology.',
    },

    # ════════════════════════════════════════════════════════════════
    # Phase 6d — QCD center symmetry / chiral SSB / CFL
    # ════════════════════════════════════════════════════════════════

    'Polyakov1978': {
        'authors': 'Polyakov, A. M.',
        'title': 'Thermal properties of gauge fields and quark liberation',
        'journal': 'Phys. Lett. B',
        'volume': 72,
        'page': '477',
        'year': 1978,
        'doi': '10.1016/0370-2693(78)90737-2',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'papers/paper36_center_symmetry/paper_draft.tex',
            'papers/paper38_cfl/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Original Polyakov-loop construction and deconfinement order parameter.',
    },
    'SvetitskyYaffe1982': {
        'authors': 'Svetitsky, B., Yaffe, L. G.',
        'title': 'Critical behavior at finite-temperature confinement transitions',
        'journal': 'Nucl. Phys. B',
        'volume': 210,
        'page': '423',
        'year': 1982,
        'doi': '10.1016/0550-3213(82)90172-9',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'papers/paper36_center_symmetry/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Svetitsky-Yaffe universality conjecture: SU(N) deconfinement = '
                 'lower-dimensional Z_N spin model.',
    },
    'PelissettoVicari2002': {
        'authors': 'Pelissetto, A., Vicari, E.',
        'title': 'Critical phenomena and renormalization-group theory',
        'journal': 'Phys. Rep.',
        'volume': 368,
        'page': '549',
        'year': 2002,
        'doi': '10.1016/S0370-1573(02)00219-3',
        'arxiv': 'cond-mat/0012164',
        'doi_verified': None,
        'used_in': [
            'papers/paper36_center_symmetry/paper_draft.tex',
        ],
        'provides': ['3D Ising nu = 0.6299', '3D 3-state Potts nu = 0.5'],
        'notes': 'Standard reference for critical exponents in 3D Ising and Potts universality classes.',
    },
    'KosPolandSimmonsDuffin2016': {
        'authors': 'Kos, F., Poland, D., Simmons-Duffin, D., Vichi, A.',
        'title': 'Precision islands in the Ising and O(N) models',
        'journal': 'JHEP',
        'volume': '08',
        'page': '036',
        'year': 2016,
        'doi': '10.1007/JHEP08(2016)036',
        'arxiv': '1603.04436',
        'doi_verified': '2026-04-29',  # WebFetch arXiv:1603.04436 confirmed (paper36 adversarial 2026-04-29)
        'used_in': [
            'papers/paper36_center_symmetry/paper_draft.tex',
        ],
        'provides': ['3D Ising nu = 0.6299709 (KPSDV bootstrap, 2016)'],
        'notes': 'Conformal bootstrap precision values for 3D Ising universality class. Title + author count + venue corrected 2026-04-29 (was wrongly listed as 3-author "Bootstrapping the O(N) archipelago" JHEP 03:086) per WebFetch verification of arXiv:1603.04436. Bibkey retained for backwards compatibility despite missing fourth-author Vichi.',
    },
    'KovtunSonStarinets2005': {
        'authors': 'Kovtun, P., Son, D. T., Starinets, A. O.',
        'title': 'Viscosity in strongly interacting quantum field theories from black hole physics',
        'journal': 'Phys. Rev. Lett.',
        'volume': 94,
        'page': '111601',
        'year': 2005,
        'doi': '10.1103/PhysRevLett.94.111601',
        'arxiv': 'hep-th/0405231',
        'doi_verified': None,
        'used_in': [
            'papers/paper36_center_symmetry/paper_draft.tex',
        ],
        'provides': ['KSS bound: eta/s >= 1/(4 pi)'],
        'notes': 'KSS holographic lower bound on shear-viscosity-to-entropy-density ratio.',
    },
    'HofmanIqbal2018': {
        'authors': 'Hofman, D. M., Iqbal, N.',
        'title': 'Generalized global symmetries and holography',
        'journal': 'SciPost Phys.',
        'volume': '4',
        'page': '005',
        'year': 2018,
        'doi': '10.21468/SciPostPhys.4.1.005',
        'arxiv': '1707.08577',
        'doi_verified': '2026-04-29',  # WebFetch arXiv:1707.08577 confirmed (paper36 adversarial 2026-04-29)
        'used_in': [
            'papers/paper36_center_symmetry/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Holographic generalized global symmetries; framework for higher-form symmetries in transport. Title corrected 2026-04-29 (was "Goldstone modes and photonization for higher form symmetries" — that is a different/related paper) per WebFetch verification of arXiv:1707.08577.',
    },
    'WalkerWang2012': {
        'authors': 'Walker, K., Wang, Z.',
        'title': '(3+1)-TQFTs and topological insulators',
        'journal': 'Front. Phys.',
        'volume': 7,
        'page': '150',
        'year': 2012,
        'doi': '10.1007/s11467-011-0194-z',
        'arxiv': '1104.2632',
        'doi_verified': '2026-04-29',  # WebFetch arXiv:1104.2632 confirmed (newly added 2026-04-29)
        'used_in': [
            'papers/paper36_center_symmetry/paper_draft.tex',
        ],
        'provides': ['Walker-Wang TQFTs hosting (3+1)-D anyon-line excitations'],
        'notes': 'Walker-Wang (3+1)-dimensional TQFT framework: provides the topological-phase context the paper invokes for the Walker-Wang anyon-mediated transport modelling assumption (no transport prediction is derived from this reference; the [KSS, 2*KSS] bracket is project-originated).',
    },
    'NambuJonaLasinio1961': {
        'authors': 'Nambu, Y., Jona-Lasinio, G.',
        'title': 'Dynamical model of elementary particles based on an analogy with superconductivity. I.',
        'journal': 'Phys. Rev.',
        'volume': 122,
        'page': '345',
        'year': 1961,
        'doi': '10.1103/PhysRev.122.345',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'papers/paper37_chiral_ssb/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Original NJL model: dynamical chiral symmetry breaking by four-fermion interaction.',
    },
    'GMOR1968': {
        'authors': 'Gell-Mann, M., Oakes, R. J., Renner, B.',
        'title': 'Behavior of current divergences under SU(3) x SU(3)',
        'journal': 'Phys. Rev.',
        'volume': 175,
        'page': '2195',
        'year': 1968,
        'doi': '10.1103/PhysRev.175.2195',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'papers/paper37_chiral_ssb/paper_draft.tex',
        ],
        'provides': ['GMOR relation: m_pi^2 f_pi^2 = -2 m_q <q-bar q>'],
        'notes': 'Gell-Mann-Oakes-Renner relation between pion mass, decay constant, and quark condensate.',
    },
    'FLAG2021': {
        'authors': 'Aoki, Y., et al. (Flavour Lattice Averaging Group)',
        'title': 'FLAG Review 2021',
        'journal': 'Eur. Phys. J. C',
        'volume': 82,
        'page': '869',
        'year': 2022,
        'doi': '10.1140/epjc/s10052-022-10536-1',
        'arxiv': '2111.09849',
        'doi_verified': None,
        'used_in': [
            'papers/paper37_chiral_ssb/paper_draft.tex',
        ],
        'provides': ['Lattice quark condensate <q-bar q> ≈ -(283 MeV)^3 ≈ -0.0227 GeV^3'],
        'notes': 'Lattice-QCD averages including chiral condensate and decay constants.',
    },
    'PDG2022': {
        'authors': 'Workman, R. L., et al. (Particle Data Group)',
        'title': 'Review of Particle Physics',
        'journal': 'Prog. Theor. Exp. Phys.',
        'volume': 2022,
        'page': '083C01',
        'year': 2022,
        'doi': '10.1093/ptep/ptac097',
        'arxiv': None,
        'doi_verified': None,
        'used_in': [
            'papers/paper37_chiral_ssb/paper_draft.tex',
        ],
        'provides': ['m_pi = 0.137 GeV', 'f_pi = 0.092 GeV', 'Lambda_QCD ~ 0.1 GeV'],
        'notes': 'Particle Data Group 2022 release; central values for hadron spectroscopy.',
    },
    'AlfordRajagopalWilczek1999': {
        'authors': 'Alford, M. G., Rajagopal, K., Wilczek, F.',
        'title': 'Color-flavor locking and chiral symmetry breaking in high density QCD',
        'journal': 'Nucl. Phys. B',
        'volume': 537,
        'page': '443',
        'year': 1999,
        'doi': '10.1016/S0550-3213(98)00668-3',
        'arxiv': 'hep-ph/9804403',
        'doi_verified': None,
        'used_in': [
            'papers/paper38_cfl/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'CFL phase: color-flavor-locked diquark condensate and emergent symmetries.',
    },
    'SonStephanov2001': {
        'authors': 'Son, D. T., Stephanov, M. A.',
        'title': 'Inverse meson mass ordering in the color-flavor-locking phase of high-density QCD',
        'journal': 'Phys. Rev. D',
        'volume': 61,
        'page': '074012',
        'year': 2000,
        'doi': '10.1103/PhysRevD.61.074012',
        'arxiv': 'hep-ph/9910491',
        'doi_verified': None,
        'used_in': [
            'papers/paper38_cfl/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'CFL effective chiral Lagrangian with inverted meson-mass hierarchy.',
    },
    'SchaeferWilczek1999': {
        'authors': 'Schäfer, T., Wilczek, F.',
        'title': 'Continuity of quark and hadron matter',
        'journal': 'Phys. Rev. Lett.',
        'volume': 82,
        'page': '3956',
        'year': 1999,
        'doi': '10.1103/PhysRevLett.82.3956',
        'arxiv': 'hep-ph/9811473',
        'doi_verified': None,
        'used_in': [
            'papers/paper38_cfl/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Quark-hadron continuity: CFL diquark <-> hadronic-baryon correspondence.',
    },
    'HironoTanizaki2018': {
        'authors': 'Hirono, Y., Tanizaki, Y.',
        'title': 'Quark-hadron continuity beyond the Ginzburg-Landau paradigm',
        'journal': 'Phys. Rev. Lett.',
        'volume': 122,
        'page': '212001',
        'year': 2019,
        'doi': '10.1103/PhysRevLett.122.212001',
        'arxiv': '1811.10608',
        'doi_verified': None,
        'used_in': [
            'papers/paper38_cfl/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'CFL emergent Z_3 1-form symmetry matches QCD center; '
                 'topological-order beyond Landau-Ginzburg.',
    },
    'GaiottoKapustinSeibergWillett2015': {
        'authors': 'Gaiotto, D., Kapustin, A., Seiberg, N., Willett, B.',
        'title': 'Generalized global symmetries',
        'journal': 'JHEP',
        'volume': '02',
        'page': '172',
        'year': 2015,
        'doi': '10.1007/JHEP02(2015)172',
        'arxiv': '1412.5148',
        'doi_verified': None,
        'used_in': [
            'papers/paper38_cfl/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Foundational paper on higher-form (1-form) global symmetries; '
                 'machinery for Z_N center symmetry analysis.',
    },
    'AlfordSchmittRajagopalSchaefer2008': {
        'authors': 'Alford, M. G., Schmitt, A., Rajagopal, K., Schäfer, T.',
        'title': 'Color superconductivity in dense quark matter',
        'journal': 'Rev. Mod. Phys.',
        'volume': 80,
        'page': '1455',
        'year': 2008,
        'doi': '10.1103/RevModPhys.80.1455',
        'arxiv': '0709.4635',
        'doi_verified': '2026-04-29',  # WebFetch arXiv:0709.4635 confirmed (paper38 adversarial 2026-04-29)
        'used_in': [
            'papers/paper38_cfl/paper_draft.tex',
        ],
        'provides': [],
        'notes': 'Comprehensive review of color superconductivity and CFL phase. Renamed 2026-04-29 from the misnomer "Hatsuda2008" (paper has no Hatsuda authorship); paper38 .tex updated correspondingly.',
    },
}


# ════════════════════════════════════════════════════════════════════
# Helper functions
# ════════════════════════════════════════════════════════════════════

def get_citation(key):
    """Look up a citation by key."""
    return CITATION_REGISTRY.get(key)


def format_citation(key, style='short'):
    """Format a citation for display.

    Args:
        key: Citation registry key
        style: 'short' (Author, Journal Volume, Page (Year))
               or 'full' (with title)
    """
    entry = CITATION_REGISTRY.get(key)
    if not entry:
        return f"[{key}: NOT IN REGISTRY]"

    authors = entry['authors'].split(',')[0].strip()
    if ',' in entry['authors']:
        authors += ' et al.'

    if style == 'short':
        page = entry['page'] or '(in press)'
        return f"{authors}, {entry['journal']} {entry['volume']}, {page} ({entry['year']})"
    else:
        return (f"{entry['authors']}, \"{entry['title']}\", "
                f"{entry['journal']} {entry['volume']}, {entry['page']} ({entry['year']})")


def find_unregistered_citations():
    """Scan codebase for citations not in the registry.

    Returns list of (file, line, text) tuples for unregistered references.
    """
    import re
    from pathlib import Path

    project_root = Path(__file__).resolve().parent.parent.parent

    # Known journal patterns
    journal_pattern = re.compile(
        r'(Nature|PRL|PRD|PRA|PRB|JHEP|JETP|Phys\.?\s*Rev|Eur\.?\s*Phys)\s*'
        r'(?:\.?\s*(?:Lett\.?|[A-Z])?\s*)?'
        r'\\?(?:textbf\{)?(\d+)\}?\s*,?\s*(\d+|[A-Z]?\d+)',
        re.IGNORECASE
    )

    # Known DOIs in registry
    known_dois = {e['doi'] for e in CITATION_REGISTRY.values() if e.get('doi')}

    unregistered = []
    for ext in ('*.py', '*.tex'):
        for filepath in (project_root / 'src').rglob(ext):
            for i, line in enumerate(filepath.read_text().splitlines(), 1):
                for match in journal_pattern.finditer(line):
                    ref_text = match.group(0)
                    # Check if this matches any known citation
                    matched = False
                    for entry in CITATION_REGISTRY.values():
                        if (str(entry.get('volume', '')) in ref_text and
                                str(entry.get('page', '')) in ref_text):
                            matched = True
                            break
                    if not matched:
                        unregistered.append((str(filepath), i, ref_text))

    return unregistered


def summary():
    """Print citation registry summary."""
    total = len(CITATION_REGISTRY)
    with_doi = sum(1 for e in CITATION_REGISTRY.values() if e.get('doi'))
    verified = sum(1 for e in CITATION_REGISTRY.values() if e.get('doi_verified'))
    with_arxiv = sum(1 for e in CITATION_REGISTRY.values() if e.get('arxiv'))

    print(f"Citation Registry: {total} papers")
    print(f"  With DOI:     {with_doi}/{total}")
    print(f"  DOI verified: {verified}/{total}")
    print(f"  With arXiv:   {with_arxiv}/{total}")
