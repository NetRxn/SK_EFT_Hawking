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
        'doi_verified': None,
        'used_in': ['papers/paper1_first_order/paper_draft.tex',
                    'src/second_order/enumeration.py'],
        'provides': [],
        'notes': 'SK-EFT for superfluids.',
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
        'title': 'Unitarity in the ADW mechanism',
        'journal': 'PRD',
        'volume': 112,
        'page': '054509',
        'year': 2025,
        'doi': '10.1103/PhysRevD.112.054509',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper5_adw_gap/paper_draft.tex'],
        'provides': [],
        'notes': 'Unitarity proof for ADW mechanism.',
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
