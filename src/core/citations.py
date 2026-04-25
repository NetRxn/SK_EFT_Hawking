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
        'title': 'QCD topological dark energy',
        'journal': None,
        'volume': None,
        'page': None,
        'year': 2025,
        'doi': None,
        'arxiv': '2506.14182',
        'doi_verified': None,
        'used_in': ['papers/paper17_dark_sector/paper_draft.tex'],
        'provides': [],
        'notes': 'QCD topological DE — 0 free params, phantom crossing. arXiv verified.',
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
    # Phase 5z Wave 2 (paper 21 majorana_rung) — pending WebFetch verification
    # All entries `doi_verified: None`. Per feedback_citation_verification_required.md,
    # these MUST be verified against primary sources via the Stage 13
    # WebFetch round before paper 21 submission.
    # ────────────────────────────────────────────────────────────────
    'NuFit60': {
        'authors': 'Esteban, I., Gonzalez-Garcia, M. C., Maltoni, M., Schwetz, T., Zhou, A.',
        'title': 'NuFIT 6.0: Three-flavor neutrino oscillation analysis',
        'journal': 'JHEP',
        'volume': '12',
        'page': '216',
        'year': 2024,
        'doi': '10.1007/JHEP12(2024)216',
        'arxiv': '2601.14386',
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'NuFit-6.0 global three-flavor oscillation fit; source for '
                 'MAJORANA.DELTA_M_SQ_21 / DELTA_M_SQ_31 / THETA_12 / THETA_13 / '
                 'THETA_23 / DELTA_CP. doi_verified pending Stage 13 WebFetch '
                 'verification round (per feedback_citation_verification_required '
                 'rule — never flip None → True without primary-source fetch).',
    },
    'KamLANDZen800': {
        'authors': 'KamLAND-Zen Collaboration (Abe, S. et al.)',
        'title': 'Search for Majorana Neutrinos with the Complete KamLAND-Zen Dataset',
        'journal': 'arXiv',
        'volume': None,
        'page': None,
        'year': 2024,
        'doi': '10.48550/arXiv.2406.11438',
        'arxiv': '2406.11438',
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'KamLAND-Zen 800 full-dataset 0νββ search. T_{1/2} > 3.8 × 10²⁶ '
                 'yr at 90% CL; m_ββ < 28-122 meV depending on NME. v2 March '
                 '2026. Source for MAJORANA.M_BB_KAMLAND_ZEN_*. doi_verified '
                 'pending Stage 13 round.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'LEGEND-1000 PCDR. Projected 99.7% CL discovery sensitivity '
                 'T_{1/2} = 1.3 × 10²⁸ yr; m_ββ = 9-21 meV reach. Covers full '
                 'inverted-ordering parameter space at 10 yr live time. '
                 'Source for MAJORANA.M_BB_LEGEND_*. doi_verified pending Stage 13.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py'],
        'provides': [],
        'notes': 'Canonical Type-I seesaw review. Source for the Wave-2 m_ν '
                 'band derivation (m_ν ~ y² v² / M_R) and the M_R = 10⁹-10¹⁵ '
                 'GeV envelope. Cited in deep-research §2.2. doi_verified '
                 'pending Stage 13.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'src/core/provenance.py',
                    'lean/SKEFTHawking/Z16AnomalyComputation.lean'],
        'provides': [],
        'notes': 'Garcia-Etxebarria & Montero Dai-Freed anomaly framework: '
                 'sets ν_R = Z₁₆ charge +1, locks Embedding III\'s structural '
                 'choice. Source for MAJORANA.* Z₁₆ context and EW.N_F_WITH_NU_R. '
                 'doi_verified pending Stage 13.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Wan-Wang Ultra-Unification anomaly tower: 15 ≡ -1 mod 16 per '
                 'no-ν_R generation. doi_verified pending Stage 13.',
    },
    'Davighi2023': {
        'authors': 'Davighi, J., Lohitsiri, N., Tasnak, R.',
        'title': 'Dai-Freed anomaly in the standard model and topological inflation',
        'journal': 'arXiv',
        'volume': None,
        'page': None,
        'year': 2023,
        'doi': '10.48550/arXiv.2304.10100',
        'arxiv': '2304.10100',
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Davighi et al. Dai-Freed-anomaly + topological inflation. '
                 'Embedding III phenomenology consistent with reheating ~10⁸ '
                 'GeV. doi_verified pending Stage 13.',
    },
    'Volovik2024Spinor': {
        'authors': 'Volovik, G. E.',
        'title': 'Fermionic quartet and vestigial gravity',
        'journal': 'JETP Lett.',
        'volume': 119,
        'page': 330,
        'year': 2024,
        'doi': '10.1134/S0021364024600293',
        'arxiv': '2312.09435',
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Volovik 2024 fermionic-quartet/vestigial-gravity construction. '
                 'Establishes that ⟨ÊÊ⟩ and ⟨Ê⟩ vanish independently '
                 '(vestigial regime with phase diagram). Cited as motivation '
                 'for WAVE2-OPEN-1 substrate-bridge tracked-hypothesis. '
                 'doi_verified pending Stage 13.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/NeutrinoMixing.lean'],
        'provides': [],
        'notes': 'HepLean reference: source for the CKMMatrix structure-note '
                 'idiom mirrored by NeutrinoMixing.PMNSMatrix. doi_verified '
                 'pending Stage 13.',
    },

    # ────────────────────────────────────────────────────────────────
    # Phase 5z Wave 2b — strengthening citations
    # All entries `doi_verified: None`. WebFetch verification deferred
    # to Stage 13 paper-21 round per feedback_citation_verification_required.
    # ────────────────────────────────────────────────────────────────
    'AntuschKingmanLindnerWetterich2003': {
        'authors': 'Antusch, S., Kingman, J., Lindner, M., Wetterich, C.',
        'title': 'Dynamical electroweak symmetry breaking by a neutrino condensate',
        'journal': 'Nucl. Phys. B',
        'volume': 658,
        'page': 203,
        'year': 2003,
        'doi': '10.1016/S0550-3213(03)00188-3',
        'arxiv': 'hep-ph/0211385',
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRung.lean'],
        'provides': [],
        'notes': 'Source for Wave 2b H_MR_FromADWSubstrate_BCS_LNV form: '
                 'coupled Dirac-Majorana NJL gap equations with M_R as '
                 'external input + supercritical bifurcation. Cited '
                 'verbatim in MajoranaRung §3a for the lepton-number-symmetry '
                 'obstruction theorem. doi_verified pending Stage 13.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRungDecoupling.lean'],
        'provides': [],
        'notes': 'Original Appelquist-Carazzone decoupling theorem. Source '
                 'for Wave 2b WAVE2-OPEN-5 quantitative bound encoding via '
                 'DecouplingRegime + H_DecouplingBoundDim6. doi_verified '
                 'pending Stage 13.',
    },
    'BallThorne1994': {
        'authors': 'Ball, R. D., Thorne, R. S.',
        'title': 'The decoupling theorem in effective scalar field theory',
        'journal': 'arXiv',
        'volume': None,
        'page': None,
        'year': 1994,
        'doi': '10.48550/arXiv.hep-th/9404156',
        'arxiv': 'hep-th/9404156',
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'Wilsonian-EFT rigorous proof of AC decoupling with '
                 'explicit (E/M)^k bounds. Cited as the post-2000 sharper '
                 'AC version that the Wave 2b decoupling encoding follows. '
                 'doi_verified pending Stage 13.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRungDecoupling.lean'],
        'provides': [],
        'notes': 'SILH framework: source for naturalC = N_f / (16π²) '
                 'estimate adopted in MajoranaRungDecoupling.naturalC. '
                 'doi_verified pending Stage 13.',
    },
    'Hill2024Bilocal': {
        'authors': 'Hill, C. T.',
        'title': 'Bilocal field theory for composite scalar bosons',
        'journal': 'Entropy',
        'volume': 26,
        'page': 146,
        'year': 2024,
        'doi': '10.3390/e26020146',
        'arxiv': None,
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex',
                    'lean/SKEFTHawking/MajoranaRungDecoupling.lean'],
        'provides': [],
        'notes': 'Bilocal NJL form-factor analysis: source for the bound-'
                 'state coefficient form used in Wave 2b naturalC. Verifies '
                 'the SILH counting C ~ N_f / (16π²) for ADW-style four-'
                 'fermion substrates. doi_verified pending Stage 13.',
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
        'doi_verified': None,
        'used_in': ['papers/paper21_majorana_rung/paper_draft.tex'],
        'provides': [],
        'notes': 'SMEFT master formula for 0νββ: rigorous EFT chain LNV → '
                 'SMEFT → LEFT → χEFT → nuclear ME. Cited in Wave 2b '
                 'paper 21 §6 as the canonical reference for the '
                 'embedding-agnostic m_ββ phenomenology. doi_verified '
                 'pending Stage 13.',
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
