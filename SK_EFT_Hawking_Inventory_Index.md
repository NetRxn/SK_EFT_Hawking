# SK-EFT Hawking Inventory Index

**Purpose:** LLM-friendly quick reference for the full inventory (`SK_EFT_Hawking_Inventory.md`). Read this first; consult the full inventory for details.

**Last synced:** 2026-04-26 session 9 FINAL+ (**Phase 5t Paper 18 + technical + stakeholder notebooks SHIPPED. Completes the Phase 5t deliverable through Stages 10-11 (paper draft + notebooks) — Phase 5t is END-TO-END at pipeline-stage level now, all Waves 1-9 + Target A + Paper 18.**). Headline deliveries:
- **Phase 5t Paper 18 + notebooks direct (this session round)** — `papers/paper18_doublon_gate/paper_draft.tex` drafted and compiled clean (6 pages, 479kB PDF). Covers the full Phase 5t story: Fermi-Hubbard dimer Hamiltonian, BDI dark state + symmetry protection, geometric SWAP as Householder reflection, direct-vs-superexchange scaling, minimal Berry-phase theorem. **+1 Paper** (paper18_doublon_gate) + **+2 Notebooks** (`Phase5t_DoublonGate_Technical.ipynb`, `Phase5t_DoublonGate_Stakeholder.ipynb`). Both notebooks execute clean via `jupyter nbconvert --execute`. Paper references Section 7 `fig_doublon_gate_spectrum` (shipped W9). Paper 18 auto-discovers as 18th paper; 2 standard CitationIntegrity + NarrativeGrounding WARN as expected for new draft (citations and prose-provenance edges not yet populated).
- **Phase 5t W8 Target A (minimal geometric phase theorem) direct** — `FermiHubbardDimer.lean` Section 19 added, **+5 new thms + 1 summary marker** (no new defs — uses existing `darkStateθ`). **W8a** `darkStateθ(θ + π) = −darkStateθ(θ)` via `Real.sin_add_pi` + `Real.cos_add_pi` — **the closed-path sign statement**; **W8b** `darkStateθ(θ + 2π) = darkStateθ(θ)` 2π periodicity; **W8c** `dotProduct (darkStateθ θ) (darkStateθ θ) = 1` normalization via `Real.sin_sq_add_cos_sq`; **W8d** dynamical phase vanishes `⟨darkStateθ, H·darkStateθ⟩ = 0` under kernel-angle condition, direct from W4a; **W8e** **bundled geometric-phase theorem** — sign flip + zero dynamical phase ⟹ accumulated phase is purely geometric and equals −1. Python mirror `dark_state_theta_norm`, `geometric_phase_loop_check`; `TestGeometricPhaseW8` +42 pytest. Phase 5t END-TO-END COMPLETE. Target B (Aharonov-Anandan + adiabatic following + Berry-connection formalism) remains Phase 6 per original roadmap scope boundary.
- **Phase 5t W9 (Python cross-validation + visualization)** — pipeline Stages 8-12 completion. **+1 Python module** (`src/experimental/doublon_gate.py`, thin wrapper around W2-W8 Lean core: ED API, scaling curves, SWAP witnesses, superexchange bound benchmark). **+1 test file** (`tests/test_doublon_gate.py`, 43 tests, 6 classes). **+1 figure** (`fig_doublon_gate_spectrum`: two-panel with singlet spectrum cross-verified numpy-vs-closed-form + superexchange bound envelope ±16t⁴/U³). Registered in `review_figures.py`.
- **Phase 5t W7 round-2 strengthening direct** — `FermiHubbardDimer.lean` Section 17 added, **+8 new thms + 1 summary marker**. Matrix-bridge layer. **W7j/k** characteristic equations `E_{±}² − U·E_{±} − 4·t² = 0`; **W7l** `charpoly_H_singlet_Δ0_factored` = `(X − C U) · (X² − C U · X − C (4·t²))` — the matrix-bridge theorem proving `{U, E_plus, E_minus}` is the complete Hubbard spectrum at Δ=0; **W7m/n/o** explicit eigenvectors `![E_{±}, 0, -2·t]` + antisymmetric doublon `![0, 1, 0]` at eigenvalue `U`; **W7p** `E_minus(t, 0) = −2·|t|` mirror of W7a; **W7q** global 1-Lipschitz bound `|E_plus(t, U₁) − E_plus(t, U₂)| ≤ |U₁ − U₂|` (Tier-1 per deep research) via sqrt-1-Lipschitz chain. Tests `TestW7Round2Strengthening` +68 pytest.
- **Phase 5t W6-deferred shipment direct** — `FermiHubbardDimer.lean` Section 18 added, **+7 new thms + 1 summary marker + 1 def**. `U_SWAP_adapted (t Δ) := fromBlocks (U_SWAP_singlet t Δ) 0 0 1` block-diagonal 6×6 lift in symmetry-adapted basis (singlet ⊕ triplet). W6D-S1/S2/S3/S3' symmetry+involution+orthogonality+transpose-mul all inherited from W6C via `Matrix.fromBlocks_{transpose, multiply, one}`; W6D-U1 `∈ Matrix.unitaryGroup (Fin 3 ⊕ Fin 3) ℝ`; W6D-A1/A2 action agreement on singlet/triplet blocks via `Matrix.fromBlocks_mulVec`. **Structural unitarity NOT SWAP claim on `{|↑,↓⟩, |↓,↑⟩}`** (latter requires Berry-phase holonomy = W8/Phase 6). Tests `TestW6Deferred6x6Lift` +43 pytest.
- **Phase 5t W7 (direct vs superexchange scaling) direct** (session 9 prior) — `FermiHubbardDimer.lean` Section 16, **+9 new thms + 1 summary marker + 3 defs**. Real-analysis formulation per deep research: bypass Hubbard, state as facts about `E_plus(t, U) := (U + √(U² + 16·t²))/2`. W7a direct-exchange value; W7b/c Vieta trace/product; W7d `HasDerivAt (E_plus t) (1/2) 0` — direct-exchange linear-in-U scaling theorem; W7e sqrt lower bound; W7f `MonotoneOn`; W7g J(t,0)=2|t|; W7h AM-GM; W7i **Tier-2 superexchange approximation bound** `|J − 4·t²/U| ≤ 16·t⁴/U³` for `4|t| ≤ U`. `TestDirectExchangeSuperexchangeW7` +61 pytest.
- **Phase 5t W6 round-2 strengthening direct** (session 9 prior) — `FermiHubbardDimer.lean` Section 15, **+5 new thms + 1 summary marker**. W6C-A1s/A2s/A3s scalar-multiple SWAP; W6C-U1 Matrix.unitaryGroup membership; W6C-K1 SWAP acts as `-1` on full kernel via W5p + W6C-A1s. `TestGeometricSWAPW6Round2` +29 pytest.
- **Phase 5t W5 core + W5 round-2 + W6A + W6B + W6C** shipped 2026-04-25 session 8 (prior session); roster preserved below.
- **Phase 5t W6 (W6A+W6B+W6C) direct (geometric SWAP core)** — `FermiHubbardDimer.lean` Sections 12/13/14 added, **+39 new thms + 8 defs + 3 summary markers**. **W6A** (EuclideanSpace infrastructure): `darkVecE`/`brightVecPlusE`/`brightVecMinusE` via `EuclideanSpace.equiv.symm`, L2 norm formulas (`‖darkVecE‖ = gap`), normalized versions, inner-product bridge via `@inner ℝ _ _ x y = dotProduct y.ofLp (star x.ofLp)` (rfl), capstone `eigenvector_triple_orthonormal`. **W6B** (OrthonormalBasis): `eigenBasis` via `Basis.toOrthonormalBasis`, component apply lemmas, unitarity of change-of-basis via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` (one-line). **W6C** (SWAP operator): `U_SWAP_singlet` as Householder reflection `I - (2/gap²)·darkVec⊗darkVec`, W6C-A1 sign flip on dark, W6C-A2/A3 identity on brights, W6C-S1/S2/S3 symmetric + involution + orthogonal (**unitarity witness**), W6C-E1 eigenvalue bundle `{-1,+1,+1}`, W6C-D1/T1 det=-1/trace=+1. Python mirror +4 W6 helpers; Lean-mirror tests `TestNormalizedEigenvectorsW6A` + `TestGeometricSWAPW6C` +67 pytest.
- **Phase 5t W6 (W6A+W6B+W6C) direct (geometric SWAP core)** — `FermiHubbardDimer.lean` Sections 12/13/14 added, **+39 new thms + 8 defs + 3 summary markers**. **W6A** (EuclideanSpace infrastructure): `darkVecE`/`brightVecPlusE`/`brightVecMinusE` via `EuclideanSpace.equiv.symm`, L2 norm formulas (`‖darkVecE‖ = gap`), normalized versions, inner-product bridge via `@inner ℝ _ _ x y = dotProduct y.ofLp (star x.ofLp)` (rfl), capstone `eigenvector_triple_orthonormal`. **W6B** (OrthonormalBasis): `eigenBasis` via `Basis.toOrthonormalBasis`, component apply lemmas, unitarity of change-of-basis via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` (one-line). **W6C** (SWAP operator): `U_SWAP_singlet` as Householder reflection `I - (2/gap²)·darkVec⊗darkVec`, W6C-A1 sign flip on dark, W6C-A2/A3 identity on brights, W6C-S1/S2/S3 symmetric + involution + orthogonal (**unitarity witness**), W6C-E1 eigenvalue bundle `{-1,+1,+1}`, W6C-D1/T1 det=-1/trace=+1. Python mirror +4 W6 helpers; Lean-mirror tests `TestNormalizedEigenvectorsW6A` + `TestGeometricSWAPW6C` +67 pytest.
- **Phase 5t W5 core (symmetry layer)** — `FermiHubbardDimer.lean` Section 10 added (+10 thms incl. summary marker, ~170 LOC). **W5a** `chiralOp_conjugation_neg` (Γ·H·Γ=-H at U=0 via direct `ext+fin_cases+simp`); **W5b** `chiral_maps_eigenvector` (Γ maps eigenvector of +E to eigenvector of -E via `Matrix.mulVec_mulVec`+`neg_smul` chain, using W2 T5 rearranged through `add_eq_zero_iff_eq_neg'`); **W5c** `spectrum_pairing_U0` (μ ∈ spec ↔ -μ ∈ spec, three-way casework off W4p); **W5d** `zero_mem_spectrum_U0`; **W5e** `darkVec_in_chiral_minus_eigenspace` (zero mode pinned to 2-dim (-1)-eigenspace of Γ); **W5f** `darkVec_is_zero_mode_pinned` (bundle); **W5g/g'** bright ± pairing `Γ·brightVec± = -brightVec∓`; **W5h** `H_singlet_real_anti_unitary_trivial` (paper-framing marker).
- **Phase 5t W5 round-2 strengthening** — `FermiHubbardDimer.lean` Section 11 added (+11 new thms + 1 summary marker, +2 defs `chiralProjPlus/Minus`). **W5i** `zero_mode_space_is_chiral_invariant` (Γ restricts to involution on ker(H)); **W5j** `chiral_preserves_nonzero` (via Γ²=I injectivity); **W5k** `charpoly_roots_U0_symmetric_under_neg` (multiset-level spectrum pairing via `Multiset.map_add`+`add_right_comm`); **W5l–W5o2** sublattice projector algebra `P_± := (1±Γ)/2` with idempotency (W5l/m), orthogonality (W5n/n'), completeness (W5o), and Γ acting as ±1 on ±1 eigenspaces (W5o1/o2) — load-bearing for W6 SWAP; **W5p** `zero_mode_unique_up_to_scalar` (strongest "pinning": ker(H_singlet t Δ 0) is exactly ℝ·darkVec when (t,Δ)≠(0,0); direct componentwise mulVec expansion + case-split on Δ=0 with explicit scalar witnesses).
- **W6 normalization decision (explore-agent recon, session 8)** — **Path A (EuclideanSpace ℝ (Fin 3)) recommended**. One-line unitarity via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` vs ~25-line manual unroll under Path B; retype cost ~2 hours; full decision matrix at `temporary/working-docs/W6_normalization_decision.md`.
- Python mirror +8 helpers total (6 W5 core + 2 round-2 projectors). Tests: `TestChiralPinningW5` (+63 core) + `TestChiralStrengthW5Round2` (+37) = **+100 pytest from W5**. `lake build SKEFTHawking.ExtractDeps` clean 8422 jobs; pytest 2463/2463 pass; validate.py 21/21 PASS.
- **Phase 5t W3 direct** — `FermiHubbardDimer.lean` +10 new thms (W3a-f: block-match theorems `H_full_acts_on_v_{Dplus,Dminus,s,t0}`, computational-basis decomposition `2•up_down = v_t0+v_s`, `2•down_up = v_t0-v_s`); unnormalized symmetry-adapted basis vectors; 34 new pytest cover block-match + decomposition.
- **Phase 5t W4 direct (strong form)** — `FermiHubbardDimer.lean` +14 new thms: W4a θ-parametrized dark state kernel, W4b/c bright eigenvector equations with Real.sqrt + linarith-via-Real.sq_sqrt, W4d gap pos, W4d' `gap² = Δ²+4t²` identity, W4e/e'/e'' brightVecPlus/Minus/darkStateθ nonzero, W4f general-U charpoly (full cubic) via `simp [Matrix.charpoly, det_fin_three, charmatrix_apply_eq/ne, map_mul/pow/ofNat, show(i≠j:Fin 3) from decide]; ring` pattern, W4g charpoly at U=0 factored, W4h fully-factored form `X·(X-C√g)·(X+C√g)`, W4i three eigenvalues distinct, W4j `eigenvectorMatrix.det = 2·(gap)³`, W4k eigenvectors linearly independent (alternate spectrum-completeness witness). 34 new pytest. 8 new summary / strengthening markers total.
- **Phase 5w W10c** (opus subagent, complete) — `QuasiOneDReduction.lean` T2/T3/T5 bound-propagation refactor + 18 new tests + paper 16 prose update + fig 104/105 regen.
- **W10c tracked-hypothesis strengthening (main session audit)** — Opus-subagent-shipped `H_AdiabaticRegimeCorrection` and `H_DispersiveUVCutoff` found to universally-quantify over what should be parameters (adiabatic version was FALSE; dispersive version was vacuously satisfiable via ∃C absorption). Fixed: moved `T_H_exact/leading`, `ω_max`, `C` outside Prop body as parameters; added `T_H_leading > 0` / `ω_max > 0` positivity; docstrings expanded with "Parameterization discipline" sections. Also fixed pre-existing unused-variable warning on `evanescent_bound.hωp`. New memory `feedback_subagent_lean_quality.md` captures the systemic lesson.
- **Paper 17 adversarial remediation** (opus subagent, complete) — 4 BLOCKERs addressed: `Glodkowski2024` corrected to arXiv:2401.01877 (Dissipative fracton superfluids, WebFetch-verified); 30 missing bibkeys populated into `CITATION_REGISTRY` (74 total entries, 15 flagged for user-verify); `Paper8` bibkey collision resolved via rename to `FractonNonAbelian2025`; semantic-tautology cluster (5 theorems) reframed as MCC (Machine-Checked Classification) with honesty-table corrections and new MCC-vs-Derived boundary section in §sec:formal-verification. Report: `papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md`. 1 remaining BLOCKER (ProductionRunHealth, blocked-on-data — needs ProductionRun → Paper17 graph edges).

**Session-8 verification (post-W6):** `lake build SKEFTHawking.ExtractDeps` clean (8422 jobs); pytest 2530/2530 pass (+63 W5 core + +37 W5 round-2 + +67 W6A/C = +167 on top of 2363 session-7 baseline); validate.py 21/21 pass.

**Session-8 verification (mid-W5):** `lake build SKEFTHawking.ExtractDeps` clean (8422 jobs); pytest 2463/2463 pass (+63 W5 core + +37 W5 round-2 = +100 on top of 2363 session-7 baseline); validate.py 21/21 pass.

**Session-7 verification:** `lake build SKEFTHawking.ExtractDeps` clean (8422 jobs); pytest 2334/2334 pass (+34 W4 on top of 2300 W10c+W3 baseline); validate.py 21/21 pass.

Session 6: Phase 5t Wave 2 FermiHubbardDimer.lean SHIPPED — Track A COMPLETE; Phase 5x W9 Paper 17 draft + validate.py fix also in the session-6 group.

**Phase 5x Wave 5 SFDM MERGER FORECAST SHIPPED 2026-04-22 session 4.** `lean/SKEFTHawking/SFDMMergerForecast.lean` (30 theorems, 0 sorry, 0 new axioms, 499 LOC). Paper 17 "money plot" formalization. BK fiducial sound-speed table (galaxy 242 / group 607 / subcluster 1525 km/s); `sfdm_sound_speed_sq` = `2μ/m` + positivity + linear-μ / inverse-m scaling (Lean L1); Landau criterion decidable `MergerRegime` classifier (Lean L6 partial); 5 canonical merger struct table (Bullet 1.77 / El Gordo 1.64 / Pandora 2.23 / A520 1.51 / MACS J0025 1.31) with `all_canonical_mergers_supersonic`, `pandora_highest_mach`, `macs_j0025_lowest_mach` (all native_decide); Rankine-Hugoniot density jump general γ + SFDM γ=2 closed form `3M²/(M²+2)` + subtractive form `3−6/(M²+2)` + monotonicity in Mach + condensate-correction non-negativity; stacked S/N √N scaling (`snr_stacked_single`, `snr_stacked_monotone`, `snr_stacked_sq`, `three_sigma_threshold`); 5 decidable numerical S/N witnesses (Bullet Roman 3σ@N=18, 4σ@N=30, 5σ@N=50; A520 Euclid 3σ@N=30, 5σ@N=50); SFDM backreaction direction (`sfdm_mu_decrease_lowers_cs_sq` + `sfdm_backreaction_raises_mach`); smoking-gun step function (`sfdm_offset_step_function`). Python: `src/dark_sector/sfdm_sk_eft.py` (~400 LOC) + `src/dark_sector/sfdm_merger_forecast.py` (~500 LOC) with full Mach → R-H → condensate → Σ_cr → κ → single/stacked S/N chain. Bullet/Euclid S/N = 0.83, Bullet/Roman S/N = 1.04 match W1b Table 6 exactly. H₀ sensitivity: H0DN raises Σ_cr ~9% (below dominant Λ uncertainty). Money plot: `fig_sfdm_velocity_threshold_step` (left panel, Fig 106) shows SFDM step vs SIDM smooth-rise vs CDM null with 5 canonical merger markers; `fig_sfdm_stacked_kappa_profile` (right panel, Fig 107) shows Euclid+Roman stacked S/N vs N with 3σ/5σ thresholds. 86 passing tests in `tests/test_sfdm_merger_forecast.py` covering every Lean↔Python mirror + geometry + assessment. Memo `docs/dark_sector/W5_SFDM_Merger_Forecast.md` (9 sections: purpose, inputs, theorem roster, Python chain, figures, H₀ tension, deferred Phase 6, triggers, references). Deferred Phase 6: L4 `mond_force_derivation` (Hard — non-analytic X√|X| calculus), L5 `fdr_noise_bound_rar` (Hard — FDR for non-analytic Lagrangian), L3 transport coefficient counting extension, per-cluster lensing likelihood modeling, Abell 520 dark-core quantitative prediction. Gates W9 (Paper 17 draft). Full-project `lake build SKEFTHawking.ExtractDeps` clean 8421 jobs. Full pytest 2172 pass / 16 skip / 0 fail (+86 from W5).

**Phase 5x Wave 8 SYNTHESIS COMPLETE 2026-04-22 session 4.** `lean/SKEFTHawking/DarkSectorSynthesis.lean` (22 theorems, 0 sorry, 0 new axioms, 1 tracked `Prop` hypothesis `H_VestigialRelicCarriesZ16Charge`). Seven cross-connections shipped: CC1 hidden-sector × fracton compatibility (`hidden_sector_fracton_compatible` consumes W2 + W7 `fracton_sm_singlet_from_ym_incompat`); CC2 collective invisibility (`emergent_gravity_dm_invisible_collective` — every `EmergentGravityDMKind` has σ_DD log10 cap ≤ -50, decidable over 5-element enum); CC3/CC4/CC4' three pairwise EoS distinctness (`w_Λ=-1 ≠ w_FG=1/3 ≠ w_fracton=0`, all `native_decide` over ℚ); CC5 cored-profile taxonomy (`SolitonCondensate ≠ Z4Subdiffusion`; `CoredProfileMechanism` enum); CC6 ℤ₁₆ × vestigial relic protection (conditional on `H_VestigialRelicCarriesZ16Charge` — `z16_vestigial_stability_under_hypothesis` + `z16_vestigial_no_vacuum_decay`); CC7/CC7' torsion-channel independence (`TorsionSource` / `TorsionChannel` / `channel_of_source` — full discharge via distinct-enum casework; Dirac axial ⊥ FG loop θ). Candidate viability matrix (`phase5x_candidates_viability_matrix` — 4 of 5 canonical candidates basic-viable, FG excluded at CDM level per W4). Empirical-hook ranking (`empirical_hook_ranking_strict`, `merger_outranks_direct_detection`, `merger_is_top_ranked` — pins Paper 17 §9 ordering to Lean-decidable ground). Python companion `src/dark_sector/synthesis.py` (7-entry `CROSS_CONNECTION_MATRIX`, Python-side mirror of Lean constants, `assess_dark_sector_synthesis()` returning structured 8-field verdict). 70 passing tests in `tests/test_dark_sector_synthesis.py` (10 classes covering each sub-theme + Python↔Lean cross-checks). Memo `docs/dark_sector/W8_Synthesis_and_CrossConnections.md` (inputs table, 7-section theorem walkthrough, cross-connection matrix, prediction ranking, honesty table, triggers-to-update). Phase 6 discharge paths registered in `Phase6_Deferred_Targets.md` (H_VestigialRelicCarriesZ16Charge via W6a+W6b+bordism; torsion channel identification via Lagrangian variational calculus). Gates W9 (Paper 17 draft). Full-project `lake build SKEFTHawking.ExtractDeps` clean 8420 jobs. Full pytest 2086 pass / 16 skip / 0 fail. Full validate.py 20/21 (sole fail = pre-existing paper16 figures empty, unchanged 5w W10b item).

**Phase 5x Wave 4 STRENGTHENED 2026-04-22 session 3.** Memo review caught that traceless-T → `w=1/3` is a tree-level kinematic obstruction on FG-DM as CDM, not just a hedge. Narrow Lean module `FangGuTorsionDM.lean` shipped (10 theorems, 0 sorry, 0 new axioms; `lean_verify` confirms only standard `propext`/`Classical.choice`/`Quot.sound`). `PerfectFluidData` struct + `mink_trace` / `eos_w` / `is_dust` / `poisson_source` defs. Main theorems: FG1 `traceless_iff_w_one_third`, FG2 `traceless_not_dust`, FG3 `traceless_poisson_source_doubled`, FG4 `dust_poisson_source_equals_rho`, FG5 `fg_cdm_obstruction`. Memo `docs/dark_sector/W4_FangGu_Torsion_DM_Assessment.md` revised (§1 verdict → "structurally compatible but kinematically obstructed at CDM level"; §3 EOS row + new §3.1 kinematic-obstruction walkthrough; §5 tree-level caveat on two-channel torsion orthogonality; §6 Lean-module rationale; §7 Paper 17 framing "compatible-but-kinematically-obstructed"; Appendix C theorem catalogue). Three literature escape hatches (cosmic-string-gas averaging, sub-sonic velocity dispersion, quantum trace anomaly) flagged as logically open but not realized in FG 2021/2023.

**Phase 5x Wave 7 NEAR-TERM COMPLETE**: FractonDarkMatter.lean (25 theorems, 0 sorry, 0 new axioms — fracton DM phenomenology wave). Phase classification `FractonDMPhase` × `FractonNoGoTheorem` with decidable `no_go_applies`. 13a `fracton_nogo_exemption` (Shen/Krishna exempt GaplessU1 + PWave), `pwave_fully_exempt`, `kapustin_selects_pwave`. 13c `fracton_lifetime_arrhenius` + `fracton_10MeV_passes_arrhenius`. 13d `fracton_bbn_condensate_sufficient` + `fracton_1MeV_passes_condensate`. Signature theorems: `fracton_bullet_sigma_zero`/`_cluster_satisfied`, `fracton_sm_singlet_from_ym_incompat` (consumes `FractonNonAbelian.no_fracton_is_ym_compatible`), `fracton_cosmo_dust_pressureless`, `fracton_gravity_attractive`, `fracton_ww_bypass`, `fracton_z4_subdiffusion_preserved` (consumes `FractonFormulas.dipole_k4_damping`), `fracton_sound_speed_subluminal`. Viable-window theorems + 4 executable witnesses via `is_viable_at_epoch` classifier. Python `src/dark_sector/fracton_dm.py` with Arrhenius / Hubble / condensate APIs + `assess_fracton_dm_status` structured verdict (computed Arrhenius floor ≈ 10.46 MeV) + 86 tests. Deferred (Phase 6): 13b thermodynamic BBN lower bound, theorems 5/6/7/14, Haah phase diagram, Dark-QCD UV completion memo.

**Phase 5x Wave 3 PARTIAL COMPLETE** (session 2, 2026-04-22): CosmologicalConstant.lean (T1 double-temperature T_dS=2·T_GH, T3 quartic Coleman-Weinberg critical-point `-A²/(4B)` general form, Λ magnitude-ratio utilities — 8 theorems, 0 sorry, 0 new axioms) + src/dark_sector/adw_cosmological_constant.py (Volovik T_dS=H/π, Gibbons-Hawking T_GH=H/(2π), Λ ratio (2.8/2.3)⁴≈2.20, W1b-corrected Klinkhamer-Volovik frozen-plateau prediction, structured CC assessment) + 45 tests. Deferred: T2 volovik_equilibrium (thermodynamic axioms), specific ADW V_eff identity -Λ⁴/(4e) (RG infrastructure), T4-T6 (Phase 6), paper-tables/assessment-memos (submission-adjacent).

**Phase 5x Wave 2b Track X COMPLETE**: HiddenSectorMixedCharge.lean extending the ℤ₁₆ singlet-channel formalism to the Wan-Wang mixed-charge channel — X1 MixedChargeHiddenSector struct, X2 u1x_cubic_mod4 (U(1)_X³ cubic anomaly), X3 u1x_linear_mod4 (U(1)_X × gravity² mixed anomaly), X4 MixedChannelJointConstraint conjunction parameterized over a ℤ₁₆ indexing `φ : Z16Indexing`, X5 c1_wan_wang_satisfies_u1x (decidable (b)+(c) for 7 q=-2 + 1 q=+6) + c1_wan_wang_joint_constraint (conditional on the tracked hypothesis), X6 mixed_channel_orthogonal_to_singlet (explicit witness: 8 ≢ 3 mod 16 yet U(1)_X cancels). 0 sorry, 0 new axioms; 1 tracked `Prop` hypothesis `H_MixedChannelZ16Cancels φ h := (13 + φ h : ZMod 16) = 0` (non-trivial — for arbitrary φ, `φ h = 3` is not provable; matches CenterFunctor Nonempty-based precedent). Python `DMCandidate` extended with x_charges field + `verify_joint_cancellation`; C-1 gets concrete Wan-Wang assignment. 8 new tests, 44 total in test_z16_hidden_sector.py. Full-project `lake build SKEFTHawking.ExtractDeps` clean 8416 jobs. Full pytest 1885 pass. Full validate.py 20/21 (sole fail is paper16 figures — pre-existing 5w W10b item, unrelated).

**2026-04-22 earlier:** **Phase 5x Wave 2 COMPLETE**: HiddenSectorClassification.lean with 9 theorems formalizing ℤ₁₆ hidden-sector DM candidate constraints — T1 anomaly_index_weyl_singlet, T2 hidden_sector_anomaly_value, T3 minimal_singlet_count (+sanity corollary), T10 all_singlet_solutions_bounded (+nineteen sanity), T11 z4x_singlet_constraint, T12 generation_independent_z16. 0 sorry, 0 axioms. First verifier-backed DM candidate constraint from formal methods. Python companion `src/dark_sector/z16_hidden_sector.py` + 36 passing tests in `tests/test_z16_hidden_sector.py`. Full-project `lake build` clean 8414 jobs.

**2026-04-22 earlier:** **Phase 5s Wave 9 CLOSED via hypothesis refactor**: 3 research-grade sorries in CenterFunctorZ2Equiv.lean converted to 2 tracked `Prop` hypotheses (`H_CFZ2_sq_e`, `H_CFZ2_sq_a`) matching `CenterFunctor.lean` precedent; h_cf2_G2 deleted. Zero axioms introduced. Verified by clean no-cache `lake build` (8413 jobs). **Phase 5w Wave 10a COMPLETE**: corrected noise formula ΔS_I = 2ℏω σ_Q Γ n_H (Keldysh + Landauer-Büttiker derivation). GrapheneNoiseFormula.lean (8 thms).)

---

## Counts (ground truth — update atomically)

**Source of truth:** `docs/counts.json`, regenerated via `scripts/update_counts.py` (which re-runs `extract_lean_deps.py` when Lean source hashes change).

| Item | Count | Source of truth |
|------|-------|-----------------|
| Lean theorems | **3728** (3617 substantive + 111 placeholder; +39 from session 8's 3689 via W6 round-2 + W7 + W7 round-2 + W6-deferred + W8 Target A + W9 in session 9) | counts.json — package-module-bound count |
| Placeholders (True := trivial) | **111** (+wave6_round2 + wave7 + wave7_round2 + wave6_deferred + wave8 summary markers in FermiHubbardDimer session 9) | Module summaries + content placeholders; see PLACEHOLDER_THEOREMS in constants.py |
| Aristotle-proved | **322** (machine) | ARISTOTLE_THEOREMS in constants.py; 44 Aristotle runs total |
| **Sorry gaps** | **0** | Project-wide (verified 2026-04-26 session 9 FINAL via `lake build SKEFTHawking.ExtractDeps`, 8422 jobs). **FermiHubbardDimer 0 sorry (2026-04-26 session 9 FINAL)**: W2+W3+W4 strong form + W5 core + W5 round-2 + W6A/B/C + W6 round-2 + W6-deferred 6×6 lift + W7 + W7 round-2 + W8 Target A + W9 Python mirror all shipped. **Phase 5t END-TO-END COMPLETE through Waves 1-9 INCLUDING W8 Target A.** Only W8 Target B (full adiabatic holonomy, Berry connection over parameterized eigenbundle) remains Phase 6. |
| **Axioms** | **1** | gapped_interface_axiom in SPTClassification.lean |
| Lean modules | **158** | counts.json — FermiHubbardDimer extended (session 9 adds Sections 15-19; no new modules). |
| Lean definitions | **2939** | counts.json — unchanged across W8 shipment (W8 uses existing `darkStateθ`). |
| Python source modules | **66** | Unchanged (dimer.py extended with W8 helpers `dark_state_theta_norm`, `geometric_phase_loop_check`). |
| Test files | **58** | Unchanged (test_fermi_hubbard_dimer.py extended with TestGeometricPhaseW8 session 9 FINAL). |
| Test count | **2816 pass**, 16 skip, 0 fail (2026-04-26 session 9 FINAL; +42 W8 on top of 2774 round-2 baseline = +196 session-9 total) | `pytest tests/ -q` |
| Figures | **110** | +1 session 9 (`fig_doublon_gate_spectrum`: Phase 5t W9 spectrum + scaling) |
| Notebooks | **52** | +2 session 9 (`Phase5t_DoublonGate_Technical.ipynb`, `Phase5t_DoublonGate_Stakeholder.ipynb`) |
| Papers | **18** | +1 session 9 (`paper18_doublon_gate`: "Formal Verification of a Geometric Quantum Gate") |
| Figures | **109** | `grep -c "^def fig_" src/core/visualizations.py` (+2 Phase 5x W9: `fig_phase5x_candidate_viability_matrix` + `fig_phase5x_empirical_hook_ranking`; +2 W5 money plot; +4 earlier Phase 5w) |
| Notebooks | **49** | `ls notebooks/*.ipynb` (+1: Phase5w_GrapheneDiracFluid_Technical) |
| Papers | **17** | `ls papers/paper*/paper_draft.tex` (+1 Phase 5x W9: Paper 17 dark sector connections — 11 sections, 4 figures, Lean-traced claims) |
| Validation checks | 16 | `python scripts/validate.py --list` |
| Stakeholder docs | 22 | See Section 9 of inventory |
| Aristotle runs | 44 | See Aristotle run table in full inventory |
| Deep research tasks | 18 + 8 + 6 + 6 + 6 + 3 | 18 Phase-5 + 8 Phase-5a + 6 Phase-5b + 6 Phase-5e + 6 Phase-5x (W1 COMPLETE) + 3 Phase-5x (W1b COMPLETE — KV/DESI Level D, fracton NON-VIABLE weak, merger CONDITIONAL GO)


---

## Inventory Sections → What to update

| Section | Covers | When to update |
|---------|--------|----------------|
| 1. Python Source | All `src/` modules with purpose + line counts | New module added or module purpose changes |
| 2. Lean Verification | 94-module table: lines, theorem count, key results | Theorem added/removed, module added |
| 3. Aristotle | Run table with dates + theorem counts | New Aristotle submission |
| 4. Notebooks | 42-notebook table: phase, topic | Notebook added or topic changes |
| 5. Papers | 14-paper table: format, lines, topic, key claims | Paper content changes |
| 6. Tests | 43-file table: test counts, coverage | Test file added or count changes |
| 7. Scripts | 14-script table | Script added or purpose changes |
| 8. Configuration | Dependency table | Dependency added |
| 9. Documentation | Reference, roadmap, stakeholder, analysis tables | Doc added/moved/content changes |
| 10. Key Formulas | Physics formulas with Lean refs | Formula added to formulas.py |
| Summary Table | All counts | Any count changes (run verification commands above) |

---

## Source module map (module → purpose, one line each)

### Core (`src/core/`)
- `constants.py` — Physical constants, experimental params, Aristotle registry, NJL/ADW model params
- `formulas.py` — Canonical physics formulas with Lean refs (137 functions including SM anomaly, Weingarten, NJL, fracton, Planck, quantum group, SU(2)_k fusion/S-matrix, E8/Rokhlin)
- `transonic_background.py` — 1D BEC transonic flow solver
- `visualizations.py` — All 80 Plotly figure functions + COLORS palette
- `aristotle_interface.py` — Aristotle API + sorry gap registry (24 unfilled across 3 Lean modules)
- `sm_anomaly.py` — SM anomaly computation in ℤ₁₆: fermion data, anomaly index, generation constraint, hidden sector check
- `provenance.py` — Parameter provenance registry (PARAMETER_PROVENANCE, tiers, verification dates)
- `citations.py` — Citation registry (CITATION_REGISTRY, DOI tracking, usage mapping)

### Phase 1-2 (`src/second_order/`)
- `enumeration.py` — Transport coefficient counting: count(N) = floor((N+1)/2)+1
- `coefficients.py` — Second-order data structures + action constructors
- `wkb_analysis.py` — WKB mode analysis, frequency-dependent Bogoliubov
- `cgl_derivation.py` — CGL dynamical KMS → FDR at arbitrary order

### Phase 3 (`src/gauge_erasure/`, `src/wkb/`, `src/adw/`)
- `gauge_erasure/erasure_theorem.py` — Non-Abelian gauge erasure → U(1) survives
- `wkb/connection_formula.py` — Exact WKB through complex turning point
- `wkb/bogoliubov.py` — Modified unitarity, decoherence
- `wkb/spectrum.py` — Full Hawking spectrum with corrections + noise
- `wkb/backreaction.py` — Acoustic BH cooling toward extremality
- `adw/wen_model.py` — Wen's lattice QED (UV completion)
- `adw/hubbard_stratonovich.py` — HS decomposition → composite tetrad
- `adw/gap_equation.py` — Coleman-Weinberg V_eff, G_c
- `adw/fluctuations.py` — SSB, NG modes (2 gravitons in 4D), Vergeles check
- `adw/ginzburg_landau.py` — GL expansion, He-3 analogy
- `adw/tetrad_gap_solver.py` — NJL-type gap equation solver, Δ*(G) curve, MF-guided scan params (Phase 5d)
- `adw/tetrad_observables.py` — MC observables: O_tet, O_met, Binder U₄, spatial correlator C(r) (Phase 5d)
- `chirality/gioia_thorngren.py` — Gioia-Thorngren chirality analysis (Phase 5a)

### Phase 4 (`src/experimental/`, `src/chirality/`, `src/fracton/`, `src/vestigial/`)
- `experimental/predictions.py` — Platform prediction tables, shot counts
- `experimental/kappa_scaling.py` — Physical kappa-scaling sweeps for all platforms
- `chirality/tpf_gs_analysis.py` — TPF vs GS no-go: 2/4 conditions evaded
- `fracton/sk_eft.py` — Fracton SK-EFT, binomial charge counting
- `fracton/information_retention.py` — Fracton retains exponentially more UV info
- `fracton/gravity_connection.py` — Kerr-Schild bootstrap, DOF gap
- `fracton/non_abelian.py` — Non-Abelian fracton obstruction (negative result)
- `vestigial/mean_field.py` — Curvature-based 3-phase classification
- `vestigial/lattice_model.py` — Euclidean lattice formulation
- `vestigial/monte_carlo.py` — Metropolis MC for lattice model
- `vestigial/phase_diagram.py` — Phase diagram from MF + MC
- `vestigial/finite_size.py` — Finite-size scaling analysis
- `vestigial/su2_integration.py` — Analytical SU(2) Haar measure integration
- `vestigial/grassmann_trg.py` — 2D Grassmann TRG implementation
- `vestigial/lattice_4d.py` — 4D hypercubic lattice model with SO(4) gauge integration
- `vestigial/fermion_bag.py` — Fermion-bag MC algorithm for 8-fermion vertices (ADW Option B)
- `vestigial/wetterich_model.py` — NJL fermion-bag MC (Option C, gauge-link-free, staggered OPs)
- `vestigial/phase_scan.py` — 4D coupling scan with Binder cumulant analysis (ADW + NJL)
- `vestigial/quaternion.py` — SU(2) quaternion algebra for SO(4) gauge (Wave 7A)
- `vestigial/so4_gauge.py` — SO(4) gauge theory via quaternion pairs, heatbath (Wave 7A)
- `vestigial/gauge_fermion_bag.py` — Hybrid fermion-bag + gauge-link MC (Wave 7B)
- `vestigial/gauge_fermion_bag_majorana.py` — 8×8 Majorana sign-free fermion-bag (Wave 7B)
- `vestigial/hs_rhmc.py` — HS+RHMC algorithm, numpy/scipy reference (Wave 7C)
- `vestigial/hs_rhmc_jax.py` — JAX CPU backend for RHMC (Wave 7C)
- `vestigial/hs_rhmc_torch.py` — PyTorch CPU backend for RHMC (production default) (Wave 7C)
- `experimental/polariton_predictions.py` — Tier 1 polariton platform predictions (Wave 1B)

---

## Lean module map (module → theorem count, key result)

| Module | Thms | Key Result |
|--------|------|------------|
| Basic | 0 | Type definitions |
| AcousticMetric | 8 | det(g)=-ρ², T_H formula |
| DiracFluidMetric | 9 | **Phase 5w Wave 2:** 3×3 Dirac fluid acoustic metric, c_s = v_F/√2, block-diag for quasi-1D, horizon at v=c_s, Lorentzian signature (**ALL PROVED, zero sorry**) |
| GrapheneHawking | 7 | **Phase 5w Wave 3:** Dispersive correction bound, T_eff positivity, EFT validity (D<1), subluminal robustness, dissipative negligibility (**ALL PROVED, zero sorry**) |
| DiracFluidSK | 9 | **Phase 5w Waves 5-7:** Conformal ζ=0, transport counting (2 conformal / 3 non-conf), Lorenz ratio positivity+monotonicity, KSS bound, EFT perturbativity (**ALL PROVED, zero sorry**) |
| SKDoubling | 9 | Uniqueness, FDR, zeroTemp_nontrivial |
| HawkingUniversality | 9 | Universality theorem |
| SecondOrderSK | 24 | Counting formula, positivity constraint; Phase 5u Wave 1b added `GammaH`, `gammaH_def/_via_kH/_nonneg`, `deltaDissFromTransport`, `deltaDissFromTransport_eq/_zero_iff` — grounds Γ_H = (γ₁+γ₂)(κ/c_s)² identification |
| WKBAnalysis | 15 | Damping biconditionals, turning point |
| CGLTransform | 7 | CGL FDR, Einstein relation |
| ThirdOrderSK | 14 | Parity alternation (general N) |
| GaugeErasure | 12 | Erasure theorem, U(1) survival (axiom removed) |
| WKBConnection | 17 | Decoherence, noise floor, unitarity |
| ADWMechanism | 21 | Critical coupling, NG modes |
| ChiralityWall | 17 | GS no-go requires all, TPF evasion |
| VestigialGravity | 18 | Phase hierarchy, EP violation |
| FractonHydro | 17 | Binomial monotonicity, erasure universal |
| FractonGravity | 20 | Bootstrap divergence, DOF gap |
| FractonNonAbelian | 14 | YM incompatibility |
| KappaScaling | 11 | Crossover balance, regime classification |
| PolaritonTier1 | 6 | Spatial attenuation ≥ 1, monotonicity, BEC recovery |
| SU2PseudoReality | 10 | One-link normalization, effective coupling, Binder cumulant limits |
| FermionBag4D | 16 | SO(4) integration, 8-fermion bounds, bag positivity+boundedness, Binder range, vestigial splitting |
| LatticeHamiltonian | 28 | BZ compact, GS 9 conditions, TPF 3 violations, ℓ²(ℤ) ∞-dim, round discontinuous, Hermitian trace real |
| GoltermanShamir | 14 | 9 conditions as substantive Props (C2 via ExteriorAlgebra, C3 via spectralGap, C5 via ground state, I1 via Hermitian, C4/C6 via resolvent), TPF evasion, Pauli exclusion, anti-commutation (axiom removed) |
| TPFEvasion | 12 | Master synthesis: 5 violations assembled, tpf_outside_gs_scope_main, two_violations_proved |
| KLinearCategory | 16 | SemisimpleCategory, FinitelyManySimples, Schur orthogonality, FusionRules, Vec_G D²=\|G\|, Rep(S₃) D²=6 |
| SphericalCategory | 18 | PivotalCategory (FIRST-EVER), CategoricalTrace, SphericalCategory, quantumDim, fibonacci φ²=φ+1, chirality limitation |
| FusionCategory | 14 | FusionCategoryData with axioms, FSymbolData, PentagonSatisfied, globalDimSq_pos, totalMult_unit, Frobenius-Perron |
| FusionExamples | 30 | Vec_{Z/2}, Vec_{Z/3}, Rep(S₃), Fibonacci: fusion rules, commutativity, unit fusion, τ⊗τ=1⊕τ, F-matrix, chirality |
| VecG | 9 | GradedVectorSpace, Day convolution, unit/assoc/simple tensor, dim multiplicativity |
| DrinfeldDouble | 15 | DrinfeldDoubleElement, twisted multiplication, conjugation action, D(G) unit laws, anyon counting |
| GaugeEmergence | 14 | Half-braiding, gauge emergence Z(Vec_G)≅Rep(D(G)), chirality limitation c≡0(8), Layer 1→2→3 bridge |
| SO4Weingarten | 14 | Weingarten 2nd/4th moment, channel positivity, bond weight, Planck occupation (**ALL PROVED, zero sorry**) |
| FractonFormulas | 45 | Charge counting, dispersion, retention, DOF gap, YM obstructions (**ALL PROVED**, Aristotle `4528aa2b`) |
| WetterichNJL | 18 | Fierz completeness, scalar/pseudoscalar/vector channels, NJL-ADW correspondence (**ALL PROVED**, Aristotle `4528aa2b`) |
| VestigialSusceptibility | 16 | Gamma trace, u_g positivity, bubble integral Π₀, RPA susceptibility, vestigial_before_tetrad, exponential window (**ALL PROVED**, Aristotle `9e2251cd`) |
| QuaternionGauge | 10 | Unit quaternion norm, identity, conjugate inverse, SO(4) dim, plaquette bounds, heatbath detailed balance (**ALL PROVED**, Aristotle `fb657b4d`) |
| GaugeFermionBag | 9 | Tetrad gauge covariance, metric invariance, bag weight real, SMW update, vestigial diagnostic, Binder limits (**ALL PROVED**, Aristotle `fb657b4d`) |
| HubbardStratonovichRHMC | 22 | HS identity, Kramers, multi-shift CG, complex pseudofermion Pfaffian identity |
| MajoranaKramers | 25 | Majorana Kramers degeneracy, sign-free determinant, 8x8 block structure |
| OnsagerAlgebra | 24 | Dolan-Grady definition, Davies isomorphism, Chevalley embedding into L(sl₂), GT connection (**ALL PROVED**, Aristotle `9d6f2432`) |
| OnsagerContraction | 12 | Inönü-Wigner contraction O→su(2), rescaling, commutator vanishing, anomaly encoding (**ALL PROVED**, Aristotle `36b7796f` + manual) |
| Z16Classification | 22 | Z₁₆ classification (axiom discharged→theorem), SuperModularCategory, 16-fold way, chirality strengthening mod 8→16, anomaly cancellation, Drinfeld bridge (**ALL PROVED**) |
| SteenrodA1 | 17 | A(1) 8-dim F₂-algebra, explicit multiplication table, Adem relations, Ext→Z₁₆ connection (**ALL PROVED**, first Steenrod formalization) |
| SMGClassification | 13 | AZClass tenfold way, SMGSymmetryData, HasSpectralGap typeclass, gapped interface conjecture, conditional theorems (**ALL PROVED**) |
| PauliMatrices | 15 | σ_x,σ_y,σ_z definitions, commutation [σ_i,σ_j]=2iε_{ijk}σ_k, anti-commutation, involutivity, traces (**ALL PROVED**, Aristotle `90ed1a98`) |
| WilsonMass | 11 | M(k)=3-cos kx-cos ky-cos kz, M=0 iff k=0 (all finite L), non-negativity, bounds (**ALL PROVED**, Aristotle `90ed1a98`) |
| BdGHamiltonian | 8 | BdGIndex 4×4, H_BdG σ⊗τ Kronecker structure, q_A definition, Kronecker commutator identity (**ALL PROVED**, Aristotle `90ed1a98`) |
| GTCommutation | 10 | **Central theorem** [H_BdG(k),q_A(k)]=0, 2×2 τ-space trig identity, GS evasion, bridge to TPF (**ALL PROVED**, Aristotle `18969de2`) |
| GTWeylDoublet | 12 | Model 2: Q_V+Q_A generate Onsager, emanant SU(2), Witten anomaly=element 8∈ℤ₁₆, bridges to GS/TPF/Z₁₆ (**ALL PROVED**) |
| ChiralityWallMaster | 17 | Three-pillar synthesis: GS no-go + GT positive + Z₁₆ anomaly, bridge theorems, status structure (**ALL PROVED**) |
| SMFermionData | 19 | SM fermion enum, ℤ₄ charges X=5(B-L)-4Y, all odd, component counts 16/15, anomaly contributions (**ALL PROVED**) |
| Z16AnomalyComputation | 23 | Anomaly 16≡0 / 15≡-1 mod 16, 3-gen anomaly -3, hidden sector theorem, "16" convergence (2 axioms discharged→theorems) (**ALL PROVED**) |
| GenerationConstraint | 13 | c₋=8N_f (discharged→theorem) + modular_invariance_constraint (REMOVED, was false). N_f≡0(3) **derived** as conditional, minimal N_f=3 (**ALL PROVED**, Aristotle `a1dfcbde`) |
| DrinfeldCenterBridge | 18 | Half-braiding ↔ D(G)-module bijection, conjugation identities, Mathlib Center API, bidirectional encoding (**ALL PROVED**) |
| VecGMonoidal | 12 | **MonoidalCategory(Vec_G)** proved, Center(Vec_G) category+monoidal+braided, forgetful functor (**ALL PROVED**, Aristotle `48493889`) |
| ToricCodeCenter | 25 | 4 toric code anyons, fusion rules, R(e,m)=-1, fermion self-stats, first computed Drinfeld center (**ALL PROVED**) |
| S3CenterAnyons | 22 | 8 non-abelian anyons, d=1,1,2,3,3,2,2,2, D²=36=|S₃|², A3⊗A3 decomposition, first non-abelian center (**ALL PROVED**) |
| CenterEquivalenceZ2 | 10 | Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2): bijection, fusion, braiding preserved (**ALL PROVED**) |
| DrinfeldDoubleAlgebra | 9 | D(G) as k-algebra: twisted convolution, unit laws, associativity, basis mul, abelian specialization (**ALL PROVED**, Aristotle `878b181f`) |
| DrinfeldDoubleRing | 3+4inst | DG newtype wrapper, Ring + Algebra k instances, distrib, basis_mul (**ALL PROVED**, Aristotle `52992d6a`) |
| DrinfeldEquivalence | 12 | Z(Vec_G)≅Rep(D(G)): simple counts, Hopf structure, antipode involutive, gauge emergence bridge (**ALL PROVED**) |
| WangBridge | 9 | Derives c₋=8N_f from SM fermion content (16 Weyl → c₋=8), fractional c₋ without ν_R, full chain to N_f≡0(3), "16 convergence" (**ALL PROVED**) |
| ModularInvarianceConstraint | 12 | ζ₂₄ root of unity, q-parameter shift (proved), framing anomaly 24\|c₋ ↔ phase=1, complete chain η→24→3\|N_f, Rokhlin "16" (**ALL PROVED**, Aristotle `b54f9611`) |
| RokhlinBridge | 14 | Rokhlin "16" convergence, with/without ν_R analysis (**ALL PROVED**) |
| QNumber | 11 | q-integers [n]_q as Laurent polynomials, classical limit [n]_1=n, [2]_1^4=16=DG_COEFF (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2 | 6 | **FIRST quantum group in a proof assistant**: U_q(sl_2) via FreeAlgebra+RingQuot, zero axioms, Chevalley relations (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2Hopf | 66 | **FIRST Hopf algebra in a proof assistant**: Bialgebra + HopfAlgebra instances on U_q(sl₂), coproduct/counit/antipode via liftAlgHom, S²=Ad(K), Serre coproduct (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4` + `79e07d55`) |
| Uqsl3 | 21 | **Phase 5i**: **FIRST rank-2 quantum group in any proof assistant**: U_q(sl₃) via FreeAlgebra+RingQuot, 8 generators, A₂ Cartan matrix [[2,-1],[-1,2]], 21 Chevalley relations (**ALL PROVED, zero sorry**, native proofs, 6.4s build) |
| Uqsl3Hopf | 189 | **Phase 5i Wave 2 / Tranche E COMPLETE 2026-04-14**: Full Hopf algebra wiring for U_q(sl₃). Coproduct Δ + counit ε + antipode S defined via RingQuot.liftAlgHom; all 21 Δ/ε/S relation-respect proofs done (incl. 4 antipode q-Serre cubics E12/E21/F12/F21 closed via palindromic Serre atom-bridge). S² = Ad(K₁²K₂²) per generator (Drinfeld theorem, Tranche D). 24 per-generator evaluation lemmas. 4 derived F·K commutation rules at module scope. 3 coalgebra axioms (coassoc + 2 counital). 16 antipode convolution helpers (8 right + 8 left + algebraMap + mul_step). **`Bialgebra` instance** (via Bialgebra.ofAlgHom) and **`HopfAlgebra` instance** (via direct constructor) wired. **0 sorry**, ~5230 lines. |
| QuantumGroupGeneric | 29 | **Phase 5m Wave 1 (2026-04-16)**: **FIRST parameterized quantum group in any proof assistant**: `QuantumGroup k A` for arbitrary Cartan matrix A via `RingQuot (QGRel k A)`. 4r generators (E_i, F_i, K_i, K_i⁻¹), 11 relation types. Cartan matrices A₁-A₃, D₄, B₂, C₂, G₂, B₃ with symmetrizability + determinant verification (**ALL PROVED, zero sorry**) |
| QuantumGroupCoproduct | 44 | **Phase 5m Wave 2 (2026-04-16)**: Generic coproduct Δ for U_q(𝔤). 11/11 QGRel relation-respect proofs (incl. SerreE/F_quad via palindromic atom-bridge, EF_diag via diamond bypass). Descended `qgComul` via `RingQuot.liftAlgHom`. Eval lemmas E/F/K/Kinv. **1347 LOC, 0 sorry** |
| QuantumGroupAntipode | 25 | **Phase 5m Wave 2 (2026-04-16)**: Generic antipode S for U_q(𝔤) via `MulOpposite`. 11/11 QGRel respect proofs. Anti-multiplicativity S(ab)=S(b)S(a). Descended `qgAntipode`. **811 LOC, 0 sorry** |
| QuantumGroupHopf | 31 | **Phase 5m Wave 2 (2026-04-16)**: Generic HopfAlgebra instance for U_q(𝔤). Counit (11/11 + descent), coalgebra (coassoc + 2 counit laws), Bialgebra via `Bialgebra.ofAlgHom`, convolution laws via `FreeAlgebra.induction` + `TensorProduct.exists_finset`. **563 LOC, 0 sorry. First generic quantum group HopfAlgebra in any proof assistant** |
| QuantumGroupInstantiation | 39 | **Phase 5m Wave 1 strengthening (2026-04-16)**: `qgA1EquivUqsl2 : QuantumGroup k cartanA1 ≃ₐ Uqsl2 k` + `qgA2EquivUqsl3 : QuantumGroup k cartanA2 ≃ₐ Uqsl3 k`. Full AlgEquiv via forward/backward AlgHom + roundtrip via `RingQuot.ringQuot_ext'` + `FreeAlgebra.hom_ext`. **629 LOC, 0 sorry, 0 sorryAx** |
| QuantumGroupMeta | 16 | **Phase 5m Wave 4 (2026-04-16)**: Exceptional Cartan matrices E₆/E₇/E₈/F₄ with symmetry verification. CartanTypeData for all exceptional types. Named generator abbreviations for SU(4) + E₆. Level 1 alcove: E₆₁=ℤ₃, E₇₁=ℤ₂, E₈₁=trivial, F₄₁=ℤ₂. **First E₆/E₇/E₈ quantum group generators in any proof assistant. 220 LOC, 0 sorry** |
| KacWaltonFusion | 63 | **Phase 5m Wave 3 (2026-04-15, updated 2026-04-16)**: Kac-Walton fusion algorithm parameterized over arbitrary Cartan types. `buildWeightDiagram` for minuscule reps via BFS building-up. SU(5)₁ Z₅ fusion ring verified (8 theorems). Cross-validated generated vs hardcoded WDs. SU(2)₁₋₃, SU(3)₁, SU(4)₁, G₂₁ Fibonacci, B₂₁ Ising fusion. **741 LOC, 0 sorry. First Kac-Walton implementation in any proof assistant** |
| SU2kFusion | 29 | **SU(2)_k fusion at k=1,2,3**: universal truncated CG rule, Ising (sigma²=1+psi), Fibonacci (tau²=1+tau), charge conjugation, assoc+comm, Fibonacci subcategory closed (**ALL PROVED by native_decide, zero sorry**) |
| Uqsl2Affine | 9 | U_q(sl_2 hat) affine quantum group: 6 generators, Chevalley + cross-relations, K invertibility, coideal property statement (**ALL PROVED, zero sorry**) |
| SU2kSMatrix | 16 | SU(2)_k S-matrices at k=1,2: unitarity S*S^T=I, Verlinde formula, non-degeneracy/modularity (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RestrictedUq | 11 | Restricted quantum group u_q(sl_2): E^ell=F^ell=0, K^ell=1 nilpotency/torsion, Chevalley→restricted, small_uq→SU(2)_k connection (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RibbonCategory | 4 | BalancedCategory, RibbonCategory, MTC definitions, su2k1/su2k2 modular (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| E8Lattice | 19 | E8 Cartan matrix: det=1, even diagonal, symmetric, positive definite, Rokhlin gap σ=8, hyperbolic plane, Serre mod 8, classification (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| AlgebraicRokhlin | 10 | Algebraic Serre theorem σ≡0 mod 8, unimodular/even/symmetric defs, characteristic vectors, E8 bridge (**ALL PROVED, zero sorry**) |
| QSqrt2 | 3 | Q(√2) for Ising MTC. **Phase 5i Wave 4a refactor (2026-04-15)**: Mul delegates to `PolyQuotQ.mulReduce 2 ![2, 0]` via toPoly/ofPoly; struct API preserved (**ALL PROVED, zero sorry**) |
| QSqrt5 | 7 | Q(√5) for Fibonacci MTC: golden ratio φ²=φ+1, φ·φ⁻¹=1, Fibonacci F²=I. **Phase 5i Wave 4b refactor (2026-04-15)**: Mul delegates via `mulReduce 2 ![5, 0]` (**ALL PROVED by native_decide**) |
| FibonacciMTC | 11 | Fibonacci MTC: F-symbols in Q(√5) isotopy gauge, F²=I PROVED, PreModularData instance, chirality (**ALL PROVED, zero sorry** — native_decide over Q(√5)) |
| Uqsl2AffineHopf | 201 | U_q(ŝl₂) Hopf algebra: coproduct/counit/antipode via RingQuot.liftAlgHom. **ALL PROVED, zero sorry** — all 8 q-Serre proofs closed (4 comul + 4 antipode). Bialgebra + HopfAlgebra instances WIRED. **Phase 5e Wave 8 complete 2026-04-15**: 20 new theorems for per-generator antipode (`uqAff_antipode_*`) + K-conjugation helpers + per-generator S² identities (`uqAff_antipode_squared_*`). Wave 8 original spec `S² = Ad(K₀K₁)` mathematically wrong for affine (rank-deficient Cartan); corrected to per-generator form with inline historical note. |
| VerifiedStatistics | 6 | Statistics extension: sample variance non-neg PROVED, Cauchy-Schwarz bound, jackknife mean-case, N_eff ≤ N (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| KerrSchild | 7 | Kerr-Schild metrics: null vector, radial_null PROVED, Sherman-Morrison inverse, Schwarzschild, DOF counting (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| SU2kMTC | 11 | **Phase 5d**: Ising F-symbols (F^σ_{ψσψ}=-1 corrected), pentagon, ModularTensorData instance (**ALL PROVED, zero sorry** — native_decide over Q(√2)) |
| CoidealEmbedding | 6 | **Phase 5d**: Coideal subalgebra embedding B_i into U_q(ŝl₂), Dolan-Grady from Chevalley (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| RepUqFusion | 13 | **Phase 5d**: Rep(u_q) → SU(2)_k fusion data correspondence, dim formulas, Peter-Weyl (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| SpinBordism | 8 | Spin bordism → Rokhlin → Wang chain, SpinBordismData structure, anomaly with/without ν_R (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| VerifiedJackknife | 5 | First verified statistical estimators: jackknife variance non-neg, autocovariance_zero non-neg, intAutocorrTime bounds (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| TetradGapEquation | 20 | **First tetrad gap equation in any formalism**: NJL-type Δ=G·N_f·Δ·I(Δ), gapIntegral, criticalCoupling=8π²/(N_f·Λ²) (PROVED, matches ADW V_eff), IVT existence, Banach uniqueness, bifurcation at G_c, vestigial connection (**ALL PROVED, zero sorry**, Aristotle `79e07d55` + `986b9f66`) |
| StimulatedHawking | 11 | **Phase 5d**: Stimulated Hawking amplification, signal-to-noise, phonon statistics (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| CenterFunctor | 9 | **Phase 5d**: Center(Vec_G) ⥤ ModuleCat(DG) — **0 sorry, 2 tracked hypotheses** (H_CF1, H_CF2 as `def ... : Prop`). Data-level evidence via CenterEquivalenceZ2 + S3CenterAnyons. |
| QCyc16 | 6 | **Phase 5e**: Q(ζ₁₆) cyclotomic field: ζ⁸=-1, ζ¹⁶=1, (√2)²=2 (**ALL PROVED by native_decide, zero sorry**) |
| QCyc5 | 9 | **Phase 5e**: Q(ζ₅) cyclotomic field: ζ⁵=1, cyclotomic relation, Fibonacci hexagon E1-E3, twist consistency (**ALL PROVED by native_decide, zero sorry**) |
| IsingBraiding | 25 | **Phase 5e**: COMPLETE braided Ising MTC: R-matrix, twist, 6 hexagon eqs, 4 ribbon conditions, Gauss sum, **trefoil=-1** (**ALL PROVED by native_decide, zero sorry, FIRST verified knot invariant**) |
| QSqrt3 | 8 | **Phase 5e**: Q(√3) for SU(2)₄ S-matrix: unitarity diagonal+off-diag, det non-zero (**ALL PROVED by native_decide, zero sorry**) |
| QLevel3 | 19 | **Phase 5e**: Q[x]/(20x⁴-10x²+1) for SU(2)₃ S-matrix: ALL 10 unitarity entries, quantum dim golden ratio (**ALL PROVED by native_decide, zero sorry**) |
| SU3kFusion | 99 | **Phase 5i**: **FIRST SU(3)_k fusion in any proof assistant**: SU(3)₁ Z₃ fusion (3 objects) + SU(3)₂ (6 anyons, Fibonacci subcategory τ⊗τ=1+τ), charge conjugation, associativity+commutativity (**ALL PROVED by native_decide, zero sorry**) |
| GaugingStep | 34 | **Phase 5h**: Gauging obstruction: NotOnSiteSymmetry, SymmetryDisentangler, GT Models 1+2, SM anomaly 16≡0 mod 16, SMGPhaseData (BCH+HW), Golterman-Shamir propagator-zero, ChiralityWall3DStatus (**ALL PROVED, zero sorry**) |
| FermiPointTopology | 33 | **Phase 5j W1-3**: Fermi-point gauge emergence: VZ Theorem 2.1 (|N|=1 → U(1)+vierbein), Mechanism A vs B, charge splitting, multi-Weyl classification (|N|≤3), SU(2) emergence chain (3 theorem + 2 heuristic + 1 speculative), SU(3) more speculative than SU(2), full emergence chain status, bridges to EmergentGravityBounds/GaugingStep/SPT (**ALL PROVED, zero sorry**) |
| PolyQuotQ | 1 | **Phase 5i Wave 4a+4c-part1+4d (2026-04-15)**: **First generic computable polynomial quotient ring over ℚ in any proof assistant**. Parametric `PolyQuotQ n` structure (`Fin n → ℚ` coeff tuples, `deriving DecidableEq`). `mulReduce n r x y` via `Array (Array ℚ)` power table + eager output materialization — avoids both exponential-recursion and lazy-closure-reeval pitfalls that disabled earlier designs under native_decide. O(n³) per mul at arbitrary degree × density. Mathlib-upstream-ready (standard copyright + docstring). QCyc3 extracted to own module (4d). Wave 4d `bf5efce`. |
| PolyQuotOver | 1 | **Phase 5i Wave 4b.ext+4d (2026-04-15)**: Generic tower extension `PolyQuotOver K m` over arbitrary `[DecidableEq K]` base ring. `mulReduce2` (degree-2 specialization, eager materialization) is the current tower primitive; `mulReduceOver` (general m) retained with documented performance caveats. First non-trivial user is QCyc15SqrtPhi (Q(ζ₁₅)[w]/(w²-φ)). Mathlib-upstream-ready. |
| QCyc3 | 9 | **Phase 5i Wave 4d (2026-04-15)**: Q(ζ₃) = ℚ[x]/(x²+x+1) concrete instance of `PolyQuotQ 2` with reduction `![-1,-1]`. Extracted from old PolyQuotQ.lean during Mathlib-style cleanup. Preserves original 9 theorems (ζ²=-1-ζ, ζ³=1, cyclotomic_sum, ζ≠1, ζ²≠1, SU(3)₁ S-matrix row orthogonality). Mathlib-style docstring. |
| QCyc15 | 8 | **Phase 5i Wave 4c-part1 (2026-04-15)**: Q(ζ₁₅) = ℚ[x]/Φ₁₅(x) as `abbrev QCyc15 := PolyQuotQ 8`. Reduction `![-1, 1, 0, -1, 1, -1, 0, 1]` (7 nonzero terms — densest cyclotomic at degree 8). Key constants: ζ, ζ², ..., ζ⁷, √5, φ, 1/φ, ω₃=ζ⁵. Theorems: ζ¹⁵=1 (4-mul chain), (√5)²=5, φ²=φ+1, φ·(1/φ)=1, ω₃³=1, cube-root sum = 0. First PolyQuotQ instance at degree 8 for a proper cyclotomic. |
| QCyc15SqrtPhi | 5 | **Phase 5i Wave 4c-part3 (2026-04-15)**: **First non-cyclotomic number field in the project**, Q(ζ₁₅, √φ) = Q(ζ₁₅)[w]/(w²-φ), degree 16 over ℚ, via `PolyQuotOver QCyc15 2`. Non-Galois — √φ escapes every cyclotomic field per Kronecker-Weber (x⁴-x²-1 splitting field contains ±i/√φ). Theorems: w²=φ, φ·(1/φ)=1, (1/√φ)²=1/φ, w≠0. Enables SU(3)_2 Fibonacci F-symbols. |
| SU3k2SMatrix | 14 | **Phase 5i Wave 4c-part2 (2026-04-15)**: **First rank-6 MTC modular data in any proof assistant**. 9 S-matrix entry classes A-I (×15 scaling) as QCyc15 values, full 6×6 S-matrix, 6 T-matrix diagonal entries (4 distinct: ζ¹³, ζ², ζ⁸, ζ⁷). Theorems: S=Sᵀ (native_decide over 36 entries), Z₃ simple-current identities (G=A·ω₃, H=A·ω₃², I=-A, orbit sum = 0), T¹⁵=1 for all 4 distinct T-matrix values (14-deep chained muls each), T₀·T₃=ζ⁶, Fibonacci subcategory entries (S₀₀=A, S₀₅=B, S₅₅=I). |
| SU3k2FSymbols | 9 | **Phase 5i Wave 4c-part3 (2026-04-15)**: **First SU(3)₂ F-symbols in any proof assistant**. Fibonacci 2×2 F-matrix over Q(ζ₁₅, √φ): F=[[1/φ, 1/√φ], [1/√φ, -1/φ]]. F²=I proved entry-by-entry (4 entries, all native_decide). Supporting: golden ratio φ²=φ+1 in the non-cyclotomic tower, 1/φ²+1/φ=1, Fibonacci equation (1/φ)²+(1/√φ)²=1. Full 120-entry catalog deferred (requires external Ardonne-Slingerland data). |

---

## Pipeline invariants (from WAVE_EXECUTION_PIPELINE.md)

1. `formulas.py` is canonical — only place physics formulas live
2. `constants.py` is canonical — only place constants + Aristotle registry live
3. `visualizations.py` is canonical — only place figure functions live
4. Every formula has a Lean theorem (zero sorry)
5. Every computed quantity has bounds (CHECK 12)
6. Every paper claim traces to computation (CHECK 14)
7. Narrative derives from data (feasibility claims need computed support)
