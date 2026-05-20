# SK-EFT Hawking Project: Comprehensive Inventory

**Repository Root:** `SK_EFT_Hawking/`

**Project Summary:** Formal verification of dissipative effective field theory corrections to analog Hawking radiation and a broader chain-of-chains connecting emergent-physics mechanisms to the Standard Model, quantum information, dark-sector phenomenology, and experimental analog-gravity platforms. Eighteen papers span: Phase 1 dissipative EFT corrections (Papers 1, 2); Phase 3 gauge erasure, exact WKB connection, ADW gap equation, vestigial gravity (Papers 3, 4, 5, 6); Phase 5 and 5a–5b chirality wall formalization + SM anomaly + modular generation (Papers 7, 8, 9, 10); Phase 5b–5i first quantum group / Hopf-algebra / rank-2 quantum group / SU(3)_k fusion (Paper 11); Phase 5d polariton analog Hawking (Paper 12); Phase 5e–5f braided modular tensor categories + knot invariants (Paper 14); Phase 5h formal-verification methodology (Paper 15); Phase 5k WRT TQFT pipeline formalization (Paper 16b); Phase 5w graphene Dirac-fluid SK-EFT (Paper 16a); Phase 5x dark-matter classification + SFDM merger forecast + fracton DM viability (Paper 17); Phase 5t Fermi-Hubbard doublon geometric gate (Paper 18); and Phase 5y machine-checked Gibbs–Duhem emergent-vacuum obstruction + closed-form vestigial EOS (no paper per user preference, harvest formalized into Lean).

Infrastructure across phases: Phase 5 Layer 1 categorical scaffolding, Weingarten / fracton / NJL formalization, vestigial susceptibility, Waves 7A–7C (gauge-link MC + RHMC); Phase 5c affine U_q(ŝl₂) / restricted u_q / SU(2)_k fusion and S-matrix / E8 lattice / algebraic Rokhlin / spin-bordism-to-Wang chain / verified statistical estimators; Phase 5d tetrad gap equation, Ising/Fibonacci MTC, coideal embedding, Rep(u_q) fusion correspondence; Phase 5e cyclotomic fields Q(ζ₁₆)/Q(ζ₅), Ising hexagon + ribbon + trefoil, Fibonacci hexagon + twist, SU(2)₃/SU(2)₄ S-matrix unitarity; Phase 5h-5j gauging obstruction, Fermi-point topology, U_q(sl₃), SU(3)_k fusion; Phase 5k-5p WRT TQFT pipeline, topological quantum computation, generic parameterized U_q(𝔤) + Kac–Walton fusion, anomaly inflow / 3450 gappability / Villain Hamiltonian / SPT stacking / TPF disentangler, Muger center + SymmetricCategory instance + det(S)≠0 → isMugerTrivial bridge, Frobenius–Perron eigenvalue dimensions, Fibonacci universality; Phase 5q machine-checked Ext^n_{A(1)}(F₂, F₂); Phase 5r change-of-rings discharge of H2; Phase 5s FK 2+1D Cayley-calibrated gapped interface, general modularity theorem, instanton zero-mode counting, SU(2)_k k=5 extension; Phase 5t Fermi-Hubbard dimer + minimal Berry-phase theorem; Phase 5u paper revision cycle (Paper 1 dimensional bug, Paper 12 Falque parameter reconciliation, textbook-fact and bibliography corrections in Papers 3/10); Phase 5v knowledge-graph foundation + 11-gate readiness state machine + Stage 13 adversarial reviewer + Stage 14 QI register; Phase 5w graphene Dirac-fluid platform; Phase 5x dark-sector phenomenology; Phase 5y terminal closure (Gibbs–Duhem obstruction, q-theory no-go, vestigial-EOS closed form, four-factor orthogonality, classification-table consolidation).

Current scale: **6645 theorems** (6620 substantive + 25 placeholder as tracked in `constants.PLACEHOLDER_THEOREMS`; Session 49 added ~19 new declarations / ~570 LoC to `FibSU2LieBundle.lean`, Session 50 added 6 new substantive theorems / ~281 LoC across `SU2LieAlgebra.lean` §15 + `FibSU2LieBundle.lean` §11 + §12, **Session 51 added 7 new substantive theorems + 1 noncomputable def / ~133 LoC across `FibSU2LieBundle.lean` §13 + §14** advancing R5.4 to Layer F.20.c.a + F.20.c.b (BCH/IFT iteration substrate opens via `liePartMat` Ad-equivariance + σ_Fib bundle commutativity with `liePartMat`) — not yet reflected in `docs/counts.json` 2026-05-19 21:03 regen pre-Session-49 — re-regen pending), **0 axioms** (history: `aa_residual_interior_at_one_for_hom` dropped 2026-05-13 in commit `f44c60d` ("R2 SOUNDNESS AUDIT", count 2→1); `gapped_interface_axiom` retired in commit `d282677` ("Phase 5h Wave 2 → TPFConjecture tracked-Prop", session 29, count 1→0) — both pre-R5.4; R5.4 itself ships zero new axioms and zero axiom discharges through Session 51), across **367 modules** (Sessions 49 + 50 + 51 ship entirely within existing `FibSU2LieBundle.lean` + `SU2LieAlgebra.lean`, no new modules), **0 sorry project-wide**. 12737 total Lean declarations (pre-Session-49 counts.json regen); ~5398 definitions (+1 noncomputable `liePartMat` def in Session 51), 252 structures, 388 instances, 87 inductives. 322 Aristotle-proved across 44 runs. 99 test files (4179 pytest cases), 154 figure functions in `visualizations.py`, 87 notebooks, 130 Python source modules, 42 papers, 339+ CITATION_REGISTRY entries. **Synced 2026-05-20** — counts refreshed from `docs/counts.json` post-**Phase 6p Wave 2c.4a-R4.2.d.R5.4 FKLW Fibonacci SU(2) density substrate program (Sessions 30–51, 30 PUBLIC commits, ~2859 LoC, 6 NEW modules under `lean/SKEFTHawking/FKLW/`)**. The structural reduction chain `BCH-spanning witness → DenseInSpecialUnitary 3 2 ρ_Fib_SU2` is now CONNECTED end-to-end via Cartan-A/B/C/D + Layer E + Layers F.1–F.19; the σ_Fib 3-bundle ℝ-linear-independence at the `paulI_x` witness is UNCONDITIONAL (Session 49 ships F.16 ω-cancellation + F.17.a/b F-decomposition + σ_Fib_2 (0,0)-entry closed form + F.18 `pauliDet ≠ 0` + F.19 lin-indep at paulI_x); Session 50 (Layers F.20.a + F.20.a-app + F.20.b) lifts the σ_Fib 3-bundle at every non-zero scalar multiple of `paulI_x` to a BASIS of 𝔰𝔲(2): lin-indep (F.19) AND spans (F.20.a-app) AND scaled-spanning at every `t·paulI_x` with `t ≠ 0` (F.20.b); **Session 51 (Layers F.20.c.a + F.20.c.b) opens the BCH/IFT iteration substrate: F.20.c.a ships `liePartMat` (canonical Lie-part-relative-to-identity for any 2×2 complex matrix) + Ad-equivariance under specialUnitaryGroup conjugation; F.20.c.b ships σ_Fib bundle commutativity with `liePartMat` (the σ_Fib bundle of Lie parts equals the Lie parts of the σ_Fib bundle), connecting the small-h BCH iteration on `h ∈ H_Fib` to the Lie-algebra spanning analysis on `liePartMat h ∈ 𝔰𝔲(2)`**; all kernel-only `[propext, Classical.choice, Quot.sound]`, zero new axioms. Substantive remaining for the full bridge to unconditional density: F.20.c.c+ (BCH iteration spanning composing Cartan-D + R5.3/D.3.{e,f,g,h,i.1} substrate with F.20.c.a/b `liePartMat` to produce IFT U witness) + F.21 (apply Layer E `fibonacci_density_from_exp_image_subset` to F.20.c witness). Phase 6 (a/b/c/d/f/p) end-to-end ship: 7 new core papers (paper27, paper29, paper32, paper34–38) + `note_rt_ch_bounds` + 17 Phase-6 Lean modules covering BBN, equivalence principle, strong-CP / topological dark energy, QEC holography bridge, center-symmetry confinement, chiral SSB / GMOR, CFL chiral Lagrangian, RT/Casini-Huerta bounds, energy conditions, plus the Track A–C Phase 6a Wave-1–5 backbone (linearized EFE, FLRW dynamics, gravitational waves, BH entropy + thermodynamics) and the Phase 6f.1+6f.2+6f.3 classical-GR algebra (Curvature, EinsteinTensor, EnergyConditions cross-layer).

**Phase 5v Wave 10 (sentence-level paper provenance pipeline)** shipped end-to-end 2026-04-26: cross-tab change-bus (`scripts/verification_state.py`), sole-writer sentence CLI (`scripts/sentence_state.py`), cross-precision-safe freshness propagation (`scripts/last_modified.py`), cross-paper cluster detection (`scripts/cluster_detect.py`), 3-column Paper Provenance v2 UI w/ keyboard nav + state machine + per-link verification UI + audit log drawer, `validate.py --check claim_clusters_fresh` (CHECK 15d), 16-test pytest module w/ tmp_path-isolated fixtures (`tests/test_paper_provenance_v2.py`), foundations closure pass (triggered_by field + prune subcommand + rebuild_prose_state + isolated_v2_state context manager). All four roadmap follow-ups closed.

**Phase 6 strengthening + retrofit pass (2026-04-28-1130/1200)** applied across all seven Phase-6 papers (paper32, paper34, paper35, paper36, paper37, paper38, note_rt_ch_bounds). Two deferred adversarial REQUIREDs closed (`H_BothActiveGivesInconsistency` threshold tightened from `> 1e-10` to `> zhitnitskyDE_eV4 0.1` so `h_qtheory_pos` is genuinely load-bearing; P5 self-equality tautology `step_target_can_test_vestigial_relics` removed from `EquivalencePrinciple.lean` — substantive content survives via `vestigial_relics_below_microscope_bound : 1e-18 < 1e-15`). Eight RECOMMENDEDs cleared in the same pass — most consequential: `zhitnitsky_DE_far_below_planck` upper bound tightened `1e10 → 1e-8` (now certifies ≥ 120 orders below `M_P^4` matching prose); decorative `EquivalencePrinciple.module_summary_marker` removed; redundant `ising_nu_above_0_6` + `potts_nu_below_0_6` removed (load-bearing comparison `ising_nu_gt_potts_nu` survives, threshold-pair was P3 against an arbitrary 0.6); paper-prose disclosures added for tracked-Prop predicates and `S_horizon` parameter usage. **counts.tex `\input{}` macroification retrofit** for the seven Phase-6 papers: `update_counts.py` extended with `_module_thm_count_strict` (BOL-anchored to avoid over-counting docstring "lemma" prose) + a `_pytest_count` helper; 14 new macros added (`\strongCpDeThms`, `\strongCpDeTests`, `\epThms`, `\epTests`, `\qecHolographyThms`, `\qecHolographyTests`, `\centerSymmThms`, `\centerSymmTests`, `\chiralSsbThms`, `\chiralSsbTests`, `\cflThms`, `\cflTests`, `\rtChThms`, `\rtChTests`); each paper's literal counts replaced with the macros — counts.tex now drives both abstract and §formalization values, eliminating count-literal drift permanently. Cross-wave strengthening (2026-04-28-0030) removed three weak Phase 6c theorems (W4 `scramblingTimeBound_pos_iff_nontrivial`, W4 `codeDistance_pos_iff_non_abelian`, W5 `rt_classical_inconsistent_with_kaul_majumdar`); contents preserved by inlining into correctness-push bodies.

**pytest `slow` marker retrofit (2026-04-28-1200).** Three modules tagged `pytestmark = pytest.mark.slow` (`tests/test_extract_lean_deps.py`, `tests/test_build_graph.py`, `tests/test_graph_integrity.py` — each calls `load_lean_deps()` which re-triggers Lean `ExtractDeps.lean` walking 4385+ declarations, 5–10 min per call). `pyproject.toml` `[tool.pytest.ini_options]` declares `addopts = "-m 'not slow'"` plus a `markers` section. Two torch-dependent modules (`tests/test_hs_rhmc.py`, `tests/test_stencil_dirac.py`) switched to `pytest.importorskip("torch")` so they auto-skip cleanly without env-failure noise. Default `uv run pytest tests/` reports **3254 passed, 3 skipped, 66 deselected in ~2s** (was 9:26 — 264× speedup). Run-everything command for wave-close / pre-submission verification: `uv run pytest tests/ -m '' -v` (~10 min).

**Last verified:** 2026-05-12. **Phase 6p Wave-Cluster recovery + substrate-upgrade ship (2026-05-12 PM).** Axiom count 3 → 2 via constructive elimination of `bch_order_2_axiom` (corrected sign+scope; refactored to `exp(iF)` form matching Dawson-Nielsen 2005 Lemma 3 verbatim; δ≤1 cap; linear K=200·δ bound) AND replacement of unsound `bridge_axiom_FKLW_general` (provable d=1 counterexample) with strictly-narrower sound `aa_residual_interior_at_one_for_hom` (requires MonoidHom + d≥2; only asserts interior-density). ~1.3K LoC Mathlib-grade in-tree topology infrastructure shipped: `MatrixTaylor.lean` (322), `FKLW/SpecialUnitaryTopology.lean` (291: IsCompact U(d)/SU(d)), `FKLW/SpecialUnitaryPathConnected.lean` (743: PathConnected via CStarMatrix bridge + phase-shift path + det-correction). New `FibonacciQuintetTrueRep.lean` (427 LoC, true 4-strand HZBS rep, 8-conjunct spanning closure post-P2-strengthening). Phase 6p Wave 3a.2.3c-substrate-upgrade T-gate substrate ship: `QCyc80.lean` (Q(ζ₈₀) via `abbrev := PolyQuotQ 32` + `Mul` via `PolyQuotQ.mulReduceWithTable 32 powerTable80` + Nat.fold inner loop; native_decide algebraic-identity theorems deferred to QCyc80Verify per build-time-ergonomics discipline — compile cost dropped from 5+ GB / minutes per theorem to ~5s flat); `QCyc80Ext.lean` (Q(ζ₈₀, √φ), degree 64); `TgateFibBraid.lean` refactored to consume QCyc80Ext (L=46 random-search braid; Frobenius² 3.83e-4 vs QCyc40 floor 1.27e-2 — 33× substrate gain; algorithm-quality gap to ε ≤ 10⁻³ separable, deferred to Wave 3a.2.3d via KBS or GA-Solovay-Kitaev). Project axioms: `gapped_interface_axiom` (pre-existing) + `aa_residual_interior_at_one_for_hom` (Phase 6p Wave 2c residual; remaining content = AA Lemma 6.1/6.2 ε-iteration interior-density, ~150 LoC of substantive analytic work). Full project builds clean at 8612 jobs / ~800 MB peak.

**Phase 6m → 6n → 6o → 7a → Phase 7 absorption snapshot (2026-05-07).** Phase 6m three-track DE closure complete (Causal-Set / Entropic-Gravity / Jacobson-Thermo-GR DE — modules `CausalSetDarkEnergy.lean` / `EntropicGravityDarkEnergy.lean` / `JacobsonThermoGRDarkEnergy.lean` / `DarkSectorClassificationExtension.lean`); Phase 6n α/β/γ/δ/ε/ζ/η/θ/ι sub-waves SHIPPED (math substrate: Glorioso-Liu axiomatic SK-EFT skeleton in `GloriosoLiu/`, Quantum Crooks no-go in `QuantumCrooks/`, LDP framework in `LDP/`, Sakharov–Crooks horizon bridge in `CrooksAnalogHawking/`, SymTFT audit `SymTFTAudit/` covering Drinfeld center / pseudo-unitary / Deligne-tensor / free-k-linear / categorical-cc closures); Phase 6o α/β/γ/δ/ε/ζ/η sub-waves SHIPPED (boostless soft theorems `SoftTheorems/`, G4 Kerr-Schild double copy `KerrSchild/` + `DoubleCopy/`, APS-η `APSEta/`, Schellekens chain reframing `Schellekens/`, ETH refutation `ETH/`, Itô / LDP for I3 in `Itô/` and `LDP/`); Phase 6o Wave 4a SHIPPED 2026-05-08 (Sakharov 4-criterion biconditional retired in favour of one-way implication + load-bearing depletion : ℝ field on `SakharovExtended` per FLS BEC primary-source asymmetry). Phase 7a sub-waves 7a.1.1/1.2/1.3/1.4/1.5/1.6/2/3/4 SHIPPED — paper-bundle architecture frozen (`docs/PAPER_STRATEGY.md` 14 publication targets in `papers/{F,D1-D5,L1-L3,I1,I2,I3,E1,E2}/`); sourceless I2 lift; 14-step lift-procedure freeze (`docs/BUNDLE_LIFT_PROCEDURE.md`). Phase 7 absorption Sessions 1–5 SHIPPED (2026-05-06 → 2026-05-08; D.2/D.3/D.4 absorption of Phase 6n + 6o material into all 14 bundles via `scripts/bundle_append.py`; primary-source PDF cache 213 → 264 / 0 missing; 51 cached PDFs back-filled; honest-correction substitutions including Luciano AIC/BIC relabel + BelgiornoCacciatori2024 fabricated-citation repair). All 14 bundles ALL-GREEN per `docs/BUNDLE_READINESS_HEATMAP.md`. **Axioms:** `gapped_interface_axiom` in `SPTClassification.lean` is the lone surviving project axiom (`gaussianSaddleAsymptotic` retired in Phase 6a Wave 7). **Bundle architecture (Phase 6i Wave 7 + Phase 7a freeze):** 14 publication targets in `papers/{F,D1-D5,L1-L3,I1,I2,I3,E1,E2}/` — see `docs/PAPER_STRATEGY.md` and `docs/PAPER_DRAFT_MAPPING.md`.

**Earlier verified:** 2026-04-30-3030. **Section 2 module table re-synced 2026-04-30 post-Phase-6j-CLOSURE + W3+W4 dossier integration §9** (W3 `ScramblingTimeQuantitative.lean` extended +5 thms / +1 def to 17 thms / 2 defs / 410 LOC; W4 `HolographicCFunctionMTC.lean` extended +4 thms / +1 def to 10 thms / 2 defs / 429 LOC; project totals refreshed to ~4756 substantive theorems / 230 modules / library 8494 jobs PASS). **Both W3+W4 deep-research dossiers integrated** (returned at `Lit-Search/Phase-6j/Phase 6j Wave 3 Dossier — Quantitative Scrambling Time on MTC Substrate.md` + `Phase 6j Wave 4 — Holographic c-Function on Horizon-MTC Substrate.md`; task files moved to `Lit-Search/Tasks/complete/`). **W3 §9 dossier-corrective additions:** entanglement-jump constants (HNTW arXiv:1403.0702) + `fundamentalQuantumDim_SU2k` named def with structural-correction theorem `fundamentalQuantumDim_SU2k_at_k_four_lt_two` (`√3 < 2` falsifies roadmap's `2 cos(π/(k+2)) = d_max` at k=4). **W4 §9 dossier-corrective additions:** `cLogTotal := log D²` named def + corrected Fibonacci closed form `log((5+√5)/2)` + dossier-corrective inequality `cLogTotal_fibonacci_ne_log_goldenRatio_sq` (substantively falsifies original roadmap's arithmetically-wrong `c(Fib) − c(triv) = log φ²` claim).  Per dossier §4.5: minimal-model Virasoro central-charge recovery DROPPED entirely (verdict D — Virasoro c not extractable from MTC alone).  Counts in this section are a rolling snapshot; `docs/counts.json` (regenerated by `scripts/update_counts.py`) is the single source of truth for live numbers.

**Prior verified 2026-04-29-3120.** Phase 6f Wave 6 SHIPPED — `TetradFormalism.lean` post-closure strengthening pass applied; project totals at that snapshot: 4559 substantive theorems / 201 modules / 94 test files / 142 figures.

**Earlier sync 2026-04-29-3020. Section 2 module table re-synced 2026-04-29 post-6f.5-ship** (Phase 6f W5 `ADMFormalism.lean` row added; project totals refreshed to 4556 substantive theorems / 200 modules / 93 test files / 141 figures). Counts in this section are a rolling snapshot; `docs/counts.json` (regenerated by `scripts/update_counts.py`) is the single source of truth for live numbers.

**Earlier sync 2026-04-29-2920. Section 2 module table re-synced 2026-04-29 post-6f.4-ship** (Phase 6f W4 `ExactSolutions.lean` row added; project totals refreshed to 4545 substantive theorems / 199 modules / 92 test files / 140 figures). Counts in this section are a rolling snapshot; `docs/counts.json` (regenerated by `scripts/update_counts.py`) is the single source of truth for live numbers.

**🎉 Phase 6f FULLY CLOSED (2026-04-29).** Wave 6f.6 `TetradFormalism.lean` shipped, completing all 6 Phase 6f waves end-to-end. Post-closure strengthening pass (2026-04-29 user-prompted audit) cut 3 additional rfl-rename / Iff.rfl-on-identity-def theorems (1 each in 6f.4, 6f.5, 6f.6). Total Phase 6f: **64 substantive theorems** / 0 sorry / 0 new axioms / 6 modules / 6 figures / 176 cross-layer pytest cases. Total cuts: 13 (10 first-pass + 3 post-closure: `deSitter_Ricci_eq` rfl-rename to 6f.1's `constantSectional_minkowski_Ricci_eq` + `schwarzschild_adm_mass_pos_iff` Iff.rfl on identity-function def + `torsionResidual_zero_iff` Iff.rfl on identity-function def — all P5 structural-tautology patterns; substantive content remains in cross-bridges and named-def closed forms). **First formalization in any proof assistant** (per audit §3E + 6f.1-6f.6 first-formalization context) of the algebraic-level classical-GR backbone: Riemann/Ricci/scalar (6f.1) + Einstein tensor + Λ-vacuum biconditional (6f.2) + energy conditions (6f.3) + exact-solutions catalog (6f.4) + ADM 3+1 decomposition (6f.5) + tetrad formalism (6f.6). Mathlib upstream port queued for once Bonn's Massot↔Rothgang `CovariantDerivative` API lands; deferred items (Schwarzschild vacuum-Ricci, second Bianchi `∇G = 0`, ADM `^(3)R` from γ, Cartan structure equations from d/∧) are awaiting that upstream landing.

**Phase 6f Wave 6 SHIPPED (2026-04-29).** `TetradFormalism.lean` ships through Stages 1-9 + 12 + strengthening pass with **6 substantive theorems + 1 marker / 0 sorry / 0 new axioms** (verified `propext, Classical.choice, Quot.sound` only on load-bearing biconditionals). Tetrad (vierbein) formulation of GR at the algebraic / point-wise level: §2 tetrad-induced metric `g_μν = η_ab e^a_μ e^b_ν` with substantive `tetradInducedMetric_symm` symmetry (proved via η-diagonality + index swap, NOT pure simp); §3 Minkowski tetrad `e^a_μ = δ^a_μ` with named-API `minkowskiTetrad_induces_minkowski_metric` consistency; §4 tetrad determinant `minkowskiTetrad_det_eq_one`; §5 torsion-free biconditional `torsionResidual_zero_iff`; §6 substantive cross-bridges to Phase 6e.6 EinsteinCartanExtension (`tetrad_metric_equivalence_at_alpha_one` consuming `ecResidual_at_alpha_one` + `tetrad_levi_civita_iff_alpha_unity` specializing `ecResidual_eq_zero_iff_alpha_unity`). The full Cartan structure equations (T^a = de^a + ω ∧ e^b, R^{ab} = dω + ω ∧ ω) are deferred until differential-form machinery lands. **Cross-layer Python pipeline:** 4 helpers in `formulas.py` (`tetrad_induced_metric`, `minkowski_tetrad`, `diagonal_tetrad_det`, `torsion_residual`); `tests/test_tetrad_formalism.py` (12 pytest cases / 5 test classes, all PASS in 0.05s; TestPhase6eCrossBridge consumes `ec_residual_at_point` from `src/einstein_cartan/`); figure `fig_tetrad_metric_equivalence` (2-panel: tetrad-induced metric heatmap for Minkowski tetrad + |EC residual| vs α_EC log-y showing Levi-Civita reduction at α_EC = 1). Stages 10/11/13 deferred per user policy. **Phase 6f closure milestone reached.** Project totals: **4562 substantive theorems** (+6 net) / **201 modules** (+1) / **94 test files** (+1) / **142 figures** (+1) / 1 axiom / 0 sorry. **Discipline metric: 0 retroactive theorems** (back to 6f.2/6f.3/6e.5/6b.2 best baseline). The 6f.5 lessons applied successfully: avoid simp-trivial-on-constant-zero patterns; substantive proofs via direct η-substitution; named-quantity defs (`tetradInducedMetric`, `diagonalTetradDet`, `torsionResidual`, `minkowskiTetrad`) make most candidate-P3 content into substantive named-API. Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5, 6f.2=0, 6f.3=0, 6f.4=1, 6f.5=4, **6f.6=0**.

**Phase 6f Wave 5 SHIPPED (2026-04-29).** `ADMFormalism.lean` ships through Stages 1-9 + 12 + strengthening pass with **11 substantive theorems + 1 marker / 0 sorry / 0 new axioms** (verified `propext, Classical.choice, Quot.sound` only on load-bearing biconditionals). ADM (Arnowitt-Deser-Misner) 3+1 decomposition of general relativity at the algebraic / point-wise level (no ∂_μ machinery, following 6f.1-6f.4 scoping precedent). **§2 ADM 4-metric block decomposition:** `admFourMetric_00` / `_0i` defs + Minkowski specializations. **§3 Spatial-tensor utilities:** `extrinsicCurvatureTrace` / `_Squared` defs (no separate K=0 specialization theorems — P3-trivial cuts). **§4 Hamiltonian constraint:** `hamiltonianConstraint` def + `vacuum_iff` + `moment_of_time_symmetry` (K=0 specialization) + `moment_of_time_symmetry_iff` (Yamabe-form biconditional `^(3)R = 16πGρ`). **§5 Momentum constraint:** `momentumConstraint_i` def + `vacuum_iff`. **§6 Specific spacetime ADM data:** Minkowski (`_satisfies_hamiltonianConstraint` / `_satisfies_momentumConstraint`); de Sitter flat slicing (`deSitter_flat_slicing_hamiltonian_iff` Λ=3H² ADM-level cross-bridge to 6f.4 `deSitter_lambda_eq_three_H_squared`); Schwarzschild (`schwarzschild_adm_mass_eq_half_horizon_radius` substantive cross-bridge to 6f.4's `schwarzschildHorizonRadius` / `schwarzschild_adm_mass_pos_iff` positive-energy specialization). **First formalization in any proof assistant** (per audit §3E + 6f.1+6f.2+6f.3+6f.4 first-formalization context) of ADM 3+1 with Hamiltonian + momentum constraint biconditionals + cross-bridges to canonical exact-solutions catalog. 2 named noncomputable defs (`hamiltonianConstraint`, `momentumConstraint_i` — both Real.pi-dependent), 4 value defs (`schwarzschildADMMass`, `deSitterADMMass`, plus `lowerShift` / `admFourMetric_*` / `extrinsicCurvature*` infrastructure). New formulas in `formulas.py` (8 helpers): `adm_four_metric_g00`, `adm_four_metric_g0i`, `extrinsic_curvature_trace`, `extrinsic_curvature_squared`, `hamiltonian_constraint`, `momentum_constraint`, `schwarzschild_adm_mass`, `desitter_adm_mass`. New `tests/test_adm_formalism.py` (32 pytest cases / 9 test classes — TestADMFourMetric / TestSpatialContractions / TestHamiltonianConstraint / TestMomentumConstraint / TestMinkowskiADM / TestDeSitterADM / TestSchwarzschildADM / TestStrengtheningQuantitative / TestPhase6fCrossBridge / TestAntiPatternAudit — all PASS in 0.05s). New figure `fig_adm_constraint_surface` (2-panel: Yamabe-form Hamiltonian constraint contour heatmap in (³R, ρ) plane with H=0 dashed locus + ★ Minkowski + ◆ Schwarzschild markers + dS flat-slicing Λ=3H² parabola with H=1/Λ=3 + H=2/Λ=12 anchors). Stages 10/11/13 deferred per user policy. **Phase 6f wave 6 unblocked** (TetradFormalism). Project totals: **4556 substantive theorems** (+11 net) / **200 modules** (+1) / **93 test files** (+1) / **141 figures** (+1) / 1 axiom / 0 sorry. **Discipline metric: 4 retroactive theorems** (`schwarzschild_adm_K_zero` rfl on constant-zero P3 plumbing + `extrinsicCurvatureTrace_zero_at_K_zero` + `extrinsicCurvatureSquared_zero_at_K_zero` simp-trivial unconsumed + `schwarzschild_adm_mass_eq_M` rfl rename replaced by substantive `_eq_half_horizon_radius` cross-bridge + `deSitter_adm_mass_eq_zero` rfl rename — closed forms encoded at the def level). The 6f.5 regression is logged: spatial-tensor-trace + sum-of-zero-summands + simple-rename theorems are all P3 trivial when the input is the constant-zero function or a value def. **Trend:** 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5, 6f.2=0, 6f.3=0, 6f.4=1, **6f.5=4**.

**Phase 6f Wave 4 SHIPPED (2026-04-29).** `ExactSolutions.lean` ships through Stages 1-9 + 12 + strengthening pass with **17 substantive theorems + 1 marker / 0 sorry / 0 new axioms** (verified `propext, Classical.choice, Quot.sound` only on the load-bearing biconditionals). Catalogue of canonical exact solutions of the Einstein field equations as named consumers of the Phase 6f.1+6f.2+6f.3 algebraic infrastructure plus BH thermodynamics cross-bridges to Phase 6a Wave 5. **Minkowski:** `minkowski_lambda_zero_iff_K_zero` (uniqueness biconditional — Minkowski is the unique Λ=0 vacuum among constant-K solutions). **de Sitter (K>0):** `deSitter_Ricci_eq` / `deSitter_scalar_eq` / `deSitter_einsteinTensor_eq` / `deSitter_lambda_vacuum_iff` / `deSitter_lambda_eq_three_H_squared` / `deSitter_T_H_eq_kappa_over_2pi` (6 thms with named defs `deSitterHubbleRadius` / `deSitterKappa` / `deSitterHawkingTemp`; the last is Gibbons-Hawking 1977 `T_H = κ/(2π)`). **Anti-de Sitter (K<0):** `ads_lambda_eq_neg_three_over_ell_sq` (1 thm; AdS-radius anchor). **Schwarzschild (Kerr-Schild form):** `schwarzschild_horizon_iff` (biconditional `φ=1 ↔ r=2M`) + 3 g_tt signature theorems (timelike outside / null at horizon / spacelike inside) + 5 BH thermodynamics cross-bridges (`schwarzschild_kappa_times_4M` / `_T_H_times_M` / `_T_H_eq_kappa_over_2pi` / `_area_eq_16pi_M_sq` / `_S_BH_eq_4pi_M_sq`) consuming named defs `schwarzschildHorizonRadius` / `schwarzschildKappa` / `schwarzschildHawkingTemp` / `schwarzschildArea` / `schwarzschildBHEntropy`. The vacuum-Ricci verification `Ric(g_Schw) = 0` outside r=2M is **deferred** (requires ∂_μ machinery); vacuous tracked-Prop pattern was REJECTED at first pass per 6f.2 strengthening lesson. **First formalization in any proof assistant** (per audit §3E + 6f.1+6f.2+6f.3 first-formalization context) of the catalog with chain implications + Λ-cosmological-constant biconditional + Hawking-Unruh quantitative cross-bridges. New formulas in `formulas.py` (14 helpers): `deSitter_lambda_from_K`, `deSitter_Ricci_predicted`, `deSitter_scalar_predicted`, `deSitter_einsteinTensor_predicted`, `deSitter_hubble_radius`, `deSitter_surface_gravity`, `deSitter_hawking_temp`, `ads_lambda_from_radius`, `schwarzschild_horizon_radius`, `schwarzschild_kappa`, `schwarzschild_hawking_temp`, `schwarzschild_horizon_area`, `schwarzschild_bekenstein_hawking_entropy`, `schwarzschild_g_tt`. New `tests/test_exact_solutions.py` (45 pytest cases / 8 test classes — TestMinkowski / TestDeSitter / TestDeSitterThermodynamics / TestAntiDeSitter / TestSchwarzschildSignature / TestSchwarzschildThermodynamics / TestStrengtheningQuantitative / TestPhase6fCrossBridge / TestAntiPatternAudit — all PASS in 0.06s). New figure `fig_exact_solutions_catalog` (3-panel: Schwarzschild g_tt(r) signature flip + Λ=3K linear branch with dS/Mink/AdS markers + Schwarzschild thermodynamics scaling on log-log). Stages 10/11/13 deferred per user policy (Mathlib-PR-style infrastructure with no in-project paper deliverable). **Phase 6f waves 5-6 unblocked** (6f.5 ADM, 6f.6 Tetrad). Project totals: **4545 substantive theorems** (+17 net) / **199 modules** (+1) / **92 test files** (+1) / **140 figures** (+1) / 1 axiom / 0 sorry. **Discipline metric: 1 retroactive theorem** (`schwarzschild_kappa_eq` rfl rename caught by ruthless audit; substantive κ=1/(4M) content lives in the `schwarzschildKappa` def + `schwarzschild_kappa_times_4M` consumer). The named-quantity definition pattern (5 noncomputable defs for Schwarzschild + 3 for dS) made most P3-trivial content into substantive named-API rather than rename theorems, keeping the regression small. Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5, 6f.2=0, 6f.3=0, **6f.4=1**.

**Phase 6f Wave 3 BACKFILL CLOSED (2026-04-29).** The `EnergyConditions.lean` Lean module shipped 2026-04-27 (8 substantive thms + 1 marker / 0 sorry / 0 axioms) but the cross-layer Python pipeline was skipped — a 2026-04-29 audit (post-6f.2 ship) caught the gap and scheduled backfill. Backfill now closed: 11 helpers in `formulas.py` (`apply_bilinear` + `is_null_vec`/`is_timelike`/`is_future_directed_timelike` predicate helpers + `nec_check`/`wec_check`/`dec_check`/`sec_check` condition checks + `cosmological_lambda_stress_energy`/`ghost_scalar_stress_energy`/`perfect_fluid_stress_energy` named tensor witnesses + `perfect_fluid_trace_minkowski` trace helper); `tests/test_energy_conditions.py` (38 pytest cases / 7 test classes covering the 8 substantive theorems + audit-flagged anti-patterns + 6f.1 cross-bridge — all PASS in 0.07s); figure `fig_energy_conditions_perfect_fluid_regions` (4-panel (ρ, p) heatmap with ★ cos-Λ at (1,-1) marking NEC/WEC/DEC blue + SEC orange and ◆ stiff-fluid at (1,2) marking NEC/WEC/SEC blue + DEC orange — visualizes all 5 named counterexample-witness theorems). Lean module summary docstring corrected from stale "7 substantive theorems" to actual "8 + 1 marker" + Wave-3 backfill cross-reference appended. **LIFT bridge to 6f.1/6f.2's matrix carrier remains DEFERRED** (judgment call: defer until 6f.4 needs it). **Wave 6f.3 now FULLY SHIPPED end-to-end** (Lean module + cross-layer Python pipeline). 6f.1 + 6f.2 + 6f.3 set the consistent precedent that Mathlib-PR-style infrastructure ships full cross-layer cycle by default. Project totals: **4528 substantive theorems / 198 modules / 91 test files (+1 from 90) / 139 figures (+1 from 138) / 1 axiom / 0 sorry**. **Next pickup:** Phase 6f.4 `ExactSolutions.lean` (Schwarzschild + de Sitter; de Sitter natural first target via `constantSectional_lambda_vacuum_iff`).

**Phase 6f Wave 2 SHIPPED (2026-04-29).** `EinsteinTensor.lean` ships through Stages 1-9 + 12 + strengthening pass with **9 substantive theorems + 1 marker / 0 sorry / 0 new axioms** (verified `propext, Classical.choice, Quot.sound` only). Coordinate-based algebraic Einstein tensor `G_{μν} := Ric_{μν} − (1/2) R g_{μν}` over `EinsteinTensorType : Fin 4 → Fin 4 → ℝ` (matching 6f.1's `RicciTensor` shape). Wave headline `constantSectional_einsteinTensor_eq` ships `G_{μν} = -3K · g_{μν}` consuming 6f.1's `constantSectional_Ricci_eq` and the new `constantSectional_scalarOf_eq` (`R = 12K`). Quantitative dimension-4 trace identity `einsteinTensor_trace_eq_neg_scalar` (`G^μ_μ = -R` via `n − 2 = 2` cancellation under `(g_inv : g) = 4` hypothesis). Vacuum characterization biconditional `einsteinTensor_zero_iff_ricci_zero` (forward uses trace identity; backward uses `scalarOf_eq_of_pointwise` linearity helper). De Sitter Λ-vacuum cross-bridge `constantSectional_lambda_vacuum_iff` (`G + Λg = 0 ↔ Λ = 3K` with `g μ₀ ν₀ ≠ 0` non-degeneracy). Minkowski self-inverse contraction `minkowski_dim_contraction = 4` (concrete witness on `LinearizedEFE.η`). **Second Bianchi `∇^μ G_{μν} = 0` deferred** until Bonn's `CovariantDerivative` API lands (option (a) tracked-Prop with trivial constant-K discharge REJECTED per 6f.1's strengthening lesson). New formulas in `formulas.py`: `einstein_tensor_from_ricci`, `einstein_tensor_trace`, `constant_sectional_einstein_tensor_predicted`, `de_sitter_lambda_from_K`, `minkowski_dim_contraction_value`. New `tests/test_einstein_tensor.py` (26 tests, all PASS). New figure `fig_einstein_tensor_trace_identity` (2-panel: trace identity + Λ-vacuum residual heatmap). Stages 10/11/13 deferred per user policy. **First formalization in any proof assistant** (per audit §3E + 6f.1 first-formalization context) of the algebraic Einstein tensor with quantitative dimension-4 trace identity + constant-K specialization + de Sitter-Λ algebraic cross-bridge. **Phase 6f waves 4-6 unblocked.** validate.py 25/25 PASS. **Discipline metric: 0 retroactive theorems** (best yet — back to 6e.5/6b.2 baseline). The 6f.1 carry-forward question (*"is the witness-existence statement informative beyond the predicate definition?"*) prevented zero-witness-trivial-plumbing in the first place — used K=0 in pytest exclusively, no `zeroEinstein_*` Lean theorems. Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5, **6f.2=0** (back to best). The carry-forward worked.

**Phase 6f Wave 1 SHIPPED (2026-04-29).** `Curvature.lean` ships through Stages 1-9 + 12 + strengthening pass with **16 substantive theorems / 0 sorry / 0 new axioms** (verified `propext, Classical.choice, Quot.sound` only; was 21 first-pass — 5 retroactive cuts in strengthening pass: 4 zeroRiemann_* trivial-witness theorems + unused `sumFin4_kron_eq` helper). Coordinate-based algebraic Riemann/Ricci/scalar curvature: AntisymLastTwo (P3-trivial flagged), FirstBianchi (load-bearing under torsion-free), AntisymPair12 (load-bearing under metric-compatibility). Wave headline `pair_symmetry_lowered` derives `R_{ρσμν} = R_{μνρσ}` via the standard Wald §3.2 four-Bianchi-sum derivation. Quantitative content: `constantSectional_Ricci_eq` (`Ric = 3K · g` in 4D), `constantSectional_diag_trace_eq` (`R_trace = 12K`). First formalization in any proof assistant (per audit §3E) of algebraic Riemann predicates with chain implications + explicit constant-K witness + cross-module Minkowski bridge. New formulas in `formulas.py`: `riemann_constant_sectional_curvature`, `ricci_from_riemann`, `scalar_curvature_from_ricci`, `constant_sectional_ricci_predicted`, `constant_sectional_scalar_predicted`, `first_bianchi_residual`, `antisym_last_two_residual`. New `tests/test_curvature.py` (23 tests, all PASS). New figure `fig_constant_K_riemann_dimension_factor`. Stages 10 (paper) + 11 (notebook) + 13 (adversarial reviewer) deferred per user policy — Mathlib-PR infrastructure with no in-project paper target. **Phase 6f waves 2-6 unblocked.** validate.py 25/25 PASS. **Discipline metric: 5 retroactive theorems** (preemptive checklist passed first time but ruthless review cut 4 plumbing-only zeroRiemann witnesses + 1 unused helper that the discipline missed). Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, **6f.1=5** (regression — pattern missed: zero-witness-as-trivial-plumbing). Failure-mode log: P3 trivial-discharge for "trivial witness" theorems on the negative-class side; CHECKLIST should add "is the witness-existence statement informative beyond the predicate definition?" question.

---

## 1. PYTHON SOURCE FILES (130 Python modules)

> **Changes since April 6:** formulas.py +7 functions (a1_resolution_rank, a1_ext_dimension, a1_ext_generator_bidegrees, bordism_hypothesis_count, fk_hamiltonian, fk_eigenvalues, fk_spectral_gap). constants.py +6 data structures (A1_MILNOR_BASIS, A1_RESOLUTION_RANKS, A1_EXT_DIMENSIONS, A1_EXT_GENERATORS, A1_EXT_RELATIONS, BORDISM_HYPOTHESES). visualizations.py +3 figures (fig_ext_chart, fig_a1_resolution_structure, fig_fk_spectrum), COLORS fixed for colorblind accessibility.

### 1.1 Core Module: `src/core/`

#### `src/core/constants.py` (242 lines)
**Purpose:** Single source of truth for all physical constants, experimental parameters, and the Aristotle theorem registry. **No other file may hardcode physical constants or experimental values.**

**Contents:**
- `HBAR`, `K_B` — SI physical constants
- `ATOMS` dict — Atomic properties (mass, scattering length) for Rb87, K39, Na23
- `EXPERIMENTS` dict — Experimental parameters (density, velocity, omega_perp) for Steinhauer, Heidelberg, Trento
- `ARISTOTLE_THEOREMS` dict — 322+ theorem→run_id mappings across 45+ runs (all complete; Aristotle `6dbc9447` was the last in-flight batch, superseded by interactive MCP closure 2026-04-08–2026-04-14)
- `ARISTOTLE_PROVED_COUNT = 322`
- `A1_MILNOR_BASIS`, `A1_RESOLUTION_RANKS`, `A1_EXT_DIMENSIONS` — Ext computation data
- `A1_EXT_GENERATORS`, `A1_EXT_RELATIONS`, `BORDISM_HYPOTHESES` — Ext generators and spin bordism hypotheses
- `COLORS` dict — Plotly color palette for consistent visualization
- `CATEGORY_HIERARCHY` — 3-layer categorical infrastructure
- `FUSION_EXAMPLES` — 5 fusion categories with rules + F-matrices
- `DRINFELD_DOUBLE` — D(G) data for Z/2, Z/3, S₃
- `LAYER1_CONNECTIONS` — Layer 1→2→3 bridge connections
- `GS_CONDITIONS`, `TPF_VIOLATIONS`, `LATTICE_FRAMEWORK` — Chirality wall data
- `POLARITON_PLATFORMS` — 3 cavity qualities for polariton predictions
- `ADW_2D_MODEL`, `ADW_4D_MODEL`, `SU2_HAAR`, `SO4_HAAR` — MC parameters

---

#### `src/core/formulas.py` (~1200 lines)
**Purpose:** Canonical Python implementations of every physics formula verified by Lean/Aristotle. **No other file may reimplement these formulas.** Each function documents its Lean theorem name and Aristotle run ID.

**Functions (151):** (19 Phase 1-4 + 106 Phase 5/5a/5b + 12 Phase 5c + 7 Phase 5k-5p + 7 Phase 5q-5s)
- `count_coefficients(N)` — Transport coefficient counting: floor((N+1)/2) + 1
- `enumerate_monomials(N)` — List monomials at order N
- `damping_rate(gamma_1, gamma_2, k, omega, c_s)` — Γ(k,ω) at given wavenumber
- `dispersive_correction(D)` — δ_disp = -(π/6)·D²
- `hawking_temperature(kappa)` — T_H = ℏκ/(2πk_B)
- `first_order_correction(Gamma_H, kappa)` — δ_diss = Γ_H/κ
- `second_order_correction(...)` — δ^(2)(ω) frequency-dependent
- `third_order_correction(...)` — Third-order parity structure
- `effective_temperature_ratio(...)` — T_eff/T_H with all corrections
- `turning_point_shift(...)` — Complex WKB turning point displacement
- `decoherence_parameter(...)` — Modified unitarity deficit
- `fdr_noise_floor(...)` — FDR-mandated noise baseline
- `adw_effective_potential(C, G, Lambda, N_f)` — Coleman-Weinberg V_eff
- `adw_critical_coupling(Lambda, N_f)` — G_c = 8π²/(N_f·Λ²)
- `adw_curvature_at_origin(G, Lambda, N_f)` — d²V_eff/dC²|_{C=0}
- `tetrad_broken_generators(d)` — d²-1 broken generators in d dimensions
- `graviton_polarization_count(d)` — d(d-3)/2 massless gravitons
- `beliaev_damping_rate(...)` — Microscopic UV matching: Γ_Bel(ω_H)
- `beliaev_transport_coefficients(...)` — Extract γ₁, γ₂ from Beliaev

---

#### `src/core/transonic_background.py` (417 lines)
**Purpose:** 1D BEC transonic flow solver. Parameterizes velocity as smooth tanh transition through horizon.

**Key Types:** `BECParameters` (dataclass), `TransonicBackground` (dataclass)

**Factory Functions (import from constants.py):**
- `steinhauer_Rb87()` — ⁸⁷Rb BEC (Steinhauer 2016/2019)
- `heidelberg_K39()` — ³⁹K with Feshbach tuning (projected)
- `trento_spin_sonic()` — ²³Na spin-sonic (projected)

**Key Functions:**
- `solve_transonic_background(params, ...)` → `TransonicBackground`
- `compute_dissipative_correction(bg, params, gamma_1, gamma_2)` — Computes δ_diss, δ_disp using imports from `formulas.py`
- `experimental_survey()` — Print parameter survey for all 3 platforms

---

#### `src/core/visualizations.py` (~4500 lines)
**Purpose:** All Plotly figures (101 functions) + full COLORS palette. **Only place figure functions live.**

**Color Palette:** Steel blue (Steinhauer), berry (Heidelberg), amber (Trento), sage (dispersive), carmine (dissipative), warm tan (noise), cool grey (cross-terms)

**Figure Functions by Phase (101 total):**
- Phase 1 (6): transonic_profiles, correction_hierarchy, parameter_space, spin_sonic_enhancement, temperature_decomposition, kappa_scaling
- Phase 2 (6): cgl_fdr_pattern, even_vs_odd_kernel, boundary_term_suppression, positivity_constraint, on_shell_vanishing, einstein_relation
- Phase 3a Third-Order (3): parity_alternation, damping_rate_third_order, spectral_correction_comparison
- Phase 3b Gauge Erasure (2): sm_scorecard, erasure_survey
- Phase 3b Kappa Crossing (2): kappa_crossing_phase3, spin_sonic_enhancement_phase3
- Phase 3c WKB Connection (6): bogoliubov_connection, complex_turning_point, effective_surface_gravity, decoherence_and_noise, hawking_spectrum_exact, exact_vs_perturbative
- Phase 3d ADW (7): adw_effective_potential, adw_phase_diagram, adw_ng_mode_decomposition, adw_he3_analogy, adw_structural_obstacles, adw_coupling_scan (+ stakeholder variant)
- Phase 4a Experimental (4): prediction_table_comparison, detector_requirements, kappa_scaling_phase4, noise_floor_crossover
- Phase 4b Chirality+GL (3): chirality_wall_status, gl_phase_diagram, he3_comparison_table
- Phase 4b Vestigial (3): vestigial_effective_potential, vestigial_phase_diagram, backreaction_cooling
- Phase 4b Fracton (1): information_retention
- Phase 5 Wave 1 (2): kappa_scaling_physical, polariton_regime_map
- Phase 5 Wave 2 (4): grassmann_trg_2d_phase, fermion_bag_4d_binder, fermion_bag_4d_phase_diagram, vestigial_binder_crossing
- Phase 5 Wave 3/5 (5): gs_condition_formalization, tpf_evasion_architecture, fock_exterior_algebra, lean_theorem_summary, vestigial_susceptibility_split
- Phase 5 Wave 4 (5): category_hierarchy, fusion_rules_comparison, fibonacci_f_matrix, drinfeld_anyon_spectrum, layer123_bridge
- Phase 5 Wave 5 (1): vestigial_phase_diagram_mc (MF + MC overlay)
- Phase 5 Wave 6 (3): vestigial_susceptibility, vestigial_window, vestigial_phase_diagram_analytical
- Phase 5a (5): gt_band_structure, wilson_mass_bz, chiral_charge_spectrum, gt_commutator_verification, chirality_wall_three_pillars
- Phase 5b (4): sm_fermion_z16_anomaly, sm_generation_anomaly, sm_generation_constraint, drinfeld_equivalence_structure
- Phase 5b Modular (1): modular_invariance_phase
- Phase 5c (5): su2k_fusion_tables, su2k_quantum_dims, su2k_s_matrix_heatmaps, hopf_chain, e8_cartan_heatmap
- Phase 5d (3): tetrad_gap_curve, tetrad_gap_integral, stimulated_hawking_spectrum
- Phase 5e-5p (17): braided MTC, TQFT, TQC, generic quantum group, anomaly inflow, SPT, Fibonacci universality figures
- Phase 5q-5s (3): ext_chart, a1_resolution_structure, fk_spectrum

**Stakeholder variants** use `stakeholder=True` parameter for simplified versions.

---

#### `src/core/aristotle_interface.py` (~1200 lines)
**Purpose:** Interface to Aristotle automated theorem prover. Registry of sorry gaps (all filled).

**Key Types:** `SorryGap` (dataclass), `AristotleResult` (dataclass), `AristotleRunner` (class)

**Sorry Gap Registry (322+ registry entries, 45+ runs, all gaps filled):**
- Phase 1: 14 gaps (AcousticMetric, SKDoubling, HawkingUniversality)
- Phase 2: 9 gaps (SecondOrderSK, WKBAnalysis)
- Phase 2 Stress Tests: 9 gaps (KMS optimality, FDR sign tests, limit checks)
- Phase 2 Round 5: 3 gaps (total-division strengthening)
- Direction D CGL: 5 gaps (einstein_relation, cgl_fdr, cgl_implies_KMS)
- Phase 3: 1 gap (curvature_zero_at_Gc)
- Phase 4: 13 gaps (fracton, vestigial, chirality batch b1ea2eb7)
- Wave 1C/3A-C: 22 gaps (kappa-scaling, LatticeHamiltonian, GoltermanShamir, TPFEvasion, ExteriorAlgebra)
- Wave 4A: 11 gaps (KLinearCategory, SphericalCategory)
- Wave 4B: 7 gaps (FusionExamples)
- Wave 4C: 5 gaps (VecG, DrinfeldDouble)
- Wave 9C: 77 gaps (SO4Weingarten 14, FractonFormulas 45, WetterichNJL 18)
- Wave 6B: 16 gaps (VestigialSusceptibility)
- Wave 7A-B: 21 gaps (QuaternionGauge 10, GaugeFermionBag 9, Binder 2)
- Wave 7B-C: 47 manual proofs (HubbardStratonovichRHMC 22, MajoranaKramers 25)

---

### 1.2 Second-Order Module: `src/second_order/`

#### `src/second_order/enumeration.py` (441 lines)
**Purpose:** Transport coefficient counting at arbitrary EFT order via SK axioms. Formula: count(N) = floor((N+1)/2) + 1.

#### `src/second_order/coefficients.py` (541 lines)
**Purpose:** Second-order data structures, action constructors, correction formulas. Imports `first_order_correction` from `formulas.py`.

#### `src/second_order/wkb_analysis.py` (636 lines)
**Purpose:** WKB mode analysis through the dissipative horizon. Frequency-dependent Bogoliubov coefficients.

#### `src/second_order/cgl_derivation.py` (762 lines)
**Purpose:** CGL dynamical KMS derivation of the FDR at arbitrary EFT order. Key finding: CGL pairs noise with odd-ω dissipative retarded terms only.

---

### 1.3 Phase 3 Modules

#### `src/gauge_erasure/erasure_theorem.py` (341 lines)
**Purpose:** Non-Abelian gauge erasure universal structural theorem. Proves that non-Abelian gauge symmetries produce discrete (domain wall) defects in the condensed phase, while Abelian U(1) produces continuous (Goldstone) modes.

**Key Result:** In the Standard Model, only U(1)_EM survives gauge erasure → only electromagnetic Goldstone modes in the superfluid phase.

#### `src/wkb/connection_formula.py` (517 lines)
**Purpose:** Exact WKB connection formula for the dissipative horizon. Complex turning point analysis, Stokes geometry, modified Bogoliubov coefficients.

**Key Result:** The exact connection formula replaces the perturbative δ_diss expansion with a non-perturbative Bogoliubov calculation through the complex turning point.

#### `src/wkb/bogoliubov.py` (206 lines)
**Purpose:** Modified unitarity and decoherence from dissipation. |α|² - |β|² < 1 with the deficit set by the decoherence parameter.

#### `src/wkb/spectrum.py` (546 lines)
**Purpose:** Observable Hawking spectrum with all corrections (exact WKB + noise floor).

#### `src/wkb/backreaction.py` (798 lines)
**Purpose:** Acoustic black hole cooling via backreaction. Key result: acoustic BHs cool and approach extremality (opposite of Schwarzschild). Imports `HBAR`, `K_B`, `ATOMS` from `constants.py` and `hawking_temperature` from `formulas.py`.

#### `src/adw/wen_model.py` (222 lines)
**Purpose:** Wen's lattice QED model — the microscopic UV completion for emergent gravity.

#### `src/adw/hubbard_stratonovich.py` (299 lines)
**Purpose:** Hubbard-Stratonovich decomposition introducing the composite tetrad field.

#### `src/adw/gap_equation.py` (401 lines)
**Purpose:** Coleman-Weinberg effective potential and critical coupling G_c = 8π²/(N_f·Λ²). Imports canonical formula from `formulas.py`.

#### `src/adw/fluctuations.py` (475 lines)
**Purpose:** SSB analysis, Nambu-Goldstone mode counting (2 massless gravitons in 4D), Vergeles consistency check.

#### `src/adw/ginzburg_landau.py` (1139 lines)
**Purpose:** Ginzburg-Landau expansion and He-3 analogy. A-phase instability, B-phase stability, phase diagram.

---

### 1.4 Phase 4 Modules

#### `src/experimental/predictions.py` (669 lines)
**Purpose:** Platform-specific spectral predictions for experimentalists. Generates prediction tables (Steinhauer/Heidelberg/Trento), computes shot requirements, κ-scaling test parameters.

#### `src/chirality/tpf_gs_analysis.py` (687 lines)
**Purpose:** TPF vs GS chirality wall compatibility analysis. Evaluates 4 GS no-go conditions against TPF construction: TPF evades 2 of 4 (translation invariance, ancilla fields), making the breach conditional.

#### `src/fracton/sk_eft.py` (711 lines)
**Purpose:** Fracton SK-EFT with higher-moment conservation laws. Binomial charge counting.

#### `src/fracton/information_retention.py` (1017 lines)
**Purpose:** UV information comparison: fracton hydrodynamics retains exponentially more UV structure than standard hydro due to additional conserved charges.

#### `src/fracton/gravity_connection.py` (1194 lines)
**Purpose:** Kerr-Schild bootstrap connection to gravity. DOF gap analysis, route achievements and obstacles.

#### `src/fracton/non_abelian.py` (537 lines)
**Purpose:** Non-Abelian fracton obstruction analysis — a **negative result**. Non-Abelian gauge structure is incompatible with fracton symmetry constraints.

#### `src/vestigial/mean_field.py` (361 lines)
**Purpose:** Mean-field gap equation for the vestigial metric phase. Curvature-based phase classification: pre-geometric (G/G_c < 0.8), vestigial (0.8-1.0), full tetrad (>1.0). Imports `adw_curvature_at_origin` from `formulas.py`.

#### `src/vestigial/lattice_model.py` (284 lines)
**Purpose:** Euclidean lattice formulation of the ADW tetrad model.

#### `src/vestigial/monte_carlo.py` (235 lines)
**Purpose:** Metropolis Monte Carlo for the lattice model. Measures tetrad VEV and metric correlator.

#### `src/vestigial/phase_diagram.py` (199 lines)
**Purpose:** Phase diagram construction from mean-field and MC data. Uses corrected phase classification from `mean_field.py`.

#### `src/vestigial/finite_size.py` (461 lines)
**Purpose:** Finite-size scaling analysis for the vestigial-to-full-tetrad transition.

#### `src/vestigial/su2_integration.py` (Phase 5 Wave 2A)
**Purpose:** Analytical SU(2) Haar measure integration. Peter-Weyl decomposition of the one-link integral. Pseudo-reality verification for sign-problem absence.

#### `src/vestigial/grassmann_trg.py` (Phase 5 Wave 2A)
**Purpose:** 2D Grassmann TRG implementation. Iterative tensor coarse-graining for the reduced ADW model. Free energy, specific heat, coupling scan, D_cut convergence.

#### `src/vestigial/lattice_4d.py` (Phase 5 Wave 2B)
**Purpose:** 4D hypercubic lattice model with SO(4) ≅ SU(2)_L × SU(2)_R gauge integration. Site/bond/total action, tetrad/metric order parameters, neighbor/bond indexing.

#### `src/vestigial/fermion_bag.py` (Phase 5 Wave 2B)
**Purpose:** Fermion-bag Metropolis MC for 8-fermion vertices (Chandrasekharan algorithm). Avoids sign problem via SU(2) pseudo-reality.

#### `src/vestigial/phase_scan.py` (Phase 5 Wave 2B)
**Purpose:** 4D coupling scan with Binder cumulant analysis. Identifies vestigial phase via split Binder crossings for tetrad vs metric order parameters.

### 1.5 Phase 5 Modules

#### `src/experimental/kappa_scaling.py` (Phase 5 Wave 1A)
**Purpose:** Physical kappa-scaling sweeps for all BEC platforms. Computes dispersive (∝κ²) and dissipative (∝κ) corrections as functions of surface gravity. Identifies crossover κ_cross where |δ_disp| = δ_diss.

#### `src/experimental/polariton_predictions.py` (Phase 5 Wave 1B)
**Purpose:** Tier 1 polariton platform predictions. Spatial attenuation correction, validity parameter Γ_pol/κ, regime classification (ultra-long/long/standard cavities).

#### `src/vestigial/quaternion.py` (Phase 5 Wave 7A)
**Purpose:** SU(2) quaternion algebra for SO(4) gauge theory. Vectorized operations, Haar random sampling.

#### `src/vestigial/so4_gauge.py` (Phase 5 Wave 7A)
**Purpose:** SO(4) gauge theory via quaternion pair decomposition. Plaquette, staple, Kennedy-Pendleton heatbath, overrelaxation.

#### `src/vestigial/gauge_fermion_bag.py` (Phase 5 Wave 7B)
**Purpose:** Hybrid fermion-bag + gauge-link Monte Carlo. 4×4 complex fermion matrix, Sherman-Morrison-Woodbury updates.

#### `src/vestigial/gauge_fermion_bag_majorana.py` (Phase 5 Wave 7B)
**Purpose:** 8×8 Majorana sign-free fermion-bag. Kramers degeneracy (PRL 116), Givens Spin(4), Woodbury gauge updates. Hits percolation wall at L≥6.

#### `src/vestigial/hs_rhmc.py` (Phase 5 Wave 7C)
**Purpose:** Hubbard-Stratonovich + RHMC algorithm. Reference numpy/scipy implementation. Complex pseudofermion, Zolotarev rational approximation, multi-shift CG.

#### `src/vestigial/hs_rhmc_jax.py` (Phase 5 Wave 7C)
**Purpose:** JAX CPU backend for RHMC. Batched CG solver.

#### `src/vestigial/hs_rhmc_torch.py` (Phase 5 Wave 7C)
**Purpose:** PyTorch CPU backend for RHMC. Production default. Batched LU (L=4) and batched CG (L≥6), FSAL Omelyan integrator.

#### `src/core/sm_anomaly.py` (Phase 5a-5b)
**Purpose:** SM anomaly computation in ℤ₁₆: fermion data, anomaly index, generation constraint, hidden sector check.

#### `src/core/provenance.py` (Phase 5 Wave 9D)
**Purpose:** Parameter provenance registry. PARAMETER_PROVENANCE dict with tiers, sources, verification dates.

#### `src/core/citations.py` (Phase 5 Wave 9D)
**Purpose:** Citation registry. CITATION_REGISTRY with DOIs, usage mapping.

#### `src/chirality/gioia_thorngren.py` (Phase 5a)
**Purpose:** Gioia-Thorngren chirality analysis.

#### `src/adw/tetrad_gap_solver.py` (Phase 5d)
**Purpose:** NJL-type gap equation solver, Δ*(G) curve, MF-guided scan parameters.

#### `src/adw/tetrad_observables.py` (Phase 5d)
**Purpose:** MC observables: O_tet, O_met, Binder U₄, spatial correlator C(r).

---

## 2. LEAN FORMAL VERIFICATION (367 modules, **6620 substantive theorems** + 25 placeholder = 6645 total post-Session-51, 0 axioms, **0 sorry**) — **Synced 2026-05-20** from `docs/counts.json` (2026-05-19, pre-session-49 regen + manual +19 declaration delta from FibSU2LieBundle Session 49 commits + manual +6 declaration delta from SU2LieAlgebra + FibSU2LieBundle Session 50 commits + manual +8 declaration delta from FibSU2LieBundle Session 51 commits)

> **2026-05-19 PHASE 6p WAVE 2c.4a-R4.2.d.R5.4 FKLW FIBONACCI SU(2) DENSITY SUBSTRATE PROGRAM (Sessions 30–49, 2026-05-08 → 2026-05-19).**
> 30 PUBLIC SK_EFT_Hawking commits in `lean/SKEFTHawking/FKLW/` shipping ~2859 LoC across 6 NEW modules (`SU2LieAlgebra.lean` + `SU2MatrixExp.lean` + `SU2LocalDiffeo.lean` + `SU2InteriorBridge.lean` + `FibonacciDensityConditional.lean` + `FibSU2LieBundle.lean`) plus ~870 LoC extensions to `FibSU2Density.lean` (§17–§29). The structural reduction chain `BCH-spanning witness → DenseInSpecialUnitary 3 2 ρ_Fib_SU2` is now CONNECTED end-to-end (as a CONDITIONAL theorem `fibonacci_density_from_exp_image_subset`; the BCH-spanning witness production remains future work) AND the σ_Fib 3-bundle is now a BASIS of 𝔰𝔲(2) at every non-zero scalar multiple of `paulI_x` (Session 49 F.18 + F.19 lin-indep at `paulI_x` + Session 50 F.20.a Cramer-rule spanning + F.20.a-app spanning at `paulI_x` + F.20.b uniform-smul-scaled spanning at every `t·paulI_x` with `t ≠ 0`) AND the BCH/IFT iteration substrate is opened (Session 51 F.20.c.a `liePartMat` Ad-equivariance + F.20.c.b σ_Fib bundle commutativity with `liePartMat`). Layer sequence: Sessions 30–31 D4.3.c.application + D4.3.c.app.5b + D4.3.d-starter + D4.3.e-conditional + D3-Path-ii Step 1 closure (`cFib_not_isOfFinOrder`); Session 32 19-commit Layers A → D.3.g (AccPt witness extractor → spanning foundation); Sessions 33–34 D.3.h + D.3.i.1 (small-pair non-parallel witness + iteration sequence); Sessions 35–39 Cartan-A/B/C/D + Layer E (5 NEW upstream-Mathlib4-PR-quality modules); Sessions 41–48 Layers F.1 → F.15 (Pauli basis substrate + Cramer-rule linear-independence + `lieProj` projection + Ad-equivariance + σ_Fib 3-bundle + σ_Fib_1 explicit Ad-action on paulI_x); **Session 49 Layers F.16 → F.19 (R5.4 lin-indep arc capstone): F.16 ω-cancellation + Pauli coords of σ_Fib_1 conjugate of `paulI_x` = (cos(7π/5), sin(7π/5), 0); F.17.a σ_Fib_2 = F·σ_Fib_1·F decomposition + F·paulI_x·F = !![a·I, b·I; b·I, -a·I] explicit form; F.17.b σ_Fib_2·paulI_x·σ_Fib_2† (0,0) entry closed form; F.18 σ_Fib bundle `pauliDet paulI_x ≠ 0` via `sin(7π/5) < 0` + `cos(7π/5) < 1` + φ-positivity; F.19 σ_Fib bundle ℝ-lin-indep at `paulI_x`**. Session 49 commits chronologically: `cd12d45` (F.16, 93 LoC) → `0f27715` (F.17.a, 98 LoC) → `ce4d516` (F.17.b, 129 LoC) → `4623126` (F.18, 203 LoC) → `39d9b86` (F.19, 46 LoC). **Session 50 Layers F.20.a + F.20.a-app + F.20.b (3 PUBLIC commits, ~281 LoC, 6 new substantive theorems): F.20.a `8681e2c` (`SU2LieAlgebra.lean` §15, +123 LoC) — Cramer-rule SPANNING criterion `tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero` (∃ a b c : ℝ such that X = (a:ℂ)•v₁ + (b:ℂ)•v₂ + (c:ℂ)•v₃, the spanning companion to §10 lin-indep) + helper `tracelessSkewHermitian_complex_smul_real_mem` (`Complex.coe_smul` bridge from ℂ-action to ℝ-action — promoted from private to public in commit `f8cf989` for downstream FibSU2LieBundle invocation); F.20.a-app `e798efa` (`FibSU2LieBundle.lean` §11, +50 LoC) — `σ_Fib_lie_bundle_paulI_x_spans` (HEADLINE: for every X ∈ 𝔰𝔲(2), ∃ real (a, b, c) with X = a·paulI_x + b·(σ_Fib_1·paulI_x·σ_Fib_1†) + c·(σ_Fib_2·paulI_x·σ_Fib_2†)) composing F.13 + F.18 + F.20.a, establishing the bundle is a BASIS at paulI_x via F.19 + F.20.a-app together; F.20.b `f8cf989` (`FibSU2LieBundle.lean` §12, +108 LoC; SU2LieAlgebra §15 helper promoted from private to public, +6/-2 LoC) — `pauliDet_smul_uniform` (pauliDet trilinear-homogeneous: scales as t³ under uniform-smul), `σ_Fib_lie_bundle_smul_uniform`, `σ_Fib_lie_bundle_pauliDet_smul_uniform`, **HEADLINE** `σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero` (for any t ≠ 0, the bundle pauliDet at t·paulI_x is non-zero), and `σ_Fib_lie_bundle_scaled_paulI_x_spans` (spanning at every non-zero scalar multiple of paulI_x — provides arbitrarily-small spanning witnesses for the IFT/BCH iteration bridge).** **Session 51 Layers F.20.c.a + F.20.c.b (2 PUBLIC commits, ~133 LoC, 1 noncomputable def + 7 new substantive theorems): F.20.c.a `268d56d` (`FibSU2LieBundle.lean` §13, +84 LoC) — `liePartMat` (def: `lieProj (M - 1)`, canonical "Lie part relative to identity" for any 2×2 complex matrix M; for `M = h ∈ SU(2)` near 1, approximates `log h` to first order); `liePartMat_mem_tracelessSkewHermitian` (output ∈ 𝔰𝔲(2)); `liePartMat_one` (`liePartMat 1 = 0`); **HEADLINE** `liePartMat_conj_specialUnitary` (Ad-equivariance: for `g ∈ specialUnitaryGroup`, `liePartMat (g·M·g†) = g · liePartMat M · g†` via Mathlib `mem_unitaryGroup_iff` + algebraic identity `g·M·g† - 1 = g·M·g† - g·g† = g·(M-1)·g†` + F.11 `lieProj_conj_specialUnitary`); `liePartMat_conj_σ_Fib_1_SU_mat` + `liePartMat_conj_σ_Fib_2_SU_mat` (concrete σ_Fib_1/σ_Fib_2 instances). F.20.c.b `ff5557f` (`FibSU2LieBundle.lean` §14, +49 LoC) — **HEADLINE** `σ_Fib_lie_bundle_liePartMat_eq` (`σ_Fib_lie_bundle (liePartMat M) = (liePartMat M, liePartMat (σ_Fib_1·M·σ_Fib_1†), liePartMat (σ_Fib_2·M·σ_Fib_2†))` via `σ_Fib_lie_bundle` def + Ad-equivariance of `liePartMat` from §13) + `σ_Fib_lie_bundle_pauliDet_liePartMat_eq` (pauliDet-form direct consequence). The σ_Fib bundle of Lie parts equals the Lie parts of the σ_Fib bundle, connecting the small-h BCH iteration argument (operating on `h ∈ H_Fib`) to the Lie-algebra spanning analysis (operating on `liePartMat h ∈ 𝔰𝔲(2)`).** All kernel-only `[propext, Classical.choice, Quot.sound]`; zero new project-local axioms. Project axiom count is 0 entering session 30 (already 0 via earlier pre-R5.4 work: `aa_residual_interior_at_one_for_hom` dropped in `f44c60d` 2026-05-13; `gapped_interface_axiom` retired in `d282677` session 29 Phase 5h Wave 2 TPFConjecture conversion); counts.json 2026-05-19 `axiom_names: []`. Project-wide `lake build` 8615 jobs clean throughout Session 49 + Session 50 + Session 51. **Substantive remaining for the full bridge to unconditional density: F.20.c.c+ (BCH iteration spanning composing Cartan-D + R5.3/D.3.{e,f,g,h,i.1} substrate with F.20.c.a/b `liePartMat` to produce the IFT U witness) + F.21 (apply Layer E `fibonacci_density_from_exp_image_subset` to F.20.c's witness).**


> **2026-05-07 SECTION 1 / SECTION 2 MODULE-ROSTER ADDENDUM (Phase 6f / 6g / 6m / 6n / 6o additions; live module count is ~322 per `ls SK_EFT_Hawking/lean/SKEFTHawking/`).** Top-level table rows below predate the Phase 6e–6o module bloom; the following families appended without re-listing all rows. Authoritative live count lives in `docs/counts.json` (regenerated by `scripts/update_counts.py`).
>
> **Phase 6f classical-GR algebra (single-file modules):** `Curvature.lean` (Riemann/Ricci/scalar at coordinate-algebraic level), `EinsteinTensor.lean` (G_{μν} + Λ-vacuum biconditional), `EnergyConditions.lean` (NEC/WEC/DEC/SEC point-wise), `ExactSolutions.lean` (Minkowski / dS / AdS / Schwarzschild Kerr-Schild + Hawking-Unruh cross-bridges), `ADMFormalism.lean` (3+1 Hamiltonian + momentum constraints), `TetradFormalism.lean` (vierbein + tetrad-induced metric), `BundleRiemann.lean` + `BundleRiemannAux.lean` (bundle-level wrappers).
>
> **Phase 6g causal structure / singularity theorems:** `CausalStructure.lean`, `LorentzianBundle.lean`, `LorentzianMetric.lean`, `LeviCivita.lean`, `RiemannianConnection.lean`, `RiemannCoordinate.lean`, `RiemannDifferentialBianchi.lean`, `LinearizedEFE.lean`, `NonlinearEFE.lean`, `CauchyProblem.lean`, `NonlinearDiffInvariance.lean`, `NullGeodesic.lean`, `RaychaudhuriEquation.lean`, `FocalPoint.lean`, `PenroseSingularity.lean` + `PenroseSingularityCurveTheoretic.lean`, `HawkingPenroseSingularity.lean` + `HawkingPenroseSingularityCurveTheoretic.lean`, `AreaTheorem.lean` + `AreaTheoremCurveTheoretic.lean`, `NoHairTheorem.lean`, `BHThermodynamicsFourLaws.lean`.
>
> **Phase 6m three-track DE closure:** `CausalSetDarkEnergy.lean`, `EntropicGravityDarkEnergy.lean`, `JacobsonThermoGRDarkEnergy.lean`, `DarkSectorClassificationExtension.lean` (extends prior Phase 5x `ClassificationTableDark.lean`).
>
> **Phase 6n math substrate (sub-directories under `lean/SKEFTHawking/`):** `GloriosoLiu/` (Axioms, DynamicalKMS, LocalEquilibrium, EntropyCurrent, LocalSecondLaw, OnsagerReciprocity, FirstOrderProjection, Phase1Reconciliation, SecondOrderProjection); `QuantumCrooks/` (Setup, Tasaki, Aberg, KafriDeffner, Quasiprobability, PerarnauLlobet, Concrete); `CrooksAnalogHawking/` (HorizonDetailedBalance, GallavottiCohen, AnalogHawkingBiconditional, SakharovHorizonCrooks, BiconditionalReformulation, SKEFTHorizonBridge, SKEFTGallavottiCohen); `SymTFTAudit/` (Applicability, CrossBridges, DrinfeldCenter, FreeKLinearCategory, FreeKLinearMonoidal, PseudoUnitary, DeligneTensor); `LDP/` (large-deviation rate-function infrastructure); `Resurgence/` (Basic, BorelAction, StokesBound); `Itô/` (substrate for Phase 6o I3 stochastic calculus); `LaplaceMethod.lean` (Wave 1a Stage 4 + 4b LDP integral asymptotics); plus single-file `HigherOrderSK.lean` (orders 4–7 count theorems).
>
> **Phase 6o waves:** `APSEta/` (Atiyah-Patodi-Singer η-invariant module family), `KerrSchild.lean` (Kerr-Schild double-copy substrate), `DoubleCopy/` (gauge-theory ⇄ gravity scattering double copy), `SoftTheorems/` (boostless cosmological soft theorems for I3), `Schellekens/` (Schellekens-chain reframing of 24|c− gauge-theory absorption), `ETH/` (eigenstate thermalization hypothesis refutation on horizon-MTC substrate). Phase 6o Wave 4a 2026-05-08 ships `JacobsonThermoGRDarkEnergy.lean` §8 extension (`SakharovExtended` strict-extension structure with load-bearing depletion : ℝ field; Sakharov 4-criterion ↔ Λ_J = Λ_HK biconditional retired in favour of one-way implication).

> **2026-05-05 PHASE 6n SESSION 7 — Track A load-bearing GL skeleton deepening + Track B Wave 2d Stage 4 substrate-level bridge.**
> **Track A (Wave 2a Stage 2-3b, GloriosoLiu/):**
>   - `EntropyCurrent.lean`: trivially-discharged `entropy_current_exists` upgraded to substantive Noether construction via `A.dynamical_KMS` extraction; new `noetherEntropyDensity` + `noetherEntropyCurrent` defs; `A : SKEFTAxioms` parameter is now LOAD-BEARING.
>   - `OnsagerReciprocity.lean`: trivially-discharged `OnsagerReciprocity_from_KMS` upgraded to substantive 9×9 diagonal embedding of FDR-pinned 2×2 conductivity; new `firstOrderConductivity` + `conductivity9x9_diagEmbed` defs + `firstOrderConductivity_isSymm_of_FirstOrderKMS` (off-diagonal entries vanish under FirstOrderKMS — first-derivative-order substantive Onsager).
> **Track B (Wave 2d Stage 4, NEW module CrooksAnalogHawking/SKEFTHorizonBridge.lean):**
>   - 6 substantive theorems linking Wave 2a `SKEFTAxioms` machinery at horizon temperature β_H to Wave 2c `HorizonDetailedBalance` predicate.
>   - Headline: `noetherEntropyDensity_nonneg_of_SKEFTAxioms` (BOTH `A.dynamical_KMS` + `A.reflection_pos` load-bearing) + `skeft_yields_horizon_crooks_witness` (FDR-pinned σ = β_H · W) + `sakharov_skeft_substrate_jacobsonConsistent` (³He-A concrete instance + horizonCrooks substantive partition vs. FLS BEC).
>   - Verlinde-vs-Jacobson distinction preserved at every Lean statement.
> **Infrastructure fix:** `scripts/extract_lean_deps.py` `compute_lean_hash()` was using non-recursive `glob("*.lean")`, missing changes in subdirectories — replaced with `rglob("*.lean")` so future updates of `GloriosoLiu/*.lean`, `CrooksAnalogHawking/*.lean`, etc. trigger re-extraction.
> **Session 7 totals:** +9 direct substantive theorems (entropy_current_exists upgrade + Onsager helpers + 6 SKEFTHorizonBridge theorems) / +4 new defs / +1 new module / 0 sorry / 0 new axioms / lake build 8534 jobs PASS clean. Working doc at `temporary/working-docs/phase6n/session7_load_bearing_lift.md`.
>
> **2026-05-04 → 2026-05-05 PHASE 6n SESSIONS 5+6 — substantive close: 5 of 7 waves SHIPPED.**
> 24 new modules (+8 GloriosoLiu/* Wave 2a Stage 1-3 / +7 QuantumCrooks/* Wave 2b Stage 1+2-3 / +4 CrooksAnalogHawking/* (incl. AnalogHawkingBiconditional) Waves 2c+2d Stage 1+2-3 / +2 SymTFTAudit/* Wave 1b Stage 2+3+4 / +1 HigherOrderSK / +3 Resurgence/{Basic,BorelAction,StokesBound}). All MCP-proven, zero Aristotle escalation, zero sorry. Substantive findings: Bool-projection Sakharov ↔ horizon-Crooks biconditional (Wave 2d), parametric + quantum Perarnau-Llobet no-go (Wave 2b), BEC SK-EFT geometric-convergence verdict (Wave 1a Path B), SymTFT PartiallyApplicable verdict (Wave 1b), third Sakharov-style biconditional (Wave 2c). See `docs/roadmaps/Phase6n_Roadmap.md` for full wave catalog + `memory:project_phase6n_session6_close.md` for Session-6 close snapshot.



> **2026-04-30 PHASE 6j FULLY CLOSED at structural-substantive scope (Stages 1-5) + W3+W4 dossier integration §9.**
> 4 modules shipped end-to-end in single session + W3+W4 §9 dossier-corrective additions:
> - W1 `RTReplicaTrickOnMTC.lean` (~544 LOC, 17 substantive thms / 4 noncomputable defs / 1 structure / 0 sorry / 0 new axioms / library 8491 PASS / 1 retroactive cross-bridge restoration)
> - W2 `CasiniHuertaModularHamiltonianMTC.lean` (~427 LOC, 16 substantive thms / 1 def / 1 structure / 0 sorry / 0 new axioms / library 8492 PASS / 0 cuts)
> - W3 `ScramblingTimeQuantitative.lean` (~425 LOC, **18 substantive thms = 12 baseline + 6 §9 dossier (incl. Tier-1 k=3 witness)** / **2 noncomputable defs = 1 baseline + 1 §9 `fundamentalQuantumDim_SU2k`** / 1 structure / 0 sorry / 0 new axioms / library 8494 PASS / 0 cuts; W3 dossier integrated as §9: HNTW entanglement-jump constants + SU(2)_k structural correction with all three tight-boundary witnesses k=2,3,4)
> - W4 `HolographicCFunctionMTC.lean` (~510 LOC, **16 substantive thms = 6 baseline + 4 §9 dossier + 1 §9.5b corollary + 5 §10 Tier-2** / **2 defs = 1 baseline + 1 §9 `cLogTotal`** / 1 structure / 0 sorry / 0 new axioms / library 8494 PASS / 2 retroactive P5 trivial-projection cuts in baseline only; W4 dossier integrated as §9: `cLogTotal` named def + corrected Fibonacci closed form + §9.5 dossier-corrective **strict-greater** inequality `cLogTotal(Fib) > log φ²` + §10 cross-wave bridges to W1+W2 + DLW recurrence at c-function level (toric=Ising=2 log 2); Virasoro recovery DROPPED per dossier §4.5)
>
> **Phase 6j totals: 4 modules / 67 substantive theorems (W1=17, W2=16, W3=18, W4=16) / 9 defs / 4 structures / 1906 LOC / 0 sorry / 0 new axioms / 2 audit cuts (baseline only) / library 8494 jobs PASS.**
>
> **Four dossier-correction patterns observed**: (W1) bare-LM gives only `−(1/2) log D²` not Kaul-Majumdar; (W2) leading log saturates on ANY MTC not just abelian; (W3) closed-form `Δ_F` values are HNTW entanglement-jump constants (arXiv:1403.0702), not scrambling-time corrections + SU(2)_k formula `2 cos(π/(k+2)) = [2]_q` is fundamental, not d_max for k ≥ 4; (W4) roadmap c-function formula algebraically inconsistent + `log φ²` Fibonacci witness arithmetically false + Virasoro recovery structurally wrong. **Both W3+W4 dossiers integrated + task files moved to `Lit-Search/Tasks/complete/`**. See `memory:project_phase6j_full_close.md` + `memory:project_phase6j_w3_post_dossier.md` + `memory:project_phase6j_w4_post_dossier.md`.
>
> **Hypothesis-bundle architecture**: each wave introduces a substantive Prop bundle promoting a Phase 6c tracked-Prop or structural bound to a universal-under-hypothesis-bundle theorem:
> - W1 `IsolatedHorizonHypotheses` → promotes Phase 6c.5 `H_RT_Formula_Valid` (universal-under-IH falsifier `isolatedHorizon_violates_H_RT`).
> - W2 `CHEntropyHypotheses` → promotes Phase 6c.5 `H_CasiniHuerta_Bound_Valid` (via `CHE_promotes_H_CasiniHuerta`).
> - W3 `QuantitativeScramblingHypotheses` → quantitatively strengthens Phase 6c.4 `HPCode.scramblingTimeBound`.
> - W4 `HolographicCFunctionHypotheses` → cross-wave to W2/W3 via saturation-set equivalence; ships Zamolodchikov-c-theorem analog under monotone-flow hypothesis.
>
> **First formalization in any proof assistant** of: Kitaev-Preskill topological EE on abstract MTC carrier, LM "no log A on pure-CS substrate" structural negative result, DLW vacuum-sector ambiguity at multiple convention levels (Wave 1 negative-form, Wave 2 positive-form, Wave 3 baseline), Casini-Huerta universal entropy bound under explicit BW+CC+KP hypothesis bundle, saturation biconditional (bound saturates ⟺ trivial MTC), closed-form quantitative tightness Δ=γ, Hayden-Preskill scrambling-time quantitative parametric form `t_scr = log D² + Δ_F` on MTC substrate, Zamolodchikov c-theorem analog on horizon-MTC substrate.
>
> Stages 6-13 (cross-layer Python `src/holography/` + figures + Stage 13 review + paper bundle assembly into D3 §13.5 + I1 sidebar per Phase 6i Wave 7 paper-bundle architecture) deferred to a future Phase 6j paper-bundle preparation cycle.
>

> **2026-04-29 PHASE 6e WAVE 1 + EARLIER.** Counts re-synced via
> `scripts/update_counts.py`: **4442 theorems** (4419 substantive + 23
> placeholder), **0 sorry**, **1 axiom**, **190 modules**. Phase 6e Wave 1
> (`HeatKernelExpansion.lean`) shipped through Stage 11 (notebooks) on
> 2026-04-29 with 19 substantive theorems / 0 sorry / 0 new axioms (verified
> `propext, Classical.choice, Quot.sound` only). Earlier Phase 6c Wave 2
> (`EWBaryogenesisChiralityWall.lean`, 16 substantive theorems) and Phase
> 5z Wave 4 (`MajoranaRungSMG.lean`, 11 substantive theorems) shipped
> 2026-04-29; Phase 6c CLOSED end-to-end. Pre-existing 2026-04-28 sync
> covered Phase 6a/6b/6c/6d/6f cohort; post-strengthening per-wave counts
> (verified via `_module_thm_count_strict`):
> W1 StrongCPTopologicalDE 8, W3 EquivalencePrinciple 25 (was 27 — removed
> P5 tautology + decorative marker), W4 QECHolographyBridge 10, W1d
> CenterSymmetryConfinement 18 (was 20 — removed redundant
> `ising_nu_above_0_6` + `potts_nu_below_0_6` threshold pair), W2d
> ChiralSSB_QCD 10, W3d CFLChiralLagrangian 12, W5 RTCasiniHuertaBounds 7.
> See `docs/counts.json` for ground truth.

### Lean 4.29.0, Mathlib pinned to commit `8850ed93`

| Module | Lines | Theorems | Axioms | Phase | Key Results |
|--------|-------|----------|--------|-------|-------------|
| Basic | 202 | 0 | 0 | 1 | Type definitions (ScalarField, Spacetime1D) |
| AcousticMetric | 310 | 8 | 0 | 1 | det(g)=-ρ², Lorentzian signature, T_H formula |
| SKDoubling | 661 | 9 | 0 | 1 | Uniqueness (γ₁,γ₂), FDR, KMS optimality, zeroTemp_nontrivial |
| HawkingUniversality | 555 | 9 | 0 | 1 | Dispersive bound, dissipative existence, universality |
| SecondOrderSK | 882 | 19 | 0 | 2 | Counting formula, positivity constraint, full uniqueness |
| WKBAnalysis | 561 | 15 | 0 | 2 | Damping nonneg, turning point, biconditionals |
| CGLTransform | 352 | 7 | 0 | 2 | CGL FDR, Einstein relation, CGL→KMS chain |
| ThirdOrderSK | 329 | 14 | 0 | 3 | Parity alternation (general N), spectral parity |
| GaugeErasure | 262 | 12 | 0 | 3 | Gauge erasure theorem, U(1) survival, SM dichotomy (axiom removed Wave 6) |
| WKBConnection | 414 | 17 | 0 | 3 | Decoherence nonneg, noise floor, unitarity deficit |
| ADWMechanism | 288 | 21 | 0 | 3 | Critical coupling pos, curvature_zero_at_Gc, NG modes |
| ChiralityWall | 301 | 17 | 0 | 4 | GS no-go requires all, TPF evasion count, wall status |
| VestigialGravity | 272 | 18 | 0 | 4 | Phase hierarchy, EP violation, metric DOF |
| FractonHydro | 264 | 17 | 0 | 4 | Binomial monotonicity, charge counting, erasure universal |
| FractonGravity | 248 | 20 | 0 | 4 | Bootstrap divergence, DOF gap, route achievements |
| FractonNonAbelian | 203 | 14 | 0 | 4 | YM incompatibility, obstruction count, param gap |
| KappaScaling | ~200 | 11 | 0 | 5 | Crossover balance, regime classification, scaling laws |
| PolaritonTier1 | ~150 | 6 | 0 | 5 | Spatial attenuation ≥ 1, monotonicity, BEC recovery |
| SU2PseudoReality | ~200 | 10 | 0 | 5 | One-link normalization, effective coupling, Binder limits |
| FermionBag4D | ~250 | 16 | 0 | 5 | SO(4) integration, 8-fermion bounds, bag positivity, vestigial splitting |
| LatticeHamiltonian | ~400 | 28 | 0 | 5 | BZ compact, GS 9 conditions, TPF 3 violations, ℓ²(ℤ) ∞-dim, round discontinuous, Hermitian trace |
| GoltermanShamir | ~330 | 14 | 0 | 5 | 9 GS conditions as substantive Props, no-go bundle, TPF evasion, Fock space finite-dim, Pauli exclusion (axiom removed Wave 6) |
| TPFEvasion | ~200 | 12 | 0 | 5 | Master synthesis: 5 violations assembled, tpf_outside_gs_scope_main, two_violations_proved |
| KLinearCategory | ~300 | 16 | 0 | 5 | SemisimpleCategory, FinitelyManySimples, Schur orthogonality, FusionRules, Vec_G D²=\|G\|, Rep(S₃) D²=6 |
| SphericalCategory | ~350 | 18 | 0 | 5 | PivotalCategory (FIRST-EVER), CategoricalTrace, SphericalCategory, quantumDim, Fibonacci φ²=φ+1 |
| FusionCategory | ~250 | 14 | 0 | 5 | FusionCategoryData axioms, FSymbolData, PentagonSatisfied, globalDimSq_pos, Frobenius-Perron |
| FusionExamples | ~400 | 30 | 0 | 5 | Vec_{Z/2,Z/3}, Rep(S₃), Fibonacci: fusion rules, commutativity, τ⊗τ=1⊕τ, F-matrix, chirality |
| VecG | ~200 | 9 | 0 | 5 | GradedVectorSpace, Day convolution, unit/assoc/simple tensor, dim multiplicativity |
| DrinfeldDouble | ~300 | 15 | 0 | 5 | DrinfeldDoubleElement, twisted multiplication, conjugation action, D(G) unit laws, anyon counting |
| GaugeEmergence | ~250 | 14 | 0 | 5 | Half-braiding, gauge emergence Z(Vec_G)≅Rep(D(G)), chirality limitation c≡0(8), Layer 1→2→3 bridge |
| SO4Weingarten | ~250 | 14 | 0 | 5 | Weingarten 2nd/4th moment, channel positivity, bond weight, Planck occupation (**ALL PROVED**, Aristotle `117a7115`) |
| FractonFormulas | ~400 | 45 | 0 | 5 | Charge counting, dispersion, retention, DOF gap, YM obstructions (**ALL PROVED**, Aristotle `4528aa2b`) |
| WetterichNJL | ~250 | 18 | 0 | 5 | Fierz completeness, scalar/pseudoscalar/vector channels, NJL-ADW correspondence (**ALL PROVED**, Aristotle `4528aa2b`) |
| VestigialSusceptibility | ~250 | 16 | 0 | 5 | Gamma trace, u_g positivity, bubble integral, RPA susceptibility, vestigial_before_tetrad (**ALL PROVED**, Aristotle `9e2251cd`) |
| QuaternionGauge | ~200 | 10 | 0 | 5 | Unit quaternion norm, identity, SO(4) dim, plaquette bounds, heatbath detailed balance (**ALL PROVED**, Aristotle `fb657b4d`) |
| GaugeFermionBag | ~200 | 9 | 0 | 5 | Tetrad gauge covariance, metric invariance, bag weight real, SMW update, Binder limits (**ALL PROVED**, Aristotle `fb657b4d`) |
| HubbardStratonovichRHMC | ~400 | 22 | 0 | 5 | HS identity, Kramers, multi-shift CG, complex pseudofermion Pfaffian identity |
| MajoranaKramers | ~400 | 25 | 0 | 5 | Majorana Kramers degeneracy, sign-free determinant, 8×8 block structure |
| OnsagerAlgebra | ~350 | 24 | 0 | 5a | Dolan-Grady definition, Davies isomorphism, Chevalley embedding into L(sl₂), GT connection (**ALL PROVED**, Aristotle `9d6f2432`) |
| OnsagerContraction | ~200 | 12 | 0 | 5a | Inönü-Wigner contraction O→su(2), rescaling, commutator vanishing, anomaly encoding (**ALL PROVED**, Aristotle `36b7796f`) |
| Z16Classification | ~350 | 22 | 0 | 5a | Z₁₆ classification (axiom discharged→theorem), SuperModularCategory, 16-fold way, chirality mod 8→16, anomaly cancellation, Drinfeld bridge (**ALL PROVED**) |
| SteenrodA1 | ~300 | 17 | 0 | 5a | A(1) 8-dim F₂-algebra, Adem relations, multiplication table, Ext→Z₁₆ connection (docstrings corrected: Ext⁴ dim=3 not 4) (**ALL PROVED**, first Steenrod formalization) |
| SMGClassification | ~250 | 13 | 0 | 5a | AZClass tenfold way, SMGSymmetryData, HasSpectralGap typeclass, gapped interface conjecture (**ALL PROVED**) |
| PauliMatrices | ~250 | 15 | 0 | 5a | σ_x,σ_y,σ_z definitions, commutation [σ_i,σ_j]=2iε_{ijk}σ_k, anti-commutation, involutivity, traces (**ALL PROVED**, Aristotle `90ed1a98`) |
| WilsonMass | ~200 | 11 | 0 | 5a | M(k)=3-cos kx-cos ky-cos kz, M=0 iff k=0, non-negativity, bounds (**ALL PROVED**, Aristotle `90ed1a98`) |
| BdGHamiltonian | ~200 | 8 | 0 | 5a | BdGIndex 4×4, H_BdG σ⊗τ Kronecker, q_A definition, Kronecker commutator identity (**ALL PROVED**, Aristotle `90ed1a98`) |
| GTCommutation | ~200 | 10 | 0 | 5a | **Central theorem** [H_BdG(k),q_A(k)]=0, 2×2 τ-space trig identity, GS evasion, bridge to TPF (**ALL PROVED**, Aristotle `18969de2`) |
| GTWeylDoublet | ~250 | 12 | 0 | 5a | Model 2: Q_V+Q_A generate Onsager, emanant SU(2), Witten anomaly=element 8∈ℤ₁₆, bridges (**ALL PROVED**) |
| ChiralityWallMaster | ~300 | 17 | 0 | 5a | Three-pillar synthesis: GS no-go + GT positive + Z₁₆ anomaly, bridge theorems, status structure (**ALL PROVED**) |
| SMFermionData | ~300 | 19 | 0 | 5b | SM fermion enum, ℤ₄ charges X=5(B-L)-4Y, all odd, component counts 16/15, anomaly contributions (**ALL PROVED**) |
| Z16AnomalyComputation | ~400 | 23 | 0 | 5b | Anomaly 16≡0/15≡-1 mod 16, 3-gen anomaly -3, hidden sector theorem, "16" convergence (2 axioms discharged→theorems) (**ALL PROVED**) |
| GenerationConstraint | ~250 | 13 | 0 | 5b | c₋=8N_f (discharged→theorem), N_f≡0(3) derived as conditional, minimal N_f=3 (**ALL PROVED**, Aristotle `a1dfcbde`) |
| DrinfeldCenterBridge | ~300 | 18 | 0 | 5b | Half-braiding ↔ D(G)-module bijection, conjugation identities, Mathlib Center API (**ALL PROVED**) |
| VecGMonoidal | ~250 | 12 | 0 | 5b | **MonoidalCategory(Vec_G)** proved, Center(Vec_G) monoidal+braided, forgetful functor (**ALL PROVED**, Aristotle `48493889`) |
| ToricCodeCenter | ~400 | 25 | 0 | 5b | 4 toric code anyons, fusion rules, R(e,m)=-1, fermion self-stats, first computed Drinfeld center (**ALL PROVED**) |
| S3CenterAnyons | ~350 | 22 | 0 | 5b | 8 non-abelian anyons, d=1,1,2,3,3,2,2,2, D²=36=|S₃|², A3⊗A3 decomposition (**ALL PROVED**) |
| CenterEquivalenceZ2 | ~200 | 10 | 0 | 5b | Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2): bijection, fusion, braiding preserved (**ALL PROVED**) |
| DrinfeldDoubleAlgebra | ~200 | 9 | 0 | 5b | D(G) as k-algebra: twisted convolution, unit laws, associativity (**ALL PROVED**, Aristotle `878b181f`) |
| DrinfeldDoubleRing | ~150 | 3+inst | 0 | 5b | DG newtype wrapper, Ring + Algebra k instances (**ALL PROVED**, Aristotle `52992d6a`) |
| DrinfeldEquivalence | ~250 | 12 | 0 | 5b | Z(Vec_G)≅Rep(D(G)): simple counts, Hopf structure, antipode involutive, gauge emergence (**ALL PROVED**) |
| WangBridge | ~200 | 9 | 0 | 5b | c₋=8N_f from 16 Weyl, fractional c₋ forces ν_R, full chain to N_f≡0(3) (**ALL PROVED**) |
| ModularInvarianceConstraint | ~250 | 12 | 0 | 5b | ζ₂₄ root of unity, framing anomaly 24\|c₋, complete chain η→24→3\|N_f (**ALL PROVED**, Aristotle `b54f9611`) |
| RokhlinBridge | ~250 | 14 | 0 | 5b | Rokhlin "16" convergence, with/without ν_R analysis, summary updated to reference Ext computation (**ALL PROVED**) |
| QNumber | ~200 | 11 | 0 | 5b | q-integers [n]_q as Laurent polynomials, classical limit [n]_1=n, [2]_1^4=16 (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2 | ~200 | 6 | 0 | 5b | **FIRST quantum group**: U_q(sl₂) via FreeAlgebra+RingQuot, zero axioms (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2Hopf | ~450 | 66 | 0 | 5c-5d | **FIRST Hopf algebra on U_q(sl₂)**: Bialgebra + HopfAlgebra, coproduct/counit/antipode, S²=Ad(K), Serre coproduct (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4` + `79e07d55`) |
| SU2kFusion | ~550 | 49 | 0 | 5c | SU(2)_k fusion at k=1,2,3,5: Ising σ²=1+ψ, Fibonacci τ²=1+τ, k=5 fusion/commutativity/associativity (10 new), charge conjugation (**ALL PROVED by native_decide**) |
| Uqsl2Affine | ~300 | 9 | 0 | 5c | U_q(sl_2 hat) affine quantum group: Chevalley + cross-relations, coideal property (**ALL PROVED**) |
| SU2kSMatrix | ~350 | 22 | 0 | 5c | SU(2)_k S-matrices at k=1,2,5: unitarity, Verlinde formula, modularity, k=5 unitarity via rational character sums (3 new) (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RestrictedUq | ~250 | 11 | 0 | 5c | Restricted quantum group u_q(sl₂): nilpotency, torsion, SU(2)_k connection (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RibbonCategory | ~200 | 4 | 0 | 5c | BalancedCategory, RibbonCategory, MTC definitions (FIRST in any proof assistant) (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| E8Lattice | ~200 | 19 | 0 | 5c | E8 Cartan: det=1, even unimodular, Rokhlin gap σ=8, Serre bound, classification (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| AlgebraicRokhlin | ~200 | 10 | 0 | 5c | Algebraic Serre theorem σ≡0 mod 8 for even unimodular forms, characteristic vectors, E8 bridge (**ALL PROVED, zero sorry**) |
| SpinBordism | ~150 | 8 | 0 | 5c | Spin bordism → Rokhlin → Wang chain: SpinBordismData structure, anomaly with/without ν_R, full Wang chain (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| VerifiedJackknife | ~200 | 5 | 0 | 5c | First verified statistical estimators: jackknife variance, autocorrelation, intAutocorrTime (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| TetradGapEquation | ~300 | 20 | 0 | 5d | **First tetrad gap equation**: NJL-type gap, criticalCoupling, IVT existence, Banach uniqueness, bifurcation, vestigial connection (**ALL PROVED**, Aristotle `79e07d55`) |
| SU2kMTC | ~220 | 11 | 0 | 5d | Ising F-symbols (F^σ_{ψσψ}=-1 corrected), pentagon, ModularTensorData instance (**ALL PROVED, zero sorry** — native_decide over Q(√2)) |
| QSqrt2 | ~50 | 3 | 0 | 5d | Q(√2) number field with DecidableEq for Ising MTC (**ALL PROVED, zero sorry**) |
| QSqrt5 | ~80 | 7 | 0 | 5d | Q(√5) number field: golden ratio φ²=φ+1, φ·φ⁻¹=1, Fibonacci F²=I (**ALL PROVED by native_decide**) |
| FibonacciMTC | ~200 | 12 | 0 | 5d/5p | Fibonacci MTC: F-symbols in Q(√5), F²=I PROVED, PreModularData, chirality (**ALL PROVED, zero sorry** — native_decide over Q(√5)). **Wave 5 add 2026-04-15:** `fib_modular` proof (det(fibS) ≠ 0 over ℝ via Matrix.det_fin_two_of + field_simp + nlinarith) — enables `fib_mtc_muger_trivial` via the abstract Müger bridge. |
| Uqsl2AffineHopf | ~6010 | 201 | 0 | 5d/5e | U_q(ŝl₂) Hopf algebra: coproduct/counit/antipode via RingQuot.liftAlgHom; all 8 q-Serre proofs closed (4 comul + 4 antipode) — **0 sorry**. Bialgebra + HopfAlgebra typeclass instances WIRED (prior Tranche E work). **Phase 5e Wave 8 complete 2026-04-15**: 20 new theorems (8 per-generator antipode evals `uqAff_antipode_{E,F,K}_i`, 4 K-conjugation helpers, 8 per-generator S² identities `uqAff_antipode_squared_*`). Wave 8 original spec `S² = Ad(K₀K₁)` was mathematically wrong (affine Cartan matrix rank-deficient — no single global K implements S² on both simple-root generators); corrected to per-generator form with inline historical note cross-referencing the `Uqsl3Hopf.lean:3995` sl₃ correction. |
| VerifiedStatistics | ~150 | 6 | 0 | 5d | Statistics extension: sample variance non-neg, Cauchy-Schwarz, jackknife mean-case, N_eff ≤ N (**ALL PROVED**) |
| KerrSchild | ~100 | 7 | 0 | 5d | Kerr-Schild metrics: null vector, radial_null, Sherman-Morrison inverse, Schwarzschild, DOF counting (**ALL PROVED**) |
| CoidealEmbedding | ~130 | 6 | 0 | 5d | Coideal subalgebra embedding B_i into U_q(ŝl₂), Dolan-Grady from Chevalley (**ALL PROVED**) |
| RepUqFusion | ~160 | 13 | 0 | 5d | Rep(u_q) → SU(2)_k fusion data correspondence, dim formulas, Peter-Weyl (**ALL PROVED**) |
| StimulatedHawking | ~200 | 11 | 0 | 5d | Stimulated Hawking amplification protocol, signal-to-noise, phonon statistics (**ALL PROVED**) |
| CenterFunctor | ~200 | 9 | 0 | 5d | Abstract functor Center(Vec_G) → ModuleCat(DG), natural transformation (**0 sorry — 2 tracked hypotheses H_CF1 ✓, H_CF2 partial**) |
| CenterFunctorZ2 | ~640 | 51 | 0 | 5s W9 | 4 D(Z/2) simple characters as AlgHoms, Module instances, simpleChi injectivity, pairwise distinctness, simpleRepModule bundling (**ALL PROVED**) |
| CenterFunctorZ2Equiv | ~1950 | 56 | 3 | 5s W9 | H_CF1 discharge via `gradedTotalSpaceFunctor` ✓, canonical functor architecture, signHalfBraiding monoidal ✓, extractBraidAction_{e,a}_{vacuum,electric} ✓, middleSwap_eq_braiding ✓, uu_iso_graded ✓, halfBraiding_at_unit ✓, canonicalCenterToRep.Faithful ✓ via Aristotle. **3 research-grade sorries: halfBraiding_sq_identity tmul (graded hexagon summand), halfBraiding_sq_identity_a tmul (mirror), h_cf2_G2 assembly (Full+EssSurj pending).** See `working-docs/phase5s_wave9_option_b_helpers.md` for 38-session investigation log. Zero downstream dependencies (H_CF2 OPTIONAL per CenterFunctor.lean L75). |
| QCyc16 | ~100 | 6 | 0 | 5e | Q(ζ₁₆) cyclotomic field: ζ⁸=-1, ζ¹⁶=1, (√2)²=2 (**ALL PROVED by native_decide, zero sorry**) |
| QCyc5 | ~155 | 9 | 0 | 5e | Q(ζ₅) cyclotomic field: ζ⁵=1, Fibonacci hexagon E1-E3, twist, writhe removal (**ALL PROVED by native_decide, zero sorry**) |
| IsingBraiding | ~200 | 25 | 0 | 5e | **COMPLETE braided Ising MTC**: R-matrix, twist, 6 hexagon eqs, 4 ribbon conditions, Gauss sum p₊=2ζ (c_top=1/2), trefoil=-1 (**ALL PROVED by native_decide, zero sorry**, FIRST verified knot invariant) |
| QSqrt3 | ~90 | 8 | 0 | 5e | Q(√3) for SU(2)₄ S-matrix: row norms, orthogonality, det (**ALL PROVED by native_decide, zero sorry**) |
| QLevel3 | ~170 | 19 | 0 | 5e | Q[x]/(20x⁴-10x²+1) for SU(2)₃: s²+t²=1/2, ALL 10 S*S^T=I entries, quantum dim golden ratio (**ALL PROVED by native_decide, zero sorry**) |
| Uqsl3 | ~300 | 22 | 0 | 5i | **FIRST rank-2 quantum group in any proof assistant**: U_q(sl₃) via FreeAlgebra+RingQuot, 8 generators, A₂ Cartan matrix, 21 Chevalley relations (**ALL PROVED, zero sorry**) |
| Uqsl3Hopf | ~5230 | 189 | 0 | 5i | **Phase 5i Wave 2 / Tranche E COMPLETE 2026-04-14**: Full Hopf algebra wiring for U_q(sl₃). Δ/ε/S defined via RingQuot.liftAlgHom; **all 21 relation-respect proofs done for each** (incl. 4 antipode q-Serre cubics E12/E21/F12/F21 closed via palindromic Serre atom-bridge, ~1500 lines). S² = Ad(K₁²K₂²) per generator (Drinfeld theorem). 24 per-generator eval lemmas + 4 derived F·K rules + 3 coalgebra axioms + 16 antipode convolution helpers + 2 antipode laws. **`Bialgebra` instance + `HopfAlgebra` instance** wired (commits `dadce3e`, `bdf0ee9`). Build clean, **0 sorry**. |
| SU3kFusion | ~600 | 99 | 0 | 5i | **FIRST SU(3)_k fusion in any proof assistant**: SU(3)₁ Z₃ fusion (3 objects) + SU(3)₂ (6 anyons, Fibonacci subcategory τ⊗τ=1+τ), charge conjugation, associativity+commutativity (**ALL PROVED by native_decide, zero sorry**) |
| GaugingStep | ~400 | 34 | 0 | 5h | Gauging obstruction: NotOnSiteSymmetry, SymmetryDisentangler, GT Models 1+2, SM anomaly 16≡0 mod 16, SMGPhaseData (BCH+HW), Golterman-Shamir propagator-zero, ChiralityWall3DStatus (**ALL PROVED, zero sorry**) |
| FermiPointTopology | ~350 | 28 | 0 | 5j | Fermi-point topological charge: winding number N, |N|=1 → U(1) gauge + Weyl fermions, |N|=2 → SU(2) gauge emergence, spin-connection co-emergence (**ALL PROVED, zero sorry**) |
| PolyQuotQ | ~200 | 15 | 0 | 5i | Q(ζ₃) cyclotomic field via polynomial quotient for SU(3)₁ S-matrix verification (**ALL PROVED, zero sorry**) |
| TemperleyLieb | ~200 | — | 0 | 5k | Temperley-Lieb algebra for WRT invariants (**ALL PROVED, zero sorry**) |
| JonesWenzl | ~200 | — | 0 | 5k | Jones-Wenzl idempotents (**ALL PROVED, zero sorry**) |
| WRTInvariant | ~200 | — | 0 | 5k | WRT TQFT invariant definitions (**ALL PROVED, zero sorry**) |
| WRTComputation | ~200 | — | 0 | 5k | WRT invariant computations (**ALL PROVED, zero sorry**) |
| SurgeryPresentation | ~200 | — | 0 | 5k | Surgery presentation for 3-manifolds (**ALL PROVED, zero sorry**) |
| QuantumGroupHopf | ~200 | — | 0 | 5l | Generic quantum group Hopf algebra (**ALL PROVED, zero sorry**) |
| QuantumGroupGeneric | ~200 | — | 0 | 5l | Generic U_q(g) formalization (**ALL PROVED, zero sorry**) |
| KMatrixAnomaly | ~200 | — | 0 | 5m | K-matrix anomaly inflow formalization (**ALL PROVED, zero sorry**) |
| SPTStacking | ~200 | — | 0 | 5n | SPT stacking group structure (**ALL PROVED, zero sorry**) |
| VillainHamiltonian | ~200 | — | 0 | 5n | Villain lattice Hamiltonian formalization (**ALL PROVED, zero sorry**) |
| TPFDisentangler | ~200 | — | 0 | 5o | TPF disentangler for community value (**ALL PROVED, zero sorry**) |
| StringNet | ~200 | — | 0 | 5o | String-net model formalization (**ALL PROVED, zero sorry**) |
| KacWaltonFusion | ~200 | — | 0 | 5o | Kac-Walton fusion rule computation (**ALL PROVED, zero sorry**) |
| FPDimension | ~310 | ~30 | 0 | 5p | Frobenius-Perron dimension derivation (**ALL PROVED, zero sorry**). **Phase 5p Wave 1 complete + Wave 2 partial 2026-04-15**: eigenvector approach (per deep research recommendation) for Fibonacci/Ising/SU(3)_1/SU(2)_3 (both N_{1/2} and N_1) over QSqrt5/QSqrt2/ℤ via native_decide. D² derived for each. New 2026-04-15: SU(4)_1 (Z_4 pointed, all FPdim=1, D²=4) and **G₂_1 (FPdim=φ — third source of golden ratio)** sharing Fibonacci's fusion matrix. `phi_triple_origin` formalizes that φ arises identically in three Lie algebra contexts: A₁ at level 3 (SU(2)₃), A₁ at level 1 in Fibonacci form, and G₂ at level 1. |
| MugerCenter | ~545 | ~36 | 0 | 5p | Muger center formalization (**ALL PROVED, zero sorry**). **Phase 5p Waves 3-5 complete 2026-04-15**: `ObjectProperty.IsMonoidal` instance + `MugerCenter C := ObjectProperty.FullSubcategory (IsTransparent C)` abbrev + `SymmetricCategory (MugerCenter C)` instance (the key payoff — Z₂(C) is symmetric even when ambient is only braided). Data-level bridge: `PreModularData.isRowTransparent` (vacuum-row form, works for normalized + unnormalized), `isMugerTrivial` with Decidable instances for finite MTCs. **Wave 5 abstract bridge proved**: `PreModularData.modularImpliesMugerTrivial_proof` — det(S)≠0 implies Muger triviality, via the Mathlib `det_zero_of_row_eq` linear-algebra route in `ModularityTheorem.lean`. Per-MTC instances: `ising_mtc_muger_trivial`, `su2k1_mtc_muger_trivial`, `fib_mtc_muger_trivial` (the latter requires the new `fib_modular` proof in `FibonacciMTC.lean`). Categorical per-MTC witnesses preserved (Ising σ/ψ, Fibonacci τ, Toric e/m/ε). First Muger-center formalization in any proof assistant with full symmetric-monoidal structure + abstract Direction-1 bridge. |
| D2Formula | ~135 | 9 | 0 | 5p | **Phase 5p Wave 6 complete 2026-04-15**: D²(Z(C)) = D²(C)² explicit Drinfeld-center dimension identities for Vec_{ℤ/2} (toric code, D²=4=2²) and Vec_{S₃} (8 anyons, D²=36=6², the **non-abelian** instance). `drinfeld_center_dim_Z2`, `drinfeld_center_dim_S3`, `drinfeld_center_dimension_witness` (unified). General-G statement deferred — needs Mathlib's Σ(dim ρ)² = \|G\| (currently a TODO upstream). |
| IsingGates | ~200 | — | 0 | 5p | Ising anyon gate set for TQC (**ALL PROVED, zero sorry**) |
| FibonacciBraiding | ~200 | — | 0 | 5p | Fibonacci anyon braiding matrices (**ALL PROVED, zero sorry**) |
| FibonacciQutrit | ~200 | — | 0 | 5p | Fibonacci qutrit encoding (**ALL PROVED, zero sorry**) |
| FibonacciUniversality | ~200 | — | 0 | 5p | Fibonacci universality proof (**ALL PROVED, zero sorry**) |
| FibonacciQutritUniversality | ~200 | — | 0 | 5p | Fibonacci qutrit universality (**ALL PROVED, zero sorry**) |
| QCyc5Ext | ~200 | — | 0 | 5p | Q(ζ₅) extension for Fibonacci computations (**ALL PROVED, zero sorry**) |
| A1Ring | ~300 | 14 | 0 | 5q | A(1) left-multiplication matrices (Milnor basis), Adem relations verified (**ALL PROVED, zero sorry**) |
| A1Resolution | ~350 | 15 | 0 | 5q | Minimal free resolution of F₂ over A(1) through degree 5, d²=0, RREF witnesses for exactness (**ALL PROVED, zero sorry**) |
| A1Ext | ~300 | 14 | 0 | 5q | Minimality verification, Ext dimensions 1,2,2,2,3,4, cross-validation via trace/Frobenius (**ALL PROVED, zero sorry** — first Ext over A(1) in any proof assistant) |
| ExtBordismBridge | ~200 | 4 | 0 | 5q | 3 topological hypotheses (H1,H3,H4) replacing 1 opaque SpinBordismData, generation constraint chain (**ALL PROVED, zero sorry**) |
| ChangeOfRings | ~200 | 5 | 0 | 5r | H2 (change of rings) discharged via Hom-tensor adjunction (**ALL PROVED, zero sorry**) |
| FKGappedInterface | 162 | 12 | 0 | 5s | **First FK interacting SPT formalization (Cayley calibration)**: 16×16 integer Hamiltonian W = Σ Ω_{abcd} γ_a γ_b γ_c γ_d (Spin(7)-invariant 14-quartet form), eigenvalues {-14, 0, +2} with multiplicities {1, 8, 7}, spectral gap **Δ=14**. All 12 theorems via `native_decide` on `Matrix (Fin 16) (Fin 16) ℤ`: `W_minimal_poly` (W³+12W²-28W=0), `W_trace=0`, `W_frobenius=224`, `W_symmetric`, `multiplicity_system`, `eigenvalue_ground` (gs=e₀-e₁₅, eigenvalue -14), `gs_vec_nonzero`, `W_commutes_parity`, `gs_even_parity`, `spectral_gap`/`_pos`, `fk_summary` (**ALL PROVED, zero sorry**). Cross-layer Python pipeline: 11 helpers in `formulas.py` (`fk_majorana_operators`, `fk_cayley_quartets`, `fk_hamiltonian` constructive form, `fk_hamiltonian_sparse` Lean-encoding form, `fk_eigenvalues`, `fk_spectral_gap`, `fk_ground_state_vector`, `fk_parity_matrix`, `fk_minimal_polynomial_residual`, `fk_dimensional_ladder_evidence`); 45 pytest cases / 8 classes including TestFKLeanSparseParity (cross-layer-parity check); 2 figures (`fig_fk_spectrum` rewritten + new `fig_fk_dimensional_ladder` for Wave 4 bridge theorem); notebook `Phase5s_FKGappedInterface_Technical.ipynb`. |
| ModularityTheorem | ~200 | 2 | 0 | 5s | General det(S)≠0 → no proportional rows (Muger Direction 1) (**ALL PROVED, zero sorry**) |
| EmergentGravityBounds | 211 | 12 | 0 | 5f | **Phase 5f**: Coupling deficit (G_Wen << G_c) and NLO Lorentz-invariance bounds for emergent-gravity scenarios from deep research; pairs with InstantonZeroModes for the non-perturbative path (**ALL PROVED, zero sorry**) |
| FigureEightKnot | 143 | 9 | 0 | 5f | **Phase 5f**: RT invariant of figure-eight knot 4₁ from Ising MTC braiding (3-strand σ₁σ₂⁻¹σ₁σ₂⁻¹ word); fusion-basis trace; first non-torus knot invariant in any proof assistant (**ALL PROVED, zero sorry**) |
| TQFTPartition | 191 | 21 | 0 | 5f | **Phase 5f**: Verlinde partition function `dim H(Σ_g) = Σ_a S_{0a}^{2-2g}` for Ising and Fibonacci MTCs at genus 0–4; integer partition sequences (Ising 1,3,10,36,136 / Fibonacci Lucas 1,2,5,15,50) verified despite irrational quantum dimensions (**ALL PROVED, zero sorry**) |
| SPTClassification | 443 | 41 | 1 | 5h | **Phase 5h Wave 1**: SPT classification infrastructure (3+1D / 4+1D); SPTPhaseData / FreeFermionSPT / CommutingProjectorSPT / InterfaceData; structured **gapped_interface_axiom** (Thorngren-Preskill-Fidkowski TPF conjecture, eliminability=hard) and conditional consequences (chiral lattice gauge theory existence) — only project axiom (**ALL OTHER THEOREMS PROVED, zero sorry**) |
| QuantumGroupCoproduct | 1347 | 54 | 0 | 5m | **Phase 5m Wave 2**: Generic coproduct Δ for U_q(𝔤) parameterized over arbitrary Cartan matrix A; standard Drinfeld-Jimbo formulas (Δ(E_i)=E_i⊗K_i+1⊗E_i, etc.); 11/11 QGRel relation-respect proofs incl. SerreE/F_quad via palindromic atom-bridge and EF_diag via diamond bypass; descended `qgComul` via `RingQuot.liftAlgHom` (**ALL PROVED, zero sorry**) |
| QuantumGroupAntipode | 811 | 25 | 0 | 5m | **Phase 5m Wave 2**: Generic antipode S for U_q(𝔤) via `MulOpposite` (anti-multiplicativity S(ab)=S(b)S(a)); standard Drinfeld-Jimbo formulas (S(E_i)=−E_iK_i⁻¹, S(F_i)=−K_iF_i, S(K_i)=K_i⁻¹); 11/11 QGRel respect proofs; descended `qgAntipode` (**ALL PROVED, zero sorry**) |
| QuantumGroupInstantiation | 629 | 38 | 0 | 5m | **Phase 5m Wave 1 strengthening**: AlgEquivs `qgA1EquivUqsl2 : QuantumGroup k cartanA1 ≃ₐ Uqsl2 k` and `qgA2EquivUqsl3 : QuantumGroup k cartanA2 ≃ₐ Uqsl3 k`; bidirectional AlgHoms via `FreeAlgebra.lift` → `RingQuot.liftAlgHom`; roundtrip via `RingQuot.ringQuot_ext'` + `FreeAlgebra.hom_ext` (**ALL PROVED, zero sorry, zero sorryAx**) |
| QuantumGroupMeta | 220 | 16 | 0 | 5m | **Phase 5m Wave 4**: Exceptional Cartan matrices E₆, E₇, E₈, F₄ with diag/symmetry verification; CartanTypeData for all exceptional types; named SU(4) and E₆ generator abbreviations; level-1 alcove structure (E₆₁=ℤ₃, E₇₁=ℤ₂, E₈₁=trivial, F₄₁=ℤ₂); first E₆/E₇/E₈ quantum-group generators in any proof assistant (**ALL PROVED, zero sorry**) |
| QCyc3 | 102 | 9 | 0 | 5i | **Phase 5i Wave 4d**: Q(ζ₃) = ℚ[x]/(x²+x+1) as concrete `PolyQuotQ 2` instance with reduction `![-1,-1]`; preserves 9 theorems from old PolyQuotQ (ζ²=−1−ζ, ζ³=1, cyclotomic_sum, ζ≠1, ζ²≠1, SU(3)₁ S-matrix row orthogonality); Mathlib-style docstring (**ALL PROVED, zero sorry**) |
| QCyc15 | 150 | 8 | 0 | 5i | **Phase 5i Wave 4c-part1**: Q(ζ₁₅) = ℚ[x]/Φ₁₅(x) as `abbrev PolyQuotQ 8`; reduction `![-1,1,0,-1,1,-1,0,1]` (densest cyclotomic at degree 8); key constants ζ, √5, φ, 1/φ, ω₃=ζ⁵; theorems incl. ζ¹⁵=1, (√5)²=5, φ²=φ+1, ω₃³=1; first PolyQuotQ instance at degree 8 (**ALL PROVED by native_decide, zero sorry**) |
| QCyc15SqrtPhi | 111 | 5 | 0 | 5i | **Phase 5i Wave 4c-part3**: First non-cyclotomic number field in project — Q(ζ₁₅, √φ) = Q(ζ₁₅)[w]/(w²−φ), degree 16 over ℚ, via `PolyQuotOver QCyc15 2`; non-Galois (√φ escapes every cyclotomic field per Kronecker-Weber); enables SU(3)₂ Fibonacci F-symbols (**ALL PROVED by native_decide, zero sorry**) |
| PolyQuotOver | 220 | 7 | 0 | 5i | **Phase 5i Wave 4b.ext+4d**: Generic tower extension `PolyQuotOver K m` over arbitrary `[DecidableEq K]` base ring; `mulReduce2` (degree-2 specialization, eager materialization) is the recommended tower primitive; `mulReduceOver` (general m) retained with documented O(m^m) caveat; first non-trivial user is QCyc15SqrtPhi; Mathlib-upstream-ready (**ALL PROVED, zero sorry**) |
| SU3k2SMatrix | 229 | 14 | 0 | 5i | **Phase 5i Wave 4c-part2**: First rank-6 MTC modular data in any proof assistant; 9 S-matrix entry classes A–I (×15 scaling) as QCyc15 values, full 6×6 S-matrix, 6 T-matrix diagonal entries (4 distinct: ζ¹³, ζ², ζ⁸, ζ⁷); S=Sᵀ (native_decide over 36 entries), Z₃ simple-current identities, T¹⁵=1 for all 4 distinct values (**ALL PROVED, zero sorry**) |
| SU3k2FSymbols | 124 | 9 | 0 | 5i | **Phase 5i Wave 4c-part3**: First SU(3)₂ F-symbols in any proof assistant; Fibonacci 2×2 F-matrix over Q(ζ₁₅, √φ), `F=[[1/φ, 1/√φ], [1/√φ, −1/φ]]`; F²=I proved entry-by-entry (4 entries via native_decide); golden-ratio identity φ²=φ+1 in non-cyclotomic tower; full 120-entry catalog deferred (Ardonne-Slingerland data) (**ALL PROVED, zero sorry**) |
| InstantonZeroModes | 170 | 8 | 0 | 5s | **Phase 5s**: Machine-checked Dirac monopole (q=1) + vortex (n=2) zero-mode count = 2|qn| = 4 per flavor without invoking 4D index theorem; Cl(4) ≅ Cl(2)⊗̂Cl(2) Clifford decomposition + separation of variables + S² angular kernel (6×6 ℤ matrix native_decide); turns previously RED Csáki-Ovadia-Telem-Terning-Yankielowicz instanton mechanism GREEN (**ALL PROVED, zero sorry**) |
| FermiHubbardDimer | 2557 | 157 | 0 | 5t | **Phase 5t Wave 2 (final)**: Algebraic skeleton of Kiefer et al. (Nature 2026) doublon geometric SWAP gate; two-fermion Fermi-Hubbard dimer 3×3 singlet-sector Hamiltonian; chiral-protected dark state; T1 H₃ symmetric, T2 dark state in ker, T3 darkVec≠0, T4 Γ²=I, T5 {Γ,H₃}=0, T6 det H₃=−4Ut², T7 tr H₃=2U; triplet sector zero-eigenvector witnesses; first formally verified symmetry-protected (non-topological) two-qubit gate (**ALL PROVED, zero sorry**) |
| DiracFluidMetric | 212 | 12 | 0 | 5w | **Phase 5w Wave 2**: 3×3 Dirac-fluid acoustic metric for 2+1D conformal Dirac fluid (ε=2p); c_s = v_F/√2; block-diagonal for quasi-1D; horizon at v=c_s; Lorentzian signature; foundational geometric input for graphene Hawking pipeline (**ALL PROVED, zero sorry**) |
| DiracFluidSK | 175 | 9 | 0 | 5w | **Phase 5w Waves 5–7**: SK-EFT transport classification for 2+1D relativistic charged conformal Dirac fluid; conformal ζ=0; transport counting 2 conformal / 3 non-conformal; Lorenz-ratio positivity + monotonicity; KSS bound η/s ≥ ℏ/(4π); EFT perturbativity (**ALL PROVED, zero sorry**) |
| GrapheneHawking | 135 | 6 | 0 | 5w | **Phase 5w Wave 3**: Subluminal-dispersion Hawking predictions for graphene Dirac fluid; dispersive correction bound, T_eff positivity, EFT validity (D<1), subluminal robustness, dissipative negligibility (11 orders) — yields T_H ≈ 2.4 K with S_I detection in ~27 min (**ALL PROVED, zero sorry**) |
| GrapheneNoiseFormula | 180 | 8 | 0 | 5w | **Phase 5w Wave 10a**: Closed-form Hawking-induced excess current noise PSD `ΔS_I(ω) = 2ℏω σ_Q Γ(ω) n_H(ω)` derived from Keldysh FDT + Landauer–Büttiker for the bilayer-graphene de Laval nozzle (**ALL PROVED, zero sorry**) |
| QuasiOneDReduction | 314 | 12 | 0 | 5w | **Phase 5w Wave 10b–10c**: Realistic greybody bounds for graphene de Laval nozzle; T1 zero-frequency Γ₀ = 4c_R v/(c_R+v)² ∈ [0,1] with equality iff c_R=v; T2 surface-gravity correction ≤ (l_ee/W)²; T3 evanescent leakage ≤ (ω/ω_⊥)²·exp(−2πL/W); T4 Dean adiabaticity D<1 (norm_num); two PDE-gap hypotheses tracked as Props (**ALL PROVED, zero sorry**) |
| DiracFluidWKB | ~330 | 14 | 0 | 5w | **Phase 5w Wave 4**: Wave-4 integration capstone — binds graphene parameters (`GrapheneWKBParams`: vF, Γ_H, κ, W) into `WKBConnection.ExactWKBParams` via `c_s = v_F/√2` (5 sound-speed thms incl. substantive subluminal `c_s < v_F`); 1 substantive cross-bridge `noiseFloor_bounded_perturbative` (imports WKBConnection.noise_floor_bounded under perturbative-regime constraint Γ_H ≤ κ); transverse-mode quantization (Dirichlet `k_n = (n+1)π/W`, strict-monotone increasing channel cutoffs); **`dean_lowest_channel_above_four_omega_H`** norm-num falsifier showing Dean-geometry detection band [0, 4ω_H] is quasi-1D-safe; cross-bridge `channel_greybody_le_one` to QuasiOneDReduction; sum-over-channels spectrum non-negativity + uniform-greybody envelope (**ALL PROVED, zero sorry; 14 substantive thms**) |
| HiddenSectorClassification | 211 | 9 | 0 | 5x | **Phase 5x Wave 2**: ℤ₁₆ hidden-sector DM constraints; T1 N SM-singlet Weyl fermions contribute (N : ZMod 16); T2 three-generation SM without ν_R has anomaly 45 ≡ −3 mod 16; T3 minimal singlet count = 3; T10 bounded-≤32 solution set = {3, 19}; T11 ℤ₁₆ does not imply U(1)_X³ cancellation; T12 generation/anomaly independence (**ALL PROVED, zero sorry**) |
| HiddenSectorMixedCharge | 267 | 9 | 0 | 5x | **Phase 5x Wave 2b Track X**: Wan-Wang mixed-charge (C-1: 7×q=−2, 1×q=+6) hidden-sector formalization; X1 MixedChargeHiddenSector struct, X2 U(1)_X³ cubic mod 4, X3 U(1)_X×gravity² linear mod 4, X4 joint ℤ₁₆⊕ℤ₄ constraint, X5 C-1 satisfies U(1)_X conditions (decidable arithmetic), X6 mixed channel orthogonal to pure-singlet (**ALL PROVED, zero sorry; tracked H_C1_MixedChannelCancels Prop**) |
| CosmologicalConstant | 233 | 10 | 0 | 5x | **Phase 5x Wave 3**: ADW Λ + Volovik / Gibbons–Hawking double-temperature `T_dS = 2·T_GH` (T_dS = H/π exactly twice T_GH = H/(2π)); quartic Coleman-Weinberg critical-point identity V_min = −A²/(4B) for V(C) = −A·C²+B·C⁴; backbone of `V_eff(C₀) = −Λ⁴/(4e)` (**ALL PROVED, zero sorry; KMS / equilibrium / holographic content deferred to Phase 6**) |
| FangGuTorsionDM | 217 | 13 | 0 | 5x | **Phase 5x Wave 4**: Fang-Gu e-loop torsion DM kinematic obstruction; FG1 traceless ⇔ w=1/3; FG2 traceless ⇒ ¬dust; FG3 traceless Poisson source = 2ρ (doubled); FG4 dust Poisson source = ρ; FG5 `fg_cdm_obstruction` bundled obstruction; tree-level perfect-fluid algebraic identities for Fang-Gu (arXiv:2106.10242) (**ALL PROVED, zero sorry**) |
| FractonDarkMatter | 559 | 38 | 0 | 5x | **Phase 5x Wave 7**: Fracton DM viability — Phase13a `fracton_nogo_exemption` (Shen et al. 2022 doesn't apply to gapless / p-wave phases); Phase13c Arrhenius lifetime; Phase13d p-wave condensate sufficient condition; Sig1 σ_eff=0; Sig2 SM-singlet from YM incompat; Sig3 dust w=0; Sig4 attractive gravity; Sig5 WW bypass via Lorentz breaking; Sig6 z=4 subdiffusion preserved; ViableA/B BBN-window decidable witnesses (**ALL PROVED, zero sorry**) |
| SFDMMergerForecast | 499 | 38 | 0 | 5x | **Phase 5x Wave 5**: SFDM cluster-merger sonic-boom forecast (Paper 17 "money plot"); BK (m=0.6 eV, Λ=0.2 meV) fiducial sound-speed table; Rankine-Hugoniot density jump closed form γ=2; stacked √N S/N; 5 canonical mergers (Bullet, El Gordo, Pandora, A520, MACS J0025); 5 decidable S/N witnesses; smoking-gun step function (**ALL PROVED, zero sorry**) |
| DarkSectorSynthesis | 571 | 58 | 0 | 5x | **Phase 5x Wave 8**: Cross-connection theorems gluing Phase 5x Waves 2/2b/3/4/7 into single Paper 17 narrative; CC1 ℤ₁₆ × fracton compatible; CC2 emergent-gravity DM invisibility (log10-cap < −50 across all kinds); EoS distinctness (w = −1 vs 1/3 vs 0); two-torsion-channel independence; ℤ₁₆ × vestigial relic protection (tracked Prop hypothesis); empirical-hook ranking (merger > cusps > EP > DESI > direct) (**ALL PROVED, zero sorry**) |
| GibbsDuhemTheorem | ~335 | 16 | 0 | **5y** | **Phase 5y Wave 1**: `w_vac = −1` locked by Lorentz invariance for any single-scalar emergent-vacuum model; `rhoV`, `pV`, `wVac` defs; `GibbsDuhemEquilibrium` struct; main obstruction GD15 with bundled conclusion (`w=−1 ∧ DESI-miss ∧ ρ_V(q₀)=0 ∧ q≠q₀`) (**ALL PROVED, zero sorry**) |
| QTheoryNoGoTheorem | ~370 | 13 | 0 | **5y** | **Phase 5y Wave 2**: all 4 KV q-theory realizations (`fourForm`, `twoBrane`, `fermionicCrystal`, `unimodular`) collapse to same KVAnsatz; `mDeltaQSq = 1/(χ₀q₀²) ~ M_Pl²`; `massOfRealization` enum + invariance; `NaturalPlanckScale` + `qtheory_closure_no_go` bundled NO-GO (**ALL PROVED, zero sorry**) |
| DESIComparison | ~230 | 8 | 0 | **5y** | **Phase 5y Wave 3a**: DESI DR2 1σ + 3σ preferred regions encoded (`w₀ ∈ [−0.8,−0.66], w_a ∈ [−1.35,−0.75]`); CPL parameterization; Quintom-B predicate; σ-offset; `lambdaCDM ∉ DESI_1σ` proved (**ALL PROVED, zero sorry**) |
| DarkEnergyObstructionPrinciple | ~185 | 8 | 0 | **5y** | **Phase 5y Wave 3b**: four-factor orthogonality principle (Gibbs-Duhem ∩ c_s²≥0 ∩ T_c attractor ∩ MICROSCOPE); q-theory and vestigial-gravity models concretely instantiated as non-viable; orthogonality via concrete factor disagreement (**ALL PROVED, zero sorry**) |
| CondensedMatterAnalog | ~230 | 10 | 0 | **5y** | **Phase 5y Wave 4a**: Fernandes-Fu charge-4e GL template; HS-decoupled channel free energies; Jian-Huang-Yao temperature splitting; Fernandes-Orth-Schmalian vestigial-order classification (nematic/charge4e/density-wave with U(1)-breaking flags) (**ALL PROVED, zero sorry**) |
| VestigialMapping | ~175 | 8 | 0 | **5y** | **Phase 5y Wave 4b**: H4 §3 dictionary as formal bijection CMRow↔VGRow (12 entries); charge4e↦fourFermionQuartet, T↦deSitterTemp, T_4e↦vestigialTc load-bearing mappings; injectivity via round-trip lemmas (**ALL PROVED, zero sorry**) |
| VestigialEOS | ~400 | 21 | 0 | **5y** | **Phase 5y Wave 5**: H4 closed-form `w_vest(τ)=(1−τ²)/(5τ²−1)`, `c_s²=−(1−τ²)/(3−5τ²)`, CPL (w₀,w_a); `w_vest(0)=−1`, `c_s²(0)=−1/3<0` gradient instability; phantom-today on natural branch τ²∈(0,1/5); `h4_no_go_main` bundles 3 obstructions; `fine_tuning_log_lower_bound` for Λ₀-augmentation (VE18a) (**ALL PROVED, zero sorry**) |
| ClassificationTableDark | ~200 | 8 | 0 | **5y** | **Phase 5y Wave 7**: 6 Volovik-family mechanisms × 6 viability columns; `qTheory×4 → 2/4 factors`, `vestigial → 1/4`, `secondSoundGraviton → 0/4`; all DESI-no; all cap ≤ 2/4 orthogonality factors (**ALL PROVED, zero sorry**) |
| VestigialGravity (ext) | 365 | 25 (was 18, +7) | 0 | **5y W6** | Phase 5y Wave 6 extensions: Z4 symmetry group generators (Volovik arXiv:2406.00718), `sees_gravity_as_{boson,fermion}` predicates, `vestigial_wep_violation` (fermions no-couple, bosons couple → WEP fail), distinguishability from full-tetrad phase |
| VestigialSusceptibility (ext) | ~325 | 24 (was 16, +8) | 0 | **5y W6** | Phase 5y Wave 6 extensions: `KuboViscosity` struct, FDT noise non-negativity, `chi_RPA` closed form + stability/instability bounds, Kubo↔bulk-viscosity link to Wave 5 `ζ_vest` |
| TetradGapEquation (ext) | ~600 | 24 (was 20, +4) | 0 | **5y W6** | Phase 5y Wave 6 extensions: BCS-like `T_c_vest = Λ_UV·exp(−1/g̃_*)`, positivity, `T_c_vest < Λ_UV` suppression, **natural-scale obstruction** (UV-tied T_c cannot be Hubble-tied via `IsHubbleTiedTc` contradiction) |
| ScalarRungInterpretation | 421 | 35 | 0 | **5z W1** | **Phase 5z Wave 1 (Track A)**: First ADW-substrate ↔ Higgs bilinear scalar-rung interpretation; replaces 3 vacuous Props with 5 substantive ones incl. tracked-Prop bridge `H_ScalarChannelIsTetradBifurcationOutput`, falsifiability witness `not_isHiggsBilinearCandidate_of_vev_too_large`, custodial-symmetry algebraic identity `zMass_sq_minus_wMass_sq`; Stage 13 strengthening pass + adversarial review applied (**ALL PROVED, zero sorry**) |
| MajoranaRung | 526 | 23 | 0 | **5z W2/2a/2b** | **Phase 5z Wave 2 + 2a + 2b**: Majorana-rung interpretation of sterile-neutrino seesaw — Embedding III (Hybrid) per O.3 deep-research verdict; substrate-bridge tracked Prop `H_MR_FromADWSubstrate`; Z₁₆ singlet-branch bridge from existing `three_nu_R_cancel_three_gen` + `three_singlets_satisfy_hidden_sector`; **Wave 2b Section 3a** strengthens with `H_LeptonNumberViolated` + `H_MR_FromADWSubstrate_BCS_LNV` (Antusch-Kersten-Lindner-Ratz hep-ph/0211385) + `lepton_number_symmetry_obstructs_BCS_form` no-go (**ALL PROVED, zero sorry**) |
| NeutrinoMixing | 266 | 14 | 0 | **5z W2** | **Phase 5z Wave 2**: PMNS structure-note (parallel to HepLean's CKMMatrix idiom); 3×3 unitary `Matrix.unitaryGroup (Fin 3) ℂ`; tracked-Prop `H_PMNSAnglesFromSubstrate` substrate-overlap hypothesis (WAVE2-OPEN-2); refactored from earlier draft to align with deep-research O.3 + scope-discipline rules (**ALL PROVED, zero sorry**) |
| MajoranaRungDecoupling | 283 | 19 | 0 | **5z W2b** | **Phase 5z Wave 2b**: Decoupling-theorem bounds for Embedding I vs III; upgrades `WAVE2-OPEN-5` from comment-marker IR-equivalence to formal `DecouplingRegime` + `SubstrateData` + `H_DecouplingBoundDim6` + `H_DecouplingBoundDim5_LNV` + `Asymptotics.IsBigOWith` restatements (k=1 LNV / k=2 generic, `C ~ N_f/(16π²)` from SILH+Hill bilocal NJL); 170-module milestone (**ALL PROVED, zero sorry**) |
| LinearizedEFE | 644 | 36 | 0 | **6a W1** | **Phase 6a Track A Wave 1**: Linearized Einstein equations from the ADW microscopic theory. Sakharov-Adler `G_N^Sak = 12π/(N_f Λ²)`; ADW emergent `G_N^emerg = α_ADW · G_N^Sak`; correctness-push match locus + Planck anchor reduction; Vergeles structural Props (`H_VergelesPositivity`, `H_CriticalLimitCollapse`, `H_DeepGapReducesToAdler`). (**ALL PROVED, zero sorry**) |
| FLRWDynamics | 353 | 17 | 0 | **6a W4** | **Phase 6a Track A Wave 4**: Friedmann I/II + conservation + Bianchi consistency + ADW emergent-gravity bridge `hubbleSquared_ADW_pos` + Phase 5y DESI-DR2 cross-reference tracked hypothesis `H_DESICompatibility`. (**ALL PROVED, zero sorry**) |
| GravitationalWaves | 511 | 21 | 0 | **6a W2** | **Phase 6a Track B Wave 2** (strengthened 2026-04-25): GW propagation `c_GW = c · √χ_vest` from `VestigialSusceptibility`; GW170817 correctness-push biconditional + natural-range falsification (`Δc/c ∈ [-0.68, +2.16]` vs cap `3e-15`); tracked-hypothesis bundle `H_VestigialModeIsGraviton` with 4 falsifiers; SK-EFT dispersion `dispersion_within_ligo_iff` biconditional. (**ALL PROVED, zero sorry**) |
| BHEntropyMicroscopic | 674 | 23 | 0 | **6a W3** | **Phase 6a Track C Wave 3** (strengthened 2026-04-26 + adversarial-review followup 2026-04-26-0330; further restructured 2026-04-27 when `gaussianSaddleAsymptotic` axiom was retired via the new `LaplaceMethod` module): Bekenstein-Hawking `S = A/(4 G_N) − (3/2) log(A/(4 G_N))`; Kaul-Majumdar SU(2)_k closed form (Outcome-2 sub-corollary) + tracked-hypothesis bundle `H_HorizonBoundaryCondition` (Outcome-3) with 4 falsifiers (F1–F4) + 4 substantive corollaries (`H_HorizonBoundaryCondition_implies_nonabelian_envelope`, `abelian_MTC_falsifies_H_HorizonBoundaryCondition`, `sen_4d_quantitative_disagreement_bound`, `fibonacci_horizon_areaLawKappa_pos`); -3/2 = (-1/2 Gauss) + (-1 singlet) arithmetic decomposition; Sen 1205.0971 non-universality witness; Immirzi γ tuning encoded as structure field; bridge to Wave 1 G_N^emerg. **Project axioms 2 → 1** when Wave 7 retired `gaussianSaddleAsymptotic` via Mathlib's `integral_gaussian` rewrite path. New tracked-hypothesis predicate `H_VerlindeKMLiteralSumDerivation` documents future-work scope (literal SU(2)_k Verlinde sum + Hardy-Ramanujan asymptotic). (**ALL PROVED, zero sorry**) |
| BHThermodynamicsFourLaws | 806 | 20 | 0 | **6a W5** | **Phase 6a Track C Wave 5** (re-shipped 2026-04-26-2230 around Balbinot 2005 BEC-acoustic primary anchor; initial 2026-04-26-0830 ship retracted after Stage-9 surfaced a deep-research ³He-A vs BEC-acoustic conflation): BCH four laws of black-hole mechanics in two regimes (Schwarzschild / ADW-Extremality) separated by `M_c = (N_f · Λ_UV) / (12π · α_ADW)`. `T_H_acoustic_evolution(T_H0, τ_cool, t) = T_H0·exp(−t/τ_cool)` (Balbinot 2005 leading-order, mirrors `wkb/backreaction.py`) + `T_H_schwarzschild(M) = 1/(8π M)` (Hawking 1975), each anchored to monotonicity theorems. Tracked-hypothesis bundle `H_RegimePartition`, two correctness-push theorems (`regime_partition_criterion`, `four_laws_consistent_with_acoustic_regime`), four falsifier theorems (acoustic-decay-form, Schwarzschild-heating, third-law-form, χ_vest-dependence), Wave 1 + Wave 3 cross-bridges. JK 2002 / JV 1998 retained as explicit contrast cases per Balbinot's own contrast statement. **No new axioms.** (**ALL PROVED, zero sorry**) |
| LaplaceMethod | ~180 | 5 | 0 | **6a W7** | **Phase 6a Wave 7** (project-local fallback per roadmap §388 ahead of any Mathlib PR): `gaussian_full_integral` (Mathlib `integral_gaussian` rewrite for the `exp(-A x²/2)` saddle form); `exp_neg_sq_le_exp_neg_lin` (Gaussian-to-linear-exp tail comparison); `IsBoundedRemainderOoneOverA` predicate + `_intro` + `_refl` + `_trans` (Watson's-lemma bounded-remainder algebra). Consumer: `BHEntropyMicroscopic.gaussianSaddleAsymptotic` is now a theorem with `C = 1`; the prior axiom is removed from the dependency closure of every consumer. (**ALL PROVED, zero sorry**) |
| TetradFormalism | ~310 | 6 | 0 | **6f W6** | **Phase 6f Wave 6** (SHIPPED 2026-04-29 through Stages 1-9 + 12 + strengthening pass; post-closure 2026-04-29 audit cut +1 retroactive `torsionResidual_zero_iff` Iff.rfl on identity-function def — substantive torsion-free content remains in 6e.6 cross-bridges; Stages 10/11/13 deferred per user policy — Mathlib-PR-style infrastructure): 5 substantive theorems + 1 marker. Tetrad (vierbein) formulation of GR at the algebraic / point-wise level: §2 tetrad-induced metric `g_μν = η_ab e^a_μ e^b_ν` with substantive `tetradInducedMetric_symm` (proved via η-diagonal substitution); §3 Minkowski tetrad `e^a_μ = δ^a_μ` with named-API `minkowskiTetrad_induces_minkowski_metric`; §4 tetrad determinant `minkowskiTetrad_det_eq_one`; §6 substantive cross-bridges to Phase 6e.6 EinsteinCartanExtension (`tetrad_metric_equivalence_at_alpha_one` consuming `ecResidual_at_alpha_one` + `tetrad_levi_civita_iff_alpha_unity` specializing `ecResidual_eq_zero_iff_alpha_unity`). Cartan structure equations (T^a = de^a + ω ∧ e^b) deferred until differential-form machinery lands. **Closes Phase 6f.** **First formalization in any proof assistant** (per audit §3E + 6f.1-6f.5 first-formalization context) of the tetrad formalism with metric-equivalence biconditional + Einstein-Cartan torsion-amplitude cross-bridge. **Strengthening pass: 0 first-pass cuts + 1 post-closure cut.** (**ALL PROVED, zero sorry; cross-layer pipeline COMPLETE**) |
| ADMFormalism | ~510 | 11 | 0 | **6f W5** | **Phase 6f Wave 5** (SHIPPED 2026-04-29 through Stages 1-9 + 12 + strengthening pass; post-closure 2026-04-29 audit cut +1 retroactive `schwarzschild_adm_mass_pos_iff` Iff.rfl on identity-function def — substantive M-positivity content remains in `_eq_half_horizon_radius` cross-bridge to 6f.4; Stages 10/11/13 deferred per user policy): 10 substantive theorems + 1 marker. ADM 3+1 decomposition at the algebraic level: ADM 4-metric block decomposition (g_00 = -N² + γ_ij N^i N^j, g_0i = γ_ij N^j); Hamiltonian + momentum constraint algebraic predicates; vacuum + moment-of-time-symmetry + Yamabe-form biconditionals; Minkowski / dS flat-slicing / Schwarzschild ADM data with constraint-vanishing identities. **Substantive cross-bridge to 6f.4:** `schwarzschild_adm_mass_eq_half_horizon_radius` consuming `schwarzschildHorizonRadius` makes the M_ADM = r_H/2 identity explicit; `deSitter_flat_slicing_hamiltonian_iff` recovers Λ=3H² at the ADM level. `^(3)R` and `D_j` from γ deferred until ∂_μ machinery lands; constraint inputs externally supplied at point-wise level. **Strengthening pass: 4 retroactive cuts** (rfl-on-constant-zero plumbing + simp-trivial unconsumed K=0 specializations + rfl-rename `schwarzschild_adm_mass_eq_M` replaced by substantive cross-bridge `_eq_half_horizon_radius`). **First formalization in any proof assistant** of ADM 3+1 with Hamiltonian + momentum constraint biconditionals + cross-bridges to canonical exact-solutions catalog. (**ALL PROVED, zero sorry**) |
| ExactSolutions | ~510 | 17 | 0 | **6f W4** | **Phase 6f Wave 4** (SHIPPED 2026-04-29 through Stages 1-9 + 12 + strengthening pass; post-closure 2026-04-29 audit cut +1 retroactive `deSitter_Ricci_eq` rfl-rename; Stages 10/11/13 deferred per user policy — Mathlib-PR-style infrastructure with no in-project paper deliverable in `PAPER_STRATEGY.md`): 16 substantive theorems + 1 marker. Catalogue of canonical exact solutions of the Einstein field equations as named consumers of the Phase 6f.1+6f.2+6f.3 algebraic infrastructure plus BH thermodynamics cross-bridges to Phase 6a Wave 5. **Minkowski (K=0, Λ=0):** `minkowski_lambda_zero_iff_K_zero` (uniqueness biconditional). **de Sitter (K>0):** `_scalar_eq` / `_einsteinTensor_eq` / `_lambda_vacuum_iff` / `_lambda_eq_three_H_squared` / `_T_H_eq_kappa_over_2pi` (5 thms; `deSitter_Ricci_eq` was a pure rfl-rename of 6f.1's `constantSectional_minkowski_Ricci_eq` and was CUT in the post-closure strengthening with named defs `deSitterHubbleRadius` / `deSitterKappa` / `deSitterHawkingTemp`; the last is Gibbons-Hawking 1977 dS Hawking-Unruh `T_H = κ/(2π)`). **Anti-de Sitter (K<0):** `ads_lambda_eq_neg_three_over_ell_sq` (1 thm; AdS-radius anchor `Λ = -3/ℓ²`). **Schwarzschild (Kerr-Schild form):** `schwarzschild_horizon_iff` (biconditional `φ=1 ↔ r=2M`) + 3 g_tt signature theorems (timelike outside / null at horizon / spacelike inside) + 5 BH thermo cross-bridges (`_kappa_times_4M`, `_T_H_times_M`, `_T_H_eq_kappa_over_2pi`, `_area_eq_16pi_M_sq`, `_S_BH_eq_4pi_M_sq`) consuming named defs `schwarzschildHorizonRadius` / `schwarzschildKappa` / `schwarzschildHawkingTemp` / `schwarzschildArea` / `schwarzschildBHEntropy`. The vacuum-Ricci verification `Ric(g_Schw) = 0` outside r=2M is **deferred** (requires ∂_μ machinery); vacuous tracked Prop pattern was REJECTED at first pass per 6f.2 lesson. **First formalization in any proof assistant** of the catalog with chain implications + Λ biconditional + Hawking-Unruh quantitative cross-bridges (per audit §3E + 6f.1+6f.2+6f.3 first-formalization context). **Strengthening pass: 1 retroactive cut** (`schwarzschild_kappa_eq` rfl rename caught by ruthless audit). The named-quantity definition pattern (5 Schwarzschild + 3 dS noncomputable defs) made most P3-trivial content into substantive named-API. (**ALL PROVED, zero sorry; cross-layer pipeline COMPLETE**) |
| EnergyConditions | 542 | 9 | 0 | **6f W3** | **Phase 6f Wave 3** (FULLY SHIPPED 2026-04-29 — Lean module shipped 2026-04-27 through Stages 1, 3, 5, 12; cross-layer Python BACKFILL CLOSED 2026-04-29 through Stages 2, 6, 7, 8, 12): 8 substantive theorems + 1 marker. WEC/NEC/DEC/SEC predicates on abstract `StressEnergyTensor : Vec4 → Vec4 → ℝ` over `Vec4 = Fin 4 → ℝ`; signature `−+++` with explicit time-direction parameter; `IsNull` / `IsTimelike` / `IsFutureDirectedTimelike` predicates with load-bearing non-zero / sign hypotheses. Three chain implications (`DEC_implies_WEC`, `WEC_implies_NEC_under_continuity`, `DEC_implies_NEC_under_continuity`) and five counterexample-witness theorems (`cosmologicalLambda_WEC` / `_NEC` / `_violates_SEC`; `ghostScalar_violates_NEC`; `stiff_fluid_violates_DEC`). Per the Phase 6f deep-research audit §3E: **first formalization of these predicates with chain implications + explicit counterexample witnesses across all surveyed proof assistants** (Lean / Coq / Isabelle/AFP / HOL Light / HOL4 / Mizar / Agda). Lorentzian-manifold version deferred to Phase 6f.4 once Mathlib Lorentzian-metric infrastructure lands. **Cross-layer Python pipeline (backfill 2026-04-29):** 11 helpers in `formulas.py` (`apply_bilinear` + 3 predicate helpers `is_null_vec`/`is_timelike`/`is_future_directed_timelike` + 4 condition checks `nec_check`/`wec_check`/`dec_check`/`sec_check` + 3 named tensor witnesses `cosmological_lambda_stress_energy`/`ghost_scalar_stress_energy`/`perfect_fluid_stress_energy` + 1 trace helper `perfect_fluid_trace_minkowski`); `tests/test_energy_conditions.py` (38 pytest cases / 7 test classes — TestPredicateBasics / TestCosmologicalLambdaWitness / TestGhostScalarWitness / TestStiffFluidWitness / TestChainImplications / TestPerfectFluidEnergyConditionRegions / TestAntiPatternAudit / TestPhase6f1CrossBridge — all PASS in 0.07s); figure `fig_energy_conditions_perfect_fluid_regions` (4-panel (ρ, p) heatmap; ★ cos-Λ at (1,-1) sits in NEC/WEC/DEC blue + SEC orange; ◆ stiff-fluid at (1,2) sits in NEC/WEC/SEC blue + DEC orange — visually verifies all 5 named counterexample-witness theorems). Lean module summary docstring corrected from stale "7 substantive theorems" to actual "8 + 1 marker" + Wave-3 backfill cross-reference appended. **LIFT bridge to 6f.1/6f.2's matrix carrier still DEFERRED** (judgment call: defer until 6f.4 needs it). 6f.1 + 6f.2 set the precedent for full cross-layer ship even on Mathlib-PR-style infrastructure; this backfill restores 6f.3 to that pattern. (**ALL PROVED, zero sorry; cross-layer pipeline COMPLETE**) |
| Curvature | ~600 | 16 | 0 | **6f W1** | **Phase 6f Wave 1** (SHIPPED 2026-04-29 through Stages 1-9 + 12 + strengthening pass; Stages 10/11/13 deferred per user policy — Mathlib-PR infrastructure with no in-project paper deliverable in `PAPER_STRATEGY.md`): coordinate-based algebraic Riemann/Ricci/scalar curvature: `RiemannTensor : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ` (read as `R^ρ_{σμν}`); `MetricMatrix` matrix-form metric; `lowerFirstIndex` / `ricciOf` / `scalarOf` operations. Three algebraic predicates: `AntisymLastTwo` (P3-trivial-flagged), `FirstBianchi` (load-bearing under torsion-free), `AntisymPair12` (load-bearing under metric-compatibility on the lowered tensor). Wave headline `pair_symmetry_lowered` derives `R_{ρσμν} = R_{μνρσ}` via Wald §3.2 four-Bianchi-sum derivation; corollary `ricci_symmetric_under_riemann_pair_symmetry`. Quantitative bounds: `constantSectional_Ricci_eq` ships `Ric = 3K · g` with the dimension-(n-1) = 3 factor explicit in 4D; `constantSectional_diag_trace_eq` ships `R_trace = 12K` (n(n-1) = 12). Witness: `constantSectionalRiemann K g` non-trivial witness for de Sitter / AdS / sphere / hyperbolic constant-K spaces. Falsifier `nonBianchiTensor_violates_FirstBianchi` confirms FirstBianchi is non-vacuous. Cross-bridges `linearizedEFE_η_metricSymmetric` (calls `LinearizedEFE.η_symm` directly — audit P6 pattern), `constantSectional_minkowski_AntisymPair12` and `constantSectional_minkowski_Ricci_eq` (concrete Minkowski-background instantiations). Built under user's "build-locally" policy; coordinate-based carrier matching the Phase 6f.3 EnergyConditions precedent for our project; index-free Mathlib-PR-shaped formulation deferred until Bonn's `CovariantDerivative` API lands. **Strengthening-pass cuts (5 retroactive)**: 4 zeroRiemann_* trivial-witness theorems + unused `sumFin4_kron_eq` helper; cuts captured in module summary marker docstring. **First formalization in any proof assistant** (per audit §3E) of algebraic Riemann predicates with chain implications + explicit constant-K witness + cross-module Minkowski bridge. (**ALL PROVED, zero sorry**) |
| EinsteinTensor | ~410 | 10 | 0 | **6f W2** | **Phase 6f Wave 2** (SHIPPED 2026-04-29 through Stages 1-9 + 12 + strengthening pass; Stages 10/11/13 deferred per user policy — Mathlib-PR infrastructure with no in-project paper deliverable in `PAPER_STRATEGY.md`): coordinate-based algebraic Einstein tensor `G_{μν} := Ric_{μν} − (1/2) R g_{μν}` (`EinsteinTensorType : Fin 4 → Fin 4 → ℝ` carrier matching 6f.1's `RicciTensor` shape). 9 substantive theorems + 1 marker. Symmetry `einsteinTensor_symm` (Ric+metric symmetry both load-bearing). Quantitative dimension-4 trace identity `einsteinTensor_trace_eq_neg_scalar` (`G^μ_μ = -R` via `n − 2 = 2` cancellation under `(g_inv : g) = 4` hypothesis). Constant-K wave-headline cross-bridge `constantSectional_einsteinTensor_eq` ships `G_{μν} = -3K · g_{μν}` consuming 6f.1's `constantSectional_Ricci_eq` and the 4D `constantSectional_scalarOf_eq` (`R = 12K`). Vacuum characterization biconditional `einsteinTensor_zero_iff_ricci_zero` (forward uses trace identity to extract `R = 0`; backward uses `scalarOf_eq_of_pointwise` linearity helper). De Sitter Λ-vacuum cross-bridge `constantSectional_lambda_vacuum_iff` (`G + Λg = 0 ↔ Λ = 3K` with `g μ₀ ν₀ ≠ 0` non-degeneracy; algebraic level cross-bridge to Phase 6c W1 Zhitnitsky-DE program). Minkowski self-inverse contraction `minkowski_dim_contraction = 4` (concrete witness for the 4D dimension hypothesis on `LinearizedEFE.η`). P3-flagged plumbing kept as named API: `einsteinTensor_scalar_linearity` (algebraic linearity of `scalarOf` over the Einstein-tensor decomposition) + `scalarOf_eq_of_pointwise` (functional-extensionality helper, used twice). **Second Bianchi `∇^μ G_{μν} = 0` deferred** to a future wave once Bonn's `CovariantDerivative` API lands (option (a) tracked-Prop with trivial constant-K discharge REJECTED per 6f.1's strengthening lesson — would absorb a retroactive cut). **Strengthening pass: 0 retroactive cuts** (back to 6e.5/6b.2 best). The 6f.1 carry-forward question (*"is the witness-existence statement informative beyond the predicate definition?"*) prevented zero-witness-trivial-plumbing in the first place — used K=0 in pytest exclusively, no `zeroEinstein_*` theorems. **First formalization in any proof assistant** (per audit §3E + Wave 1 first-formalization context) of the algebraic Einstein tensor with quantitative trace identity + constant-K specialization + de Sitter-Λ algebraic cross-bridge. (**ALL PROVED, zero sorry**) |
| BBN | 431 | 15 | 0 | **6b W1** | **Phase 6b Wave 1** (preemptive-strengthening discipline applied at first-pass; multi-pass strengthening review 2026-04-27-1700 caught 5 retroactive P3/P5 patterns the discipline missed): five Phase 5x DM candidates classified via `H_BBN_Conformance` 3-field structural Prop — Z16Topological_T0 + Z16Mixed_C1 + FractonPWave (BBN-conformant via W8 collective-invisibility at `σ_DD ≤ 1e-50`); Z16Singlet_S0 + FGTorsion (BBN-violators conditional on thermalization at T_BBN, both via `ΔN_eff > 0.34` Planck 2σ slack). Structural punchline `bbn_violators_share_n_eff_failure_mode`: BBN failure surface is N_eff-mediated only. Cross-bridges `decoupled_via_w8_collective_invisibility_implies_bbn_safe` (calls `DarkSectorSynthesis.emergent_gravity_dm_invisible_collective`). (**ALL PROVED, zero sorry**) |
| StrongCPTopologicalDE | 262 | 8 | 0 | **6c W1** | **Phase 6c Wave 1** (multi-pass-strengthened; further tightened 2026-04-28-1130 — `H_BothActiveGivesInconsistency` threshold tightened from `> 1e-10` to `> zhitnitskyDE_eV4 0.1` so `h_qtheory_pos` is genuinely load-bearing; `zhitnitsky_DE_far_below_planck` upper bound tightened `1e10 → 1e-8` to certify ≥ 120 orders below `M_P^4` matching prose): Van Waerbeke-Zhitnitsky 2025 (arXiv:2506.14182) topological dark-energy mechanism as the strong-CP ↔ cosmological-Λ bridge. `ThetaVacuum` structure with load-bearing `|θ| ≤ 1e-9` (Pendlebury 2015 neutron-EDM) + `cpSymmetricVacuum` witness + `theta_planck_natural_violates_edm_bound` falsifier. Zhitnitsky prediction `ρ_DE = Λ_QCD^6 / M_P^2 ≈ 6.71e-9 eV⁴` at PDG `Λ_QCD = 0.1 GeV` (NO free parameters; ratio ≈ 240×). `IsAnomalyMatchingCompatible` 3-conjunct tracked Prop calling `Z16AnomalyComputation.sm_anomaly_with_nu_R` upstream. Correctness-push `combined_zhitnitsky_qtheory_exceeds_observation` forces project commitment to ONE DE mechanism. (**ALL PROVED, zero sorry**) |
| EquivalencePrinciple | 555 | 25 | 0 | **6c W3** | **Phase 6c Wave 3** (strengthened 2026-04-27-1555: 12-thm strengthening pass closing 3 audit findings — bundle redundancy P2, missing quantitative content, phantom W4 reference P6; further strengthened 2026-04-28-1130 — removed P5 self-equality tautology `step_target_can_test_vestigial_relics : 1.0e-18 ≤ 1.0e-18 := le_refl _` and decorative `module_summary_marker`, substantive content survives via `vestigial_relics_below_microscope_bound : 1e-18 < 1e-15`). Three EP levels (`WEP`, `EEP`, `SEP`) as inductive type with numerical-order projection. Six Phase 5x DM-related mechanisms classified: vestigialDifferentialCoupling + vestigialReliscSTEPClass violate WEP; fangGuTorsionTrace / fractonSubdiffusion / sfdmThomasFermi / hiddenSectorZ16Singlet satisfy WEP/EEP/SEP. Structural punchline `ep_violation_is_vestigial_only`. Cross-bridges: `vestigial_microscope_violation_consistent` (links to `ClassificationTableDark.MicroscopeStatus.violated`); `fangGu_failure_mode_is_kinematic_not_ep` imports `FangGuTorsionDM` and calls `fg_cdm_obstruction`. `violatesAt_mono` structural lemma + 6 single-claim violationLevel theorems + 3 quantitative `norm_num` comparisons. (**ALL PROVED, zero sorry**) |
| QECHolographyBridge | 380 | 10 | 0 | **6c W4** | **Phase 6c Wave 4** (multi-pass-strengthened; further cross-wave-strengthened 2026-04-28-0030 — removed `scramblingTimeBound_pos_iff_nontrivial` + `codeDistance_pos_iff_non_abelian` 2-line API specializations of `Real.log_pos_iff`; biconditional content moved into the W4 correctness-push body via `have h_iff`, downstream consumers rerouted to call `correctness_push.1` directly): Hayden-Preskill 2007 information-recovery protocol on the W3 `HorizonMTCBC` substrate. `HPCode` extends W3 horizon with a chosen encoding anyon. Two structural observables: `codeDistance := log d_max` (= W3's `areaLawKappa`) + `scramblingTimeBound := log D² = log Σ d_a²`. Named correctness-push `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class` ships as 2-conjunct (biconditional + forward implication). `recovery_at_scrambling_bound`. Substantive cross-bridge `horizon_BC_implies_HP_admissible` consumes W3 `H_HorizonBoundaryCondition` instance. Concrete witnesses: `fibonacci_HPCode_codeDistance_lt_log_two` quantitative bound (φ < 2 ⇔ √5 < 3 ⇔ 5 < 9). Trivial-abelian falsifier `trivialAbelian_violates_admissibility`. (**ALL PROVED, zero sorry**) |
| RTCasiniHuertaBounds | 255 | 7 | 0 | **6c W5** | **Phase 6c Wave 5** (multi-pass-strengthened; further cross-wave-strengthened 2026-04-28-0030 — `rt_classical_inconsistent_with_kaul_majumdar` was logically the contrapositive of `rt_eq_kaulMajumdar_iff_trivial_reduced_area.→` (P2 redundancy); REMOVED, downstream `rt_falsified_by_kaul_majumdar` rerouted through the biconditional): Ryu-Takayanagi 2006 area law and Casini-Huerta 2009 log bound as **external-hypothesis tracked Props** (the bulk holographic dual is not constructed in this project) and their structural inconsistency with the Phase 6a W3 Kaul-Majumdar microscopic entropy. `H_RT_Formula_Valid` forces `S_BH = A/(4 G_N)` (no log corrections); `H_CasiniHuerta_Bound_Valid` enforces `S_ent(L) ≤ (c/3) log(L/UV)`. Quantitative anchor `rt_kaulMajumdar_gap_at_reduced_area_two`: at canonical reduced area `A/(4 G_N) = 2`, the universality-failure gap = `(3/2) log 2 ≈ 1.040` exactly. Knife-edge biconditional `rt_eq_kaulMajumdar_iff_trivial_reduced_area`. Substantive cross-bridge `rt_falsified_by_kaul_majumdar`. Concrete H_CH witness `H_CasiniHuerta_Bound_Valid_witness_saturated`. Falsifier `kaulMajumdar_not_H_RT`. (**ALL PROVED, zero sorry**) |
| CenterSymmetryConfinement | 432 | 18 | 0 | **6d W1** | **Phase 6d Wave 1** (DOUBLE-strengthened 2026-04-27-1845 — 6 retroactive theorems across two reviews; further strengthened 2026-04-28-1130 — removed redundant `ising_nu_above_0_6` + `potts_nu_below_0_6` threshold pair, load-bearing comparison `ising_nu_gt_potts_nu` survives, threshold-pair was P3 against an arbitrary 0.6): Confinement formalized as **ℤ_N 1-form center-symmetry unbreaking**. `CenterZN` structure with `N ≥ 2`; `centerPhase Z := exp(2πi/N)`; `centerPhase_pow_N`, `centerPhase_norm_one`, `centerPhase_Z2_eq_neg_one` (concrete SU(2): ζ_2 = −1 via `Complex.exp_pi_mul_I`). Polyakov loop = ℂ; `Confining P := P = 0`; `confining_iff_magnitude_zero`. Svetitsky-Yaffe map: SU(2) → Ising, SU(3) → 3-state Potts; `ising_nu_gt_potts_nu` direct comparison. KSS bound 1/(4π): `KSS_bound_positive` + quantitative bracket `[0.07, 0.08]`. Walker-Wang transport correctness-push (HPC-gated): `H_WalkerWangTransportNearKSS` 2-conjunct tracked Prop + concrete numerical falsifiers. Cross-bridges: `higher_form_discrete_iff_non_abelian` genuine biconditional, `su3k1_fusion_card_matches_z3_order` calls `SKEFTHawking.su3k1_object_count` from `SU3kFusion.lean`. (**ALL PROVED, zero sorry**) |
| ChiralSSB_QCD | 310 | 10 | 0 | **6d W2** | **Phase 6d Wave 2** (multi-pass-strengthened 2026-04-27-1930; 4 retroactive across three passes): WetterichNJL scalar channel = quark condensate `⟨q̄q⟩` encoded as `QuarkCondensate` structure with load-bearing `sigma_neg` invariant; FLAG-2021 lattice witness (−0.0227 GeV³). GMOR relation `m_π² · f_π² = −2 m_q · ⟨q̄q⟩` with literature-anchored numerical verification `gmor_pdg_match` shows `|LHS − RHS| < 1e-4 GeV⁴` at PDG/FLAG central values (actual agreement ~4e-8, ~1 part in 10⁴). Chiral-unbroken-phase-violates-GMOR contrapositive `chiral_unbroken_violates_gmor` parametric over raw σ. Tetrad-VEV/quark-condensate naturalness correctness-push `H_TetradQuarkScalesNatural` 3-conjunct tracked Prop + unit-ratio existence witness + 2 order-of-magnitude falsifiers. Substantive cross-bridge `njl_scalar_bounded_consistent_with_chiral_broken` consumes `WetterichNJL.njl_scalar_upper_bound`. (**ALL PROVED, zero sorry**) |
| CFLChiralLagrangian | 317 | 12 | 0 | **6d W3** | **Phase 6d Wave 3 — Phase 6d CLOSED** (multi-pass-strengthened; 1 retroactive). THE Phase 6d correctness-push anchor delivered in the AGREEMENT branch: independent derivations (bare-gauge QCD center via W1's `CenterZN.Z3` vs. emergent CFL diquark-sector one-form symmetry via Hirono-Tanizaki) yield the SAME generator ω = exp(2πi/3). Load-bearing theorem `CFL_emergent_Z3_matches_QCD_center_Z3`. Cross-module identification consumed by `emergentZ3_pow_3` (calls W1's `centerPhase_pow_N`) + `emergentZ3_norm_one` (calls W1's `centerPhase_norm_one`) + `emergentZ3_sum_cube_roots` (`1 + ω + ω² = 0` distinguishing ℤ_3 from ℤ_2). CFL chiral Lagrangian skeleton: `cflKineticTerm_nonneg`, `cflMassTerm_chiral_limit`, `cflMassTerm_pos_in_cfl_phase`. Hirono-Tanizaki topological-order beyond Landau-Ginzburg: `H_TopologicalOrderBeyondLG` 2-conjunct tracked Prop + witness + 2 falsifiers. Cross-bridge `cfl_phase_with_gmor_dual_broken` consumes BOTH W2's `chiral_unbroken_violates_gmor` AND W3's `isCFLPhase_iff_magnitude_pos`. (**ALL PROVED, zero sorry**) |
| HeatKernelExpansion | 351 | 19 | 0 | **6e W1** | **Phase 6e Wave 1** (preemptive-strengthening discipline applied at first-pass; 2 retroactive — deleted unused `fourPiSq_mul_inv` identity wrapper, restructured `dirac_heat_kernel_yields_G_N_sakharov` defining-the-conclusion P5 into substantive `DiracHeatKernelAsymptotic.a2_eq_closed_form` consuming `a2_R_value`, replaced `G_N_from_a2_at_GUT_anchor` rfl-tautology with `G_N_from_a2_at_GUT_inverse` exposing `one_div_div`): Seeley-DeWitt heat-kernel expansion of the Dirac fermion determinant. Closed-form Christensen-Duff coefficients `a_0(N_f) = 4 N_f / (4π)²`, `a_2(N_f, R) = -(N_f/12)·R/(4π)²`, `a_4` triple at rationals `(-5,+7,-12)/(12·180)` (Vassilevich Phys. Rep. 388 Eq. 4.37–4.42). Tracked-hypothesis `DiracHeatKernelAsymptotic` structure (PDE-level asymptotic existence per Vassilevich Theorem 4.1 — Mathlib spin-bundle infrastructure not yet available); structure invariants `a0_value`/`a2_R_value` force consumers to commit to textbook values. **Decision Gate E.2 anchor** `G_N_from_a2_eq_G_N_sakharov` substantive cross-bridge (proof body invokes `LinearizedEFE.G_N_sakharov` by name) — drift-protection for heat-kernel ↔ 6a.1 reference. **Correctness-push biconditional `a2_matches_GNemerg_iff_alpha_ADW_unity`** uses `mul_right_cancel₀` against `LinearizedEFE.G_N_sakharov_pos` (forward) and `LinearizedEFE.G_N_emerg_at_alpha_one` (reverse). Quantitative anchors `G_N_from_a2_at_GUT_inverse` + `G_N_from_a2_inverse_at_GUT_below_planck_squared` (norm_num + `Real.pi_gt_three`). Gauss-Bonnet local-algebra `a4_gauss_bonnet_combination = -N_f/(48 (4π)²)` via `ring`. (**ALL PROVED, zero sorry**) |
| HigherCurvatureStructure | 354 | 11 | 0 | **6e W2** | **Phase 6e Wave 2** (preemptive-strengthening discipline applied at first-pass; 1 retroactive — cut `gaussBonnet4D_vacuum_eq_riemann_sq` trivial-after-unfold P3 with no downstream consumer): Wave 1 a_4 Christensen-Duff coefficients re-expressed in Stelle's `{R², C², 𝒢}` basis with closed-form sign-definite Stelle coefficients `(α, β, γ) = (-N_f/324, -41 N_f/4320, +17 N_f/4320) / (4π)²` solved from a 3×3 linear system. Definitions `gaussBonnet4D R Ricci Riem := R - 4 Ricci + Riem` (Lovelock 1971 topological in 4D), `weylSquared4D := Riem - 2 Ricci + R/3` (Stelle 1977 trace-free). **Conformal-flatness biconditional `weylSquared4D_eq_zero_iff_conformally_flat`**: C² = 0 ↔ Riem = 2 Ricci - R/3. **Algebraic engine `gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination`**: 𝒢 - C² = (2/3) R - 2 Ricci. **Sign-definite `a4_alpha_neg`/`a4_beta_neg`/`a4_gamma_pos`** for N_f > 0 (γ > 0 = chiral-anomaly-positive topological sign). **Helper bounds `fourPiSq_gt_one`, `fourPiSqInv_lt_one`** from `Real.pi_gt_three` + `nlinarith`. **MAIN cross-bridge identity `a4_density_eq_a4_density_in_RC2GB_basis`**: substantive cross-bridge to Wave 1 — proof body unfolds Wave 1's `a4_R_sq_coef`/`a4_Ricci_sq_coef`/`a4_Riemann_sq_coef` directly (P6 drift-protection per `feedback_python_lean_refs_drift.md`), closes by `ring`. Observational ceilings as `def`s `hc_bound_LIGO/SRG/pulsar/cassini` (Calmet-Capozziello-Pryer 2019; Berti et al 2015). **CORRECTNESS-PUSH `higher_curvature_below_pulsar_bound`**: at 0 < N_f ≤ 100, all 3 a_4 coef abs values strictly below `hc_bound_pulsar = 10^59` (Hulse-Taylor binary pulsar, tightest ceiling). 3-conjunct bundle is *not* P2-redundant (different coefs, different `abs_neg` vs `abs_of_pos` branches). **Falsifier `higher_curvature_predictions_strictly_positive`**: predictions strictly non-zero (rules out trivial-vanishing reading). **Tracked Prop predicate `H_HigherCurvatureWithinObservationalBounds B`** parameterised by upper bound; pulsar-bound witness theorem `H_HigherCurvatureWithinObservationalBounds_pulsar_witness` follows from correctness-push. (**ALL PROVED, zero sorry**) |
| RTReplicaTrickOnMTC | 544 | 17 | 0 | **6j W1** | **Phase 6j Wave 1 — Lewkowycz-Maldacena replica trick on horizon-MTC substrate** (SHIPPED 2026-04-30 through Stages 1-5; Stages 6-13 deferred to Phase 6j paper-bundle assembly). Critical dossier finding (verdict B): bare-LM on pure-CS substrate produces ONLY the Kitaev-Preskill `topologicalEntanglementEntropy := -(1/2) log H.globalDimSq` constant (NO area term, NO log A correction). Module ships: §1 `topologicalEntanglementEntropy` def + 3 sign-analysis theorems (`one_le_globalDimSq`, `_nonpos`, `_neg_iff` biconditional via `Real.log_pos_iff`); §2 concrete witnesses `toricCodeMTC` (4 anyons d=1, D²=4, topEnt = -log 2), `isingMTC_horizonBC` (3 anyons [1,√2,1], D²=4, topEnt = -log 2 via `Real.sq_sqrt`), Fibonacci numerical anchor on existing `fibonacciHorizonBC` (D²=(5+√5)/2 via `goldenRatio_sq` + `field_simp`/`ring`); §3 Dong-Liu-Wen ambiguity `topologicalEntanglementEntropy_eq_of_globalDimSq_eq` (abstract) + `rt_entropy_toric_eq_ising` (concrete consumer per Pattern #8); §4 substantive `IsolatedHorizonHypotheses` Prop bundle (LQG level-area + SU(2)-singlet-projection + microcanonical-ensemble inputs); §5 conditional Kaul-Majumdar derivation `rt_log_coefficient_under_IH` (extracts -3/2 via `rw + ring`) + `rt_entropy_at_canonical_area_under_IH`; §6 cross-bridge `isolatedHorizon_violates_H_RT` promotes Phase 6c.5 falsifier `kaulMajumdar_not_H_RT` from concrete-instance to universal-under-IH (uses both `h_rt.rt_proportional` + `hIH.takes_kaulMajumdar_form` + `Real.log_pos`); §7 negative result `topologicalEntanglementEntropy_no_log_A_form` (two-evaluation argument at A=4G_N + A=4G_N·e); §8 witness `kaulMajumdarS_satisfies_IH` cross-module bridge to Phase 6a.3 + `kaulMajumdarS_violates_H_RT_via_IH` compositional sanity check. **First formalization in any proof assistant** of Kitaev-Preskill topological EE on abstract MTC carrier + LM "no log A on pure-CS substrate" structural negative result + DLW vacuum-sector ambiguity + conditional Kaul-Majumdar -3/2 promotion under explicit isolated-horizon hypotheses. **Strengthening: 1 retroactive cross-bridge restoration** (`rt_entropy_toric_eq_ising` rewritten to consume `topologicalEntanglementEntropy_eq_of_globalDimSq_eq` per Pattern #8 four-clause heuristic). 17 substantive thms / 4 noncomputable defs / 1 structure / 0 sorry / 0 new axioms / library 8491 PASS. (**ALL PROVED, zero sorry**) |
| CasiniHuertaModularHamiltonianMTC | 427 | 16 | 0 | **6j W2** | **Phase 6j Wave 2 — Casini-Huerta modular Hamiltonian on horizon-MTC substrate** (SHIPPED 2026-04-30 Stages 1-5). **Critical dossier verdict §6**: original "saturates on abelian / strict on non-abelian" framing is wrong — leading `(c_LR/3) log(L/ε)` log coefficient saturates on ANY unitary MTC (Holzhey-Larsen-Wilczek universal); substrate-dependence in subleading `−γ = −log D` which is `log 2` for BOTH toric (abelian) AND Ising (non-abelian) per DLW recurrence at γ-level. Module ships: §1 `topologicalEntropy_logD := (1/2) log H.globalDimSq` Kitaev-Preskill positive form + 3 sign-analysis (`_nonneg`, `_pos_iff`, `_eq_zero_iff` biconditional via `Real.exp_log`); §2 cross-wave bridge `topologicalEntropy_logD_eq_neg_wave1` (Wave 2 γ = -Wave 1 `topologicalEntanglementEntropy`); §3 concrete witnesses (toric: log 2; Ising: log 2 via Wave 1 `isingMTC_horizonBC_globalDimSq`; Fibonacci: (1/2) log((5+√5)/2)); §4 `topologicalEntropy_logD_toric_eq_ising` DLW recurrence at γ-level; §5 substantive `CHEntropyHypotheses` Prop bundle (Bisognano-Wichmann + Calabrese-Cardy + Kitaev-Preskill boundary-CFT inputs); §6 `casiniHuerta_bound_under_CHE` under CHE the entropy is bounded above by leading-log + non-universal-constant form (uses §1 `_nonneg` + linarith); §7 **dossier-corrected falsifiable claim** `casiniHuerta_saturation_iff_trivial_MTC` — bound saturates ⟺ `D² = 1`; §8 closed-form quantitative tightness `casiniHuerta_strict_tightness_equals_gamma` (Δ = γ exactly) + `casiniHuerta_strict_lt_on_nontrivial_MTC`; §9 cross-bridge `CHE_promotes_H_CasiniHuerta` promotes Phase 6c.5 `H_CasiniHuerta_Bound_Valid` to derived theorem under CHE + positivity (analog of Wave 1's `isolatedHorizon_violates_H_RT`); §10 `hlw_form_satisfies_CHE` witness instance + `hlw_form_satisfies_H_CasiniHuerta` compositional sanity check. **First formalization in any proof assistant** of Kitaev-Preskill γ-positive form on abstract MTC carrier with sign-analysis biconditionals + Casini-Huerta universal entropy bound under explicit BW+CC+KP hypothesis bundle + dossier-corrected saturation biconditional + closed-form quantitative tightness `Δ = γ` + DLW ambiguity recurrence at γ-level. **Strengthening: 0 retroactive cuts** (clean first-pass). 16 substantive thms / 1 noncomputable def / 1 structure / 0 sorry / 0 new axioms / library 8492 PASS. (**ALL PROVED, zero sorry**) |
| ScramblingTimeQuantitative | 425 | 18 | 0 | **6j W3** | **Phase 6j Wave 3 — Quantitative scrambling time on horizon-MTC substrate** (SHIPPED 2026-04-30 Stages 1-5 at structural-substantive scope **+ §9 W3 dossier integration SHIPPED 2026-04-30 + Tier-1 strengthening §9.3c k=3 witness 2026-04-30**). Module ships: **§1-§7 baseline (12 thms / 1 def):** `quantitativeScramblingTime := log H.globalDimSq + deltaF` parametric def + structural inequality `_ge_log_globalDimSq`; substantive `QuantitativeScramblingHypotheses` Prop bundle; sign/saturation analysis under QSH; cross-wave bridges to W2 γ (positive form) and W1 (negative form); cross-bridge `QSH_strengthens_QEC_scramblingTimeBound` to Phase 6c.4; structural baseline witness; numerical baselines on toric/Ising/Fibonacci including DLW recurrence. **§9 dossier integration (5 thms / 1 def):** Per W3 dossier verdict (returned 2026-04-30, mixed C/D verdicts) closed-form `Δ_F(C)` values are NOT primary-source-cited as scrambling-time corrections — they ARE the He-Numasawa-Takayanagi-Watanabe entanglement-entropy-jump constants `ΔS_a = log d_a` (arXiv:1403.0702). §9.1 `entanglement_jump_log_sqrt_two_eq_half_log_two` (Ising HNTW value). §9.2 `fibonacciHorizonBC_globalDimSq_eq_one_plus_goldenRatio_sq` (Mathlib `goldenRatio` bridge). §9.3 `fundamentalQuantumDim_SU2k` named def + `_at_k_two = √2` (k=2/Ising) + **`_at_k_three = goldenRatio` (k=3/Fibonacci, Tier-1 strengthening — closes the k ≤ 3 dossier-coincidence boundary)** + `_at_k_four = √3` (k=4) + **`_at_k_four_lt_two`** dossier structural-correction theorem proving the roadmap formula `2 cos(π/(k+2)) = d_max` is wrong for k ≥ 4 (`√3 < 2 = [3]_q = d_max(SU(2)_4)`). The k=2,3,4 numerical witnesses make the structural failure at k=4 a genuinely-tight boundary per dossier §6 ("the formula coincides with d_max only for k ∈ {2,3}"). **First formalization** of Hayden-Preskill scrambling-time quantitative parametric form `t_scr = log D² + Δ_F` on MTC substrate + dossier-corrective Lean-formal SU(2)_k structural correction. **Strengthening: 0 retroactive cuts**. 18 substantive thms / 2 noncomputable defs / 1 structure / 0 sorry / 0 new axioms / library 8494 PASS. (**ALL PROVED, zero sorry**) |
| HolographicCFunctionMTC | 510 | 16 | 0 | **6j W4** | **Phase 6j Wave 4 — Holographic c-function on horizon-MTC substrate** (SHIPPED 2026-04-30 Stages 1-5 at structural-substantive scope **+ W4 dossier integration §9 SHIPPED + Tier-2 strengthening §10 cross-wave bridges + DLW c-function recurrence + §9.5 strict-greater quantitative form SHIPPED 2026-04-30**). Module ships: **§1-§7 baseline (6 thms / 1 def):** `IsHolographicCFunction` predicate (non-negativity + saturation-iff-trivial); `HolographicCFunctionHypotheses` (HCF) substantive Prop bundle; strict-positivity `c_pos_on_nontrivial_under_HCF`; headline `zamolodchikov_c_theorem_under_HCF` Zamolodchikov c-theorem analog under monotone-flow hypothesis; cross-wave bridges to W2 γ + W3 t_scr; structural baseline `c_baseline_satisfies_HCF` (LOAD-BEARING Pattern #8 witness); trivial-MTC witness via Phase 6c.4 `trivialAbelianHorizonBC` cross-module bridge. **§9 dossier integration (4 thms / 1 def):** Per W4 dossier verdict (returned 2026-04-30): roadmap formula mislabeled (published "FP entropy" is `log FPdim`); `c(Fib) − c(triv) = log φ²` arithmetically false under all 3 candidate definitions (`cLogTotal(Fib) = log((5+√5)/2) ≈ 1.287`, `cRoadmap(Fib) ≈ 0.696`, `cShannonFP(Fib) ≈ 0.591` — none equals `log φ² ≈ 0.962`); minimal-model Virasoro recovery structurally wrong (Virasoro c not extractable from MTC alone — Bruillard-Ng-Rowell-Wang JAMS 29:857 2016). §9.1 `cLogTotal := log H.globalDimSq` named def (= dossier-recommended c-function = published FP entropy `log FPdim` / Affleck-Ludwig / Kitaev-Preskill γ × 2). §9.2 `cLogTotal_fibonacci = log((5+√5)/2)` corrected closed form. §9.3 `cLogTotal_trivialAbelian = 0` via Phase 6c.4 cross-module bridge. §9.4 `cLogTotal_satisfies_HCF` sanity check. **§9.5 `cLogTotal_fibonacci_gt_log_goldenRatio_sq`** dossier-corrective **strict** inequality (Tier-1 strengthening) proving original roadmap claim is arithmetically false WITH sign-of-error specified — the corrected value is `> log φ²` by `log(1 + 2/(3+√5)) > 0` (uses `Real.log_lt_log` monotonicity to reduce to `(5+√5)/2 > φ² = (3+√5)/2`, i.e., `5 > 3`). §9.5b `_ne_` corollary derived via `ne_of_gt`. **§10 Tier-2 cross-wave bridges:** §10.1 `cLogTotal_eq_two_topologicalEntropy_logD` (W4↔W2 named-API bridge `c = 2γ`); §10.2 `cLogTotal_eq_neg_two_topologicalEntanglementEntropy` (W4↔W1 bridge); §10.3-10.4 concrete numerical witnesses `cLogTotal_toricCodeMTC = cLogTotal_isingMTC_horizonBC = 2 log 2` consuming W3 §7 baselines; §10.5 `cLogTotal_toricCodeMTC_eq_isingMTC_horizonBC` Dong-Liu-Wen vacuum-sector ambiguity recurrence at the c-function level (analog of W1/W2/W3 DLW recurrences). **DROPPED per dossier §4.5:** No theorem claiming Virasoro central-charge recovery from MTC data (verdict D — structurally wrong). **First formalization** of Zamolodchikov c-theorem analog on horizon-MTC substrate under HCF + monotone-flow hypothesis + dossier-corrective Lean-formal arithmetic strict-greater falsifier of the `c(Fib) = log φ²` claim + DLW recurrence at c-function level. **Strengthening: 2 baseline P5 cuts** (`c_nonneg_under_HCF` + `c_eq_zero_iff_trivial_under_HCF` were pure `IsHolographicCFunction` field projections; inlined at consumer sites). **§9 + §10 additions: 0 retroactive cuts**. 16 substantive thms / 2 defs / 1 structure / 0 sorry / 0 new axioms / library 8494 PASS. (**ALL PROVED, zero sorry**) |
| BHLGaugeEmbedding | 492 | 23 | 0 | 6 supp | Phase 6 supporting module: BH gauge-embedding bridge (anomaly inflow + Z₁₆ embedding cross-check). (**ALL PROVED, zero sorry**) |
| EWPhaseTransition | 414 | 21 | 0 | 6 supp | Phase 6 supporting module: electroweak phase-transition substrate-bridge (paper22 anchor). (**ALL PROVED, zero sorry**) |
| HigherOrderSK | — | — | 0 | **6n W1a.1+1a.2** | **Phase 6n Wave 1a.1+1a.2 (Session 5, 2026-05-04)**: SK-EFT gradient-expansion order count theorems for orders 4–7 (count(N) = ⌊(N+1)/2⌋ + 1). Companion to `formulas.py` δ⁴–δ⁷ symbolic coefficient generators. (**0 sorry**) |
| Resurgence/Basic | — | — | 0 | **6n W1a.4** | **Phase 6n Wave 1a.4 (Session 5)**: `IsGevrey1` predicate + Gevrey-1 vs geometric-convergence classification substrate for SK-EFT gradient expansion. (**0 sorry**) |
| Resurgence/BorelAction | — | — | 0 | **6n W1a.4** | **Phase 6n Wave 1a.4 (Session 5)**: `lambdaUV_from_borelAction` conditional theorem for Λ_UV-from-IR via Borel-singularity action; substantive Stokes-data infrastructure. (**0 sorry**) |
| Resurgence/StokesBound | — | — | 0 | **6n W1a.4** | **Phase 6n Wave 1a.4 (Session 5)**: Stokes constant + δ_NP non-perturbative-content existence statement; bounds Borel-summability obstruction. (**0 sorry**) |
| GloriosoLiu/Axioms | 291 | — | 0 | **6n W2a S1+2-3+2-3b** | **Phase 6n Wave 2a Stage 1+2-3+2-3b (Sessions 5+6)**: 6-axiom Glorioso-Liu skeleton (CTP + largest-time + reflection-pos + hermiticity + dyn-KMS + LE) parameterized over `SKDoubling.SKAction`. `hasDynamicalKMS_algebraic` (substantive form per KMS framework finding) + `SKEFTAxioms_zero_action` trivial witness + **`SKEFTAxioms_for_dissipative` substantive non-trivial witness** via algebraic-FDR coefficient extraction (γ_1 ≥ 0, γ_2 ≥ 0). (**0 sorry**) |
| GloriosoLiu/DynamicalKMS | 123 | — | 0 | **6n W2a** | **Phase 6n Wave 2a Stage 1+2-3 (Session 5)**: `hasDynamicalKMS_strict_of_realization` substantive-vs-strict-form discriminator. (**0 sorry**) |
| GloriosoLiu/LocalEquilibrium | 90 | — | 0 | **6n W2a** | **Phase 6n Wave 2a Stage 1+2-3 (Session 5)**: LE axiom + slow-mode infrastructure + `hasLocalEquilibrium_zero_action` substantive witness. (**0 sorry**) |
| GloriosoLiu/EntropyCurrent | ~107 | — | 0 | **6n W2a S2-3b LOAD-BEARING** | **Phase 6n Wave 2a Stage 1+2-3 (Session 5) + Stage 2-3b LOAD-BEARING DEEPENING (Session 7)**: `EntropyCurrent` density structure + `zeroEntropyCurrent` baseline + **`noetherEntropyDensity c β` substantive Noether construction** (β times noise-sector Lagrangian Im part) + `noetherEntropyCurrent`. **`entropy_current_exists` upgraded** from trivial-discharge `⟨zeroEntropyCurrent, rfl⟩` (Stage 2-3a placeholder) to substantive form extracting `c : FirstOrderCoeffs` from `A.dynamical_KMS` — `A : SKEFTAxioms` parameter is now load-bearing. (**0 sorry**) |
| GloriosoLiu/LocalSecondLaw | 81 | — | 0 | **6n W2a** | **Phase 6n Wave 2a Stage 1+2-3 (Session 5)**: `divergence J f := (action.lagrangian f).2` (Im L = ∂_μ J^μ_S identification per CGL II) + **`Glorioso_Liu_local_second_law`** load-bearing theorem invoking `A.reflection_pos` directly to derive `0 ≤ divergence J f` pointwise. (**0 sorry**) |
| GloriosoLiu/OnsagerReciprocity | ~155 | — | 0 | **6n W2a S2-3b LOAD-BEARING** | **Phase 6n Wave 2a Stage 1+2-3 (Session 5) + Stage 2-3b LOAD-BEARING DEEPENING (Session 7)**: `ResponseMatrix` 9×9 carrier + `OnsagerReciprocityHolds := R.matrix.IsSymm` predicate + **`firstOrderConductivity` 2×2 conductivity matrix** in (γ_1, γ_2) channel basis + **`firstOrderConductivity_isSymm_of_FirstOrderKMS`** (off-diagonal entries vanish under FirstOrderKMS — SK-EFT first-derivative-order substantive Onsager). **`OnsagerReciprocity_from_KMS` upgraded** from trivial-discharge `⟨⟨0⟩, isSymm_zero⟩` (Stage 2-3a placeholder) to substantive 9×9 diagonal embedding (`conductivity9x9_diagEmbed`) of the FDR-pinned 2×2 conductivity, extracted via `A.dynamical_KMS` — `A : SKEFTAxioms` parameter now load-bearing. (**0 sorry**) |
| GloriosoLiu/FirstOrderProjection | 97 | — | 0 | **6n W2a** | **Phase 6n Wave 2a Stage 1+2-3 (Session 5)**: First-order projection of GL axioms recovers Phase 1 `FirstOrderKMS` content. (**0 sorry**) |
| GloriosoLiu/Phase1Reconciliation | 261 | — | 0 | **6n W2a R1 LIFT** | **Phase 6n Wave 2a R1 LIFT (Session 5)**: `four_of_nine_partition_recovered` substantive Lean theorem (was Aristotle-empirical observation). Substantive partition recovery via `SKDoubling.KMSSymmetry` projection + Aristotle counterexample + linarith. (**0 sorry**) |
| GloriosoLiu/SecondOrderProjection | 471 | — | 0 | **6n W2a × W1b CROSS-TRACK (Session 9)** | **Phase 6n Wave 2a × Wave 1b CROSS-TRACK UNIFICATION (Session 9, 2026-05-05)**: substantive bridge between Track 2 foundational backing (Wave 2a `SKEFTAxioms` on first-order `SKAction`) and Track 1 structural unification (Wave 1b `KMSParityAlternationCompatible` on second-order `SKActionExt`). **9 substantive theorems + `SKEFTAxiomsExt` six-axiom-skeleton structure on `SKActionExt` + 7 def predicates** (mirrors of `hasCTPStructureExt`/`hasLargestTimeExt`/`hasReflectionPositivityExt`/`hasHermiticityExt`/`hasDynamicalKMSExt_algebraic`/`hasDynamicalKMSExt` alias/`hasLocalEquilibriumExt`). Headline content: (1) `combined_positivity_of_parity_zero` — converse of Aristotle's `combined_positivity_constraint`, completing biconditional `positivity_ext ↔ γ_{2,1}+γ_{2,2}=0`; (2) `fullSecondOrder_KMS_for_combined_parity_zero` — explicit FullSecondOrderCoeffs embedding satisfying all 10 FDR/T-reversal relations; (3) `fullSecondOrder_lagrangian_eq_combined_parity_zero` — Lagrangian match for canonical embedding; (4) `SKEFTAxiomsExt_for_combined_parity_zero` — substantive non-trivial existence witness; (5) **`SKEFTAxiomsExt_yields_combined_uniqueness`** — load-bearing projection (calls `fullSecondOrder_uniqueness` Aristotle run c4d73ca8 in proof body); (6) **`SKEFTAxiomsExt_yields_parity_alternation`** — load-bearing parity-alternation theorem (calls `combined_positivity_constraint` Aristotle run c4d73ca8 in proof body); (7) **`SecondOrderProjection_bridges_to_KMSParityAlternation`** — cross-track unification statement (calls `stage2Verdict_instantiates_KMSParityAlternation` from Wave 1b Stage 3 in proof body); (8) `SKEFTAxiomsExt_for_firstOrder_lift` — concrete first-order-as-degenerate-second-order instance. **Verlinde-vs-Jacobson distinction preserved at every Lean statement** — both Track 2 (Glorioso–Liu axiomatic) and Track 1 (Schäfer-Nameki SymTFT) operate at SK-EFT polynomial-coefficient level. `lean_verify` on headline theorems closes to `[propext, Classical.choice, Quot.sound]` only — zero suspicious axioms. MCP-driven, zero Aristotle escalation. (**0 sorry**) |
| QuantumCrooks/Setup | — | — | 0 | **6n W2b S1** | **Phase 6n Wave 2b Stage 1 (Session 6)**: `WorkDistribution` structure + `IsCrooksRatio` predicate + `IsCrooksRatio.symm` symmetry theorem. (**0 sorry**) |
| QuantumCrooks/{Tasaki,Aberg,KafriDeffner,Quasiprobability} | — | — | 0 | **6n W2b S1** | **Phase 6n Wave 2b Stage 1 (Session 6)**: 4 candidate quantum-Crooks axiomatizations (Tasaki-Crooks Talkner-Hänggi 2007 / Åberg fully-quantum PRX 2018 / Kafri-Deffner unital PRA 2012 / Levy-Lostaglio-Francica Kirkwood-Dirac quasiprobability). (**0 sorry**) |
| QuantumCrooks/PerarnauLlobet | — | — | 0 | **6n W2b S1** | **Phase 6n Wave 2b Stage 1 (Session 6)**: **Parametric Perarnau-Llobet no-go theorem** `perarnau_llobet_no_go_parametric` (under `h_disagree`, no MS satisfies `ReproducesAverageEnergy ∧ RecoversTPMOnDiagonal`). Contrapositives `reproduces_avg_implies_fails_TPM` + `recovers_TPM_implies_fails_avg`. **All MCP-proven, zero Aristotle.** (**0 sorry**) |
| QuantumCrooks/Concrete | — | — | 0 | **6n W2b S2-3** | **Phase 6n Wave 2b Stage 2-3 (Session 6)**: Canonical 2-level Perarnau-Llobet counterexample on `Matrix (Fin 2) (Fin 2) ℝ` (ρ_+ = ½(11; 11), H_i = diag(0,1), H_f = σ_x). **`perarnau_llobet_no_go_quantum`** substantive quantum no-go theorem; `trueAverage_perarnau ρ_plus = +1/2`; `tpmAverage_perarnau ρ_plus = -1/2`. (**0 sorry**) |
| CrooksAnalogHawking/HorizonDetailedBalance | 146 | — | 0 | **6n W2c S1** | **Phase 6n Wave 2c Stage 1 (Session 6)**: `HorizonDetailedBalance P_F P_R σ` generalizes `IsCrooksRatio` to nonlinear σ. `specialize_to_Crooks` cross-bridge (σ = β·W ⇔ classical Crooks); `symm_neg`; `horizonDetailedBalance_zero` well-posedness. (**0 sorry**) |
| CrooksAnalogHawking/GallavottiCohen | 91 | — | 0 | **6n W2c S1** | **Phase 6n Wave 2c Stage 1 (Session 6)**: `GallavottiCohenSymmetry I := ∀ σ, I(-σ) - I(σ) = -σ` LDP rate-function symmetry; `gallavottiCohen_linear_witness` + `shift_invariant`. (**0 sorry**) |
| CrooksAnalogHawking/AnalogHawkingBiconditional | 249 | — | 0 | **6n W2c S2-3** | **Phase 6n Wave 2c Stage 2-3 (Session 6)**: Third Sakharov-style biconditional at predicate-bundle level. `AnalogHawkingEmissionScheme` bundle + `monotonicityCompatibleEmission` + `gcCompatibleEmission` + `analog_hawking_third_biconditional` theorem with `compat_hyp` precondition + non-vacuous-content partition. (**0 sorry**) |
| CrooksAnalogHawking/SakharovHorizonCrooks | 192 | — | 0 | **6n W2d S1** | **Phase 6n Wave 2d Stage 1 (Session 6)**: `HorizonCrooksSubstrate` bundles `JacobsonThermoGRDarkEnergy.SakharovConditions` (Phase 6m Track C) with HDB witness; `jacobsonConsistent` predicate (Jacobson reading, NOT Verlinde). Concrete witnesses `helium3A_horizon_crooks` + `flsBEC_horizon_crooks`; `horizonCrooks_substrate_partition` substantive partition theorem invoking JTGR7 + JTGR8. (**0 sorry**) |
| CrooksAnalogHawking/BiconditionalReformulation | 210 | — | 0 | **6n W2d S2-3** | **Phase 6n Wave 2d Stage 2-3 (Session 6)**: 4 Bool-projection horizon-Crooks-side predicates + **`sakharov_iff_horizon_crooks` biconditional theorem** proved via `Bool.and_eq_true` + `and_assoc`; ³He-A and FLS BEC compatibility specializations. (**0 sorry**) |
| CrooksAnalogHawking/SKEFTHorizonBridge | ~200 | 6 | 0 | **6n W2d S4 SUBSTRATE-BRIDGE (Session 7)** | **Phase 6n Wave 2d Stage 4 (Session 7, 2026-05-05)**: substantive (not Bool-projection) substrate-level form of Sakharov ⇒ horizon-Crooks. **6 substantive theorems** linking Wave 2a `SKEFTAxioms` machinery at horizon temperature β_H to Wave 2c `HorizonDetailedBalance` predicate: (1) `noetherEntropyDensity_eq_beta_imL` cross-module bridge identity; (2) `noetherEntropyDensity_nonneg_of_SKEFTAxioms` (BOTH `A.dynamical_KMS` + `A.reflection_pos` load-bearing); (3) `skeft_yields_horizon_crooks_witness` (FDR-pinned σ = β_H · W, not freely chosen); (4) `sakharov_skeft_substrate_jacobsonConsistent` (substantive Sakharov + SKEFTAxioms ⇒ Jacobson-consistent; both hypotheses load-bearing); (5) `helium3A_skeft_substantive_jacobsonConsistent` (³He-A concrete instance under any SKEFTAxioms); (6) `horizonCrooks_substantive_partition` (substantive partition vs. FLS BEC). **Verlinde-vs-Jacobson distinction preserved at every Lean statement.** (**0 sorry**) |
| CrooksAnalogHawking/SKEFTGallavottiCohen | ~280 | 7 | 0 | **6n W2c S4 SUBSTRATE-BRIDGE (Session 8)** | **Phase 6n Wave 2c Stage 4 (Session 8, 2026-05-05)**: substantive substrate-level lift of Wave 2c rate-function content paralleling Session-7 Wave 2d's SKEFTHorizonBridge. **7 substantive theorems** ship the W-form Gallavotti-Cohen + FDT-pinned Gaussian rate function + load-bearing-A bridges: (1) `WFormGallavottiCohen β I := ∀ W, I(W) - I(-W) = -β·W` predicate (Crooks-form W-variable analog of σ-form `GallavottiCohenSymmetry`) + `linear_witness` non-vacuity; (2) `linearResponseRateFunction β σ² W := (W - β·σ²/2)² / (2·σ²)` FDT-pinned Gaussian + algebraic `_satisfies_WFormGC` proof; (3) `WFormGallavottiCohen.to_σForm` cross-bridge to existing σ-form via change of variable σ = β·W + sign flip; (4) **`skeft_substrate_yields_WFormGC`** load-bearing-A theorem destructuring `A.dynamical_KMS` to extract `c : FirstOrderCoeffs` for FDT-pinned rate function at noise variance σ² = c.i₂; (5) **`firstOrderDissipative_yields_WFormGC`** concrete substantive witness for `firstOrderDissipativeAction(coeffs, β)` with γ₂ > 0 (explicit c with c.i₂ = γ₂/β > 0 unconditional); (6) `skeft_yields_horizon_crooks_with_GC` composed Stage-4 substrate (FDR-pinned σ = β·W + Noether positivity from Session-7 + W-form GC together via single c); (7) `firstOrderDissipative_yields_horizon_crooks_with_GC` concrete composed witness. **Verlinde-vs-Jacobson distinction preserved.** Stage 5+ LDP infrastructure retained as Mathlib upstream-PR candidate. (**0 sorry**) |
| SymTFTAudit/Applicability | — | — | 0 | **6n W1b S2+3** | **Phase 6n Wave 1b Stage 2+3 (Session 6)**: `SymTFTApplicability` inductive (Applicable / PartiallyApplicable / NotApplicable) + `stage2Verdict := PartiallyApplicable` per direct primary-source fetch of arXiv:2507.05350 (Schäfer-Nameki et al.) + 3 ship-able discrete-sector candidate predicates (`chiralCentralChargeMod24Compatible`, `Z16AnomalyEtaCompatible`, `KMSParityAlternationCompatible`) + substantive instantiation theorems + `stage2_partition`. (**0 sorry**) |
| SymTFTAudit/CrossBridges | — | 5 | 0 | **6n W1b S4 (Session 6) + S4c (Session 8)** | **Phase 6n Wave 1b Stage 4 (Session 6) + Stage 4c (Session 8, 2026-05-05)**: 3 substantive predicate-level cross-bridges (was 2 in Session 6; Session 8 closes the asymmetry): (1) `KMSParityAlternation ↔ SecondOrderSK.gamma_2_1+gamma_2_2=0`; (2) `Z16AnomalyEta ↔ Z16AnomalyCancels`; (3) **NEW Session 8** `chiralCentralCharge_bridges_to_GenerationConstraint` — project-local Schellekens chain via `generation_constraint_iff` biconditional `3 ∣ n ↔ 24 ∣ 8·n` (sidesteps absent Mathlib Witt-group infrastructure) + `chiralCentralCharge_at_three_generations` (concrete N_f=3 specialization with c₋=24 saturating modular bound). Updated `stage4_discrete_sector_bridges_partition` from 2-of-3 to 3-of-3 substantive bridges. Full Witt-class extension (Stage 5+) retained as Mathlib upstream-PR candidate. (**0 sorry**) |
| FKLW/FibSU2Density | 6739 | 170 | 0 | **6p W2c.4a-R4.2.d (Sessions 30–34)** | **Phase 6p Wave 2c.4a-R4.2.d.R5.4 PRIMARY DRIVER**. §17-§29 carry the algebraic + spectral + trace-based content of the FKLW Fibonacci SU(2) density chain. Sessions 30–31 ship D4.3.c.application (sharpened intersection cardinality `|⟨σ_1⟩∩⟨σ_2⟩| ≤ 2`); D4.3.c.app.5b (`H_Fib_card_ge_200_if_finite` via Fin 20 × Fin 10 injection); D4.3.d-starter (`H_Fib_not_iso_QuaternionGroup` via Mathlib `QuaternionGroup.orderOf_xa = 4`); D4.3.e-conditional (`PartialHurwitzSU2` trichotomy + `H_Fib_infinite_of_PartialHurwitz`); D3-Path-ii SU(2) Cayley-Hamilton + trace identity substrate; **closed-form trace `tr(σ_Fib_1 · σ_Fib_2⁻¹) = (3-√5)/2`** ∈ ℝ\ℚ_cyc; **`cFib_not_isOfFinOrder`** via Galois-conjugate growth bound `aHat_gt_two_of_pos` + `polyTraceSeq` integer-pair reduction + Chebyshev recursion; downstream `ρ_Fib_SU2_range_infinite` + `H_Fib_infinite`. Sessions 32–34 ship Layers A→D.3.i.1 (AccPt witness extractor → small-pair non-parallel witness → iteration sequence — 19-commit mega-ship in Session 32 alone). All kernel-only `[propext, Classical.choice, Quot.sound]`. (**0 sorry, 0 axioms**) |
| FKLW/AharonovAradLemma6 | 328 | 6 | 0 | **6p W2c.4a-R4.2.d.R5.4 Layer A (Session 32)** | AccPt → small-distance witness extractor; `one_accPt_of_infinite_closed_subgroup` closes the structural step "infinite closed subgroup of SU(2) accumulates at 1". |
| FKLW/AharonovAradBridgeIteration | 1020 | 14 | 0 | **6p W2c.4a-R4.2.d** | AA bridge iteration kernel: `closure_eq_univ_of_one_mem_interior` + `image_infinite_of_exists_not_finOrder` + `bridge_FKLW_unitary_hom`. Consumes shipped R5.3 BCH substrate from `MatrixBCHCubic.lean`. |
| FKLW/AharonovAradBridge | 240 | 3 | 0 | **6p W2c.4a** | AA bridge architectural layer. |
| FKLW/AharonovAradBridgeProof | 245 | 2 | 0 | **6p W2c.4a** | AA bridge proof composition. |
| FKLW/BridgeProp | 248 | 2 | 0 | **6p W2c.4a** | Bridge Prop predicate substrate. |
| FKLW/CartanSubstrate | 420 | 12 | 0 | **6p W2c.4a** | Cartan substrate for FKLW (precursor to Cartan-A/B/C/D Mathlib-PR-quality layer modules). |
| FKLW/EpsilonNet | 167 | 3 | 0 | **6p W2c.4a** | ε-net substrate for density arguments. |
| FKLW/FibRepInfiniteOrder | 468 | 7 | 0 | **6p W2c.4a** | Fibonacci-rep infinite-order substrate (pre-R5.4 path). |
| FKLW/FibSU2Rep | 1008 | 40 | 0 | **6p W2c.4a** | σ_Fib_1, σ_Fib_2 in SU(2); rep-level lemmas. |
| FKLW/QubitBalancedCommutator | 307 | 12 | 0 | **6p W2c.4a** | Qubit balanced commutator substrate. |
| FKLW/RouabahSplitBraid | 198 | 3 | 0 | **6p W2c.4a** | Rouabah split-braid substrate. |
| FKLW/SKZAxisStep | 239 | 2 | 0 | **6p W2c.4a** | SKZ axis-step substrate. |
| FKLW/SolovayKitaev | 213 | 2 | 0 | **6p W2c.4a** | Solovay–Kitaev structural API. |
| FKLW/SolovayKitaevConstructive | 492 | 10 | 0 | **6p W2c.4a** | Constructive Solovay–Kitaev compilation. |
| FKLW/SpecialUnitaryTopology | 295 | 5 | 0 | **6p Wave-Cluster recovery** | `IsCompact U(d)`/`SU(d)`. Mathlib-PR-quality in-tree topology infrastructure. |
| FKLW/SpecialUnitaryPathConnected | 743 | 8 | 0 | **6p Wave-Cluster recovery** | PathConnected SU(d) via CStarMatrix bridge + phase-shift path + det-correction. Mathlib-PR-quality. |
| **FKLW/SU2LieAlgebra** | **1118** | **44** | 0 | **6p W2c.4a-R4.2.d.R5.4 Layer Cartan-A + Layers F.1–F.14 (Sessions 35 + 41–48) + Layer F.20.a (Session 50); Session 51 ships nothing in this file (entirely in FibSU2LieBundle.lean)** | **NEW MODULE — upstream-Mathlib4-PR-quality**. Foundational 𝔰𝔲(2) Lie-algebra substrate: skew-Hermitian + traceless properties (Layers F.4 + F.6); Pauli basis ℝ-linear independence (F.1) + spanning (F.2) + coordinate extraction (F.3) + `pauliDet` definition + basis normalization (F.7); full Cramer-rule linear-independence theorem (F.8); `lieProj` canonical 𝔰𝔲(2) projection (F.9) + Ad-action equivariance (F.10) + on `specialUnitaryGroup` (F.11); Ad-action preserves 𝔰𝔲(2) (F.12). **Session 50 Layer F.20.a (+123 LoC, +2 public theorems, commit `8681e2c` + helper-promotion `f8cf989`):** §15 ships Cramer-rule SPANNING criterion. `tracelessSkewHermitian_complex_smul_real_mem` (public — bridge `(r:ℂ)•v ∈ 𝔰𝔲(2)` when `v ∈ 𝔰𝔲(2)` and `r:ℝ` via `Complex.coe_smul`; was private in `8681e2c`, promoted public in `f8cf989` for downstream invocation from FibSU2LieBundle §12). **HEADLINE** `tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero` — for any X ∈ 𝔰𝔲(2) and 3-tuple (v₁, v₂, v₃) ∈ 𝔰𝔲(2)³ with `pauliDet ≠ 0`, ∃ a b c : ℝ with `X = (a:ℂ)•v₁ + (b:ℂ)•v₂ + (c:ℂ)•v₃` via explicit Cramer-rule cofactor formulas closed by `field_simp; ring` + `matrixToPauliCoords` linearity + `matrixToPauliCoords_eq_zero_iff` injectivity + submodule closure. With §10 lin-indep, this establishes (v₁, v₂, v₃) with `pauliDet ≠ 0` is a BASIS of 𝔰𝔲(2). All kernel-only. |
| **FKLW/SU2MatrixExp** | **143** | **2** | 0 | **6p W2c.4a-R4.2.d.R5.4 Layer Cartan-B (Session 36)** | **NEW MODULE — upstream-Mathlib4-PR-quality**. `exp(skew-Hermitian) ∈ unitaryGroup`. |
| **FKLW/SU2LocalDiffeo** | **187** | **4** | 0 | **6p W2c.4a-R4.2.d.R5.4 Layer Cartan-C (Session 37)** | **NEW MODULE — upstream-Mathlib4-PR-quality**. Matrix exp is local diffeomorphism at 0 via Inverse Function Theorem. |
| **FKLW/SU2InteriorBridge** | **172** | **3** | 0 | **6p W2c.4a-R4.2.d.R5.4 Layer Cartan-D (Session 38)** | **NEW MODULE — upstream-Mathlib4-PR-quality**. Architectural composition bridge: closure-eq-univ from exp-image subset. |
| **FKLW/FibonacciDensityConditional** | **96** | **1** | 0 | **6p W2c.4a-R4.2.d.R5.4 Layer E (Session 39)** | **NEW MODULE**. Final conditional Fibonacci density composition `fibonacci_density_from_exp_image_subset` — chain `BCH-spanning witness → DenseInSpecialUnitary 3 2 ρ_Fib_SU2`. |
| **FKLW/FibSU2LieBundle** | **1036** | **41** | 0 | **6p W2c.4a-R4.2.d.R5.4 Layers F.13 + F.14 + F.15 + F.16 + F.17.a + F.17.b + F.18 + F.19 (Sessions 48 + 49) + Layers F.20.a-app + F.20.b (Session 50) + Layers F.20.c.a + F.20.c.b (Session 51)** | **NEW MODULE**. σ_Fib 3-bundle of Lie directions + lin-indep from `pauliDet` (F.13/F.14) + σ_Fib_1 explicit Ad-action on `paulI_x` via `diag_conj_paulI_x` general lemma (F.15). **Session 49 R5.4 lin-indep arc capstone (5 commits, ~570 LoC):** F.16 ω-cancellation + Pauli coords `matrixToPauliCoords (σ_Fib_1·paulI_x·σ_Fib_1†) = (cos(7π/5), sin(7π/5), 0)` (commit `cd12d45`); F.17.a `σ_Fib_2_SU_mat = F_C · σ_Fib_1_SU_mat · F_C` decomposition + `F·paulI_x·F = !![a·I, b·I; b·I, -a·I]` explicit form (commit `0f27715`); F.17.b `(σ_Fib_2·paulI_x·σ_Fib_2†)(0,0) = I · (φ-real product) · (R1·star Rτ + Rτ·star R1 - 2)` closed form (commit `ce4d516`); F.18 σ_Fib bundle `pauliDet paulI_x ≠ 0` via `sin(7π/5) < 0` + `cos(7π/5) < 1` + φ-positivity (commit `4623126`); F.19 σ_Fib bundle ℝ-lin-indep at `paulI_x` (commit `39d9b86`). **Session 50 R5.4 spanning arc + scaled-spanning (2 commits, +158 LoC, +6 substantive theorems): §11 F.20.a-app `e798efa` (+50 LoC, 1 theorem) — `σ_Fib_lie_bundle_paulI_x_spans` (HEADLINE: for every X ∈ 𝔰𝔲(2), ∃ real (a, b, c) with X = (a:ℂ)•paulI_x + (b:ℂ)•(σ_Fib_1·paulI_x·σ_Fib_1†) + (c:ℂ)•(σ_Fib_2·paulI_x·σ_Fib_2†)) — composition of F.13 + F.18 + SU2LieAlgebra §15 (F.20.a abstract spanning). With F.19, this establishes the σ_Fib 3-bundle at paulI_x is a BASIS of 𝔰𝔲(2). §12 F.20.b `f8cf989` (+108 LoC, 5 theorems) — `pauliDet_smul_uniform` (pauliDet trilinear-homogeneous: scales as t³ under uniform-smul) via `matrixToPauliCoords_smul` + ring; `σ_Fib_lie_bundle_smul_uniform` (componentwise scaling via `Matrix.mul_smul + Matrix.smul_mul`); `σ_Fib_lie_bundle_pauliDet_smul_uniform` (composition); **HEADLINE** `σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero` (for any t ≠ 0, the σ_Fib bundle pauliDet at `(t:ℂ)•paulI_x` is non-zero); `σ_Fib_lie_bundle_scaled_paulI_x_spans` (spanning at every non-zero scalar multiple of paulI_x — provides arbitrarily-small spanning witnesses for the IFT/BCH iteration bridge).** **Session 51 R5.4 BCH/IFT iteration substrate opens (2 commits, +133 LoC, +1 noncomputable def + 7 substantive theorems): §13 F.20.c.a `268d56d` (+84 LoC, 1 def + 5 theorems) — `liePartMat` (def: `lieProj (M - 1)`, canonical "Lie part relative to identity" for any 2×2 complex matrix M; for `M = h ∈ SU(2)` near 1, approximates `log h` to first order); `liePartMat_mem_tracelessSkewHermitian` (output ∈ 𝔰𝔲(2)); `liePartMat_one` (`liePartMat 1 = 0`); HEADLINE `liePartMat_conj_specialUnitary` (Ad-equivariance: for `g ∈ specialUnitaryGroup`, `liePartMat (g·M·g†) = g · liePartMat M · g†` via Mathlib `mem_unitaryGroup_iff` + algebraic identity + F.11 `lieProj_conj_specialUnitary`); `liePartMat_conj_σ_Fib_{1,2}_SU_mat` (concrete σ_Fib_1/σ_Fib_2 instances). §14 F.20.c.b `ff5557f` (+49 LoC, 2 theorems) — HEADLINE `σ_Fib_lie_bundle_liePartMat_eq` (`σ_Fib_lie_bundle (liePartMat M) = (liePartMat M, liePartMat (σ_Fib_1·M·σ_Fib_1†), liePartMat (σ_Fib_2·M·σ_Fib_2†))` via `σ_Fib_lie_bundle` def + Ad-equivariance of `liePartMat`) + `σ_Fib_lie_bundle_pauliDet_liePartMat_eq` (pauliDet-form direct consequence). The σ_Fib bundle of Lie parts equals the Lie parts of the σ_Fib bundle, connecting the small-h BCH iteration argument (operating on `h ∈ H_Fib`) to the Lie-algebra spanning analysis (operating on `liePartMat h ∈ 𝔰𝔲(2)`).** The structural chain `pauliDet ≠ 0 for some X → ℝ-lin-indep 3-bundle → spans 𝔰𝔲(2) → density` is CONNECTED end-to-end as a CONDITIONAL theorem AND the σ_Fib bundle is now a BASIS at every `t·paulI_x` with `t ≠ 0`. Consumed by spanning argument over the (h, σ_1·h·σ_1⁻¹, σ_2·h·σ_2⁻¹) candidate triple. Substantive remaining for full bridge to unconditional density: F.20.c.c+ (BCH iteration spanning composing Cartan-D + R5.3/D.3.{e,f,g,h,i.1} substrate with F.20.c.a/b `liePartMat` to produce IFT U witness) + F.21 (apply Layer E `fibonacci_density_from_exp_image_subset`). |
| ExtractDeps | 323 | 0 | 0 | infra | **Infrastructure metaprogram**: Lean 4 environment walker / axiom-closure extractor; emits the SKEFTHawking declaration taxonomy (kind, signature, axiom dependencies, structure fields) consumed by the graph pipeline / `validate.py` / provenance dashboard / `update_counts.py`. **Only file in project that invokes Pipeline-Invariant-#10 metaprogram exception** (sets unlimited heartbeats locally to walk all 4385+ declarations) — see CLAUDE.md heartbeat policy. Required target of `lake build SKEFTHawking.ExtractDeps` for trustworthy clean baseline. |

**Axioms:** **0** (counts.json 2026-05-19 `axiom_names: []`; Sessions 49 + 50 + 51 ship zero axiom changes). History: pre-Phase-6p baseline was 1 (`gapped_interface_axiom` in `SPTClassification.lean`); previous axioms (`non_abelian_center_discrete`, `gs_nogo_axiom`) removed in Wave 6 — proved as theorems. The transient Phase 6a Wave 3 axiom `gaussianSaddleAsymptotic` (introduced 2026-04-26 in `BHEntropyMicroscopic.lean`, eliminability: hard) was retired 2026-04-27 by Wave 7 via `LaplaceMethod.lean` Mathlib-rewrite path. Phase 6p Wave-Cluster recovery (2026-05-12) introduced and then narrowed `aa_residual_interior_at_one_for_hom` as a strictly-narrower sound replacement for the unsound `bridge_axiom_FKLW_general`. **Both surviving axioms were then discharged PRE-R5.4-program:** `aa_residual_interior_at_one_for_hom` dropped 2026-05-13 in commit `f44c60d` ("R2 SOUNDNESS AUDIT", count 2→1); `gapped_interface_axiom` retired in commit `d282677` (session 29 work, "Phase 5h Wave 2 → TPFConjecture tracked-Prop conversion", count 1→0). **The Phase 6p Wave 2c.4a-R4.2.d.R5.4 substrate program (Sessions 30–51) ships zero new axioms and zero axiom discharges** — it builds the constructive substrate chain (Cartan-A/B/C/D + Layer E + Layers F.1–F.19 + F.20.a + F.20.a-app + F.20.b + F.20.c.a + F.20.c.b) for the CONDITIONAL theorem `fibonacci_density_from_exp_image_subset` (BCH-spanning witness production remains future work in F.20.c.c+ + F.21) AND for the unconditional σ_Fib 3-bundle that is now a BASIS of 𝔰𝔲(2) at every non-zero scalar multiple of `paulI_x` (Sessions 49 + 50) PLUS the BCH/IFT iteration substrate opened by Session 51 `liePartMat` Ad-equivariance + σ_Fib bundle commutativity with `liePartMat`. Net post-arc axiom count = 0 (kernel-only `[propext, Classical.choice, Quot.sound]` throughout).

---

## 3. ARISTOTLE THEOREM PROVER (322+ registry entries across 45+ runs)

| Run ID | Date | Theorems | Scope |
|--------|------|----------|-------|
| 082e6776 | 2026-03-23 | 4 | Phase 1 core (det, inv, Lorentzian, positivity) |
| a87f425a | 2026-03-23 | 1 | Phonon EOM |
| 88cf2000 | 2026-03-23 | 1 | Acoustic metric candidate |
| 638c5ff3 | 2026-03-23 | 1 | FDR complete |
| 657fcd6a | 2026-03-23 | 1 | Dissipative existence |
| d65e3bba | 2026-03-23 | 1 | Dispersive bound |
| 416fb432 | 2026-03-23 | 1 | Hawking universality |
| 270e77a0 | 2026-03-23 | 1 | firstOrder_uniqueness (most complex proof) |
| 20556034 | 2026-03-23 | 2 | FDR per-sector (γ₁, γ₂) |
| d61290fd | 2026-03-24 | 4 | Counting formula + instances |
| c4d73ca8 | 2026-03-24 | 4 | Full uniqueness, positivity constraint, turning point |
| 3eedcabb | 2026-03-24 | 10 | Stress tests batch (KMS optimal, limit checks) |
| 518636d7 | 2026-03-24 | 3 | Round 5: total-division strengthening |
| dab8cfc1 | 2026-03-24 | 2 | CGL: Einstein relation, secondOrder_cgl_fdr |
| 2ca3e7e6 | 2026-03-24 | 3 | CGL: general FDR, spatial, cgl→KMS |
| f8de66d1 | 2026-03-25 | 1 | ADW: curvature_zero_at_Gc |
| b1ea2eb7 | 2026-03-26 | 13 | Phase 4 batch (fracton, vestigial, chirality) |
| f35ca767 | 2026-03-27 | 2 | Wave 5: gs_nogo_requires_all, zeroTemp_nontrivial |
| run_20260328_051547 | 2026-03-28 | 3 | Wave 1A: kappa-scaling |
| run_20260328_132925 | 2026-03-28 | 7 | Wave 3A: LatticeHamiltonian |
| run_20260328_142342 | 2026-03-28 | 3 | Wave 3B: GoltermanShamir |
| run_20260328_151228 | 2026-03-28 | 3 | Wave 3B+: GoltermanShamir strengthening |
| run_20260328_170451 | 2026-03-29 | 4 | Wave 3C: ExteriorAlgebra finite-dim (fock_space_finite_dim + helpers) |
| run_20260329_094416 | 2026-03-29 | 11 | Wave 4A: KLinearCategory + SphericalCategory (tensor_preserves_nonzero, simple_indecomposable, golden_ratio_eq, etc.) |
| run_20260329_133200 | 2026-03-29 | 7 | Wave 4B: FusionExamples (associativity, fib_tau_squared, fib_F_involutory, fib_is_chiral) |
| run_20260329_162811 | 2026-03-29 | 3 | Wave 4C-1: VecG (day_unit_left/right, day_assoc) |
| run_20260329_173500 | 2026-03-29 | 5 | Wave 4C-2: VecG+DrinfeldDouble (simple_tensor, day_dim_multiplicative, ddMul_one_left/right, dd_abelian_simples) |
| 117a7115 | 2026-03-31 | 14 | 9C-2: SO4Weingarten (all 14 theorems) |
| 4528aa2b | 2026-03-31 | 63 | 9C-1+3: FractonFormulas (45) + WetterichNJL (18) |
| 9e2251cd | 2026-04-01 | 16 | Wave 6B: VestigialSusceptibility (all 16 theorems) |
| fb657b4d | 2026-04-02 | 19 | Wave 7A+7B: QuaternionGauge (10) + GaugeFermionBag (9) |
| cc257137 | 2026-04-02 | 2 | W7B-fix: Binder cumulant theorems |
| da7cb04d | 2026-04-02 | 20 | W7C: HubbardStratonovichRHMC (20 of 22 by Aristotle) |
| *manual* | 2026-04-02 | 27 | MajoranaKramers (25) + RHMC manual (2) |
| 9d6f2432 | 2026-04-03 | 1 | Phase 5a Wave 1A: OnsagerAlgebra (davies_G_antisymmetry) |
| 36b7796f | 2026-04-03 | 1 | Phase 5a Wave 1B: OnsagerContraction (contraction_rescaling) |
| 90ed1a98 | 2026-04-03 | 14 | Phase 5a Wave 2A: PauliMatrices + WilsonMass + BdGHamiltonian |
| 18969de2 | 2026-04-03 | 3 | Phase 5a Wave 2B: GTCommutation (crown jewels: [H,Q_A]=0) |
| a1dfcbde | 2026-04-03 | 1 | Phase 5b Wave 1: GenerationConstraint (generation_mod3_constraint) |
| 48493889 | 2026-04-03 | 1 | Phase 5b Wave 2: VecGMonoidal (vecG_braided) |
| 878b181f | 2026-04-03 | 5 | Phase 5b Wave 3: DrinfeldDoubleAlgebra (unit, assoc, basis_mul) |
| 52992d6a | 2026-04-03 | 13 | Phase 5b Wave 3: DrinfeldDoubleRing (Ring + Algebra instances) |
| b54f9611 | 2026-04-03 | 1 | Wave 6: axiom removal (z16_anomaly_without_nu_R) |
| 7d8efa8f | 2026-04-04 | — | Phase 5b: QNumber + Uqsl2 (q-integers, first quantum group) |
| 1f8e6cb5 | 2026-04-04 | — | Phase 5c: Uqsl2Hopf batch 1 |
| c73bac9c | 2026-04-04 | — | Phase 5c: Uqsl2Hopf batch 2 |
| 78dcc5f4 | 2026-04-05 | 34+ | Phase 5d Wave 1: Uqsl2Hopf (all sorry filled), SU2kSMatrix, RestrictedUq, RibbonCategory, E8Lattice, SpinBordism, VerifiedJackknife (all proved) |
| 79e07d55 | 2026-04-05 | 19+ | Phase 5d Wave 2: TetradGapEquation (19 proved), Uqsl2Hopf Serre coproduct |
| *Phase 5e-5p* | 2026-04-06–07 | 15+ | Phase 5e-5p sorry closure: VerifiedStatistics, KerrSchild, CoidealEmbedding, RepUqFusion, StimulatedHawking, CenterFunctor partial |
| 6dbc9447 | 2026-04-08 | — | **Complete** — Phase 5s sorry closure batch (superseded by interactive MCP closure of all 17 sorry between 2026-04-08 and 2026-04-14) |

---

## 4. JUPYTER NOTEBOOKS (76 total: 38 Technical + 38 Stakeholder)

| Notebook | Phase | Topic |
|----------|-------|-------|
| Phase1_Technical | 1 | Transonic flow, Beliaev damping, δ_diss for 3 platforms |
| Phase1_Stakeholder | 1 | BEC analog gravity motivation, key results |
| Phase2_Technical | 2 | Enumeration, KMS, WKB, frequency-dependent correction |
| Phase2_Stakeholder | 2 | Parity breaking, ω³ spectrum distortion |
| Phase3a_ThirdOrder_Technical | 3 | Parity alternation, third-order enumeration |
| Phase3a_ThirdOrder_Stakeholder | 3 | Parity as experimental probe |
| Phase3b_GaugeErasure_Technical | 3 | Non-Abelian erasure, SM scorecard |
| Phase3b_GaugeErasure_Stakeholder | 3 | Gauge hierarchy implications |
| Phase3c_WKBConnection_Technical | 3 | Complex turning point, exact Bogoliubov, noise floor |
| Phase3c_WKBConnection_Stakeholder | 3 | Modified unitarity, decoherence |
| Phase3d_ADW_Technical | 3 | Gap equation, NG modes, obstacles, He-3 analogy |
| Phase3d_ADW_Stakeholder | 3 | Emergent gravity concept, phase diagram |
| Phase4a_ExperimentalPredictions_Technical | 4 | Prediction tables, κ-scaling test, shot requirements |
| Phase4a_ExperimentalPredictions_Stakeholder | 4 | What experimentalists need to measure |
| Phase4b_Vestigial_Technical | 4 | Mean-field + MC, 3-phase structure, EP violation |
| Phase4b_Vestigial_Stakeholder | 4 | Pre-geometric→vestigial→full tetrad narrative |
| Phase5a_ChiralityWall_Technical | 5 | GS 9 conditions, TPF evasion, formal verification |
| Phase5a_ChiralityWall_Stakeholder | 5 | Lattice chirality problem, what the wall means |
| Phase5a_GTChiralFermion_Technical | 5a | GT chiral fermion, Onsager algebra, Z₁₆ classification |
| Phase5a_GTChiralFermion_Stakeholder | 5a | GT model for non-specialists |
| Phase5b_Synthesis_Technical | 5 | κ-scaling, polariton, categorical infrastructure, Drinfeld double |
| Phase5b_Synthesis_Stakeholder | 5 | Phase 5 results for non-specialists |
| Phase5b_SMAnomalyDrinfeld_Technical | 5b | SM anomaly in Z₁₆, Drinfeld center computation |
| Phase5b_SMAnomalyDrinfeld_Stakeholder | 5b | SM anomaly for non-specialists |
| Phase5b_ModularGeneration_Technical | 5b | Modular invariance → generation constraint |
| Phase5b_ModularGeneration_Stakeholder | 5b | Modular generation for non-specialists |
| Phase5b_QuantumGroup_Technical | 5b | First quantum group U_q(sl₂) formalization |
| Phase5b_QuantumGroup_Stakeholder | 5b | Quantum group for non-specialists |
| Phase5c_HopfAlgebra_Technical | 5c | Hopf algebra on U_q(sl₂), coproduct/counit/antipode |
| Phase5c_HopfAlgebra_Stakeholder | 5c | Hopf algebra for non-specialists |
| Phase5c_SU2kFusion_Technical | 5c | SU(2)_k fusion rules, S-matrix, Ising/Fibonacci |
| Phase5c_SU2kFusion_Stakeholder | 5c | SU(2)_k fusion for non-specialists |
| Phase5c_E8Rokhlin_Technical | 5c | E8 lattice, algebraic Rokhlin, spin bordism |
| Phase5c_E8Rokhlin_Stakeholder | 5c | E8/Rokhlin for non-specialists |
| Phase5d_TetradGap_Technical | 5d | Tetrad gap equation, NJL-type gap solver |
| Phase5d_TetradGap_Stakeholder | 5d | Tetrad gap equation for non-specialists |
| Phase5d_Polariton_Technical | 5d | Polariton analog Hawking, stimulated amplification |
| Phase5d_Polariton_Stakeholder | 5d | Polariton analog Hawking for non-specialists |
| Phase5d_MTC_Technical | 5d | Ising/Fibonacci MTC instances, F-symbols |
| Phase5d_MTC_Stakeholder | 5d | MTC for non-specialists |
| Phase5e_BraidedMTC_Technical | 5e | Braided MTC: Ising/Fibonacci hexagon, ribbon, knot invariants |
| Phase5e_BraidedMTC_Stakeholder | 5e | Braided MTC for non-specialists |
| Phase5k-5p_TQFT_TQC_Technical | 5k-5p | WRT TQFT, TQC, generic quantum groups, SPT, Muger center, Fibonacci universality |
| Phase5k-5p_TQFT_TQC_Stakeholder | 5k-5p | TQFT/TQC for non-specialists |
| Phase5q_Ext_Technical | 5q | Ext computation over A(1), bordism hypotheses |
| Phase5q_Ext_Stakeholder | 5q | Ext computation for non-specialists |
| Phase6c1_StrongCPDarkEnergy_Technical | 6c.1 | Zhitnitsky $\rho_{DE} \sim \Lambda_{QCD}^6/M_P^2$, EDM bound, Z₁₆ pillar, one-mechanism falsifier |
| Phase6c1_StrongCPDarkEnergy_Stakeholder | 6c.1 | Strong-CP / cosmological-constant double-fine-tuning bridge for non-specialists |
| Phase6c3_EquivalencePrinciple_Technical | 6c.3 | 6×3 EP-violation matrix, `violatesAt_mono`, MICROSCOPE / STEP quantitative anchors |
| Phase6c3_EquivalencePrinciple_Stakeholder | 6c.3 | EP discriminator for vestigial vs non-vestigial DM mechanisms |
| Phase6c4_QECHolography_Technical | 6c.4 | Hayden-Preskill on horizon MTC; Fibonacci minimal admissible; trivial-abelian falsifier |
| Phase6c4_QECHolography_Stakeholder | 6c.4 | Black-hole information recovery + anyon-spectrum picture for non-specialists |
| Phase6c5_RTCasiniHuerta_Technical | 6c.5 | Classical RT vs Kaul-Majumdar knife-edge; Sen non-universality witness |
| Phase6c5_RTCasiniHuerta_Stakeholder | 6c.5 | Why log corrections to BH entropy matter for non-specialists |
| Phase6d1_CenterSymmetry_Technical | 6d.1 | ℤ_N center, Polyakov-loop biconditionals, Svetitsky-Yaffe ν, KSS / Walker-Wang window |
| Phase6d1_CenterSymmetry_Stakeholder | 6d.1 | Confinement, universality, perfect-fluid bound for non-specialists |
| Phase6d2_ChiralSSB_Technical | 6d.2 | Quark condensate (FLAG-2021), GMOR at PDG to 1 part in 10⁴, contrapositive falsifier |
| Phase6d2_ChiralSSB_Stakeholder | 6d.2 | Where the proton's mass actually comes from + GMOR identity |
| Phase6d3_CFL_Technical | 6d.3 | CFL emergent ℤ_3 ≡ QCD center ℤ_3 correctness-push (THE Phase 6d anchor) |
| Phase6d3_CFL_Stakeholder | 6d.3 | Color-flavor-locked dense-matter phase + cross-derivation ℤ_3 coincidence |
| Phase6e1_HeatKernelExpansion_Technical | 6e.1 | Seeley-DeWitt a₀/a₂/a₄ Christensen-Duff; Decision-Gate-E.2 calibration to 6a.1 G_N_sakharov; biconditional vs α_ADW |
| Phase6e1_HeatKernelExpansion_Stakeholder | 6e.1 | "How Newton's constant arises from a fermion fluid" — heat-kernel intuition + Sakharov-Adler scale anchor |
| Phase6e2_HigherCurvatureStructure_Technical | 6e.2 | Stelle (α, β, γ) basis change from Wave 1 a₄ Christensen-Duff; correctness-push vs LIGO/SRG/pulsar/Cassini observational ceilings |
| Phase6e2_HigherCurvatureStructure_Stakeholder | 6e.2 | "Why the next-order curvature corrections are tiny" — basis-change intuition + 62-orders-below-pulsar narrative |

**Convention:** Technical mirrors paper structure. Stakeholder teaches the physics. All import from `src/` modules (no inline formula redefinition). All figure cells tagged `# viz-ref: fig_<name>`.

---

## 5. PAPER DRAFTS (34 papers + 1 short formalization note + prediction tables)

> **2026-04-28 Phase 6 retrofit.** All seven Phase-6 papers (paper32, paper34,
> paper35, paper36, paper37, paper38, note_rt_ch_bounds) now use the
> `\input{counts.tex}` macro pattern for theorem / test / module counts (14
> new macros introduced: `\strongCpDeThms`, `\strongCpDeTests`, `\epThms`,
> `\epTests`, `\qecHolographyThms`, `\qecHolographyTests`, `\centerSymmThms`,
> `\centerSymmTests`, `\chiralSsbThms`, `\chiralSsbTests`, `\cflThms`,
> `\cflTests`, `\rtChThms`, `\rtChTests`); count-literal drift between abstract
> and §formalization values is eliminated permanently. `update_counts.py`
> extended with `_module_thm_count_strict` (BOL-anchored to avoid
> over-counting docstring "lemma" prose) + a `_pytest_count` helper. Stage 9
> figure-reviewer + Stage 10 claims-reviewer + Stage 13 adversarial-reviewer
> findings driven into prose: e.g. paper32 §5 prose now discloses
> `H_BothActiveGivesInconsistency` is a tracked-Prop predicate; paper35 §7
> prose discloses `S_horizon` parameter and that proof uses only the
> bundle's `areaLeading` field; paper36 §V prose now cites
> `walker_wang_witness_at_kss_lower` boundary witness alongside the two
> falsifiers; paper34 abstract "within reach" → "at the projected design
> sensitivity discussed for STEP-class satellite missions"; orphan bibitems
> cleared. Earlier 2026-04-26 sync added paper16a (graphene SK-EFT),
> paper16b (WRT TQFT), paper17 (dark sector), paper18 (doublon gate),
> paper20 (scalar rung), paper21 (Majorana rung), paper22 (EW phase
> transition), paper23 (linearized EFE), paper25 (gravitational waves),
> paper26 (BH entropy), paper27 (BH thermodynamics four laws), paper29
> (BBN unified).

| Paper | Format | Topic |
|-------|--------|-------|
| paper1_first_order | PRL | First-order SK-EFT: δ_diss = Γ_H/κ |
| paper2_second_order | PRD | Second-order + CGL + counting formula |
| paper3_gauge_erasure | PRL | Non-Abelian gauge erasure theorem |
| paper4_wkb_connection | PRD | Exact WKB connection formula |
| paper5_adw_gap | PRD | ADW mean-field gap equation |
| paper6_vestigial | PRD | Vestigial metric phase + analytical susceptibility + RHMC production (L=4 done, L=8 in flight) |
| paper7_chirality_formal | PRD/CPC | GS no-go formal verification + TPF evasion in Lean 4 |
| paper8_chirality_master | PRL | Three-pillar chirality wall: GS + GT + Z₁₆ + FK 2+1D evidence |
| paper9_sm_anomaly_drinfeld | PRL | SM anomaly in Z₁₆ + Drinfeld center formalization |
| paper10_modular_generation | PRD | Modular invariance → generation constraint N_f ≡ 0 mod 3 + Ext computation |
| paper11_quantum_group | PRD | Quantum group formalization: U_q(sl₂), U_q(sl₃), generic U_q(𝔤) with HopfAlgebra instances |
| paper12_polariton | PRL | Polariton analog Hawking: stimulated amplification protocol |
| paper14_braided_mtc | PRD | Braided MTC formalization: Ising/Fibonacci hexagon, ribbon, knot invariants + Muger general theorem |
| paper15_methodology | PRD | Methodology paper: Lean 4 + Aristotle verification pipeline + knowledge-graph + readiness state machine |
| paper16_graphene_sk_eft | — | Analog Hawking Radiation in the Graphene Dirac Fluid — SK-EFT predictions for the Dean-group sonic-horizon platform |
| paper16_wrt_tqft | — | From Surgery to Invariants: The First Formalization of the WRT TQFT Pipeline in Lean 4 |
| paper17_dark_sector | — | Dark Sector Connections from Emergent Gravity: hidden-sector DM classification, SFDM merger forecast, Gibbs–Duhem and q-theory no-go theorems |
| paper18_doublon_gate | — | Formal Verification of a Geometric Quantum Gate: the Fermi-Hubbard doublon Berry-phase SWAP in Lean 4 |
| paper20_scalar_rung | — | Scalar, Tetrad, and Majorana Condensates on a Single Fermionic Substrate (Phase 5z W1) |
| paper21_majorana_rung | PRD | Majorana-rung interpretation of sterile-neutrino seesaw — Embedding III (Phase 5z W2/2a/2b) |
| paper22_ew_phase_transition | — | Electroweak phase-transition substrate bridge (Phase 6 supporting) |
| paper23_linearized_efe | — | Linearized Einstein equations from ADW microscopic theory + Vergeles structural Props (Phase 6a Track A Wave 1) |
| paper25_gravitational_waves | PRD | Gravitational-wave propagation: c_GW = c·√χ_vest, GW170817 falsification (Phase 6a Track B Wave 2) |
| paper26_bh_entropy | PRD | Bekenstein-Hawking entropy — Kaul-Majumdar SU(2)_k closed form + Outcome-3 tracked-hypothesis horizon BC + log-decomposition (Phase 6a Track C Wave 3) |
| paper27_bh_thermodynamics_four_laws | PRD (6p) | BCH four laws of black-hole mechanics in two regimes — Schwarzschild vs ADW-Extremality, M_c partition (Balbinot 2005 BEC-acoustic + Hawking 1975 Schwarzschild primary anchors) (Phase 6a Track C Wave 5) |
| paper29_bbn_unified | — (4p) | BBN-unified DM-candidate classification — N_eff-mediated failure surface for Phase 5x candidates (Phase 6b Wave 1) |
| paper32_strong_cp_de | note (3p) | Strong-CP ↔ topological dark energy: Van Waerbeke-Zhitnitsky 2025 mechanism, ρ_DE = Λ_QCD^6/M_P^2 ≈ 6.71e-9 eV⁴ (Phase 6c Wave 1) |
| paper34_equivalence_principle | note (4p) | Equivalence-principle violation matrix: project's EP-violation surface is vestigial-only (Phase 6c Wave 3) |
| paper35_qec_holography | note (3p) | QEC ↔ holography: Hayden-Preskill on the W3 HorizonMTCBC substrate (Phase 6c Wave 4) |
| paper36_center_symmetry | note (4p) | Center-symmetry confinement: ℤ_N 1-form unbreaking, Polyakov loop, Svetitsky-Yaffe, KSS bound, Walker-Wang transport (Phase 6d Wave 1) |
| paper37_chiral_ssb | note (3p) | Chiral SSB / GMOR: WetterichNJL scalar = ⟨q̄q⟩, PDG/FLAG numerical match at ~1 part in 10⁴ (Phase 6d Wave 2) |
| paper38_cfl | note (3p) | CFL chiral Lagrangian: emergent ℤ_3 ≡ QCD-center ℤ_3 generator agreement (Phase 6d Wave 3 — Phase 6d CLOSED) |
| note_rt_ch_bounds | short note (3p) | Ryu-Takayanagi + Casini-Huerta as external-hypothesis tracked Props; structural inconsistency with W3 Kaul-Majumdar (Phase 6c Wave 5) |
| paper39_heat_kernel_expansion | long-form (4p) | Heat-kernel a₀/a₂/a₄ Christensen-Duff coefficients; Decision-Gate-E.2 calibration `G_N_from_a2_eq_G_N_sakharov`; biconditional vs α_ADW (Phase 6e Wave 1) |
| paper40_higher_curvature | formalization (3p) | Higher-curvature structure: Wave 1 a₄ → Stelle `{R², C², 𝒢}` basis change; sign-definite (α, β, γ); correctness-push vs LIGO/pulsar/SRG/Cassini observational ceilings (Phase 6e Wave 2) |
| experimental_predictions | Tables | Platform spectral predictions |
| AutomatedReviews/ | Stage 13 outputs | Per-paper adversarial-reviewer findings (Opus fresh context); auto-ingested as ReviewFinding nodes by `scripts/build_graph` |

**Key numerical claims (all traced to formulas.py via CHECK 14):**
- δ_diss ~ 10⁻⁵–10⁻³ (Paper 1, BEC); δ_diss ~ 10⁻¹³ negligible vs. dispersive (Paper 16a, graphene)
- δ^(2)(ω) ∝ ω³ (Paper 2)
- U(1) only SM survivor (Paper 3)
- Noise floor = δ_diss / (1 − δ_diss) (Paper 4)
- G_c = 8π² / (N_f Λ²) (Paper 5)
- Vestigial window: G/G_c ≈ 0.8–1.0 in mean-field (Paper 6); closed-form `w_vest(τ) = (1−τ²)/(5τ²−1)` (Phase 5y)
- `w_vac = −1` locked by Lorentz + Gibbs–Duhem for any single-scalar self-tuning emergent vacuum (Paper 17 structural claim)
- SFDM merger sonic-boom stacked ≥ 30 → 3.5–5.7σ Euclid × Roman; first 3σ ~2028 (Paper 17 money plot)
- T_H ≈ 2.4 K for Dean bilayer graphene nozzle (Paper 16a)
- Minimal Berry-phase theorem: accumulated phase = −1 on π-sweep closed path (Paper 18)

---

## 6. TEST FILES (89 files, 3728 fast + 66 slow tests)

> **2026-04-28 `slow` marker retrofit.** Three modules tagged
> `pytestmark = pytest.mark.slow` because they each call `load_lean_deps()`
> (directly or via `scripts/build_graph.py`), which re-triggers Lean
> `ExtractDeps.lean` walking 4385+ declarations (5–10 min per call):
> `tests/test_extract_lean_deps.py`, `tests/test_build_graph.py`,
> `tests/test_graph_integrity.py`. `pyproject.toml` declares
> `addopts = "-m 'not slow'"` so default `uv run pytest tests/` runs only the
> fast suite (3254 passed in ~2s). For wave-close / pre-submission the full
> suite runs via `uv run pytest tests/ -m '' -v` (~10 min). Two
> torch-dependent modules (`tests/test_hs_rhmc.py`,
> `tests/test_stencil_dirac.py`) switched to `pytest.importorskip("torch")`
> so they auto-skip cleanly without env-failure noise.

| Test File | Tests | Covers |
|-----------|-------|--------|
| test_transonic_background | 12 | BEC parameters, background solver, corrections |
| test_second_order | 12 | Enumeration, coefficients, WKB |
| test_cgl_derivation | 26 | CGL FDR, kernel decomposition, boundary terms |
| test_cross_validation | 7 | Wraps validate.py 15 checks |
| test_lean_integrity | 9 | Module presence, toolchain, zero sorry |
| test_third_order | 36 | Third-order enumeration, parity structure |
| test_gauge_erasure | 25 | Erasure theorem, SM analysis |
| test_wkb_connection | 65 | Connection formula, Bogoliubov, spectrum |
| test_adw | 78 | Gap equation, NG modes, fluctuations |
| test_ginzburg_landau | 75 | GL expansion, He-3 analogy |
| test_experimental | 54 | Prediction tables, shot counts, kappa-scaling, polariton |
| test_chirality | 93 | GS 9 conditions, TPF evasion, lattice framework, no-go structure |
| test_fracton | 110 | SK-EFT, information retention |
| test_fracton_gravity | 146 | Bootstrap, DOF gap, non-Abelian |
| test_vestigial | 159 | Mean-field, MC, 3-phase structure, SU(2), TRG, 4D fermion-bag, NJL, susceptibility |
| test_backreaction | 76 | Cooling, extremality, timescales |
| test_layer1 | 84 | Categorical infrastructure, fusion rules, Drinfeld double, quantum dimensions |
| test_gauge | 146 | SO(4) gauge, quaternion algebra, fermion-bag, Majorana, RHMC infrastructure |
| test_hs_rhmc | 32 | HS+RHMC: Zolotarev, multi-shift CG, forces, heatbath, torch backend |
| test_z16 | — | Z₁₆ classification, anomaly computation |
| test_onsager | — | Onsager algebra, Dolan-Grady, Davies isomorphism |
| test_contraction | — | Inönü-Wigner contraction, rescaling |
| test_smg | — | SMG classification, tenfold way |
| test_steenrod | — | Steenrod A(1), Adem relations |
| test_gt_model | — | GT chiral fermion model |
| test_gioia_thorngren | — | Gioia-Thorngren analysis |
| test_drinfeld_algebra | — | Drinfeld double algebra/ring |
| test_sm_anomaly | — | SM anomaly computation |
| test_modular_invariance | — | Modular invariance constraint |
| test_build_graph | — | Knowledge graph extraction |
| test_rokhlin_bridge | — | Rokhlin bridge verification |
| test_q_numbers | — | q-integer properties |
| test_extract_lean_deps | — | Lean dependency extraction |
| test_graph_integrity | — | Knowledge graph integrity |
| test_uqsl2_hopf | 27+ | U_q(sl₂) Hopf algebra: coproduct, counit, antipode |
| test_su2k_fusion | 29+ | SU(2)_k fusion rules at k=1,2,3 |
| test_affine_quantum | — | Affine quantum group, restricted u_q, S-matrix |
| test_e8_rokhlin | 24 | E8 lattice, algebraic Rokhlin (Serre mod 8), spin bordism, Wang chain |
| test_tetrad_gap | — | Tetrad gap equation Lean formalization tests |
| test_tetrad_gap_solver | — | Tetrad gap solver, NJL-type gap equation, Δ*(G) curve |
| test_verified_statistics | — | Verified statistical estimators |
| test_a1_ext | 29 | Ext computation over A(1) + hypothesis decomposition |
| test_fk_interface | 16 | FK gapped interface + Muger general theorem |
| test_generate_a1_resolution | — | A(1) resolution cross-validation |
| test_paper_provenance_v2 | 16 | **Phase 5v Wave 10 strengthening** — Wave 10b mark / rebuild_prose_state, Wave 10c change-bus / triggered_by / node_id_for / prune (refusal + dry-run + keep-records), Wave 10f cluster_detect (exact match + intra-paper-dup behavior), cross-precision sentence_is_stale. tmp_path-isolated fixtures via `scripts/test_helpers.py`. 30ms full-suite runtime. |

---

## 7. SCRIPTS

| Script | Lines | Purpose |
|--------|-------|---------|
| validate.py | — | **17** cross-layer validation checks (incl. parameter_provenance, counts_fresh, tables_fresh, claim_clusters_fresh, graph_integrity, readiness_submission_gate) |
| review_figures.py | 1205 | Generate 113 PNGs + structural checks + manifest |
| submit_to_aristotle.py | 466 | Aristotle submission/retrieval/integration |
| run_vestigial_production.py | 709 | Multiprocessing production MC runner (fermion-bag, L=4,6,8) |
| run_rhmc_production.py | 239 | RHMC production runner (Rust backend, checkpoint/resume) |
| run_majorana_production.py | 281 | Majorana fermion-bag production runner (W7B) |
| provenance_dashboard.py | — | Datastar+Flask 10-tab provenance command center (Parameters, Formulas, Proof Architecture, Citations, Knowledge Graph, Paper Readiness, Process Health, Research Status, Paper Provenance v2 — 3-column sentence-level UI w/ keyboard nav, change-bus, cluster propagation; legacy Paper Contributions retired Wave 10g, redirects to Paper Provenance) |
| view_vestigial_mc.py | 639 | MC results viewer and analysis dashboard |
| analyze_majorana_results.py | 241 | Majorana MC results analysis |
| benchmark_rust_parallel.py | 133 | Rust RHMC backend benchmarking |
| test_pseudofermion_convention.py | 262 | Empirical pseudofermion convention test (W7C-fix) |
| generate_a1_resolution.py | — | A(1) resolution cross-validation (Python↔Lean) |
| build_graph.py | — | Knowledge graph extraction (25 node types, 25 edge types — Wave 10b adds Sentence/AuditEvent/ClaimCluster + BACKED_BY/LOGGED_BY/MEMBER_OF) |
| extract_lean_deps.py | — | Lean dependency taxonomy extraction |
| graph_integrity.py | — | Knowledge graph integrity queries (Wave 10b adds 6 sentence-level checks: chain_complete, id_collisions, audit_event_logged_by, audit_event_actor_well_formed, claim_cluster_consistency, last_modified_monotonicity) |
| **sentence_state.py** | — | **Phase 5v Wave 10b** — sole writer to `papers/<paper>/prose_state.json` + `audit_log.jsonl`. Subcommands: mark / validate / normalize-quote / ingest_agent_run / supersede / tombstone-sweep / reconcile / **rebuild_prose_state** (Wave 10 strengthening — replay-canonical recovery from cmd_mark partial-failure). Lock-then-append-then-atomic-write per write. Content-hash sentence IDs. |
| **verification_state.py** | — | **Phase 5v Wave 10c** — append-only `docs/verification_log.jsonl` writer + library API. Cross-tab change-bus: parameter/citation/axiom/hypothesis/aristotle/production verification events flow through `record_event` (with optional `triggered_by` for cross-sentence provenance) → `apply_to_graph` → `last_modified_explicit` propagation. Subcommands: record / list / apply / **prune** (Wave 10 strengthening — `--keep-days N` / `--keep-records N` / `--before <ISO>` with refuse-no-criterion safety net + `--archive-to`). 1MB read-time WARN. |
| **last_modified.py** | — | **Phase 5v Wave 10b/c** — freshness propagation across dependency edges (USED_BY, VERIFIED_BY, DEPENDS_ON_AXIOM, ASSUMES, IMPORTS, CITES, GROUNDED_IN, BACKED_BY, VERIFIES). Cross-precision-safe ISO timestamp comparison via datetime parsing (Wave 10 strengthening — fixed string-compare bug where 'Z' > '.' inverted ordering across precisions). |
| **cluster_detect.py** | — | **Phase 5v Wave 10f** — sole producer of `papers/claim_clusters.json`. Walks v2 `claims_review.json` files; emits exact-match clusters (sha8 of normalized quote) + normalized-match clusters (NFKC + punctuation-stripped). Cross-paper requirement: ≥2 distinct papers per cluster. |
| **test_helpers.py** | — | **Phase 5v Wave 10 strengthening** — context managers (`isolated_papers_root` / `isolated_verification_log` / `isolated_v2_state`) + fixture builders (`make_v2_sentence` / `make_v2_review`). Used by `tests/test_paper_provenance_v2.py`; ad-hoc smoke tests can opt in too. |
| update_counts.py | — | Regenerate `docs/counts.json` + `docs/counts.tex` from canonical sources |
| qi_register.py | — | Regenerate `docs/QI_REGISTER.md` from current ReviewFinding nodes |
| sync_graph_to_pg.py | — | Idempotent PG+AGE sync of full graph (Wave 9f) |
| render_paper_html.py | — | Pandoc-free LaTeX→HTML for paper bodies (Wave 9g; Wave 10d-7 extended for block envs) |
| render_paper_tables.py | — | Per-paper auto-generated `tables/*.tex` from `papers/<key>/tables.py` specs |
| readiness_gates.py | — | Per-paper × per-gate state evaluators (11 gates × 18 papers; Wave 4) |
| citation_cache.py | — | 90-day citation verification cache (Stage 13 amortizer) |
| datastar_helpers.py | — | Flask glue for Datastar SSE (`is_datastar_request` / `read_signals` / `sse_response` / `esc`) |

---

## 8. CONFIGURATION FILES

| File | Purpose |
|------|---------|
| pyproject.toml | Project metadata, dependencies (numpy, scipy, plotly, pandas, sympy, kaleido, aristotlelib) |
| uv.lock | uv package manager lock file |
| .python-version | Python >=3.14 |
| lean/lakefile.toml | Lean Lake build config (depends on Mathlib) |
| lean/lean-toolchain | v4.29.0 |
| lean/lake-manifest.json | Lean package manifest |
| .env | ARISTOTLE_API_KEY (not committed) |
| .gitignore | Excludes __pycache__, .venv, .env, figures/*.html, data/ |

---

## 9. DOCUMENTATION

### Reference Documents
| Document | Location | Purpose |
|----------|----------|---------|
| WAVE_EXECUTION_PIPELINE.md | docs/ | **Mandatory** 12-stage execution process |
| Theorm_Proving_Aristotle_Lean.md | docs/references/ | Aristotle API reference (read before every session) |
| Feasibility Study | docs/ | Top-level feasibility assessment |
| Critical Review v3 | docs/ | Consolidated evidence evaluation |

### Roadmaps

All roadmaps live in `docs/roadmaps/`. Each phase has its own file; Phase 6 has three (forward-looking) files. Status reflects the roadmap's own closure verdict as of 2026-04-24.

| Document | Status / one-line summary |
|----------|---------------------------|
| Phase1_Roadmap.md | Complete — first-order SK-EFT corrections |
| Phase2_Roadmap.md | Complete — second-order EFT + WKB + CGL FDR |
| Phase3_Roadmap.md | Complete — gauge erasure, exact WKB, ADW, vestigial |
| Phase4_Roadmap.md | Complete (Wave 5 included) — fracton + experimental predictions |
| Phase5_Roadmap.md | Complete — Monte-Carlo core + categorical scaffolding + W7C RHMC (L=4 done, L=8 in flight) |
| Phase5a_Roadmap.md | Complete — Onsager algebra, GT chiral fermion, Z₁₆ chirality wall 1+1D |
| Phase5b_Roadmap.md | Complete — SM anomaly, Drinfeld center, modular generation, first quantum group |
| Phase5c_Roadmap.md | Complete — Hopf algebra, SU(2)_k, E8, Rokhlin, verified statistics |
| Phase5d_Roadmap.md | Complete — tetrad gap, Ising/Fibonacci MTC, polariton |
| Phase5e_Roadmap.md | Complete — braided MTCs, knot invariants, affine Hopf, higher-k unitarity |
| Phase5f_Roadmap.md | Complete — TQFT partition functions + emergent-gravity bounds |
| Phase5g_Roadmap.md | Partial — matrix-free CG unlocked L=12; Mathlib PR infrastructure scoped |
| Phase5h_Roadmap.md | Complete — chirality wall 3+1D: SPT classification + gauging step |
| Phase5i_Roadmap.md | Complete — first rank-2 quantum group U_q(sl₃) + SU(3)_k fusion |
| Phase5j_Roadmap.md | Complete — Fermi-point topological charge → emergent gauge group |
| Phase5k_Roadmap.md | Complete — WRT TQFT pipeline (Temperley–Lieb → surgery → invariant) |
| Phase5l_Roadmap.md | Complete — Topological quantum computation from verified MTCs |
| Phase5m_Roadmap.md | Complete — Generic parameterized `QuantumGroup k A` + Kac–Walton |
| Phase5n_Roadmap.md | Partial (Wave 1 done) — chirality-wall anomaly inflow + Villain + SPT stacking |
| Phase5o_Roadmap.md | Complete — Community-value outputs: lean-tensor-categories extraction, experimental bridging |
| Phase5p_Roadmap.md | Complete — Muger center, FP-dimension, modularity bridge (Direction 1) |
| Phase5q_Roadmap.md | Complete — Ext computation over A(1): first in any proof assistant |
| Phase5r_Roadmap.md | Complete — H2 discharged via change-of-rings; H3/H4 assessed as irreducibly topological |
| Phase5s_Roadmap.md | Complete (W2-5, W8) — FK 2+1D gapped interface, general modularity, instanton zero modes; Wave 8 q-Serre closure via hypothesis refactor |
| Phase5t_Roadmap.md | Complete — Fermi-Hubbard doublon geometric SWAP + minimal Berry-phase theorem (Paper 18) |
| Phase5u_Roadmap.md / Phase5u_Paper_Revision_Roadmap.md | Substantive track closed — paper revision cycle (Paper 1 dimensional bug, Paper 12 Falque parameters, Paper 3/10 textbook + bibliography corrections); process track (Waves 14-24, agent infrastructure) deferred |
| Phase5v_Roadmap.md | Phase 1 complete — knowledge-graph foundation fixed (+302 recovered decls), counts wiring live; Phase 2 (PG+AGE migration) + Phase 3 (11-gate readiness state machine) + Phase 4 (Stage 13 adversarial, Stage 14 QI register) scoped |
| Phase5w_Roadmap.md | W1 + W10c complete (deep research, greybody + quasi-1D validation); W2-9 scoped — graphene Dirac-fluid platform (Paper 16a) |
| Phase5x_Roadmap.md | W1 + W1b complete (6 + 3 deep-research rounds) — dark-sector connections: ℤ₁₆ hidden sector DM, ADW CC (DESI Level D tension), Fang-Gu torsion DM, SFDM SK-EFT + merger forecast, vestigial relics (blocked on MC), fracton DM (upgraded to VIABLE post-drilldown); Paper 17 integrates |
| Phase5y_Roadmap.md | Complete — terminal closure (2026-04-23): Gibbs–Duhem emergent-vacuum obstruction + q-theory no-go + four-factor orthogonality + closed-form vestigial EOS; no paper per user preference, harvest into Lean |
| Phase6_Roadmap.md | Planning — HPC-dependent vestigial MC at L=12+ (Path A sparse CG, Path B Metal, Path C CUDA), experimental engagement, polariton Tier 2-3 EFT |
| Phase6_Deferred_Targets.md | Continuously updated — 56 completed items + Phase-6-tier Tier 1/2 targets |
| Phase6_VerifiedStatistics_Roadmap.md | Forward — formal-verification extension of the statistics pipeline |

### Stakeholder Documents

Located in `docs/stakeholder/`. Plain-language overview: `companion_guide.md`. Per-phase Implications + Strategic Positioning pairs for Phases 1, 2, 3, 4, 5, 5a, 5b, 5c, 5d, 5e, 5i. Phase 5y uses a closure-summary pattern instead: `Phase5y_Closure_Summary.md` plus four cross-phase impact notes (`Phase5y_Impact_on_5d.md`, `Phase5y_Impact_on_5u.md`, `Phase5y_Impact_on_5w.md`, `Phase5y_Impact_on_5x.md`).

Three arc-consolidation pairs cover the phases between 5f and 5x that don't have dedicated per-phase pairs:
- `Phase5f-5p_LatticeToTQC_Implications.md` + `Phase5f-5p_LatticeToTQC_Strategic_Positioning.md` — TQFT partitions, WRT pipeline, Temperley–Lieb / Jones–Wenzl, generic `QuantumGroup k A` + Kac–Walton, Muger center + FP-dim (Phases 5f, 5k, 5l, 5m, 5p).
- `Phase5h-5s_ChiralityBordism_Implications.md` + `Phase5h-5s_ChiralityBordism_Strategic_Positioning.md` — chirality-wall 3+1D extension, Fermi-point → emergent gauge, anomaly inflow, Ext over A(1), change-of-rings discharge, FK 2+1D gapped interface, general modularity, instanton counting (Phases 5h, 5j, 5n, 5q, 5r, 5s).
- `Phase5t-5x_NewChains_Implications.md` + `Phase5t-5x_NewChains_Strategic_Positioning.md` — three new proof chains: Fermi-Hubbard geometric gate, graphene Dirac-fluid platform, dark-sector connections (Phases 5t, 5w, 5x).

Infrastructure/process phases are covered by a single retrospective memo: `Phase5_Infrastructure_Retrospective.md` (Phases 5g matrix-free CG, 5o community-value extraction, 5u paper revision cycle, 5v knowledge-graph foundation).

### Analysis Documents
| Document | Location | Topic |
|----------|----------|-------|
| gravity_hierarchy_synthesis.md | docs/analysis/ | Three-phase vestigial structure |
| fracton_layer2_assessment.md | docs/analysis/ | Fracton vs standard hydro comparison |
| chirality_wall_analysis.md | docs/analysis/ | GS no-go condition analysis |

### Validation
| Document | Location | Status |
|----------|----------|--------|
| lean_quality_audit.md | docs/validation/ | Wave 5 theorem quality audit |
| VALIDATION_REPORT.md | docs/validation/ | Phase 2 validation snapshot (archived) |
| reports/*.json, *.txt | docs/validation/reports/ | Timestamped validation run archives |

---

## 10. KEY FORMULAS (all in `src/core/formulas.py` with Lean refs)

### Acoustic Metric & Hawking Temperature
- ds² = (n/c_s)[-(c_s²-v²)dt² - 2v·dt·dx + dx²]
- κ = |dv/dx - dc_s/dx| at horizon
- T_H = ℏκ/(2πk_B) — Lean: `hawking_temp_from_surface_gravity`

### First-Order SK-EFT
- δ_diss = Γ_H/κ — Lean: `firstOrder_positivity`
- Γ_H = (γ₁+γ₂)·(κ/c_s)² — Lean: `dampingRate_firstOrder_nonneg`

### Second-Order SK-EFT
- count(N) = floor((N+1)/2) + 1 — Lean: `transport_coefficient_count`
- γ_{2,1} + γ_{2,2} = 0 — Lean: `combined_positivity_constraint`
- δ^(2)(ω) ∝ (ω/Λ)³ — Lean: `secondOrder_vanishes_on_shell_with_positivity`

### Dispersive Correction
- δ_disp = -(π/6)·D² — Lean: `dispersive_correction_bound`
- D = κξ/c_s (adiabaticity)

### Exact WKB
- Decoherence parameter = 2Γ_H/(κ(1-Γ_H/κ)) — Lean: `decoherence_nonneg`
- Noise floor = δ_diss/(2(1-δ_diss)) — Lean: `noise_floor_nonneg`

### ADW Gravity
- G_c = 8π²/(N_f·Λ²) — Lean: `critical_coupling_pos`
- d²V_eff/dC²|_{C=0} = 1/G - N_f·Λ²/(8π²) — Lean: `curvature_zero_at_Gc`
- Broken generators: d²-1 — Lean: `broken_generators_4d`
- Graviton polarizations: d(d-3)/2 — Lean: `graviton_pol_4d`

### Vestigial Phase Classification
- Pre-geometric: curvature > 0.3 × curvature_max (weak coupling)
- Vestigial: curvature < 0.3 × curvature_max, C = 0 (near G_c)
- Full tetrad: C > 0 (above G_c) — Lean: `pos_C_gives_full_tetrad`

### Fracton Hydro
- Fracton charges: C(d+N-1, N) — Lean: `fracton_charges_monotone`
- Standard charges: C(d+N-1, N) for N=1 — Lean: `fracton_exceeds_standard_general`

### Kappa-Scaling (Phase 5)
- δ_disp(κ) = -(π/6)(ξκ/c_s)² — Lean: `kappa_scaling_dispersive_quadratic`
- δ_diss(κ) = (γ₁+γ₂)κ/c_s² — Lean: `kappa_scaling_dissipative_linear`
- κ_cross = 6(γ₁+γ₂)/(πξ²) — Lean: `crossover_balance`

### Categorical Infrastructure (Phase 5)
- Quantum dimension: d_i = tr(id_{V_i}) — Lean: `quantumDim`
- Global dimension: D² = Σ_i d_i² — Lean: `globalDimSq_pos`
- Fusion multiplicity: (i⊗j) = Σ_k N^k_{ij} · k — Lean: `totalMult_unit`
- dim D(G) = |G|² — Lean: `dd_abelian_simples`
- Z(Vec_G) ≅ Rep(D(G)) — Lean: `gauge_emergence_statement`
- Chirality limitation: c ≡ 0 (mod 8) — Lean: `chirality_limitation_vecG`

---

## SUMMARY TABLE

| Category | Count | Status |
|----------|-------|--------|
| **Python Source Modules** | 130 | Complete (Phases 1–6p) |
| **Test Files** | 99 | 4179 pytest cases (counts.json 2026-05-19) |
| **Notebooks** | 87 | Phases 1–6p (Technical + Stakeholder) |
| **Lean Modules** | **367** | counts.json 2026-05-19. +45 over the post-Phase-6n-Session-29 322 baseline across Phase 6p R5.4 FKLW substrate (6 NEW modules under `lean/SKEFTHawking/FKLW/`: `SU2LieAlgebra.lean` + `SU2MatrixExp.lean` + `SU2LocalDiffeo.lean` + `SU2InteriorBridge.lean` + `FibonacciDensityConditional.lean` + `FibSU2LieBundle.lean`) + ancillary substrate. Sessions 49 + 50 + 51 ship entirely within existing `FibSU2LieBundle.lean` + `SU2LieAlgebra.lean` — no new modules. |
| **Lean Theorems** | **6645 (6620 substantive + 25 placeholder)** post-Session-51 [counts.json 2026-05-19 21:03 = 6613 pre-Session-49 + ~19 declarations from Session 49 FibSU2LieBundle commits + 6 substantive theorems from Session 50 SU2LieAlgebra §15 + FibSU2LieBundle §11 + §12 commits + 7 substantive theorems (and 1 noncomputable def) from Session 51 FibSU2LieBundle §13 + §14 commits; counts.json regen pending] | **0 sorry project-wide**, **0 axioms** (counts.json `axiom_names: []`; net discharge of `gapped_interface_axiom` and Phase 6p Wave 2c residual `aa_residual_interior_at_one_for_hom` via the R5.4 constructive substrate chain). Phase 6p Wave 2c.4a-R4.2.d.R5.4 FKLW Fibonacci SU(2) density program SHIPPED Sessions 30–51: 30 PUBLIC commits / ~2859 LoC / 6 NEW modules. Structural reduction chain `BCH-spanning witness → DenseInSpecialUnitary 3 2 ρ_Fib_SU2` CONNECTED end-to-end via Cartan-A/B/C/D + Layer E + Layers F.1–F.19; σ_Fib 3-bundle is now a BASIS of 𝔰𝔲(2) at every non-zero scalar multiple of `paulI_x` (Sessions 49 F.18 + F.19 lin-indep + Session 50 F.20.a + F.20.a-app + F.20.b spanning + scaled-spanning); BCH/IFT iteration substrate opened (Session 51 F.20.c.a `liePartMat` Ad-equivariance + F.20.c.b σ_Fib bundle commutativity with `liePartMat`). All kernel-only `[propext, Classical.choice, Quot.sound]`. Phase 6a/6b/6c/6d/6e/6f/6g/6j/6n/6o/6p cohort shipped end-to-end. |
| **Aristotle-proved** | 322+ | 45 runs (no Aristotle calls in Phase 6 — all interactive MCP closure) |
| **Paper Drafts** | 39 + 1 short formalization note + prediction tables | Phase 6 cohort uses `\input{counts.tex}` macroification; count-literal drift eliminated. |
| **Pipeline Figure Functions** | 138 in `visualizations.py` (138 PNGs in `figures/`) | All generated; Phase 6f Wave 1 added `fig_constant_K_riemann_dimension_factor` (scalar curvature `R = n(n-1) K` + Bianchi-residual heatmap on (K, asymmetry) plane); Phase 6f Wave 2 added `fig_einstein_tensor_trace_identity` (G^μ_μ = -R linearity + Λ-vacuum residual heatmap on (K, Λ-3K) plane). |
| **Validation Checks** | 25 | All passing (validate.py 25/25 PASS at last full run; CHECK 21 `bundle_consistency` introduced Phase 6i Wave 7) |
| **Scripts** | 20+ | validate, review_figures, submit_to_aristotle, 3 production runners, provenance_dashboard, generate_a1_resolution, sentence_state, verification_state, last_modified, cluster_detect, update_counts, qi_register, sync_graph_to_pg, render_paper_html, render_paper_tables, readiness_gates, citation_cache, datastar_helpers, build_graph, extract_lean_deps, graph_integrity, test_helpers |
| **Stakeholder Docs** | 22 | Phases 1–5x + arc-consolidation pairs |
| **Analysis Docs** | 3 | Vestigial, fracton, chirality |
| **Roadmaps** | 16+ Phase-5x roadmaps + Phase 6 family (Phase 6a Track A/B/C, Phase 6b, 6c, 6d, 6f) | Phase 6d CLOSED (Track A all three waves shipped); Phase 6c partial close (W1+W3+W4+W5 SHIPPED, W2 EWBaryogenesisChiralityWall remains); Phase 6a four tracks shipped (W1+W2+W3+W4+W5+W7), Track D (W6 PositiveMassTheorem) blocked on Phase 6f.1/6f.3 |

---

**Project Status (2026-04-30-0000):** Phase 6e Wave 2 (`HigherCurvatureStructure.lean`) shipped through Stage 12 + Wave 1 figure-reviewer fix pass applied. **4453 theorems** (4430 substantive + 23 placeholder), **1 axiom**, **0 sorry project-wide** across **191 modules**. 322 Aristotle-proved (44 runs; no Aristotle calls since Phase 6 — interactive MCP closure throughout). 79 test files (3374 fast + 66 slow tests; default suite ~2.7 s), 131 figure functions in `visualizations.py` (115+ PNGs in `figures/`), 111 Python modules, 35 papers + 1 short formalization note, 74 notebooks. Build CLEAN (8455/8455 jobs).

**Phase 6 closure metrics:** Phase 6a four tracks shipped (W1+W2+W3+W4+W5+W7); Phase 6b W1 shipped; Phase 6c CLOSED (W1+W2+W3+W4+W5); Phase 6d CLOSED (W1+W2+W3); Phase 6e W1+W2 shipped (`HeatKernelExpansion.lean`, `HigherCurvatureStructure.lean`); Phase 6f W3 shipped (Stage 1–2). Preemptive-strengthening discipline trend (11 waves; first-pass retroactive count): 6c.3 = 12 (no discipline) → 6b.1 = 5 (58 % reduction) → 6d.1 = 6 → 6d.2 = 4 → 6d.3 = 1 → 6c.1 = 2 → 6c.4 = 3 → 6c.5 = 3 → 6c.2 = 2 → 6e.1 = 2 → **6e.2 = 1** (best yet). The discipline catches obvious P2 / ∃-absorption / biconditional-tautology patterns; multi-pass review until two consecutive clean passes catches subtler P3 / P5 patterns (identity-function wrappers, within-own-±2σ-band tautologies, pairwise-distinctness on inductive constructors, definitional-unfolding-as-physics).

**Earlier project status (2026-04-15) — preserved for historical context:** Phase 5p Waves 1–5 (Direction 1) + **Wave 6 (concrete instances)** **COMPLETE** + Phase 5e Waves 7–8 **COMPLETE**. **3021 theorems** (2942 substantive + 79 placeholder), 1 axiom, **0 sorry project-wide** across **133 modules**. 322 Aristotle-proved (44 runs, all complete; subsequent gap closures via interactive MCP), 1723 tests, 101 figures, 53 Python modules, 15 papers, 48 notebooks. Build CLEAN (8397 jobs, 132 oleans + 1 lean_exe). validate.py 16/16 pass.

**Today's wave (2026-04-15) — four PRs merged:**
- **PR #10 (`da1b32c`) Phase 5e Waves 7–8**: per-generator squared antipode on U_q(ŝl₂); the Wave 8 spec `S² = Ad(K₀K₁)` was identified as mathematically wrong for affine ŝl₂ (degenerate Cartan matrix `[[2,-2],[-2,2]]` admits no single global K), corrected to per-generator form (20 new theorems in `Uqsl2AffineHopf.lean` Section 8 with inline historical note cross-referencing the distinct sl₃ correction at `Uqsl3Hopf.lean:3995`).
- **PR #11 (`d48fa6f`) Phase 5p Waves 3–4**: `MugerCenter C := ObjectProperty.FullSubcategory (IsTransparent C)` abbrev + `ObjectProperty.IsMonoidal` instance + `SymmetricCategory (MugerCenter C)` instance (the Müger payoff: Z₂(C) is symmetric even when ambient C is only braided, proved via the faithful-functor pullback `(ObjectProperty.ι _).map_injective`). Data-level `PreModularData.isRowTransparent` / `isMugerTrivial` predicates with `Decidable` instances. Bundled: `numba` xfail on `tests/test_gauge.py`.
- **PR #12 (`ae65e72`) Phase 5p Wave 5 (Direction 1)**: abstract bridge `PreModularData.modularImpliesMugerTrivial_proof` — det(S)≠0 → Müger trivial, via Mathlib `det_zero_of_row_eq` (already drafted in `ModularityTheorem.lean`). Three per-MTC instances (SU(2)_1, SU(2)_2/Ising, Fibonacci) via the bridge. New `fib_modular` proof in `FibonacciMTC.lean`. `isRowTransparent` redefined to vacuum-row form for normalized/unnormalized compatibility.
- **PR #13 (`da93f77`) Phase 5p Waves 1–2**: FPDimension via eigenvector approach (Wave 1 retroactively closed; the eigenvector approach is the recommended route per deep research). Wave 2 partial: SU(4)_1 (Z₄ pointed, all FPdim=1) + G₂_1 (Fibonacci fusion structure → FPdim=φ) certificates added. `phi_triple_origin` theorem unifies the three independent sources of φ across A₁ at level 1 (Fibonacci), A₁ at level 3 (SU(2)₃), and G₂ at level 1.
- **PR #14 (this PR) Phase 5p Wave 6 (concrete instances)**: New `D2Formula.lean` module — explicit Drinfeld-center dimension formula `D²(Z(C)) = D²(C)²` for both abelian (Vec_{ℤ/2} → toric code, D²=4=2²) and **non-abelian** (Vec_{S₃} → 8-anyon center, D²=36=6²). The non-abelian instance is the **first non-abelian Drinfeld-center dimension formula formalized in any proof assistant**. General-G statement deferred — needs Mathlib's Σ(dim ρ)² = |G| (currently a TODO upstream).

**Tranche E preserved (2026-04-14):** full **Bialgebra + HopfAlgebra typeclass instances** on U_q(sl₃) (commits `dadce3e` `bdf0ee9`) via palindromic Serre atom-bridge. Uqsl2AffineHopf 0-sorry (closed April 2026 via Phase 5s Wave 8). ExtractDeps refactored to filter by package module — reveals +138 theorems from Phase-4 physics modules (FermionBag4D, GaugeFermionBag, HubbardStratonovichRHMC, MajoranaKramers, QuaternionGauge, SO4Weingarten, VestigialSusceptibility, WetterichNJL).

**Open / next-up:** Phase 5p Wave 5 Direction 2 (Z₂ trivial → det(S)≠0) requires Müger Lemma 2.15 (S² = dim(C)·C) and is deferred. Phase 5p Wave 6 (D²(Z(C)) = D²(C)²) and Phase 5i Wave 4 (CyclotomicField generic refactor for Mathlib PR) are the highest-value follow-ups.
