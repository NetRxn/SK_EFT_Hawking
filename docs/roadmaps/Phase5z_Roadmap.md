# Phase 5z: Scalar Condensate Ladder — Higgs, Majorana, and EW Phase Transition on a Single Fermionic Substrate

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22). First new phase after the Phase 5y closure and five-NO-GO dark-energy sweep.*

**Status update 2026-04-26-1340:** Phase 5z is now **FOUR WAVES SHIPPED**. Wave 1 (Track A flavor-singlet `ScalarRungInterpretation`), Wave 1b (Track A BHL gauge embedding `BHLGaugeEmbedding`), Wave 2 (Track B `MajoranaRung` + `NeutrinoMixing`), and Wave 3 (Track C `EWPhaseTransition`) all shipped end-to-end through Stages 1–8 + 10 (Stages 9 + 13 user-triggered). **Wave 3 shipped 2026-04-26**: `EWPhaseTransition.lean` 19 theorems + 1 structure + 12 defs, zero sorry, zero new axioms. Implements the LO high-T finite-T potential (Anderson-Hall, Quiros), critical temperature `T_c = √(μ²/c_T)`, latent-heat order parameter, first-order/crossover predicate (cubic-coefficient sign), SM benchmark (`m_H = 125.20`, `λ = 0.13`, `c_T = 0.4`, `E ≈ 0.01`, `T_c ≈ 139` GeV), KLRS 1996 lattice crossover threshold (m_H = 72 GeV), `crossover_excludes_baryogenesis` load-bearing exclusion theorem (Phase 6c.2 input). Tracked hypotheses: `H_VacuumStableUnderRG` (Buttazzo+ 2013 metastability) + `H_HierarchyEWLambdaUV` (Λ_UV ≫ v_EW). Adds figure `fig_ew_transition_phase_diagram` (5 traces, 2-panel V_T(φ) profiles + (m_H, E) phase partition) + 36 pytest in `tests/test_ew_phase_transition.py` + Python `src/ew_phase_transition/` (3 modules) + 4 `formulas.py` additions (`ew_finite_t_potential`, `ew_thermal_mass_sq`, `ew_critical_temperature`, `ew_latent_heat`) + 3 new bibkeys (`KLRS1996`, `ButtazzoEtAl2013`, `ShaposhnikovWetterich2010`). New paper `papers/paper22_ew_phase_transition/paper_draft.tex` (PRD format, 4 pages, 372 KB).

**Status update 2026-04-26-1300:** Wave 1b (`BHLGaugeEmbedding.lean`) shipped through Stages 1–8 + 10: 23 theorems + 3 structures + 15 defs, zero sorry, zero new axioms. Implements the BHL gauge-embedding transplant per O.2 verdict (Scenario A 3/5): extended Fierz basis dim count, gauge-covariance tracked hypotheses, concrete BHL `m_H = √2 m_t`, BHL gap problem (`bhl_minimal_overshoots_pdg`), Hill 2025 bilocal correction recovery (`bilocal_correction_can_match_pdg` at dilution 0.402). Adds figure `fig_bhl_bilocal_correction` (4 traces, 2-panel) + 24 pytest in `tests/test_bhl_embedding.py` + Python `src/scalar_rung/bhl_embedding.py` + 5 `formulas.py` additions + 4 new bibkeys (MTY1989, Hill2025Redux, AAA2020, Cvetic1999). Paper 20 expanded with §6 BHL Gauge Embedding (6 pages, 611 KB). Stages 9 (figure review) + 13 (adversarial) are user-triggered.

**Earlier status update 2026-04-25-0210:** Wave 1 (Track A) **SHIPPED end-to-end through Stages 1–13** of the wave-execution pipeline, and **all three Phase 5z deep-research deliverables have landed** in `Lit-Search/Phase-5z/`.

Wave 1 summary:
- Strengthening pass replaced 3 vacuous Props with 5 substantive ones (including tracked-hypothesis bridge `H_ScalarChannelIsTetradBifurcationOutput` + custodial-symmetry identity `zMass_sq_minus_wMass_sq`)
- Stage 9 figure review PASS; Stage 11 technical + stakeholder notebooks shipped clean; Stage 13 adversarial review re-invocation closed all 18 BLOCKERs + 7/8 REQUIREDs; the final deferred REQUIRED (WebFetch verification of 10 new bibkeys) was **CLOSED 2026-04-26** — 4 of 10 bibkeys were wrong (3 wrong-arXiv plus 1 HALLUCINATED citation `WetterichNJL` = nonexistent PLB 901 136223 2024, replaced with Wetterich Ann. Phys. 327, 2184 (2012) / arXiv:1201.6505). All 10 entries now `doi_verified: True`; paper 20 recompiles clean; Lean rebuilds clean. Finding report at `papers/AutomatedReviews/2026-04-26-0130-citation-verification/paper20_scalar_rung.md`.
- `ScalarRungInterpretation.lean` ships **20 theorems**, zero sorry, zero new axioms
- Python `src/scalar_rung/` + 24 passing tests; figure `fig_higgs_mass_parameter_scan`; flagship paper `paper20_scalar_rung` (5 pages, 13/13 bibkeys registered)
- Falsifiability-anchor verdict: **Gate Z.1 STRUCTURAL-ONLY** at the current schematic-leading-log scope (m_H = 125 GeV reachable only along a 1-D tuning curve in (Λ_UV, G_c))

Deep-research verdicts (delivered):
- **O.2 Structural (`5z-Open Question 02-Structural.md`):** **Scenario A (doublet-compatible), strength 3/5.** The Wetterich-NJL scalar channel admits an SU(2)_L × U(1)_Y Higgs-compatible extension via the Bardeen-Hill-Lindner auxiliary-field route. Not Wetterich-native; requires a transplant theorem `BHLGaugeEmbedding` in Lean importing the BHL–MTY–Hill construction onto the `WetterichNJL` Clifford-16 Fierz basis. **Gate Z.2 effectively resolved** — Wave 3 proceeds with SU(2)-indexed finite-T potential.
- **Yukawa overlap (`5z-Yukawa Couplings...Emergent Weyl Modes.md`):** **No closed-form in VZ primary sources.** The VZ construction mechanically supports the overlap definition (projector Π·Ω is explicit, Weyl mode `Ψ = ΠΩψ` is closed-form), but Yukawa `y_fg = ⟨P_FP,f | σ̂ | P_FP,g⟩` is a **derived/proposed extension**, not a theorem of VZ2014. Wave 1 extension must mark the overlap module as a *structural postulate extending VZ2014*. F-theory GUT constructions (Heckman-Vafa, Cremades-Ibáñez-Marchesano, Leontaris) provide an analogue closed-form for future transplantation.
- **O.3 Sterile-ν embedding (`Phase 5z, Wave 2 — Sterile-Neutrino Embedding...`):** **Hybrid Embedding III recommended.** Fundamental Lean field `ν_R : SterileNeutrino` whose UV interpretation is an ADW-substrate bound state; Majorana mass `M_R` as a Z₁₆-invariant condensate scale. Forced by the proved `hidden_sector_required` theorem (Embedding II incurs +3 mod 16 hidden-sector TQFT burden; Embedding III adds zero IR cost). `M_R` enters as `noncomputable constant` with substrate-bridge axiom marked `informal_lemma` (the `Λ_ADW → M_R` derivation is not closed in primary literature).

Net effect: **Wave 1 quantitative extension, Wave 2, and Wave 3 are all now unblocked.** Next session can pick any.

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. Core rung machinery in place: `WetterichNJL.lean` (18, scalar/pseudoscalar/vector channels + NJL–ADW correspondence), `TetradGapEquation.lean` (20, generic NJL-type gap equation + bifurcation), `VestigialSusceptibility.lean` (16, RPA bubble + Kubo connection from Phase 5y Wave 6), `FermiPointTopology.lean` (33, emergent-Weyl mode counting), `ADWMechanism.lean` (21), `HiddenSectorClassification.lean` (9, COMPLETE 2026-04-22), `Z16AnomalyComputation.lean` (23), `SpinBordism.lean` (8), `RokhlinBridge.lean` (14), `SMFermionData.lean` (19), `VestigialGravity.lean` (24 after Phase 5y Wave 6), `TetradGapEquation.lean` (24 after 5y Wave 6).

**Thesis.** Higgs, Majorana, and tetrad condensates sit as rungs of a single Landau hierarchy on one fermionic substrate. The machinery is mostly in place; Phase 5z is a reinterpretation program with physics-paper output plus falsifiable microscopic predictions.

**Correctness-push framing.** Every 5z wave must answer (1) what existing modules it integrates with, (2) what new constraint it adds that the program cannot state without it, and (3) what would falsify the wave. Waves where (3) is interesting are flagged as **correctness-push highlights**.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §3 (5z) and §2 (architectural constraints)
> 4. Re-read Phase 5y closure context: `docs/roadmaps/Phase5y_Roadmap.md` + `docs/stakeholder/Phase5y_Closure_Summary.md` (5z does NOT inherit 5y's NO-GO — different physical domain)
> 5. For 5z.1: read `WetterichNJL.lean`, `TetradGapEquation.lean`, `FermiPointTopology.lean` (especially for Yukawa-as-overlap-integral)
> 6. For 5z.2: read `HiddenSectorClassification.lean`, `Z16AnomalyComputation.lean`, `SpinBordism.lean`, `RokhlinBridge.lean`, `SMFermionData.lean`
> 7. For 5z.3: read `src/adw/ginzburg_landau.py`, `src/vestigial/phase_diagram.py`, `src/vestigial/finite_size.py`
> 8. Any ambiguity in overlap-integral form for Yukawa couplings, `SU(2)×U(1)` index structure of the WetterichNJL scalar channel, or sterile-neutrino embedding: drop a deep-research prompt into `Lit-Search/Tasks/` and flag to user (see Open Questions §O below)

---

## Scope Lock & Out-of-Scope

**IN SCOPE for 5z:**
- Lean formalization of the Higgs bilinear as WetterichNJL scalar rung, including a microscopic prediction of `m_H` from condensate parameters (correctness-push)
- Yukawa couplings as overlap integrals on FermiPointTopology emergent Weyl modes
- Mexican-hat potential as specialization of the TetradGapEquation bifurcation
- W/Z mass matrix stated as explicit output of Anderson-Higgs on the scalar rung (subsumes former 7.1 bridge: Higgs ↔ tetrad)
- Majorana bilinear as ℤ₂-graded rung connecting sterile-ν seesaw to the ℤ₁₆ singlet branch
- Order of the EW phase transition (first-order vs crossover) predicted from microscopic parameters
- PMNS structure note (parallel to HepLean CKM) without full PMNS phenomenology

**OUT OF SCOPE for 5z (deferred to backlog or later phases):**
- Full flavor program (CKM phases, FCNC, CP-violation fitting, mass hierarchy) — HepLean handles CKM
- Leptogenesis dynamics (scoped for 6c.2 extension, not 5z)
- Nonlinear effective action for gravity (Phase 6e)
- Cosmological perturbation theory around vestigial / scalar-rung backgrounds (Phase 6b)
- Full Boltzmann-code EW-phase-transition fitting — microscopic prediction is the 5z output; Boltzmann integration belongs to Phase 6b.3 or external collaboration
- Extra-dimensional / string-theoretic completions of the scalar rung (OOS by program framing)

**Phase 5x relationship:** Phase 5x dark-matter waves (fracton DM, Fang-Gu torsion, vestigial relics, SFDM, hidden-sector-classification) are unaffected. The scalar rung interpretation does not alter the ℤ₁₆ anomaly-forcing of hidden-sector content proved in Phase 5x Wave 2.

**Phase 5y relationship:** 5y's Gibbs-Duhem / q-theory NO-GO applies to cosmological-scale emergent dark-energy mechanisms. 5z operates at the EWSB scale on the same Landau hierarchy but for a distinct order parameter — no NO-GO inheritance. Parallel to 5x on this point.

---

## Track A: Scalar-Rung Physics (FLAGSHIP — 5z.1)

### Motivation

The WetterichNJL module already formalizes the scalar/pseudoscalar/vector channel decomposition of an NJL-type fermion bilinear. If the scalar channel is identified with the Higgs bilinear, then (a) the Mexican-hat potential is a specialization of the existing TetradGapEquation bifurcation, (b) Yukawa couplings become overlap integrals of SM fermions against emergent Weyl modes on the FermiPointTopology substrate, and (c) the W/Z mass matrix emerges as the explicit Anderson-Higgs output of the scalar rung. **A microscopic prediction for `m_H` is the correctness-push anchor:** if the prediction is incompatible with 125 GeV given realistic microscopic parameters, the scalar-rung framing is falsified as a quantitative theory of EWSB — itself a structurally meaningful publishable result.

This is the single flagship wave of Phase 5z: paper-bearing, program-bearing, and falsifiable.

### Wave 1 — `ScalarRungInterpretation.lean` [Pipeline: Stages 1–12]

**Status:** **SHIPPED 2026-04-24 through Stages 1–13** (end-to-end; Stage 13 re-invocation cleared all BLOCKERs 2026-04-25). Deep-research result for Wave 1 extension (Scenario A via BHL bridge) now available — see header status block; a quantitative-scope follow-up wave (call it Wave 1b) is now unblocked, which would add `BHLGaugeEmbedding`-style SU(2)_L × U(1)_Y-indexed scalar-channel extension as a transplant from BHL–MTY–Hill literature.

**Goal:** Formalize the identification of the WetterichNJL scalar channel with the Higgs bilinear, the Yukawa-as-overlap construction, and the `m_H` microscopic prediction.

**Prerequisites:** None beyond existing infrastructure. Open Question O.2 (WetterichNJL SU(2)×U(1) structure) should be resolved via deep research before committing to the SM-embedded form; a flavor-singlet-first fallback path is scoped below. **Wave 1 shipped in the flavor-singlet frame; SM-embedding extension blocked on O.2.**

**Module structure:**
- `lean/SKEFTHawking/ScalarRungInterpretation.lean`
  - Scalar-channel identification predicates: `IsHiggsBilinear (σ : ScalarChannel) : Prop` mapping WetterichNJL's scalar channel to an SU(2)-doublet Higgs bilinear (or flavor-singlet fallback if O.2 resolves singlet-only)
  - Mexican-hat specialization: theorem `mexican_hat_is_tetrad_bifurcation` tying `V(Φ) = −μ²|Φ|² + λ|Φ|⁴` to the specific branch of `TetradGapEquation`'s bifurcation
  - Yukawa overlap construction: `YukawaCoupling (f g : FermiPointTopology.WeylMode) : ℝ` as overlap integral, with linearity lemmas in mode space
  - Anderson-Higgs W/Z mass matrix: theorem `ew_mass_matrix_from_scalar_vev` stating M_W/M_Z ratio from condensate parameters + gauge-coupling ratio
  - **Correctness-push predicate:** `HiggsMassFromCondensate (μ, λ, g_Y, Λ_UV, N_f) → ℝ` — closed-form microscopic prediction for `m_H`
  - **Falsifiability theorem:** `scalar_rung_quantitative_EWSB_iff_m_H_matches_125` — biconditional under explicit parameter assumptions
- Target ~16–20 theorems.

**Python side (`src/scalar_rung/`):**
- `src/scalar_rung/__init__.py` — namespace init
- `src/scalar_rung/higgs_prediction.py` — numerical evaluation of `HiggsMassFromCondensate` over a parameter grid
- `src/scalar_rung/ew_mass_matrix.py` — W/Z mass-matrix computation from condensate VEV + gauge couplings
- Formula additions to `src/core/formulas.py`: `higgs_mass_from_condensate`, `w_mass_from_vev`, `z_mass_from_vev`, each with `Lean:` cross-references

**Bridges:**
- Integrates with `WetterichNJL.lean`, `TetradGapEquation.lean`, `VestigialSusceptibility.lean`, `FermiPointTopology.lean`, `ADWMechanism.lean`
- Feeds `MajoranaRung.lean` (Wave 2) — same Landau-hierarchy framework, different bilinear
- Feeds `EWPhaseTransition.lean` (Wave 4) — the scalar-channel bifurcation is the transition order parameter

**Deliverables (SHIPPED):**
- ✅ `lean/SKEFTHawking/ScalarRungInterpretation.lean` — **18 theorems, 0 sorry, 0 new axioms**; build clean via `lake build SKEFTHawking.ExtractDeps` (8431 jobs)
- ✅ `tests/test_scalar_rung.py` — **24 tests** covering Mexican-hat / Anderson-Higgs / Yukawa overlap / microscopic m_H scan / quantitative-match predicate
- ✅ Flagship paper `papers/paper20_scalar_rung/paper_draft.tex` — **4 pages**, compiles clean, "Scalar, Tetrad, and Majorana Condensates on a Single Fermionic Substrate"
- ✅ Figure `fig_higgs_mass_parameter_scan` in `visualizations.py` — heatmap of predicted m_H over `(Λ_UV, G_c)` plane at fiducial `(N_f=15, λ_4=0.13)`, gold contour at 125.25 GeV with ±50% tolerance band
- ✅ Inventory delta: **+18 thms, +1 Lean module, +3 Python modules** (`scalar_rung/__init__.py`, `higgs_prediction.py`, `ew_mass_matrix.py`), **+1 test file, +1 paper, +1 figure**. Total project: **3976 thms (+18), 167 modules (+1), 0 sorry, 1 axiom unchanged**.
- ✅ Stage 1 (constants/provenance): `EW_PARAMS` dict (17 entries) + 13 new `PARAMETER_PROVENANCE` entries (PDG 2024 / DERIVED / PROJECTED tiers); `parameter_provenance` check passes
- ✅ Stage 7 cross-layer validation: `validate.py` 21/21 PASS

**Deferred from Wave 1 (Stage 9 / 11 / 13):**
- Stage 9 LLM figure review (`physics-qa:figure-reviewer`) — user-side trigger; structural review passed (0 errors, 23 unrelated warnings in pre-existing figs)
- Stage 11 technical/stakeholder notebooks — defer to later wave or as user request
- Stage 13 adversarial review — user-triggered

**Risk:** Medium → realized. The flavor-singlet frame proceeded clean. The SU(2)×U(1) index structure of the WetterichNJL scalar channel is the single largest remaining unknown (Open Q O.2 — deep-research prompt filed). Quantitative scope of paper 20 is gated on O.2 resolution.

**Correctness-push highlight (verdict).** The microscopic m_H prediction reaches 125.25 GeV only along a 1-D tuning curve in the `(Λ_UV, G_c)` plane — a **structural-only Gate Z.1 verdict** at the current scope. The narrowness of the matching curve (rather than a generic region of parameter space) is itself the load-bearing publishable result. Re-evaluation under Scenario A of O.2 (SU(2)×U(1)-dressed scalar channel) would tighten or relax the verdict.

---

## Track B: Majorana Seesaw Rung (5z.2)

### Motivation

The Hidden-Sector Classification (Phase 5x Wave 2, COMPLETE 2026-04-22) formalizes the ℤ₁₆ anomaly-forced hidden-sector singlet branch. Adding a Majorana bilinear as a ℤ₂-graded rung on the same Landau hierarchy connects sterile-neutrino seesaw phenomenology directly to the anomaly-matching infrastructure — the first such bridge in a formally-verified setting. Parallels HepLean's CKM treatment but via the condensate rung, not as a Yukawa-matrix parameterization.

Phase 5z.2 ships a `NeutrinoMixing.lean` *structure note* (PMNS form parallel to CKM) without pursuing full PMNS phenomenology; phenomenology remains in the backlog.

### Wave 2 — `MajoranaRung.lean` [Pipeline: Stages 1–8]

**Status (2026-04-26):** **SHIPPED end-to-end Stages 1-12.** `MajoranaRung.lean` (14 substantive theorems + 5 defs + 1 structure) and `NeutrinoMixing.lean` (7 theorems + structure-note scope) both build clean (`lake build SKEFTHawking.ExtractDeps` 8433 jobs). 32 new pytest in `tests/test_majorana_rung.py` all pass. `validate.py` 21/21 PASS. Embedding III (Hybrid) per O.3 verdict — fundamental Lean ν_R, M_R parameterized inside `MajoranaRungData`, WAVE2-OPEN-1 substrate-bridge tracked-hypothesis (`H_MR_FromADWSubstrate`), Z₁₆ singlet-branch bridge proves from existing `three_nu_R_cancel_three_gen` + `three_singlets_satisfy_hidden_sector`. PMNS structure-note via `Matrix.unitaryGroup (Fin 3) ℂ` with WAVE2-OPEN-2 (`H_PMNSAnglesFromSubstrate`). **Paper 21** (`papers/paper21_majorana_rung/paper_draft.tex`, PRD format, 5 pages, 632 KB, P1 readiness gates passed). **2 figures** (`fig_seesaw_y_m_r_band`, `fig_m_beta_beta_vs_m_lightest`). **2 notebooks** (`Phase5z_MajoranaRung_{Technical,Stakeholder}.ipynb`, both viz_consistency + notebook_exec clean). 9 new CITATION_REGISTRY bibkeys (NuFit60, KamLANDZen800, LEGEND1000, MohapatraSmirnov2006, GarciaEtxebarriaMontero2019, WanWang2020, KawasakiYanagida2023 [renamed from `Davighi2023` 2026-04-25 after CitationIntegrity WebFetch flushed hallucinated authors], Volovik2024Spinor, TooBySmithHepLean) — all `doi_verified: True` after 2026-04-25 CrossRef + arXiv + NASA ADS round. **Stages 9 (LLM figure review) + 13 (adversarial review) are user-triggered.**

**Goal:** Formalize the Majorana bilinear as a ℤ₂-graded rung and bridge to HiddenSectorClassification's ℤ₁₆ singlet branch.

**Prerequisites:** Wave 1 in-flight but not blocking (shares Landau-hierarchy framing but bilinear structure is independent).

**Module structure:**
- `lean/SKEFTHawking/MajoranaRung.lean`
  - Majorana bilinear structure: `MajoranaBilinear (ψ : Fermion) : Prop` with ℤ₂ grading
  - Seesaw connection: `seesaw_mass_from_majorana_rung` — theorem tying `m_ν ~ y²v²/M_R` to rung parameters (M_R = condensate scale, y = Yukawa overlap)
  - ℤ₁₆ singlet-branch bridge: `majorana_rung_compatible_with_hidden_singlet` — theorem that the Majorana rung's charge assignment is compatible with the HiddenSectorClassification singlet branch under `HiddenSectorClassification.singlet_sector_has_anomaly_plus3`
  - **Correctness-push predicate:** `HiddenSinglet_MassScale_ObservationalBound` — the Majorana-rung prediction for `M_R` from ℤ₁₆ anomaly-matching constraints, compared to observational neutrino mass scales (Δm²_atm, Δm²_sol) and mixing angles (θ_12, θ_23, θ_13)
- Target ~10–12 theorems.

**Module structure (continued):**
- `lean/SKEFTHawking/NeutrinoMixing.lean` — PMNS structure note (parallel to HepLean's CKM)
  - Definition of PMNS unitary matrix as 3×3 unitary with three mixing angles + one Dirac phase (+ two Majorana phases flagged separately)
  - Parameterization lemmas (PDG convention); no phenomenology fitting
  - Cross-reference to HepLean CKM when available; stub if not
- Target ~5–6 theorems.

**Python side:**
- `src/majorana_rung/seesaw_prediction.py` — numerical `M_R` from rung parameters, `m_ν` prediction
- Formula additions: `seesaw_mass`, `pmns_angle_from_overlap` (if O.3 resolves)

**Bridges:**
- Integrates with `HiddenSectorClassification.lean` (Phase 5x W2), `Z16AnomalyComputation.lean`, `SMFermionData.lean`, `SpinBordism.lean`, `RokhlinBridge.lean`
- Parallels Wave 1 (`ScalarRungInterpretation.lean`) — same Landau-hierarchy scaffolding

**Deliverables:**
- Both modules zero-sorry, building clean
- `tests/test_majorana_rung.py`, `tests/test_neutrino_mixing.py`
- PRD paper `papers/paper21_majorana_rung/paper_draft.tex` — Majorana rung + ℤ₁₆ bridge
- Short arXiv note `papers/note_pmns_structure/` — PMNS structure parallel to CKM (no phenomenology)
- Inventory update: +15–18 theorems, +2 Lean modules, +1 Python module, +1 PRD paper + 1 short note

**Estimated LOE:** 2.5–4 person-months
**Risk:** Low–medium. The ℤ₁₆ singlet-branch bridge is structurally clean (Hidden-Sector Classification is complete). Main risk is Open Q O.3 (sterile-ν embedding choice for the seesaw map); scoped so that either embedding yields a valid wave — only the quantitative predictions change.

**Correctness-push highlight.** If the ℤ₁₆ singlet-count constraint is incompatible with observed neutrino mass scales and mixing angles under the Majorana-rung interpretation, microscopic parameters are bounded — a quantitative constraint derived from anomaly-matching rather than fit.

---

## Track C: Electroweak Phase Transition (5z.3)

### Motivation

The order of the electroweak phase transition (first-order vs crossover) is a microscopic prediction from the scalar-rung identification. Vacuum stability and hierarchy observations enter as subsections, not as independent waves. Relevant to EW baryogenesis and connects to the Phase 6c.2 bridge theorem (EW baryogenesis ↔ chirality wall).

### Wave 3 — `EWPhaseTransition.lean` [Pipeline: Stages 1–8, with optional Stage 10–11]

**Goal:** Formalize the EW phase transition as a specific trajectory through the TetradGapEquation bifurcation / scalar-rung potential, predict the transition order.

**Prerequisites:** Wave 1 (`ScalarRungInterpretation.lean`) must be complete — the scalar-channel bifurcation is the transition order parameter.

**Module structure:**
- `lean/SKEFTHawking/EWPhaseTransition.lean`
  - Finite-T effective potential: `V_T(Φ, T)` as Φ-dependent extension of the Mexican-hat with thermal correction (hard-thermal-loop resummed leading term)
  - Transition-order predicate: `FirstOrderEW (params) : Prop` vs `CrossoverEW (params) : Prop` with the predicate set partitioning by `V_T` barrier height and critical temperature
  - **Correctness-push theorem:** `transition_order_from_microscopic_parameters` — explicit map from `(Λ_UV, N_f, G_c, λ)` to the transition order, ruling in or out EW baryogenesis viability
  - Vacuum stability sublemma: `vacuum_stable_iff_λ_positive_under_RG_running` (structural, not fit-dependent)
  - Hierarchy-observation sublemma: `condensate_scale_hierarchy_Λ_EW_vs_Λ_Planck` — predicted hierarchy factor
- Target ~10–14 theorems.

**Python side:**
- `src/ew_phase_transition/` — new subpackage
  - `potential.py` — finite-T Higgs potential, barrier height, latent heat
  - `order_classifier.py` — first-order vs crossover classifier over parameter grid
  - `baryogenesis_compatibility.py` — compatibility with strong-enough first-order transition threshold
- Reuses: `src/adw/ginzburg_landau.py` (Landau-theory machinery), `src/vestigial/phase_diagram.py`, `src/vestigial/finite_size.py` (finite-size-scaling for cross-validation if MC data available)
- Formula additions: `ew_barrier_height`, `ew_critical_temperature`, `ew_latent_heat`

**Bridges:**
- Depends on Wave 1 (`ScalarRungInterpretation.lean`) for the scalar-channel potential
- Feeds Phase 6c.2 (EW baryogenesis ↔ chirality wall bridge) as the "transition-order" input
- Feeds Phase 6b.3 (vestigial inflation) via shared slow-roll machinery (if that wave proceeds)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_ew_phase_transition.py`
- Conference/review paper `papers/paper22_ew_phase_transition/paper_draft.tex` — review-length piece on microscopic prediction of transition order
- Figure: `fig_ew_transition_phase_diagram` in `visualizations.py` — first-order/crossover partition of `(Λ_UV, N_f)` plane with baryogenesis-viable region highlighted
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Finite-T Higgs potential requires careful bookkeeping of thermal loop corrections; scope explicitly limits to hard-thermal-loop resummed leading term (full two-loop deferred to backlog). Cross-validation against lattice EWPT results (historical computational baselines available) is optional but recommended.

**Correctness-push highlight.** If the microscopic prediction is robustly crossover, EW baryogenesis in the SM-as-embedded-in-scalar-rung is forbidden — pushing baryogenesis to leptogenesis or BSM mechanisms. Directly feeds Phase 6c.2.

---

## Decision Gates

**Gate Z.1 — after Wave 1 ships:** ✅ **RESOLVED (STRUCTURAL-ONLY branch locked in 2026-04-25).** The microscopic `m_H` prediction reaches 125 GeV only along a 1-D tuning curve in the natural (Λ_UV, G_c) plane under the schematic leading-log closure. Under the current flavor-singlet frame, the scalar-rung framing is therefore *structural-only*. The O.2 deep research (delivered 2026-04-25, verdict Scenario A strength 3/5) shows that a quantitative extension via the BHL auxiliary-field bridge is available; the activated quantitative-scope follow-up would be Wave 1b (`BHLGaugeEmbedding` transplant). Paper 20 is reframed as "structural identification" per roadmap's NO-branch fallback.

**Gate Z.2 — before Wave 3 begins:** ✅ **RESOLVED (2026-04-25 via O.2 delivery).** O.2 verdict: Scenario A (doublet-compatible) strength 3/5; literature-supported (BHL, MTY, Hill) but requires a transplant theorem `BHLGaugeEmbedding` that is not Wetterich-native. Wave 3 proceeds with direct SU(2) indices in the finite-T potential, citing BHL-class extension as load-bearing for the index structure.

**Gate Z.3 — optional paper gate:** If all three flagship deliverables produce consistent predictions, consider a unified Annals-length review paper bundling Waves 1–3 as a single "Scalar Condensate Ladder" paper rather than three independent papers. User decision — defer until Wave 2 + Wave 3 actually ship.

---

## Dependencies

```
Track A: Wave 1 (ScalarRungInterpretation) → Gate Z.1

Track B: Wave 2 (MajoranaRung + NeutrinoMixing)
  — independent of Track A; can run in parallel

Track C: Wave 3 (EWPhaseTransition)
  — depends on Wave 1; Gate Z.2 before start

Parallelism:
  Waves 1 and 2 independent → parallel execution possible
  Wave 3 blocked on Wave 1 completion (not just start)
```

---

## Timeline

| Wave | Track | Scope | PM | Dependencies | Priority |
|------|-------|-------|-----|--------------|----------|
| Wave 1 | A | `ScalarRungInterpretation.lean` + flagship paper + Python scalar-rung package | 2–4 | None (Gate Z.2 before EW in Wave 3) | **TIER 0 — flagship** ✅ SHIPPED |
| Wave 1b | A | `BHLGaugeEmbedding.lean` (BHL transplant: gauge-indexed scalar channel + Hill bilocal correction) + paper 20 §6 | 1–2 | Wave 1 complete; O.2 verdict | **TIER 0 — quantitative-scope follow-up** ✅ SHIPPED 2026-04-26 |
| Wave 2 | B | `MajoranaRung.lean` + `NeutrinoMixing.lean` + PRD paper + short note | 2.5–4 | None; parallel with Wave 1 | **TIER 1** ✅ SHIPPED |
| Wave 3 | C | `EWPhaseTransition.lean` + conference paper + Python ew_phase_transition package | 3–5 | Wave 1 complete; Gate Z.2 | **TIER 1** ✅ SHIPPED 2026-04-26 |

**Total Phase 5z LOE:** 7.5–13 person-months Lean + paper-writing. Parallel execution: wall-clock 4–7 months minimum.

**Deliverables cumulative:**
- 4 new Lean modules (`ScalarRungInterpretation`, `MajoranaRung`, `NeutrinoMixing`, `EWPhaseTransition`)
- 3 new Python subpackages (`src/scalar_rung/`, `src/majorana_rung/`, `src/ew_phase_transition/`)
- 3 papers (flagship, PRD Majorana, conference EW) + 1 short PMNS structure note
- ~41–54 new theorems
- Zero new axioms target; zero sorry target

---

## Open Questions (resolve via deep research as needed)

**O.1** — Repo convention for "interpretation / bridge" modules vs "new physics" modules. Affects 5z packaging and, later, all Phase 6c bridge theorems. Propose: `ScalarRungInterpretation.lean` (interpretation) vs `MajoranaRung.lean` (new-physics rung) — document the convention in `docs/ARCHITECTURE_SCOPE.md` as part of Wave 1 Stage 12.

**O.2 — LOAD-BEARING — ✅ RESOLVED 2026-04-25.** Verdict: **Scenario A (doublet-compatible), strength 3/5.** The Wetterich-NJL scalar channel admits a Higgs-compatible SU(2)_L × U(1)_Y extension via the Bardeen-Hill-Lindner auxiliary-field bridge (BHL 1990, MTY 1989, Hill 2025). Not Wetterich-native; requires a transplant theorem `BHLGaugeEmbedding` in Lean. Full verdict, 15-paper literature survey, and signature proposals in `Lit-Search/Phase-5z/5z-Open Question 02-Structural.md`. Activates Wave 1b (quantitative extension) + tightens Wave 3 (SU(2)-indexed finite-T potential).

**O.Yukawa — ✅ RESOLVED 2026-04-25 (honest-gap verdict).** Verdict: **no closed-form in VZ primary sources.** Volovik-Zubkov construction mechanically supports the projector `Ψ = ΠΩψ` in closed form, but Yukawa `y_fg = ⟨P_FP,f | σ̂ | P_FP,g⟩` is a derived/proposed extension, NOT a theorem of VZ2014. Wave 1 overlap module must be marked as a *structural postulate extending VZ2014*. Analogue closed-form available in F-theory GUT constructions (Heckman-Vafa, Cremades-Ibáñez-Marchesano) for future transplantation. Full verdict + signature proposals in `Lit-Search/Phase-5z/5z-Yukawa Couplings as Overlap Integrals on Volovik–Zubkov Fermi-Point Emergent Weyl Modes.md`.

**O.3 — ✅ RESOLVED 2026-04-25.** Verdict: **Hybrid Embedding III recommended.** Fundamental Lean field `ν_R : SterileNeutrino` with UV interpretation as an ADW-substrate bound state; Majorana mass `M_R` as a ℤ₁₆-invariant condensate scale. Z₁₆ classification forces this (Embedding II incurs +3 mod 16 hidden-sector TQFT burden; Embedding III adds zero IR cost while preserving substrate self-consistency). `M_R` enters Lean as `noncomputable constant` with substrate-bridge axiom marked `informal_lemma` since `Λ_ADW → M_R` derivation is not closed in primary literature. Full verdict + signature proposals in `Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for the Majorana Rung.md`.

**O.4** — Which paper journal targets: `Paper 20 (Scalar Rung)` — Annals or PRD; `Paper 21 (Majorana Rung)` — PRD; `Paper 22 (EW Phase Transition)` — conference or review venue. Finalized at Stage 10 per paper.

---

## What Success Looks Like

**Track A (Scalar Rung):**
- `ScalarRungInterpretation.lean` with 16–20 theorems, zero sorry
- Microscopic `m_H` prediction as explicit function of `(Λ_UV, N_f, G_c, λ)`
- Flagship paper `papers/paper20_scalar_rung/` shipped; claims-reviewer green; no BLOCKERs in Stage 13 adversarial
- **Program-level value:** first formal-verification-grade statement of "Higgs-as-condensate-rung" with an explicit falsifiability test (125 GeV)

**Track B (Majorana Rung):**
- `MajoranaRung.lean` with 10–12 theorems, zero sorry
- `NeutrinoMixing.lean` with 5–6 theorems (structure-note scope)
- PRD paper `papers/paper21_majorana_rung/` shipped; short PMNS note filed
- **Program-level value:** first formal bridge from ℤ₁₆ anomaly-matching to sterile-ν seesaw phenomenology

**Track C (EW Phase Transition):**
- `EWPhaseTransition.lean` with 10–14 theorems, zero sorry
- Microscopic prediction of first-order vs crossover over parameter grid
- Conference/review paper `papers/paper22_ew_phase_transition/` shipped
- **Program-level value:** baryogenesis-viability feeds directly to 6c.2 bridge theorem

**Cumulative program deliverables:**
- 4 new Lean modules, 3 new Python subpackages, 3 papers + 1 short note
- ~41–54 new theorems, zero sorry target maintained, zero new axioms target
- Correctness-push anchors: `m_H` vs 125 GeV (5z.1), ℤ₁₆ singlet-mass compatibility (5z.2), transition-order (5z.3)

---

## Cross-References

**Prior phases this extends / harvests from:**
- Phase 3 (WetterichNJL) — `WetterichNJL.lean`, `src/vestigial/wetterich_model.py`
- Phase 5d (TetradGapEquation) — `TetradGapEquation.lean`, `src/adw/tetrad_gap_solver.py`
- Phase 5j (FermiPointTopology) — `FermiPointTopology.lean`
- Phase 5x Wave 2 (Hidden-Sector Classification) — `HiddenSectorClassification.lean`, COMPLETE 2026-04-22
- Phase 5c (Wang-Rokhlin chain, SpinBordism, SMFermionData) — existing anomaly-matching infrastructure

**Parallel phases (unaffected by 5z closure):**
- Phase 5u (Paper 10 polariton) — continues on own timeline
- Phase 5d (RHMC ADW fermion-bootstrap) — continues on own timeline
- Phase 5w (Graphene Dirac fluid) — continues on own timeline
- Phase 5x (Dark matter, all waves) — unaffected
- Phase 5y (CLOSED 2026-04-23) — 5z uses 5y's Vestigial extensions (Wave 6) but does not reopen 5y

**Downstream phases this feeds:**
- Phase 6a (linearized gravity) — scalar rung provides no direct GR input but Yukawa-overlap machinery reused
- Phase 6c.2 (EW baryogenesis ↔ chirality wall) — transition-order output from 5z.3 is the primary input
- Phase 6d.2 (chiral SSB for QCD) — WetterichNJL scalar-channel identification is parallel to the QCD quark-condensate identification; Wave 1's identification theorem generalizes

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §3

**Correctness-push highlights from strategy doc §12:**
- 5z.1: Predicted `m_H` vs 125 GeV — falsifies scalar-rung framing as quantitative EWSB theory

---

*Phase 5z roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. First new phase after Phase 5y closure. Three waves (scalar rung, Majorana rung, EW phase transition), three correctness-push anchors, three papers + one short note. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 7.5–13 Lean + paper-writing.*
