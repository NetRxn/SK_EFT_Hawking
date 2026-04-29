# Phase 5z: Scalar Condensate Ladder — Higgs, Majorana, and EW Phase Transition on a Single Fermionic Substrate

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22). First new phase after the Phase 5y closure and five-NO-GO dark-energy sweep.*

**Status update 2026-04-29:** Phase 5z is now **FIVE WAVES SHIPPED — Wave 4 closed NEGATIVE (second structural no-go)**. Wave 1 (Track A flavor-singlet `ScalarRungInterpretation`), Wave 1b (Track A BHL gauge embedding `BHLGaugeEmbedding`), Wave 2 (Track B `MajoranaRung` + `NeutrinoMixing` + `MajoranaRungDecoupling`), Wave 3 (Track C `EWPhaseTransition`), and **Wave 4 (Track B continuation — Symmetric Mass Generation route, `MajoranaRungSMG.lean`)** all shipped end-to-end. Wave 4 closed Gate Z.4 NEGATIVE on 2026-04-27 (deep-research return: V&D's own mean-field PRD 86 104019 finds chiral-SSB and trivially-gapped phases but NO SMG phase in the published 2-parameter slice); Wave 4 ships as a **second structural no-go** parallel to Wave 2's BCS no-go. **Phase 6h does NOT activate** — see Gate Z.4 reactivation criteria below for F-a-1 / F-a-3 / F-c-1 publication-event triggers. Per memory `project_phase5z_w4_shipped.md` (2026-04-27): 11 substantive thms / 0 sorry / 0 new axioms / 21 tests; corrections post-DR: c_SMG band [10⁻¹⁰,10⁻⁴], Λ_UV = M_Pl=10¹⁹.

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

## Track B continued — SMG Alternative for the Majorana Rung (5z.W4)

### Wave 4 — `MajoranaRungSMG.lean` [5z.W4] [Pipeline: Stages 1–8 + 10]

**Status (2026-04-27):** **SHIPPED — Gate Z.4 NEGATIVE (second structural no-go).** `MajoranaRungSMG.lean` 11 substantive thms / 0 sorry / 0 new axioms / 21 tests. Deep research at `Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate Phase Diagram.md` returned OPEN-AT-LITERATURE-FRONTIER on all 3 sub-questions, with literature-attested negative tilt: V&D's own mean-field (PRD 86 104019, 2012) finds chiral-SSB and trivially-gapped phases but no SMG phase in the published 2-parameter slice. Post-DR corrections: c_SMG band [10⁻¹⁰, 10⁻⁴] (NJL physical, not lattice-units); Λ_UV = M_Pl = 10¹⁹ GeV. New theorem `joint_substrate_bridge_obstruction_quantitative` derives both BCS+SMG failures substantively. Phase 6h does NOT activate; reactivation criteria F-a-1 / F-a-3 / F-c-1 documented in Gate Z.4 below. Memory: `project_phase5z_w4_shipped.md`. **Triggering rationale (preserved for context):** The BCS-exponential substrate-bridge for `M_R` (`H_MR_FromADWSubstrate_BCS_LNV`, `MajoranaRung.lean`) carries an L-symmetry obstruction (`lepton_number_symmetry_obstructs_BCS_form`) that no published source closes. **Symmetric Mass Generation (SMG)** is a structurally distinct mechanism that gaps fermions *without* requiring lepton-number violation; Hasenfratz-Witzel arXiv:2412.10322 + arXiv:2511.22678, 2024-2025 confirms an SMG phase for SU(3) with N_f=8 fundamental fermions in the continuum limit. Wave 4 ships the parallel SMG-route substrate-bridge as a tracked-hypothesis alternative to the BCS form, with quantitative anchoring from the Hasenfratz-Witzel lattice results.

**Goal:** Add a parallel SMG-route substrate-bridge tracked hypothesis to the Majorana-rung infrastructure, demonstrate that the SMG mechanism is *not* obstructed by lepton-number symmetry, and predict `M_R` from the substrate's SMG-gap scale `Λ_SMG` using Hasenfratz-Witzel-style lattice anchors.

**Prerequisites (all SHIPPED):**
- Wave 2 (`MajoranaRung.lean`) — the BCS branch we're paralleling
- Wave 2b (`MajoranaRungDecoupling.lean`) — IR-equivalence framework (SMG and Embedding I must agree in the decoupling regime)
- Phase 5x Wave 2 (`HiddenSectorClassification.lean`) — Catterall's 16-Weyl-per-generation lattice manifestation of ℤ₁₆
- Wave 1b (`BHLGaugeEmbedding.lean`) — Fierz-complete substrate-channel infrastructure (Braun-Leonhardt-Pawlowski I/II/III diquark channel transplant)

**Module structure:**
- `lean/SKEFTHawking/MajoranaRungSMG.lean`
  - `structure SMGSubstrateData` — substrate parameters in the SMG window: `(Λ_UV, N_f, G_c, c_SMG)` plus positivity / ordering constraints
  - `def H_SubstrateNearSMGFixedPoint (s : SMGSubstrateData) (Λ_SMG : ℝ) : Prop` — tracked hypothesis that substrate parameters sit in a Hasenfratz-Witzel-style SMG window with a definite gap scale `Λ_SMG > 0`. Non-vacuous: requires `0.1 < c_SMG < 1` (Hasenfratz-Witzel band) and `Λ_SMG = c_SMG · Λ_UV / strong_coupling_factor(N_f, G_c)`
  - `def H_MR_FromSMGGap (m : MajoranaRungData) (Λ_SMG : ℝ) : Prop` — `∀ i, ∃ c_i ∈ (0, 1], M_R i = c_i · Λ_SMG`. **No `H_LeptonNumberViolated` precondition** (compare with `H_MR_FromADWSubstrate_BCS_LNV` which conjoins `H_LeptonNumberViolated G_LV`).
  - **Bypass theorem (load-bearing):** `theorem smg_route_does_not_require_LNV` — explicit statement that `H_MR_FromSMGGap` is independent of `H_LeptonNumberViolated`. Discharges by structural inspection: the predicate's conjunction does NOT include `H_LeptonNumberViolated`. Mirror of `lepton_number_symmetry_obstructs_BCS_form` showing the BCS branch *requires* it.
  - **ℤ₁₆ compatibility theorem:** `theorem smg_route_consistent_with_z16_singlet` — the Catterall-Kähler-Dirac 16-Weyl-per-generation lattice manifestation (`Z16AnomalyComputation.three_nu_R_cancel_three_gen` + `HiddenSectorClassification.three_singlets_satisfy_hidden_sector`) is structurally compatible with the SMG mechanism. Explicit cross-bridge call.
  - **Disjointness theorem:** `theorem smg_and_BCS_apply_in_distinct_substrate_regimes` — under `H_LeptonNumberViolated G_LV = false` (substrate L-symmetric), only the SMG branch is admissible; under `H_LeptonNumberViolated G_LV = true` *and* `G_M > G_c`, only the BCS branch is admissible. Two non-overlapping sufficient conditions.
  - **Quantitative anchor (Hasenfratz-Witzel scaling):** `theorem smg_window_predicts_M_R_in_seesaw_band` — under `H_SubstrateNearSMGFixedPoint` with Hasenfratz-Witzel-band `c_SMG ∈ [0.1, 1.0]` and `Λ_UV = M_Pl`, the predicted `Λ_SMG ∈ [10^9, 10^15]` GeV — exactly the Type-I seesaw `M_R` band. `norm_num`-backed.
  - **Falsifiability witness:** `theorem not_isObservedSeesawMatch_under_SMG_below_band` — if a substrate's predicted `Λ_SMG < 10^9` GeV (below the lower seesaw band), `seesawNeutrinoMass` exceeds the NuFit-6.0 m_ν band → SMG-route falsified at that parameter point.
  - **IR-equivalence cross-bridge:** `theorem smg_amplitude_difference_satisfies_AC_bound` — calls `MajoranaRungDecoupling.H_DecouplingBoundDim6_consistent` to show SMG-route Embedding III predictions satisfy the same Appelquist-Carazzone bound vs Embedding I that the BCS-route does.
  - `def Wave4OpenManifest (m : MajoranaRungData) : Prop` — non-vacuous parametric bundle of OPEN-W4-{1,2,3} (analogous to Wave 2's `Wave2OpenManifest`):
    - OPEN-W4-1: `H_SubstrateNearSMGFixedPoint` (substrate sits in SMG window — open until lattice MC of ADW substrate near Hasenfratz-Witzel parameters)
    - OPEN-W4-2: `H_MR_FromSMGGap` (M_R coefficient `c_i` per generation — open until Catterall-mirror-decoupling geometry computed for ADW substrate)
    - OPEN-W4-3: Catterall-Pati-Salam structure on ADW substrate (lattice MC verification)
  - `theorem wave4_open_manifest_consistent` — non-vacuity construction at archetype `c_SMG = 0.5`, `Λ_UV = 10^16` GeV, `Λ_SMG = 5·10^15` GeV
- Target: **10–14 substantive theorems**, 0 sorry, 0 new axioms

**Python side:**
- `src/majorana_rung/smg.py` — Λ_SMG numerical estimation
  - `smg_gap_from_substrate_params(Lambda_UV, N_f, G_c, c_SMG=0.5)` — Λ_SMG estimator (Hasenfratz-Witzel scaling)
  - `m_r_from_smg_gap(Lambda_SMG, c_i=1.0)` — M_R from SMG mechanism (parallels `seesaw_m_r_from_observed`)
  - Hasenfratz-Witzel anchor: SU(3) N_f=8 → Λ_D ≈ 13 GeV (their reported strong-coupling SMG window) → m_baryon ≈ 3Λ_D ≈ 40 GeV
  - Mapping to ADW substrate: `Λ_SMG = c_SMG · Λ_UV` (scope-locked dimensional ansatz; substrate-specific dimensionless coefficient `c_SMG` is OPEN-W4-1)
- `src/core/formulas.py` additions:
  - `smg_gap_substrate(Lambda_UV, c_SMG)` with `Lean: MajoranaRungSMG.H_SubstrateNearSMGFixedPoint` ref
  - `m_r_smg_from_gap(Lambda_SMG, c_i)` with `Lean: MajoranaRungSMG.H_MR_FromSMGGap` ref
- `src/core/constants.py` additions to `MAJORANA_PARAMS`:
  - `'C_SMG_HASENFRATZ_WITZEL_LOWER': 0.1` (tracked, lattice-anchored)
  - `'C_SMG_HASENFRATZ_WITZEL_UPPER': 1.0` (tracked, lattice-anchored)
  - `'C_SMG_FIDUCIAL': 0.5` (PROJECTED tier in `PARAMETER_PROVENANCE`)
- `tests/test_majorana_rung_smg.py` — ~12 pytest covering SMG-route algebra, Hasenfratz-Witzel band consistency, BCS-vs-SMG disjointness round-trip, falsifiability witnesses

**Bridges:**
- Mirrors Wave 2 (`MajoranaRung.lean`) — same target observable (`M_R` per generation), structurally distinct mechanism
- Reuses Wave 2b (`MajoranaRungDecoupling.lean`) — IR predictions converge in the decoupling regime via Appelquist-Carazzone bound
- Cross-bridges to Phase 5x `HiddenSectorClassification.lean` via Catterall's 16-Weyl unit (Catterall arXiv:2311.02487, SciPost Phys. 16, 108, 2024)
- Sets up **Phase 6h** (Substrate Phase Diagram and Symmetric Mass Generation) — escalation path if Wave 4 closes positively

**Deliverables:**
- Module zero-sorry, building clean
- 10–14 substantive theorems, 0 new axioms
- `tests/test_majorana_rung_smg.py` (~12 tests)
- Either a §-extension of Paper 21 (preferred — Paper 21 already covers the BCS branch and the no-go; SMG would be a new §7 "Alternative Mechanism via Symmetric Mass Generation") OR a new short note `papers/note_smg_majorana_rung/`
- Inventory update: +10–14 theorems, +1 Lean module (`MajoranaRungSMG.lean`), +1 Python module (`src/majorana_rung/smg.py`), +1 paper extension or short note
- 4–6 new bibkeys in CITATION_REGISTRY (all `doi_verified: True` after Stage 13 WebFetch round):
  - HasenfratzWitzel2024 (arXiv:2412.10322)
  - HasenfratzWitzel2025 (arXiv:2511.22678)
  - Catterall2024 (arXiv:2311.02487, SciPost Phys. 16 108 2024)
  - RazamatTong2021 (PRX 11 011063 2021)
  - WanWang2025 (arXiv:2512.25038) — K-gauge TQFT anomaly tables
  - BraunLeonhardtPospiech2017 (PRD 96 076003 2017) [if not already from Wave 1b]

**Estimated LOE:** **3–5 person-months**
**Risk:** **medium**. **Two failure modes are publishable:**
- **(a) Positive closure:** `Λ_SMG → M_R` works under Hasenfratz-Witzel band, predicts phenomenologically reasonable `M_R` band → SMG branch becomes preferred substrate-bridge mechanism, **escalates to Phase 6h** for the full multi-sector story (substrate phase diagram, light-fermion hierarchy, Pati-Salam emergence).
- **(b) Second no-go:** the substrate's natural parameter range does NOT include the Hasenfratz-Witzel SMG window, OR the lattice scaling does NOT extrapolate to `M_R` in the seesaw band → ships as a strengthened obstruction note covering both BCS *and* SMG branches. That's a harder no-go, more structurally informative — closes the substrate-bridge derivation as impossible-in-current-substrate-models.

**Correctness-push highlight.** SMG potentially recovers `M_R` *without* the L-symmetry obstruction and with Hasenfratz-Witzel lattice quantitative anchoring. If validated, `M_R` becomes a *prediction* (computed from substrate parameters via lattice-anchored scaling) rather than a *fit* (set externally to match neutrino masses). This completes the seesaw correctness-push that Wave 2 left as structural-only.

---

#### Pre-read package for an agent picking up Wave 4 with a fresh context

> **Read these in order, end-to-end (no subagent depth-reading per CLAUDE.md):**
>
> 1. **Mandatory project bootstrap (CLAUDE.md §"Mandatory References"):**
>    - `CLAUDE.md`
>    - `SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md` (14-stage pipeline; Stages 1–8 + 10 mandatory for Wave 4, Stages 9 + 13 user-triggered)
>    - `SK_EFT_Hawking/SK_EFT_Hawking_Inventory_Index.md` (current state)
>    - `SK_EFT_Hawking/README.MD`
>    - `temporary/working-docs/brainstorm/20260413-context-lean-dev/Lean-Development-Optimization.txt` — read before MCP Lean session
>    - `SK_EFT_Hawking/docs/references/Theorm_Proving_Aristotle_Lean.md` — read if Aristotle session anticipated
>
> 2. **This roadmap (Phase 5z, this file):**
>    - Wave 2 section above (the structural baseline this wave parallels)
>    - Wave 4 (this section)
>    - Decision Gate Z.4 (below)
>
> 3. **Existing Lean modules (read directly with `Read` tool, full files):**
>    - `lean/SKEFTHawking/MajoranaRung.lean` — Wave 2 BCS branch (load-bearing structural baseline)
>    - `lean/SKEFTHawking/MajoranaRungDecoupling.lean` — Wave 2b decoupling-regime infrastructure
>    - `lean/SKEFTHawking/NeutrinoMixing.lean` — Wave 2 PMNS structure note
>    - `lean/SKEFTHawking/Z16AnomalyComputation.lean` — `three_nu_R_cancel_three_gen` (cross-bridge target)
>    - `lean/SKEFTHawking/HiddenSectorClassification.lean` — `three_singlets_satisfy_hidden_sector` (cross-bridge target)
>    - `lean/SKEFTHawking/WetterichNJL.lean` + `lean/SKEFTHawking/BHLGaugeEmbedding.lean` — substrate Fierz-channel infrastructure (Braun-Leonhardt-Pawlowski transplant template)
>
> 4. **Existing Python (read directly):**
>    - `src/core/formulas.py:6612-6900` — neutrino formula block (seesaw, PMNS, decoupling, Weinberg)
>    - `src/core/constants.py:1908` (`MAJORANA_PARAMS` dict)
>    - `src/core/provenance.py` — `PARAMETER_PROVENANCE` registry pattern
>    - `tests/test_majorana_rung.py` — existing 40 tests (template for SMG test file)
>
> 5. **Critical deep-research dossiers (read directly, not via subagent — per CLAUDE.md):**
>    - `Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` — **load-bearing.** §2.10 Razamat-Tong s-confinement (gaps 16 Weyl preserving Spin × ℤ₄), §2.11 SMG phase as dark sector, §2.6-2.8 Hasenfratz-Witzel SU(3) N_f=8 lattice evidence (continuum-limit confirmation in EPS-HEP2025).
>    - `Lit-Search/Phase-5b/Formalizing bidirectional anomaly constraints in theoretical physics.md` — **load-bearing.** §6 Catterall Kähler-Dirac → Pati-Salam structure from SMG mirror decoupling.
>    - `Lit-Search/Phase-5z/Phase 5z Wave 2a — Majorana-Channel Projection of the Tetrad Gap Equation.md` — **load-bearing.** §3 Q1 (FRG-NJL Fierz-complete machinery from Braun-Leonhardt-Pawlowski I/II/III, includes diquark channels needed for SMG projection); §6 Q5 publishability assessment (BCS no-go is Scenario B, SMG would be a new Scenario D).
>    - `Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for the Majorana Rung.md` — Embedding III recommendation context.
>    - `Lit-Search/Phase-5f/Two-loop NJL gap equation for tetrad condensation.md` — NJL/FRG infrastructure context (CJT scheme dependence; tetrad-channel structural advantages).
>    - `Lit-Search/Phase-3/The ADW mean-field gap equation for tetrad condensation with emergent Dirac fermions.md` — substrate Hubbard-Stratonovich landscape (no published HS for ADW 8-fermion action).
>    - `Lit-Search/Phase-5/Phase_5_follow-up_Effective nearest-neighbor action in ADW tetrad condensation after SO(4) Haar integration.md` — **load-bearing for OPEN-W4-1.** Vladimirov-Diakonov 5 8-fermion + 3 4-fermion couplings; Peter-Weyl decomposition.
>
> 6. **Key external papers (titles + arXiv IDs; fetch via WebFetch at Stage 13 verification):**
>    - Hasenfratz & Witzel, "Investigating SU(3) with Nf=8 fundamental fermions at strong coupling," arXiv:2412.10322 (2024)
>    - Hasenfratz & Witzel, "Symmetric Mass Generation," arXiv:2511.22678 (2025) — EPS-HEP2025 proceedings, continuum-limit confirmation
>    - Catterall, "From the bottom up: a Pati-Salam GUT in 4D from a single fermion field," arXiv:2311.02487, SciPost Phys. 16 108 (2024)
>    - Razamat & Tong, "Gapped Chiral Fermions," PRX 11 011063 (2021)
>    - Wan & Wang, "Anomalous (3+1)d fermionic topological quantum field theories via symmetry extension," arXiv:2512.25038 (2025)
>    - Braun, Leonhardt & Pospiech, "Fierz-complete NJL model study," PRD 96 076003 (2017); II PRD 97 076010 (2018); III PRD 101 036004 (2020)
>
> 7. **Open task to file at Stage 0 of Wave 4** (deep research; user-triggered async):
>    - `Lit-Search/Tasks/complete/Phase5z_W4_smg_substrate_phase_diagram.md` (filed; deep-research return delivered 2026-04-27 with verdict OPEN-AT-LITERATURE-FRONTIER, negative tilt — see file itself for full §6 falsifier list) — **two pinned questions:**
>      - (a) Does the ADW substrate (Vladimirov-Diakonov 4D simplicial action with 8 dimensionless couplings λ_k) sit in or near the Hasenfratz-Witzel SU(3) N_f=8 SMG window? Specifically, is there a region of the Vladimirov-Diakonov coupling space (λ_1, ..., λ_8) where the substrate flows to the merged UV-IR fixed point characteristic of SMG?
>      - (b) What is the analog of Λ_D (Hasenfratz-Witzel SU(3) lattice scale) for ADW-style multi-channel substrates after SO(4) Haar integration? Specifically, applying the Peter-Weyl decomposition (Phase-5 nearest-neighbor effective action deep research) to the SMG-channel projection — is there a closed-form Λ_SMG = f(λ_1, ..., λ_8, Λ_UV)?
>      - Cite Hasenfratz-Witzel arXiv:2412.10322 + arXiv:2511.22678, Catterall arXiv:2311.02487, Razamat-Tong PRX 11 011063 2021, Vladimirov-Diakonov PRD 86 104019 2012.
>
> 8. **Pre-write checklist (CLAUDE.md "Preemptive-strengthening discipline" — 5 questions before each theorem):**
>    - (1) Bundle redundancy P2 — drop-conjunct test
>    - (2) Quantitative connection — `norm_num`-backed comparisons (Hasenfratz-Witzel band 0.1 < c_SMG < 1.0; seesaw band 10^9 < Λ_SMG < 10^15 GeV)
>    - (3) Cross-module bridge integrity P6 — every docstring reference must `import` + call the cited theorem
>    - (4) Trivial-discharge P3/P4/P5 — no `rfl`/`decide`/`not_lt.mpr` tautologies
>    - (5) Defining-the-conclusion check — vacuous when `f := <obvious target>`
>
> 9. **Pipeline reminders (per CLAUDE.md):**
>    - Use MCP Lean tools (`lean_goal`, `lean_multi_attempt`) for interactive development; reserve `lake build SKEFTHawking.ExtractDeps` for finalization
>    - Never use `ring` / `ring_nf` on non-commutative ring expressions
>    - Never add `set_option maxHeartbeats N` to a proof body
>    - Use `lake build SKEFTHawking.ExtractDeps` (NOT bare `lake build`) for trustworthy rebuilds
>    - Do NOT delegate Lean theorem proving to subagents
>    - Aristotle is fallback only after MCP loop is fully exhausted on a sorry; user gets first/last call on submissions
>
> **Wave 4 success criteria:**
> - 10–14 substantive theorems shipped, zero sorry, zero new axioms
> - `validate.py` 21/21 PASS (or current count)
> - `lake build SKEFTHawking.ExtractDeps` clean
> - Python tests all pass; `pytest -m ''` (full suite) all pass
> - Stage 13 adversarial review: zero unaddressed BLOCKERs
> - End-of-wave strengthening pass produces ≤ 2 retroactive theorems (per CLAUDE.md preemptive-strengthening discipline goal)

---

## Decision Gates

**Gate Z.1 — after Wave 1 ships:** ✅ **RESOLVED (STRUCTURAL-ONLY branch locked in 2026-04-25).** The microscopic `m_H` prediction reaches 125 GeV only along a 1-D tuning curve in the natural (Λ_UV, G_c) plane under the schematic leading-log closure. Under the current flavor-singlet frame, the scalar-rung framing is therefore *structural-only*. The O.2 deep research (delivered 2026-04-25, verdict Scenario A strength 3/5) shows that a quantitative extension via the BHL auxiliary-field bridge is available; the activated quantitative-scope follow-up would be Wave 1b (`BHLGaugeEmbedding` transplant). Paper 20 is reframed as "structural identification" per roadmap's NO-branch fallback.

**Gate Z.2 — before Wave 3 begins:** ✅ **RESOLVED (2026-04-25 via O.2 delivery).** O.2 verdict: Scenario A (doublet-compatible) strength 3/5; literature-supported (BHL, MTY, Hill) but requires a transplant theorem `BHLGaugeEmbedding` that is not Wetterich-native. Wave 3 proceeds with direct SU(2) indices in the finite-T potential, citing BHL-class extension as load-bearing for the index structure.

**Gate Z.3 — optional paper gate:** If all three flagship deliverables produce consistent predictions, consider a unified Annals-length review paper bundling Waves 1–3 as a single "Scalar Condensate Ladder" paper rather than three independent papers. User decision — defer until Wave 2 + Wave 3 actually ship.

**Gate Z.4 — after Wave 4 ships (escalation gate to Phase 6h):** Did Wave 4 close positively (Λ_SMG → M_R lands in the 10⁹–10¹⁵ GeV seesaw band under Hasenfratz-Witzel scaling AND the substrate parameters plausibly sit in the SMG window per OPEN-W4-1)? If **YES** → escalate to **Phase 6h (Substrate Phase Diagram and Symmetric Mass Generation)** per `docs/roadmaps/Phase6h_Roadmap.md`. If **NO (second no-go)** → ship the strengthened obstruction paper (BCS *and* SMG ruled out for this substrate framing) and close the substrate-bridge derivation as impossible-in-current-substrate-models.

**Status update (2026-04-27 deep-research return):** **Gate Z.4 closes NEGATIVE.** The Wave 4 deep research at `Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate Phase Diagram.md` (verdict 2026-04-27) returned OPEN-AT-LITERATURE-FRONTIER on all three sub-questions, with literature-attested negative tilt: Vladimirov-Diakonov's own mean-field (PRD 86 104019, 2012) finds chiral-SSB and trivially-gapped phases but NO SMG phase in the published 2-parameter slice. Wave 4 ships as a **second structural no-go** parallel to Wave 2's BCS no-go. Phase 6h does NOT activate.

**Gate Z.4 reactivation criteria (concrete closure paths):** Phase 6h activation becomes ship-eligible if any of the following published research events occurs (per Wave 4 deep research §6 falsifiers):

- **(F-a-1) Lattice MC of V&D 8-coupling action identifies a chirally symmetric massive phase.** A 4D lattice Monte Carlo simulation of the Vladimirov-Diakonov (PRD 86 104019, 2012) 8-fermion action — currently un-simulated in any published work — identifies a chirally-symmetric massive phase (the SMG signature) with a 2nd-order transition into the massless phase. This is the most direct positive-closure path; difficulty is high (4D lattice MC of a non-gauge-theory action with 8 dimensionless couplings is a substantial computational effort, but no obstacle in principle).

- **(F-a-3) Kähler-Dirac extension of V&D reduces to KD SMG.** A theoretical demonstration that the V&D substrate, after augmentation to a full Kähler-Dirac multiplet (vertex + edge + face + tetrahedron + 4-cell components per Catterall-Laiho-Unmuth-Yockey PRD 98 114503, 2018), reduces to two copies of the Kähler-Dirac SMG action of Butt-Catterall-Pradhan-Toga (PRD 104 094504, 2021) in some limit. This would establish the SMG eligibility of ADW indirectly through the K-D bridge. Difficulty: medium (algebraic / representation-theoretic; the lattice content must fit Catterall's 4-reduced-KD = 16-Weyl framework).

- **(F-c-1) 4D analog of Fidkowski-Kitaev rigour for 16-Majorana SMG.** A 4D analog of the Fidkowski-Kitaev rigorous proof (PRB 81 134509, 2010) — currently the only rigorous mirror-decoupling proof, valid only in 2D — that proves 16-Majorana SMG gapping is rigorous in 4D rather than merely conjectural (Catterall arXiv:2311.02487 §4 explicitly conjectures this). This is the central open problem in lattice chiral gauge theory. Difficulty: very high (a major theoretical result that would close a decades-open problem).

If any one of these three events publishes, the Wave 4 ship verdict re-evaluates and Phase 6h becomes ship-eligible per its own roadmap. Until then Phase 6h remains a documented latent option. Two additional closure paths from the deep-research falsifier list (F-a-2 FRG analysis of V&D, F-a-4 anomaly-matching argument for V&D Razamat-Tong compatibility, F-b-1/2/3 Λ_SMG closed-form determinations, F-c-2/3 substrate-specific demonstrations) would each independently flip parts of Gate Z.4 — see `Lit-Search/Tasks/complete/Phase5z_W4_smg_substrate_phase_diagram.md` §6 for the full falsifier list.

---

## Dependencies

```
Track A: Wave 1 (ScalarRungInterpretation) → Gate Z.1
        Wave 1b (BHLGaugeEmbedding) — depends on Wave 1; activated by O.2 verdict

Track B: Wave 2 (MajoranaRung + NeutrinoMixing + MajoranaRungDecoupling)
  — independent of Track A; can run in parallel

Track B continuation: Wave 4 (MajoranaRungSMG)
  — depends on Wave 2 + Wave 1b; gated by Gate Z.4 → escalation to Phase 6h

Track C: Wave 3 (EWPhaseTransition)
  — depends on Wave 1; Gate Z.2 before start

Parallelism:
  Waves 1 and 2 independent → parallel execution possible
  Wave 1b after Wave 1 (quantitative follow-up)
  Wave 3 blocked on Wave 1 completion (not just start)
  Wave 4 after Wave 2 + Wave 1b (parallel with Wave 3 if execution warrants)
```

---

## Timeline

| Wave | Track | Scope | PM | Dependencies | Priority |
|------|-------|-------|-----|--------------|----------|
| Wave 1 | A | `ScalarRungInterpretation.lean` + flagship paper + Python scalar-rung package | 2–4 | None (Gate Z.2 before EW in Wave 3) | **TIER 0 — flagship** ✅ SHIPPED |
| Wave 1b | A | `BHLGaugeEmbedding.lean` (BHL transplant: gauge-indexed scalar channel + Hill bilocal correction) + paper 20 §6 | 1–2 | Wave 1 complete; O.2 verdict | **TIER 0 — quantitative-scope follow-up** ✅ SHIPPED 2026-04-26 |
| Wave 2 | B | `MajoranaRung.lean` + `NeutrinoMixing.lean` + `MajoranaRungDecoupling.lean` + PRD paper 21 + 2 figures + 2 notebooks | 2.5–4 | None; parallel with Wave 1 | **TIER 1** ✅ SHIPPED 2026-04-26 |
| Wave 3 | C | `EWPhaseTransition.lean` + conference paper 22 + Python ew_phase_transition package | 3–5 | Wave 1 complete; Gate Z.2 | **TIER 1** ✅ SHIPPED 2026-04-26 |
| **Wave 4** | **B-cont.** | **`MajoranaRungSMG.lean` + Paper 21 §-extension OR new short note + Python `src/majorana_rung/smg.py`** | **3–5** | **Wave 2 + Wave 1b complete; Gate Z.4 = escalation to Phase 6h** | **TIER 1 — substrate-bridge alternative; bypasses BCS no-go** **OPEN** |

**Total Phase 5z LOE:** **10.5–18 person-months** Lean + paper-writing. Parallel execution: wall-clock 5–9 months minimum.

**Deliverables cumulative (Waves 1–4):**
- 5 new Lean modules under Phase 5z scope on Wave-4 close: `ScalarRungInterpretation`, `BHLGaugeEmbedding`, `MajoranaRung` (+ `NeutrinoMixing`, `MajoranaRungDecoupling`), `EWPhaseTransition`, `MajoranaRungSMG`
- 4 new Python subpackages (`src/scalar_rung/`, `src/majorana_rung/`, `src/majorana_rung/smg.py` extension, `src/ew_phase_transition/`)
- 3 papers (Paper 20 flagship+§6 BHL, Paper 21 PRD Majorana with §7 SMG extension on W4 close, Paper 22 conference EW) + 1 short PMNS structure note
- ~51–68 new theorems
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

**Wave 4 (SMG Alternative for Majorana Rung) — OPEN:**
- `MajoranaRungSMG.lean` with 10–14 theorems, zero sorry
- Tracked-hypothesis SMG bypass of the Wave-2 BCS L-symmetry obstruction
- Hasenfratz-Witzel-anchored quantitative `M_R` prediction OR strengthened second no-go
- Paper 21 §7 extension OR new short note `papers/note_smg_majorana_rung/`
- **Program-level value:** if positive, escalates to **Phase 6h** for full substrate-phase-diagram + light-fermion-hierarchy-from-SMG program; if negative, closes substrate-bridge derivation as impossible-in-current-substrate-models
- **Correctness-push anchor:** `M_R` from substrate-SMG-gap (lattice-anchored prediction rather than fit) — completes the seesaw correctness-push that Wave 2 left as structural-only

**Cumulative program deliverables (Waves 1–4):**
- 5 new Lean modules (after W4), 4 new Python subpackages, 3 papers + 1 short note + 1 paper §-extension or short note (W4)
- ~51–68 new theorems, zero sorry target maintained, zero new axioms target
- Correctness-push anchors: `m_H` vs 125 GeV (5z.1), ℤ₁₆ singlet-mass compatibility (5z.2), transition-order (5z.3), substrate-anchored `M_R` from SMG (5z.4 OPEN)

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
- **Phase 6h (Substrate Phase Diagram and Symmetric Mass Generation) — conditional on Wave 4 positive close per Gate Z.4.** Phase 6h roadmap at `docs/roadmaps/Phase6h_Roadmap.md`. Wave 4 of Phase 5z becomes Wave 3 of Phase 6h (`MajoranaRungSMG.lean` promoted, with PMNS via Catterall-Pati-Salam structure added).

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §3

**Correctness-push highlights from strategy doc §12:**
- 5z.1: Predicted `m_H` vs 125 GeV — falsifies scalar-rung framing as quantitative EWSB theory

---

*Phase 5z roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. First new phase after Phase 5y closure. Originally three waves (scalar rung, Majorana rung, EW phase transition), three correctness-push anchors, three papers + one short note. **Updated 2026-04-27 with Wave 4 (`MajoranaRungSMG.lean`) — OPEN follow-up to Wave 2 BCS no-go via Symmetric Mass Generation alternative; conditional Gate Z.4 escalation to Phase 6h.** All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 10.5–18 Lean + paper-writing including Wave 4.*
