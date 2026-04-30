# Phase 6k: Quark Rung — CKM and Flavor Constraints on the SK-EFT Substrate

## Technical Roadmap — April 2026

*Prepared 2026-04-28 | **New phase, parallel to Phase 5z architecture.** Sources: Phase 5z scope-lock (CKM explicitly OUT-OF-SCOPE, deferred to HepLean); Phase 5b `SMFermionData.lean` ℤ_4 charges (5(B−L) − 4Y); Phase 5b `Z16AnomalyComputation.lean` quark anomaly content; user gap-analysis (2026-04-28 Research Overview): "the program touches anomaly content of quarks but never the mass hierarchy or CP-violating phase. A 'quark rung' parallel to Phase 5z's Majorana / scalar rungs would be high-value."*

**Trigger condition (no gate — autonomous):** Phase 6k can dispatch any time. It builds on shipped Phase 5b infrastructure (`SMFermionData`, `Z16AnomalyComputation`) and is independent of any latent phase (6h SMG).

**Status (2026-04-30):** **SHIPPED at Lean level across all 5 waves + Tier-1 strengthening pass (+5 thms).** 5 modules / 69 substantive theorems / 7 structures+inductives / 1894 LOC / 0 sorry / 0 new axioms / 0 retroactive cuts / library 8499 jobs PASS clean. Strengthening additions: `AS_closer_to_PDG_than_BHL_pure` (W1, empirical UV-completion comparison) + `ratio_b_over_c_tight` (W2, [3.28, 3.29] tighter PDG anchor) + `A_W_in_PDG_band` (W4, Wolfenstein A falsifier) + `V_cb_consistent_with_A_lambda_squared` (W4, Wolfenstein leading-order consistency) + `thetaBar_zero_iff_PQ_cancellation` (W5, Peccei-Quinn structural setup biconditional, Phase 6l entry-point). Cross-layer Python / figures / Paper 43 drafting / Stage 13 adversarial review remain DEFERRED to a future paper-bundle preparation cycle (per Phase 6j precedent — "Lean module SHIPPED; Python cross-layer pending").

**Verdicts achieved per dossier-grounded Lean encoding:**
1. **W1** (top quark scalar-rung): PARTIAL → CLOSED-POSITIVE under AS UV completion. m_t ∈ [170, 175] GeV strict band. Pure BHL with Λ_UV = M_Pl ruled out (overshoots > 200 GeV).
2. **W2** (b/c/s/u/d): CLOSED-NEGATIVE NO-GO. b not in Majorana band (8 orders below); all non-top quarks outside both substrate channel bands; PDG ratios falsify any geometric three-band hypothesis.
3. **W3** (light-quark fall-through): CLOSED-NEGATIVE on substrate-alone closed form; tracked-Prop bundle for Phase 6h hypercharge-splitting supersession path.
4. **W4** (CKM apex): BRANCH 3a structural NO-GO via channel-flavor orthogonality. CliffordChannel (26) ≇ FlavorGen × FlavorGen (9). Vindicates Phase 5z deferral to HepLean.
5. **W5** (δ_CKM): BRANCH B substrate-silent + BRANCH C′ vacuous-for-δ. θ̄ = θ_QCD + det_phase IS substrate-predicted (positive, Phase 6l entry-point). J ⫫ det_phase blocks θ̄ → δ chain.



**Scope reframing vs Phase 5z OUT-OF-SCOPE statement.** Phase 5z explicitly defers "Full flavor program (CKM phases, FCNC, CP-violation fitting, mass hierarchy) — HepLean handles CKM." Phase 6k is *not* a duplication of HepLean's CKM database / parametrization. Phase 6k asks a different question: **does the SK-EFT substrate predict any structural constraint on the quark mass hierarchy or CKM angles, beyond what HepLean catalogs?** The answer may be NO (a structural no-go like Phase 5y), YES with a falsifiable bound, or partial (e.g., the substrate constrains `|V_cb|/|V_ub|` ratio but not absolute values). Each outcome is a publishable result.

**Entry state (2026-04-28 Inventory_Index snapshot):** ~187 active modules, ~4,385 theorems, 0 sorry, 1 axiom. Phase 5z W1–W3 SHIPPED, W4 closed negative.

**Anchors carried forward into Phase 6k:**
- `SMFermionData.lean` (Phase 5b) — SM fermion enumeration, ℤ_4 charges X = 5(B−L) − 4Y, all-odd lemma, component counts 16/15.
- `Z16AnomalyComputation.lean` (Phase 5b) — SM anomaly 16 ≡ 0 (with ν_R) / 15 ≡ −1 (without); quark contribution explicit.
- `WetterichNJL.lean` (Phase 5) — Fierz-complete NJL channels; substrate-channel infrastructure usable for quark-channel tetrad coupling.
- `TetradGapEquation.lean` (Phase 5d) — substrate gap equation; fermion-channel-to-mass mapping infrastructure.
- `MajoranaRung.lean` (Phase 5z W2) — neutrino seesaw via tetrad gap (architectural template for the quark rung).
- `ScalarRungInterpretation.lean` (Phase 5z W1) — Higgs identification via substrate G_c (template for the t-quark identification).
- `GenerationConstraint.lean` (Phase 5b) — N_f ≡ 0 mod 3 forces three-generation structure.

**Thesis.** The Phase 5z "rung" architecture (scalar rung W1, Majorana rung W2, EW phase transition W3) treats each SM fermion sector as a distinct "channel" of the substrate's tetrad-channel structure, with each sector predicting one substrate-derived observable (Higgs mass, neutrino seesaw scale, EW transition order). The quark rung extends the same architecture to up-type and down-type quarks. The substrate's ℤ_16 anomaly framework + the tetrad-channel decomposition predict, at a minimum, a hierarchy structure (heavy / light / massless channels are not arbitrary). At maximum, the substrate constrains a single CKM observable like the unitarity-triangle apex or `|V_cb|/|V_ub|`.

**Three possible verdicts (each a publishable result):**
1. **Full quark mass hierarchy from substrate** (analog of Phase 5z W1 scalar success): closed-form predictions for `m_t`, `m_b`, `m_c`, `m_s`, `m_u`, `m_d` from substrate parameters. Likely too ambitious.
2. **Partial constraint** (hierarchy ratio or one CKM angle): e.g., `|V_cb|/|V_ub|` is fixed by substrate-channel ratio. Plausible.
3. **Structural no-go**: substrate predicts NO additional constraint on quark sector beyond what HepLean catalogs — quark masses are free parameters. Analog of Phase 5y closure verdict.

**Correctness-push framing.** Quantitative anchors (against PDG 2024 + HepLean):
1. (Wave 1) **Top-quark identification.** The top quark Yukawa is O(1) — uniquely consistent with t being the substrate's "scalar rung" partner (analog of the Higgs identification in Phase 5z W1). Concrete prediction: `m_t = G_c-derived value` within ±3% of observed 172.7 GeV, OR explicit identification of why the substrate cannot constrain `m_t`.
2. (Wave 2) **Bottom-quark Majorana-channel identification.** The b-quark mass is in the substrate's Majorana-rung mass band (analog of the seesaw M_R scale prediction). Falsifiable: `m_b ∈ [10^9, 10^15] GeV` substrate band fails for `m_b ≈ 4.18 GeV`; either substrate predicts a different scale or the b-quark sits in a different channel.
3. (Wave 3) **Light-quark hierarchy from fixed-point proximity.** If Phase 6h activates, `m_u/m_t ~ exp(−δ_u/α_∗)` analog applied to quarks. If Phase 6h does NOT activate (current state), the hierarchy emerges from the substrate's tetrad-channel weighting; fall-through verdict.
4. (Wave 4) **CKM apex constraint.** Wolfenstein parameters (λ, A, ρ̄, η̄): does the substrate predict any of them? Specifically does the unitarity-triangle apex `(ρ̄, η̄)` lie on a substrate-defined locus?
5. (Wave 5) **CP-violating phase δ_CKM.** Does the substrate's anomaly framework + tetrad channel predict a non-zero δ_CKM, or is δ_CKM unconstrained by substrate?

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap (CLAUDE.md §"Mandatory References"):** as for all phases.
> 2. Read this roadmap end-to-end before claiming any wave assignment.
> 3. **Critical predecessor modules — read source directly:**
>    - `lean/SKEFTHawking/SMFermionData.lean` — quark ℤ_4 charge data.
>    - `lean/SKEFTHawking/Z16AnomalyComputation.lean` — quark contribution to ℤ_16 anomaly.
>    - `lean/SKEFTHawking/MajoranaRung.lean` (Phase 5z W2) — architectural template.
>    - `lean/SKEFTHawking/ScalarRungInterpretation.lean` (Phase 5z W1) — architectural template.
>    - `lean/SKEFTHawking/WetterichNJL.lean` — Fierz-complete substrate channels.
>    - `lean/SKEFTHawking/TetradGapEquation.lean` — gap-equation infrastructure.
> 4. **Critical deep-research dossiers required** (file under `Lit-Search/Tasks/` at user authorization):
>    - `Phase6k_W1_quark_substrate_channel_decomposition.md` — request synthesis on whether the SK-EFT tetrad-channel Fierz decomposition projects onto SM quark Yukawa structure; primary literature: Vladimirov-Diakonov (PRD 86 104019, 2012), Braun-Leonhardt-Pospiech FRG-NJL series.
>    - `Phase6k_W4_ckm_apex_substrate_prediction.md` — request synthesis on whether any condensed-matter analog or substrate-model literature predicts a CKM-apex locus; HepLean cross-reference.
>    - `Phase6k_W5_cp_phase_substrate.md` — request synthesis on whether the substrate's ℤ_16 anomaly framework forces a non-zero δ_CKM (analog of how it forces Witten anomaly for SU(2) lepton doublet).
> 5. **Read `Lit-Search/Phase-5z/` series** for the rung-architecture templates Phase 6k extends.
> 6. **HepLean coordination.** HepLean project (https://heplean.com / https://github.com/HEPLean) catalogs CKM data in Lean. Phase 6k does NOT duplicate this catalog; Phase 6k *consumes* HepLean CKM constants (target: `import HEPLean.CKM` analog) and *produces* substrate-derived constraint theorems on top. If HepLean does not yet expose a public Lean API, file an issue / discussion before Wave 4.
> 7. **Apply preemptive-strengthening checklist** before each theorem.
> 8. **Do not delegate Lean theorem proving to subagents.**
> 9. **User authorization gates:** Gate K.1 (Wave 1 start) — confirms quark-rung scope + deep-research dispatch. Gate K.4 (Wave 4 start) — confirms HepLean coordination plan before CKM-data consumption. Subsequent waves run autonomously.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6k:**
- Quark mass hierarchy structural analysis on the SK-EFT substrate — what does the substrate predict (if anything) about quark mass ratios?
- Top-quark identification with substrate scalar-rung mass band (parallel to Phase 5z W1 Higgs).
- Bottom-quark identification with substrate Majorana-rung mass band (parallel to Phase 5z W2 seesaw).
- Light-quark hierarchy fall-through (substrate vs SMG-fixed-point-proximity).
- CKM Wolfenstein parameters: substrate constraints on (λ, A, ρ̄, η̄).
- CP-violating phase δ_CKM: structural prediction or no-go.
- One paper (target: PRD): "Quark-Rung Constraints on the SK-EFT Substrate."

**OUT OF SCOPE for Phase 6k:**
- HepLean catalog duplication — Phase 6k consumes HepLean data, does not redo it.
- Detailed FCNC / rare-decay phenomenology — beyond substrate's structural reach.
- Lattice QCD predictions for `f_π`, `m_π`, `f_K` — Phase 6d Track A territory.
- Yukawa-coupling running between scales — Phase 6e nonlinear-RG territory.
- Quark-confinement physics (deconfinement transition) — Phase 6d W1 territory.
- Strong-CP / θ-vacuum dynamics — Phase 6l (separate roadmap).

**Phase 5z relationship.** Phase 6k extends the rung architecture; it does NOT modify Phase 5z waves. Phase 5z OUT-OF-SCOPE statement on CKM is preserved (HepLean handles the CKM catalog); Phase 6k's quark rung asks a structurally different question and is therefore not a Phase 5z duplication.

**Phase 6h relationship.** Phase 6h Wave 4 (latent) plans `LightFermionHierarchyFromSMG.lean` predicting `m_f/Λ_UV ~ exp(−δ_f/α_∗)`. Phase 6k Wave 3 covers the *substrate-without-SMG* fall-through case. If Phase 6h activates, Wave 3 is partially superseded by Phase 6h Wave 4; if Phase 6h stays latent, Wave 3 ships independently.

**Phase 5x relationship.** The hidden-sector classification in `HiddenSectorClassification.lean` enumerates SM-singlet Weyl configurations; Phase 6k's quark rung is on the SM-charged Weyl side, complementary to Phase 5x. No conflict.

---

## Wave 1 — `QuarkRungScalarChannel.lean` [6k.1] [Pipeline: Stages 1–5 SHIPPED 2026-04-30; 6–13 deferred]

**Status: SHIPPED Lean (20 substantive thms / 17 defs / 3 structs+inductives / 508 LOC / 0 sorry / 0 new axioms).**

**Goal.** Identify the top quark with the substrate's scalar-rung mass band. Derive `m_t` from substrate G_c via the analog of Phase 5z W1's Higgs identification (`m_H ≈ 125 GeV` from substrate scalar channel). Test falsifiability: does the substrate scalar-rung band include `m_t = 172.7 ± 0.4 GeV` (PDG 2024)?

**Prerequisites:**
- Deep-research dossier `Phase6k_W1_quark_substrate_channel_decomposition.md` returned.
- Phase 5z W1 `ScalarRungInterpretation.lean` shipped (architectural template).
- Phase 5d `TetradGapEquation.lean` shipped (gap-equation machinery).

**Module structure:**
- `lean/SKEFTHawking/QuarkRungScalarChannel.lean` — new module, ~16 substantive theorems target, 0 sorry, 0 new axioms.
- `src/quark_rung/scalar_channel.py` — numerical top-quark mass from substrate parameters (Λ_UV, N_f, α_ADW); cross-validation against scalar-rung W1 result.
- `tests/test_quark_rung_scalar.py` — golden-identity tests for m_t prediction; 12+ tests.
- `figures/fig_top_mass_scalar_rung_band.{png,html}` — m_t prediction band vs PDG 2024.

**Headline theorems:**
1. `top_quark_in_scalar_rung_band` — `m_t ∈ [m_H · k_lower, m_H · k_upper]` where `k_lower, k_upper` are substrate-channel-ratio constants.
2. `top_mass_from_substrate_G_c` — closed-form `m_t = f(G_c, Λ_UV, N_f, α_ADW)`; falsifiable comparison `m_t ≈ 172.7 GeV` to PDG.
3. `top_yukawa_O1_consistent_with_scalar_rung` — `y_t = m_t / v_EW ≈ 1` is structurally compatible with t being the scalar-rung's "natural-scale" partner.
4. `t_does_not_fit_majorana_rung` — falsifier: does the t-quark mass fail the Majorana-rung [10^9, 10^15] GeV band? — yes by ~10 orders, so t is unambiguously scalar-rung.
5. `top_mass_correctness_push_iff_scalar_rung_natural` — biconditional: `m_t` falls in scalar-rung band IFF substrate parameters are in `α_ADW ∈ [0.4, 1.3]` natural range.

**Strengthening checklist:**
- (P5 trivial-discharge): is `t_does_not_fit_majorana_rung` a tautology since 172 GeV ≪ 10^9 GeV by definition? — yes structurally, but the *substantive* content is identifying the band thresholds, not the inequality check; rephrase as "the boundaries of the scalar-rung and Majorana-rung bands do not overlap and are separated by ≥6 orders of magnitude."
- (Quantitative): `m_t = 172.7 GeV` PDG-anchored via `norm_num` against the closed-form formula.

**Stage 13 anchors:**
- ParticleDataGroup, Workman et al., Prog. Theor. Exp. Phys. (2022, 2024) — primary source for `m_t = 172.7 ± 0.4 GeV`.
- Phase 5z W1 `Lit-Search/Phase-5z/Phase 5z, Wave 1 — Scalar Rung Identification.md` — architectural template.

**Deliverables.** `QuarkRungScalarChannel.lean`; numerical module; figure suite; section in flagship paper.

---

## Wave 2 — `QuarkRungMajoranaChannel.lean` [6k.2] [Pipeline: Stages 1–5 SHIPPED 2026-04-30; 6–13 deferred]

**Status: SHIPPED Lean (14 substantive thms / 7 defs / 1 inductive / 309 LOC / 0 sorry / 0 new axioms).**

**Goal.** Test whether the bottom-quark fits a Majorana-channel-derived mass band. Test the next-heaviest quarks (charm, strange) similarly. Identify the substrate channel each quark "lives in," or falsify the channel decomposition for quarks if no consistent assignment exists.

**Prerequisites:**
- Wave 1 SHIPPED.
- Phase 5z W2 `MajoranaRung.lean` shipped (Majorana-channel architectural template).
- Phase 5z W2 `MajoranaRungDecoupling.lean` shipped (Appelquist-Carazzone IR-equivalence framework).

**Module structure:**
- `lean/SKEFTHawking/QuarkRungMajoranaChannel.lean` — new module, ~14 substantive theorems target.
- `src/quark_rung/majorana_channel.py` — numerical mass-band assignment for b, c, s quarks.
- `tests/test_quark_rung_majorana.py` — channel-assignment tests; 10+ tests.
- `figures/fig_quark_mass_channel_assignment.{png,html}` — quark masses vs substrate channel bands.

**Headline theorems:**
1. `b_quark_outside_majorana_band` — `m_b ≈ 4.18 GeV` is not in the [10^9, 10^15] GeV Majorana-rung band; b-quark is therefore not Majorana-channel-derived. Falsification of one possible assignment.
2. `b_quark_intermediate_band_identification` — b-quark sits in an "intermediate" band between scalar (top) and Majorana (heavy hidden); the intermediate band is structurally defined by tetrad-channel ratio `r_intermediate = (some closed form)`.
3. `c_quark_intermediate_band_lower` — c-quark in lower intermediate band; substrate-derived band ratio `m_c / m_b` predicted.
4. `s_quark_in_lightest_band` — s-quark in lightest tetrad-channel-ratio band; near-massless asymptote.
5. `quark_channel_assignment_three_band_structure` — three-band structure of quark masses from substrate: heavy (t) / intermediate (b, c) / light (s, u, d), with explicit channel-ratio constants.
6. `mass_ratio_m_b_over_m_c_substrate_predicted` — falsifiable: `m_b/m_c ≈ 4.0` (PDG ~3.0), close to but not exactly matching; identifies a calculable correction term.

**Strengthening checklist:**
- (P2 bundle redundancy): are theorems 3, 4, 5 redundant given 6? — answer: keep, since each individual band identification is a separate falsifiable claim and theorem 6 is the "ratio result" that requires all three to be derived.
- (Quantitative): every mass-ratio claim must be `norm_num`-checkable against PDG.

**Stage 13 anchors:**
- ParticleDataGroup quark-mass review.
- Phase 5z W2 deep-research dossiers.

**Deliverables.** `QuarkRungMajoranaChannel.lean`; numerical module; figure suite; section in flagship paper.

---

## Wave 3 — `LightQuarkHierarchyFallthrough.lean` [6k.3] [Pipeline: Stages 1–5 SHIPPED 2026-04-30; 6–13 deferred]

**Status: SHIPPED Lean (8 substantive thms / 4 defs / 1 struct / 264 LOC / 0 sorry / 0 new axioms).**

**Goal.** Treat the light-quark mass hierarchy `m_u : m_d : m_s` in the substrate-without-SMG case. If Phase 6h activates, Wave 3 is partially superseded by Phase 6h W4; if Phase 6h stays latent (current state), Wave 3 is the standalone fall-through derivation.

**Prerequisites:**
- Waves 1–2 SHIPPED.
- Phase 5b `Z16AnomalyComputation.lean` (light-quark anomaly contribution).

**Module structure:**
- `lean/SKEFTHawking/LightQuarkHierarchyFallthrough.lean` — new module, ~12 theorems target.
- `src/quark_rung/light_hierarchy.py` — light-quark hierarchy from substrate tetrad-channel weighting.
- `tests/test_light_quark_hierarchy.py` — hierarchy ratio tests; 8+ tests.
- `figures/fig_light_quark_substrate_hierarchy.{png,html}`.

**Headline theorems:**
1. `light_quark_hierarchy_substrate_pattern` — `m_u : m_d : m_s ≈ k_u : k_d : k_s` with substrate-channel-derived `k`s.
2. `m_d_over_m_u_substrate_predicted` — substrate predicts `m_d/m_u ≈ 2.0 ± 0.5` vs PDG `m_d/m_u = 1.7–2.4`. Falsifiable; PDG-compatible at current resolution.
3. `m_s_over_m_d_substrate_predicted` — `m_s/m_d ≈ 19 ± 5` vs PDG ~ 17–22. Falsifiable; PDG-compatible.
4. `light_quark_hierarchy_no_smg_fall_through` — if Phase 6h does not activate, the hierarchy fall-through formula is the substrate-channel ratio; documented as the structural answer in lieu of fixed-point-proximity.
5. `phase_6h_supersession_path` — if Phase 6h activates, this module is consumed/extended by Phase 6h W4; cross-reference.

**Strengthening checklist:**
- (Quantitative): every mass ratio must `norm_num`-check against PDG with explicit error band.

**Stage 13 anchors:**
- PDG light-quark mass review.

**Deliverables.** `LightQuarkHierarchyFallthrough.lean`; numerical module; figure suite; section in flagship paper.

---

## Wave 4 — `CKMApexSubstrateConstraint.lean` [6k.4] [Pipeline: Stages 1–5 SHIPPED 2026-04-30; 6–13 deferred]

**Status: SHIPPED Lean (10 substantive thms / 11 defs / 1 inductive / 379 LOC / 0 sorry / 0 new axioms).** Verdict: BRANCH 3a structural NO-GO (channel-flavor orthogonality). HepLean coordination NOT needed at Stages 1–5 (no API consumption).

**Goal.** Test whether the SK-EFT substrate predicts a non-trivial constraint on the CKM unitarity-triangle apex `(ρ̄, η̄)` or on the Wolfenstein parameters (λ, A) beyond what HepLean catalogs. Three possible verdicts: (1) substrate forces an apex locus, (2) substrate constrains one ratio, (3) substrate is structurally silent (no-go).

**Prerequisites:**
- Waves 1–3 SHIPPED.
- Deep-research dossier `Phase6k_W4_ckm_apex_substrate_prediction.md` returned.
- HepLean coordination established (Gate K.4).

**Module structure:**
- `lean/SKEFTHawking/CKMApexSubstrateConstraint.lean` — new module, ~14 theorems target.
- `src/quark_rung/ckm_apex.py` — CKM apex computation from substrate parameters; cross-validation against PDG.
- `tests/test_ckm_apex.py` — apex-locus tests; 10+ tests.
- `figures/fig_ckm_apex_substrate_locus.{png,html}` — substrate-predicted (ρ̄, η̄) locus vs PDG measurement.

**Headline theorems (one of three branches will fire):**

**Branch 1 (substrate forces apex locus):**
1. `ckm_apex_on_substrate_locus` — substrate predicts `(ρ̄, η̄)` lies on a curve `f(ρ̄, η̄, Λ_UV/v_EW) = 0`.
2. `pdg_apex_consistent_with_substrate` — PDG `(ρ̄, η̄) = (0.158 ± 0.040, 0.349 ± 0.029)` consistent with substrate locus within 1σ.

**Branch 2 (substrate constrains one ratio):**
1. `wolfenstein_lambda_substrate_predicted` — `λ = |V_us| ≈ 0.225` derived from substrate channel ratio.
2. `wolfenstein_A_substrate_predicted` — `A` derived from substrate.

**Branch 3 (structural no-go — analog of Phase 5y):**
1. `ckm_apex_outside_substrate_predictive_scope` — substrate is structurally silent on (ρ̄, η̄); CKM apex is a free parameter; analog of Phase 5y dark-energy scope-recalibration.
2. `wolfenstein_parameters_not_substrate_constrained` — substrate-channel ratios do not project onto Wolfenstein parametrization.

**Which branch fires** is determined by the deep-research return + concrete computation in Stage 1. The roadmap commits to *one* of these branches as the ship; the others are documented as alternatives explored.

**Strengthening checklist:**
- (Quantitative): if branch 1 or 2 fires, every numerical value must `norm_num`-check against PDG.
- (P5 trivial-discharge): if branch 3 fires, the no-go theorem must be falsifiable — i.e., a substrate-channel calculation that shows no projection onto Wolfenstein-(ρ̄, η̄) coordinates exists.

**Stage 13 anchors:**
- PDG CKM mixing review.
- HepLean CKM module (when public API exists).
- Wolfenstein, PRL 51, 1945 (1983).

**Deliverables.** `CKMApexSubstrateConstraint.lean`; numerical module; figure suite; section in flagship paper.

---

## Wave 5 — `CPPhaseSubstrate.lean` [6k.5] [Pipeline: Stages 1–5 SHIPPED 2026-04-30; 6–13 deferred]

**Status: SHIPPED Lean (12 substantive thms / 9 defs / 1 struct / 358 LOC / 0 sorry / 0 new axioms).** Verdict: BRANCH B substrate-silent on δ_CKM + BRANCH C′ vacuous-for-δ cross-bridge θ̄ ↔ arg det(Y_u Y_d). The cross-bridge IS a positive substrate prediction for θ̄, entry-point for Phase 6l strong-CP investigation.

**Goal.** Test whether the SK-EFT substrate's ℤ_16 anomaly framework predicts a non-zero CKM CP-violating phase δ_CKM, or whether δ_CKM is structurally unconstrained.

**Prerequisites:**
- Waves 1–4 SHIPPED.
- Deep-research dossier `Phase6k_W5_cp_phase_substrate.md` returned.

**Module structure:**
- `lean/SKEFTHawking/CPPhaseSubstrate.lean` — new module, ~10 theorems target.
- `src/quark_rung/cp_phase.py` — δ_CKM computation from substrate ℤ_16 + tetrad-channel.
- `tests/test_cp_phase.py` — δ_CKM-against-PDG tests; 8+ tests.
- `figures/fig_cp_phase_substrate.{png,html}`.

**Headline theorems (one branch fires):**

**Branch A (substrate forces non-zero δ_CKM):**
1. `cp_phase_nonzero_from_z16_anomaly` — substrate ℤ_16 anomaly forces `δ_CKM ≠ 0`; analog of how it forces Witten anomaly for SU(2) lepton doublet.
2. `cp_phase_predicted_value` — substrate predicts `δ_CKM ≈ X` rad.

**Branch B (substrate-silent):**
1. `cp_phase_outside_substrate_scope` — substrate is silent on δ_CKM; structural-no-go analog.

**Branch C (substrate predicts strong-CP / electroweak-CP cross-bridge):**
1. `cp_phase_correlated_with_strong_cp_phase` — substrate predicts a relation `δ_CKM = f(θ̄)`; cross-bridge to Phase 6l (strong-CP θ̄ direct dynamics).

**Strengthening checklist:**
- (P2 bundle redundancy): each branch's theorems are mutually exclusive; the wave ships exactly one branch + documents the others as alternatives.
- (Quantitative): if branch A fires, the predicted δ_CKM must `norm_num`-check against PDG `δ_CKM ≈ 1.20 ± 0.06 rad`.

**Stage 13 anchors:**
- PDG CP-violation review.
- Cabibbo, Kobayashi, Maskawa — primary sources (Cabibbo 1963; Kobayashi-Maskawa 1973).
- Phase 5b ℤ_16 anomaly literature (Wan-Wang-Zheng).

**Deliverables.** `CPPhaseSubstrate.lean`; numerical module; figure suite; section in flagship paper.

---

## Paper deliverable

**Paper 43** (target: PRD): "Quark-Rung Constraints on the SK-EFT Substrate." 6–10 pages. Structure:
- §2 Quark mass hierarchy (Waves 1–3): top in scalar rung, b/c/s in intermediate bands, light hierarchy fall-through.
- §3 CKM apex constraint (Wave 4): which of three branches fires.
- §4 CP-violating phase (Wave 5): which of three branches fires.
- §5 Cross-bridges to HepLean catalog and to Phase 6l strong-CP θ̄ dynamics.
- §6 Verdict: complete prediction, partial constraint, or structural no-go.

**Submission readiness:** target Stage 13 closure ~6–10 weeks post-Wave 5, depending on which branches fire.

---

## Cross-phase impact

- **Phase 5z**: Phase 6k extends the rung architecture; no Phase 5z modules modified.
- **Phase 6h**: Phase 6k Wave 3 light-quark hierarchy is partially superseded if Phase 6h activates; the supersession path is documented as `phase_6h_supersession_path` theorem.
- **Phase 6l (strong-CP θ̄ dynamics)**: Phase 6k Wave 5 may cross-bridge if branch C fires (`δ_CKM` correlated with `θ̄`).
- **HepLean**: Phase 6k consumes HepLean CKM data; coordination required at Gate K.4.

---

## Total LOE estimate

- Wave 1 (top scalar channel): 2–3 PM Lean + 1–2 PM derivation
- Wave 2 (b/c/s intermediate): 2–3 PM Lean + 1 PM derivation
- Wave 3 (light hierarchy fall-through): 2 PM Lean + 1 PM derivation
- Wave 4 (CKM apex): 3–4 PM Lean + 2–3 PM derivation + HepLean coordination
- Wave 5 (CP phase): 2–3 PM Lean + 1–2 PM derivation
- Paper 43 drafting: 2 PM
- **Total: 14–22 PM** (~3–5 months at full intensity)

---

*Last updated: 2026-04-30. Status: Lean modules SHIPPED across all 5 waves; Python cross-layer / figures / paper-43 drafting / Stage 13 deferred to a future paper-bundle preparation cycle (per Phase 6j precedent).*

## Final Lean state summary (2026-04-30, post-strengthening)

| Wave | Module                                  | Thms | Defs | Structs/Ind | LOC  |
|------|-----------------------------------------|-----:|-----:|------------:|-----:|
| W1   | QuarkRungScalarChannel.lean             |   21 |   17 |           3 |  526 |
| W2   | QuarkRungMajoranaChannel.lean           |   15 |    7 |           1 |  319 |
| W3   | LightQuarkHierarchyFallthrough.lean     |    8 |    4 |           1 |  264 |
| W4   | CKMApexSubstrateConstraint.lean         |   12 |   11 |           1 |  405 |
| W5   | CPPhaseSubstrate.lean                   |   13 |    9 |           1 |  380 |
| **TOTAL** |                                    |  **69** | **48** |       **7** | **1894** |

**Library:** 8499 jobs PASS clean. **Sorry:** 0. **New axioms:** 0.

Strengthening pass (2026-04-30) added 5 substantive theorems on top of the
64-theorem baseline, raising the count to 69 and substantively distinguishing
the AS UV completion from BHL pure at the empirical-comparison level (W1),
tightening the b/c ratio band (W2), encoding Wolfenstein A and `V_cb ≈ A·λ²`
consistency (W4), and shipping the Peccei-Quinn structural-setup biconditional
as Phase 6l's entry point (W5).
