# Phase 6m: Untested Dark-Energy Mechanism Probes (Phase 5y Reframe)

## Technical Roadmap — April 2026

*Prepared 2026-04-28 | **New phase, structurally parallel to Phase 5y.** Sources: `docs/ARCHITECTURE_SCOPE.md` (Phase 5y closure verdict 2026-04-23: "obstruction covers Volovik-family mechanisms specifically; entropic gravity, causal-set approaches, Jacobson-type thermodynamic GR are outside the tested scope"); user gap-analysis (2026-04-28 Research Overview): "the Volovik family is closed, but the closure was deliberately scoped — the architecture-scope memo flags entropic gravity, causal sets, and Jacobson-type thermodynamic GR as untested. Each is a candidate for a Phase 5y-style 6-round probe."*

**Trigger condition (no gate — autonomous):** Phase 6m can dispatch any time. It is independent of all other Phase 6 roadmaps.

**Status (2026-04-30):** **R1-R5 SHIPPED + R6 Lean closure SHIPPED + ruthless strengthening pass + cross-module proof-chain pass SHIPPED across all three tracks + Wave 4 consolidation. Phase 6m FULLY CLOSED at the Lean-formalization scope.** 4 new modules / **50 substantive thms** (51 first-pass → 44 post-strengthening → 50 with +6 cross-module proof-chain bridges) / 0 sorry / 0 new axioms / library 8507 jobs PASS. **Phase 6m modules now CALL Phase 5y `DESIComparison.InDESIRegion` and `DarkEnergyObstructionPrinciple.IsViable` in proof bodies** — DEC and Lovelock both ¬InDESIRegion `desiDR2_1sigma`; DEC and Hu-Sawicki both fail `IsViable` via `viability_iff_all_four`; existential Class-(c) → orthogonality-failure witness in DSCE11. **Phase 6m material → D5 §8–§12 + §10.5/§11.5 per `PAPER_DRAFT_MAPPING.md` (updated 2026-04-30); D5 drafting scheduled in `Phase7_Roadmap.md` Wave 3.** D5 §10.5 + §11.5 strategy-consistent drafts at `temporary/working-docs/d5_section_10_5_barrow_prescription_dependence.md` + `d5_section_11_5_sakharov_lambda_j_vs_lambda_hk.md` (originals preserved at `short_note_*`).

**R1 outcomes:**
- **Track A (Causal-Set DE):** 5 mechanisms surveyed; 3 CLEARED → R2 (Sorkin everpresent-Λ Models 1+2; BDG action-fluctuation DE); 1 NO-GO at R1 (causal-set d'Alembertian — gives DM not DE; 4D B̃ instability); 1 OPEN-AT-FRONTIER. **Headline structural finding:** Phase 5y GD obstruction is structurally inapplicable to causal-set DE (combinatorial d.o.f., not thermodynamic-scalar) — first non-Volovik entrant outside GD universality class.
- **Track B (Entropic-Gravity DE):** 9 candidates enumerated; 3 FALSIFIED at 2.8-4.2σ (Verlinde 2017, Padmanabhan/CosMIn, Hossenfelder-Verlinde — all predict exact ΛCDM, sharing ΛCDM's empirical fate); 1 NOT a DE candidate (Verlinde 2011); 5 MARGINAL → R2 (Cadoni-Tuveri DEC, HDE event-horizon, Tsallis HDE, Barrow HDE, Odintsov-D'Onofrio-Paul 4-param). **Headline:** clean taxonomy distinguishing class (a) self-tuning-by-clever-dynamics from class (b) self-tuning-as-no-scalar-to-tune.
- **Track C (Jacobson-Thermo-GR DE):** 9 mechanisms enumerated; 2 ELIMINATED (Verlinde 2010, EFS); 6 SURVIVORS → R2 (M1 Jacobson 1995, M2/M7 Padmanabhan/CosMIn, M3 Eling-Guedens-Jacobson f(R), M4 Cai-Cao Lovelock subset, M8 KSS Lorentz-violating superfluid, M9 Volovik-Jannes Weyl-superfluid substrate). **Headlines:** (i) GD obstruction structurally inapplicable to Jacobson class (no Lagrangian scalar in relevant sector); (ii) Λ_J (Jacobson integration constant) and Λ_HK (Seeley-DeWitt heat-kernel a₀) are NOT dual descriptions — they are independent contributions, substrate-dependent agreement (Λ_J = Λ_HK on Volovik-Jannes ³He-A; differ on Finazzi-Liberati-Sindoni acoustic-BEC). Phase 6e cross-bridge anchor.

**R2 outcomes:**
- **Track A (Causal-Set DE):** 0 CLEARED-R2, 3 NEEDS-R3 (all R1 survivors), 1 NO-GO-R2 reconfirmed (causal-set d'Alembertian). **Three convergent structural gaps prevented R2 clearance:** (i) no published DESI DR2 ensemble fit; (ii) Barrow-bound evasion is prescription-dependent — *publishable structural caveat* (Zwane-Afshordi-Sorkin 2018 covariant prescription is one admissible regularization, not uniqueness-forced); (iii) BDG first-principles σ_Λ propagation through Friedmann is unfinished; (iv) c_s² = 1 is by prescription, not derived. R1 GD-inapplicability finding **reinforced under R2** across all admissible prescription branches.
- **Track B (Entropic-Gravity DE):** 0 CLEARED-R2, **4 NO-GO-R2** (Cadoni-Tuveri DEC, HDE event-horizon, Tsallis HDE, Barrow HDE), 1 NEEDS-R3 (Odintsov-D'Onofrio-Paul). **Three structural findings:** (i) r_d-anchoring rescue partially restores ΛCDM-class candidates statistically (2.8-4.2σ → 1-2σ) but doesn't fix CMB/dwarf-galaxy issues; (ii) Tsallis/Barrow HDE Bayesian disfavor (Δlog 𝓑 ≈ −8 to −13) is r_d-anchoring-INDEPENDENT (Occam-driven); (iii) Luciano-Saridakis vs Tyagi-Haridasu-Basak conflict resolved (frequentist vs Bayesian + framework artifact + dataset choice; no genuine data disagreement). Class-(d) HDE-class introduced at R2 (single-scalar apparent-horizon-temperature — GD applies).
- **Track C (Jacobson-Thermo-GR DE):** **5 CLEARED-R2** (M1, M2/M7, M3, M4, M9); 1 NEEDS-R3 (M8 KSS — Lorentz-violation incompatible with Jacobson's SO(3,1) Rindler horizons at EFT level). **Three publishable structural findings:** (i) Sakharov-induced-gravity criterion (4 conditions: fermionic-node existence, universal coupling, tr(I)≠0, IR Lorentz-invariance recovery) — first systematic Λ_J vs Λ_HK comparison on common substrate in literature; (ii) unimodular reformulation as Λ_HK escape route admits M1, M2/M7, M3, M4, M9 (not M8); (iii) CosMIn = 4π is postulate, not derivation (Padmanabhan: "needs new fundamental principle") — must not be credited as predictive content.

**R3 outcomes:**
- **Track A (Causal-Set DE):** **0 CLEARED-R3, 3 NEEDS-R4 (structural), 1 NO-GO-R2 reaffirmed.** All three R2 NEEDS-R3 candidates carry forward to R4 on STRUCTURAL grounds, not phenomenological viability — physically excluded by joint DESI+σ₈+ISW at ≳5σ. R4 carry-forward driven by: (i) **publishable Barrow-bound prescription-dependence short-paper** (Barrow bound robust on per-PLC prescription gives α ≲ 3×10⁻⁶; ZAS-2018 covariant prescription lifts ~3 orders of magnitude — non-uniqueness is publishable structural caveat at CQG/JCAP Letter); (ii) BDG action-fluctuation first-principles σ_Λ ~ α_BDG/√V structurally reproduces Sorkin heuristic with α_BDG = √(K(M)/V) computable from MYZ 2025 bi-action integrals — ε derivation from path-sum-internal consistency open R4+ question; (iii) c_s² = 1 by prescription not derived. **GD inapplicability robust across all 4 admissible prescriptions** (local stochastic Barrow/Zuntz, covariant nonlocal ZAS 2018, spatially homogeneous ADGS 2004 Model 1, per-PLC fluctuating Barrow branch) — first publishable structural result.
- **Track B (Entropic-Gravity DE):** **8 NO-GO-R3 unanimous** — first complete-mechanism-family NO-GO closure in Phase 6m. Verlinde 2017 / Padmanabhan-CosMIn / Hossenfelder-Verlinde NO-GO via CMB Boltzmann + Bullet-Cluster (r_d-independent; Yoon-Guha 2304.07301 confirms dS attractor stability via matter+radiation but ΛCDM-equivalence at observable scales). Cadoni-Tuveri DEC strengthened on three structural grounds: GD theorem forces w_DE = −1 at FLRW, GCG-class CMB Sandvik-Tegmark-Zaldarriaga-Waga 2004 falsification (99.999% of α>0 ruled out), Bullet-Cluster ≳5σ tension. Li 2004 HDE event-horizon: w_a > 0 sign mismatch vs DESI w_a < 0. Tsallis/Barrow HDE: Δlog 𝓑 ≈ −8 to −13 Occam parameter-volume (Tyagi-Haridasu-Basak 2504.11308; Luciano-Paliathanasis-Saridakis 2506.03019 confirms BH limit). Odintsov-D'Onofrio-Paul: predicted Δlog 𝓑 ≈ −15 to −17 by extrapolation from Tyagi (Adhikary-Das-Odintsov-Paul 2507.15273 reports goodness-of-fit but no Bayesian evidence — consistent with Tyagi). r_d-anchoring rescue partial — softens Verlinde-class to ≲1.5σ but CMB+Bullet-Cluster falsifiers r_d-independent. **Track B closes structurally.**
- **Track C (Jacobson-Thermo-GR DE):** **4 CLEARED-R3 + 1 NEEDS-R4 (PARTIAL) + 1 NO-GO-R3 likely.** M1 Jacobson 1995 CLEARED-R3 (class (b) GD inapplicable, fixed-r_d 1σ, Sakharov criterion all hold). M2/M7 Padmanabhan/CosMIn CLEARED-R3 with epistemic flag (CosMIn = 4π postulate explicitly NOT credited as predictive; class (b′), native unimodular). M3 EGJ f(R) CLEARED-R3 conditional on §3 fixed-r_d projection — Plaza-Kraiselburd "very strong" preference projected to weaken to "strong" (ΔAIC, ΔBIC 6-10) under Planck-DR3 r_d prior. M4 Pure Lovelock NO-GO-R3 likely; monitor DR3 — causality-bounded |α̃₂|_max ≈ 0.15 (CEMZ; Brigante-Liu-Myers-Shenker-Yaida) puts (w₀, w_a) ≈ (−0.99, −0.05) at edge of Quintom-B 1σ box, not robustly inside. M8 KSS NEEDS-R4 (PARTIAL closure via path (a)) — SO(3)-restricted Jacobson recovers ADM Hamiltonian + momentum constraints (literature analog: Arata-Liberati-Neri 2603.28851 covariant phase space, April 2026), not full Einstein dynamics; path (b) self-defeating (loses Weinberg evasion); path (c) genuinely OPEN research. M9 Volovik-Jannes CLEARED-R3 — anchors cross-bridge as sole substrate where Λ_J = Λ_HK rigorously demonstrated. **Track C remains highest-survival track.** Two parallel publishable short-note opportunities surface: (a) Sakharov-induced-gravity criterion systematic Λ_J vs Λ_HK comparison (³He-A vs SM-vacuum-as-topological-medium vs Weyl semimetals vs acoustic BEC) — first systematic comparison in literature; (b) [Track A] Barrow-bound prescription-dependence.

**R1+R2+R3 deliverables:**
- Round-1 synthesis working docs at `SK_EFT_Hawking/temporary/working-docs/phase6m_T{A,B,C}_R1_synthesis.md`.
- Round-2 synthesis working docs at `SK_EFT_Hawking/temporary/working-docs/phase6m_T{A,B,C}_R2_synthesis.md`.
- Round-3 synthesis working docs at `SK_EFT_Hawking/temporary/working-docs/phase6m_T{A,B,C}_R3_synthesis.md`.
- Returned dossiers at `Lit-Search/Phase-6m/{Phase 6m Track A Round 3 — Gibbs-Duhem Filter + Quantitative Closure.md, 6m-Track B Round 3 — ..., Phase 6m Track C Round 3 — ...}`.
- Completed task prompts at `Lit-Search/Tasks/complete/Phase6m_T{A,B,C}_R{1,2,3}_*.md`.

**R3 SHIPPED 2026-04-30 (same-day return; dossiers landed 17:56-17:59 in `Lit-Search/Phase-6m/`):**
- TA R3 (Causal-Set DE): Verdict **3 NEEDS-R4 (structural) + 1 NO-GO-R2 reaffirmed**. Carry-forward driven by 3 publishable structural caveats; **no CLEARED-R3 candidates**. See `phase6m_TA_R3_synthesis.md`.
- TB R3 (Entropic-Gravity DE): Verdict **8 NO-GO-R3 unanimous — first complete-mechanism-family closure**. See `phase6m_TB_R3_synthesis.md`.
- TC R3 (Jacobson-Thermo-GR DE): Verdict **4 CLEARED-R3 + 1 NEEDS-R4 (M8 PARTIAL) + 1 NO-GO-R3 likely (M4)**. Track C remains highest-survival track. See `phase6m_TC_R3_synthesis.md`.
- Completed task prompts: `Lit-Search/Tasks/complete/Phase6m_T{A,B,C}_R3_*.md`.

**R4 SHIPPED 2026-04-30 (combined dispatch returned same day):**
- Returned dossier: `Lit-Search/Phase-6m/ 6m Round 4 (Combined) — c_s² Stability Filter.md` (~54 KB / 405 lines).
- Synthesis: `SK_EFT_Hawking/temporary/working-docs/phase6m_R4_synthesis.md`.
- Completed task prompt at `Lit-Search/Tasks/complete/Phase6m_R4_cs_squared_stability_filter_combined.md`.

**R4 outcomes (per track):**
- **Track A:** 2 CLEARED-R4 vacuous (CST-M1, CST-M2 — c_s² = 1 by prescription; cuscuton-like degeneracy via Afshordi-Chung-Geshnizjani 2007 [hep-th/0609150]; ZAS 2018 CAMB implementation uses PPF c_s² = 1 per Hu 0801.2433); **1 NO-GO-R4 (CST-PLC)** via sub-Hubble inconsistency (delta-correlated random field has no kinetic term in standard sense; cuscuton-like degeneracy fails because per-PLC ansatz inhomogeneous in all 4 directions); 1 CLEARED-R4 vacuous + derivation-pending (CST-BDG — comprehensive 9-reference literature survey confirms NO published δΛ effective action sourced by BDG variance; MYZ 2025 §6 explicitly states "a better understanding of the correct dynamics... is needed"; Aslanbeigi-Saravani-Sorkin 1403.1622 4D GCB instability flagged as prior-prejudice pointer toward eventual NO-GO); 1 NO-GO-R2 reaffirmed in unified c_s² < 0 statement (d'Alembertian).
- **Track B:** 8 informational only (Track B closed structurally at R3; **R2 §5(c) Hossenfelder-Verlinde dS-instability claim explicitly SUPERSEDED by Yoon-Guha 2304.07301 (2023)** — matter+radiation FLRW backgrounds stabilize de Sitter trajectory as smooth attractor; imposter-mass parameter values λ² ∈ [1.85×10⁴, 2.26×10⁴] reproduce observed q ∈ [-0.95, -0.55]); HDE-class PPF c_s² = 1 + DEC GCG hydrodynamic c_s² > 0 + Verlinde 2017/Padmanabhan c_s² undefined — none load-bearing.
- **Track C:** Pure-Λ class (M1, M2/M7, M9) CLEARED-R4 vacuous (w_DE = -1; no δΛ at linear level). **M3 EGJ f(R) per-variant** at DESI b ≈ 0.21 (Plaza-Kraiselburd 2504.05432 best-fits: Hu-Sawicki b ≲ 0.11 upper / Starobinsky 0.827 / Exp 1.020 / ArcTanh 1.750; Feng et al. 2510.23105 combined b = 0.206 = "common reference 0.21"): **Hu-Sawicki NO-GO-R4** (parameter range narrow; ΔBIC = +10.088 disfavored at DESI DR2; chameleon viability requires b → 0 trivializing to ΛCDM); **Starobinsky-DE marginal CLEARED-R4** (data prefer b = 0.827; viability at b = 0.21 satisfied; ΔBIC = -14.476); **Exponential CLEARED-R4 (strongest-of-any-track)** (ΔBIC = -21.894; exp(-19.05) ≈ 5.3×10⁻⁹ exponential x₀ suppression makes model trivially chameleon-screened; Solar-System screening automatic; m(R₀) ≈ 5×10⁻⁷); **ArcTanh / Hyp Tangent CLEARED-R4 (strongest-of-any-track)** (ΔBIC = -20.899; sech²(19.05) ≈ 4·exp(-38) ≈ 10⁻¹⁷ suppression). **M4 Pure Lovelock NO-GO-R4 reaffirmed** via combined CEMZ + Brustein-Sherf hyperbolicity bound |α̃₂|_max ≈ 0.15: at α̃₂ = +0.15, c_s² < 1 sub-luminal but (w₀, w_a) excluded from Quintom-B 1σ at ~3σ (Cai-Ren-Qiu-Li-Zhang 2505.24732); at α̃₂ < 0 needed for Quintom-B, c_s² > 1 super-luminal violates CEMZ. Wald-second-law chain forces c_s² ≥ 0 (lower bound) but ACTIVE constraint c_s² ≤ 1 untouched. **M8 KSS CLEARED-R4 conditional via path (a)** (Arata-Liberati-Neri 2603.28851 covariant phase space; SO(3)-restricted Jacobson recovers ADM constraints not full dynamics; KSS Eqs. 5.10-5.30 give anisotropic c_s²(k̂) ≥ 0 in pathology-free regime; Wald-second-law chain consistent in path-(a)-restricted regime). Conditional on (i) path (a) operative throughout + (ii) c_s²(k̂) ≥ 0 throughout. **Wald-second-law chain coherent across TC M3 (f'(R) > 0 ⇒ κ_eff² > 0) and TB class-(d) HDE** (BH-limit GD fixed point with deformed area law A^(α); Krishna-Mathew 2002.02121 confirms holographic equipartition consistency for Kaniadakis/Tsallis entropies). **Unimodular ↔ GR perturbation invariance** (Basak-Fabre-Shankaranarayanan 1511.01805) preserves c_s² for trace-free DOF.

**Cross-track R4 integration:** (a) HDE-class (TB) ↔ M8 KSS (TC) imposter-field analogy — both feature non-hydrodynamical c_s² prescribed by horizon-thermodynamic frameworks; PPF c_s² = 1 applies coherently. (b) Wald-second-law chain shared structural feature between TC M3 (b′) and TB class-(d). (c) Yoon-Guha ↔ M8 KSS stabilization analog identified as forward-pointer for R5+ (no published result yet establishes this analog).

**R5 SHIPPED 2026-04-30 (combined dispatch returned same day):**
- Returned dossier: `Lit-Search/Phase-6m/Phase 6m Round 5 — DESI DR2 (w₀, w_a) Comparison (Combined Tracks A:B:C + Phase 6e Sakharov Cross-Bridge Closure).md` (~54 KB / 651 lines).
- Synthesis: `SK_EFT_Hawking/temporary/working-docs/phase6m_R5_synthesis.md`.
- Completed task prompt at `Lit-Search/Tasks/complete/Phase6m_R5_desi_dr2_comparison_combined.md`.

**R5 outcomes (per track):**
- **Track A:** 3 NO-GO-R5 phenomenological (Sorkin Models 1+2 + BDG); causet d'Alembertian NO-GO-R2 reaffirmed (not in R5 pool). Multi-tier conditioning hierarchy sharpened: f_DESI < 10⁻⁵ at 95% C.L. post-Tier-(4) (raw / SN / ISW / σ₈). BDG (w₀, w_a) statistically equivalent to Model 1 across L_corr regimes (KS p > 0.1). Phantom-crossing topology vs DESI: ρ² ≲ 5% (weak, prescription-dependent). DR3 forecast: no re-entry. **Three publishable structural caveats survive independently of DESI:** (i) GD-inapplicability robust across all prescriptions; (ii) Barrow-bound prescription-dependence (short-paper); (iii) BDG σ_Λ = α_BDG/√V first-principles decomposition.
- **Track B:** **8 NO-GO-R5 unanimous CONFIRMED — first complete-mechanism-family NO-GO closure in Phase 6m**. DR2-specific Bayesian evidence: Tyagi-Haridasu-Basak 2504.11308 (PRD 113, 063507, 2026) gives \|log 𝓑\| ∼ 6.2 disfavor for Tsallis HDE; Luciano-Paliathanasis-Saridakis 2506.03019 (JHEAp 49, 100427, 2026) gives factor 5-6 disfavor for Barrow HDE; Hossenfelder-Verlinde dS-instability NO LONGER load-bearing per Yoon-Guha 2304.07301 (residual model fails CMB independently). 7-of-8 candidates have r_d-independent NO-GO mechanism. Paper-45 framing locked.
- **Track C:** **5+ R5 survivors — highest-survival track in Phase 6m.** Pure-Λ class (M1, M2/M7, M9) PARTIAL-VIABLE under fixed-r_d Planck DR3 prior (≲1.5σ); NEEDS-MONITORING under floating-r_d (2.8-4.2σ); fixed-vs-floating r_d split = key empirical decider by 2030. **M3 EGJ f(R) strongest CLEARED-R5 of any track in Phase 6m** — Plaza-Kraiselburd 2504.05432 (PRD 112, 023554, 2025): "very strong statistical evidence in favor of f(R) over ΛCDM" (ΔAIC ≃ ΔBIC ≳ 20 = "very strong"/"decisive"). Per-variant: Exp + ArcTanh CLEARED (strongest); Starobinsky marginal; **Hu-Sawicki NO-GO-R5** via chameleon Solar-System constraint at b ≃ 0.21. M4 Pure Lovelock NO-GO-R5 reaffirmed: causality-respecting |α̃₂|_max ≃ 0.15 puts (w₀, w_a) ≃ (−0.99, −0.05) at 1σ-box edge, not robustly inside. M8 KSS CLEARED-R5 conditional via R4 path-(a) (Arata-Liberati-Neri 2603.28851); OPEN-R6+ via path-(c). M9 Volovik-Jannes CLEARED-R5 as structural cross-bridge anchor (NOT primary cosmological-Λ predictor).

**Phase 6e cross-bridge final closure:** Sakharov four-condition criterion validated on Volovik-Jannes ³He-A (Λ_J = Λ_HK ∼ Δ₀⁴/(6π²ℏ³); all 4 conditions hold); falsified on Finazzi-Liberati-Sindoni acoustic-BEC (PRL 108, 071101, [arXiv:1103.4841]; condition (ii) fails — only phonons have BEC effective metric). **First systematic Λ_J vs Λ_HK comparison on common substrate in literature.** Track-C survivor substrate-class assignment: M1 + M9 in Sakharov-class; M2/M7 in Sakharov-class with epistemic flag; M3 in class-(b′); M4 in class-(b″); M8 OUTSIDE Sakharov class. Unimodular reformulation as Λ_HK escape route admits 5/6 (NOT M8). Biconditional Lean closure hook: `sakharov_induced_gravity_criterion_iff_lambda_j_eq_lambda_hk`.

**DR3 + Roman (~2030) cross-track forecast:** Pure-Λ class floating-r_d disfavor reaches ≳5σ at DR3 + >7σ at Roman; fixed-r_d remains <3σ throughout. f(R) Exp/ArcTanh preference exceeds 3σ at DESI Y3 (≳5σ at Roman + DESI Y3 floating-r_d). M4 still at 1σ-box edge. M8 (α, β, T) region narrows but conditional verdict survives.

**Post-R3 strengthening pass (2026-04-30; pre-R4-R5 returns):**
- `SK_EFT_Hawking/temporary/working-docs/phase6m_unified_gd_taxonomy.md` — unified 7-class Phase 6m GD taxonomy (Class 0 + (a) + (b) + (b′) + (b″) + (c) + (d)) consolidating TA "combinatorial-vs-thermodynamic-scalar" + TB "a/b/c/d" + TC "b/b'/b''/OPEN" into single classification namespace. Wave 4 `DarkSectorClassificationExtension.lean` + paper-45 will reference this taxonomy.
- `SK_EFT_Hawking/temporary/working-docs/phase6m_cross_reconciliation_pass.md` — cross-reconciliation pass over 9 R1-R3 synthesis docs verifying internal consistency on DESI DR2 contour, Sakharov criterion, Yoon-Guha 2304.07301, r_d-anchoring values, ³He-A numerics, Lovelock |α̃₂|_max. **Verdict: PASS.** 5 reference-evolution arcs handled coherently; 0 transcription errors in syntheses; Phase 6m R1-R3 deliverable structurally locked down.
- `SK_EFT_Hawking/temporary/working-docs/short_note_barrow_prescription_dependence_outline.md` (~18 KB; CQG/JCAP Letter; ~24 references; 6 sections + computational appendix + open questions) — independent-of-R4-R5 publication outline.
- `SK_EFT_Hawking/temporary/working-docs/short_note_sakharov_lambda_j_vs_lambda_hk_outline.md` (~20 KB; CQG/PRD; ~32 references; 6 sections; ³He-A numerics validated) — independent-of-R4-R5 publication outline.
- `SK_EFT_Hawking/temporary/working-docs/citation_registry_phase6m_batch_add_proposal.md` (~27.5 KB; 62 new entries across 13 TA + 21 TB + 20 TC + 8 cross-track; 1 textbook-exempt; ~70 fetchable via `back_fill_primary_sources.py --fetch`) — proposal for human-review merge into `CITATION_REGISTRY` before paper-45 drafting.

**Methodology — Phase 5y reframe.** Phase 5y closed the Volovik-family q-theory dark-energy direction with a six-round deep-research program returning a uniform NO-GO. Phase 6m applies the same six-round methodology to *three explicitly out-of-scope* mechanism families flagged by `ARCHITECTURE_SCOPE.md`:
- **Causal-set theory dark energy** (Sorkin 1989; Sorkin-Surya 2004; Ahmed-Dowker-Surya 2017): emergent Λ from underlying discrete causal-set structure.
- **Entropic gravity dark energy** (Verlinde 2011, 2017): emergent gravity + DE from entanglement / holographic entropy considerations.
- **Jacobson-thermodynamic-GR dark energy** (Jacobson 1995; Padmanabhan 2010): GR equations from thermodynamic identities at local Rindler horizons; Λ as a thermodynamic "boundary term."

Each mechanism gets a six-round probe (analog of Phase 5y rounds 1–6) returning either a NO-GO (with structural obstruction theorem in Lean) or a PARTIAL-VIABLE verdict (with explicit substrate-realization conditions). The endpoint is `ClassificationTableDark.lean` extension covering all three new families.

**Entry state (2026-04-28 Inventory_Index snapshot):** ~187 active modules, ~4,385 theorems, 0 sorry, 1 axiom. Phase 5y CLOSED; `ARCHITECTURE_SCOPE.md` 2026-04-23 explicitly flags these three as "outside tested scope."

**Anchors carried forward into Phase 6m:**
- `GibbsDuhemTheorem.lean` (Phase 5y) — Gibbs-Duhem emergent-vacuum obstruction; the structural template Phase 6m tests against the new mechanism families.
- `QTheoryNoGoTheorem.lean` (Phase 5y) — realization-independent obstruction template.
- `DarkEnergyObstructionPrinciple.lean` (Phase 5y) — four-factor orthogonality decomposition (Gibbs-Duhem ∩ c_s² ≥ 0 ∩ natural T_c ∩ MICROSCOPE).
- `DESIComparison.lean` (Phase 5y) — DESI DR2 (w₀, w_a) comparison infrastructure.
- `ClassificationTableDark.lean` (Phase 5y) — dark-sector classification consolidation (Phase 6m extends).
- `ARCHITECTURE_SCOPE.md` — predictive-scope boundary documentation (Phase 6m updates).

**Thesis.** Phase 5y's closure was decisive *and scoped*. The architecture-scope memo explicitly preserves three untested mechanism families as candidates for future probes. Phase 6m exercises the same six-round methodology against each; each probe ships either a NO-GO with formal obstruction (extending the Layer 3 dark-sector OUT-OF-SCOPE boundary) or a PARTIAL-VIABLE result (opening a new substrate-realization chain). In either case, the architectural-scope statement gets sharper.

**Three-track structure:**
- **Track A (Causal-set DE):** Waves 1a–1f, six rounds.
- **Track B (Entropic-gravity DE):** Waves 2a–2f, six rounds.
- **Track C (Jacobson-thermodynamic-GR DE):** Waves 3a–3f, six rounds.
- **Wave 4:** classification consolidation + `ARCHITECTURE_SCOPE.md` update.

**Correctness-push framing.** Quantitative anchors (against DESI DR2 + observational constraints):
1. (Track A) Causal-set predicted Λ from `Λ ~ √(N_causet)/V_causet` (Sorkin everpresent-Λ): does Λ_predicted match observed `Λ_obs ≈ 1.1 × 10⁻⁵² m⁻²` within order of magnitude?
2. (Track B) Entropic-gravity predicted DE EOS `w(z)` from holographic-entanglement entropy: matches DESI DR2 (w₀, w_a) ≈ (−0.8 ± 0.07, −0.7 ± 0.3)?
3. (Track C) Jacobson-thermodynamic-GR boundary-term Λ: does the local-Rindler-horizon thermodynamics force Λ to a fixed value, or leave it as a free integration constant?

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap.**
> 2. Read this roadmap end-to-end before claiming any wave assignment.
> 3. **Critical predecessor modules — read source directly:**
>    - `lean/SKEFTHawking/GibbsDuhemTheorem.lean` (Phase 5y).
>    - `lean/SKEFTHawking/QTheoryNoGoTheorem.lean` (Phase 5y).
>    - `lean/SKEFTHawking/DarkEnergyObstructionPrinciple.lean` (Phase 5y).
>    - `lean/SKEFTHawking/ClassificationTableDark.lean` (Phase 5y).
>    - `docs/ARCHITECTURE_SCOPE.md` — read fully; this is what Phase 6m updates.
> 4. **Critical deep-research dossiers required** — six per track, dispatched in sequence at Stage 1 of each wave. Track A round 1 example: `Phase6m_TA_R1_causal_set_de_landscape.md`. (Naming convention: `Phase6m_T<A|B|C>_R<1..6>_<topic>.md`.)
> 5. **Phase 5y methodology mirror.** Each round filters the candidate-mechanism realizations against the four-factor orthogonality decomposition (Gibbs-Duhem ∩ c_s² ≥ 0 ∩ natural T_c ∩ MICROSCOPE). Surviving realizations get a Lean obstruction or viability theorem.
> 6. **Apply preemptive-strengthening checklist.**
> 7. **Do not delegate Lean theorem proving to subagents.**
> 8. **User authorization gates:** Gate M.1 (Track A start), Gate M.2 (Track B start), Gate M.3 (Track C start), Gate M.4 (consolidation/scope-update wave). Each track can run autonomously after its gate.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6m:**
- Six-round deep-research probe of causal-set theory dark energy (Track A).
- Six-round deep-research probe of entropic-gravity dark energy (Track B).
- Six-round deep-research probe of Jacobson-thermodynamic-GR dark energy (Track C).
- Per-track NO-GO / PARTIAL-VIABLE / VIABLE verdict in Lean.
- Extension of `ClassificationTableDark.lean` covering all three families.
- Update to `docs/ARCHITECTURE_SCOPE.md` recording the new probes' verdicts.
- One paper (target: Phys. Rep. or PRD): "Untested Dark-Energy Mechanisms on the SK-EFT Substrate: Causal-Set, Entropic, Jacobson-Thermodynamic Probes."

**OUT OF SCOPE for Phase 6m:**
- Re-opening Volovik-family q-theory (Phase 5y closure stands).
- Full causal-set lattice simulation — beyond formalization scope; deep-research synthesis only.
- Tensor-network holographic codes — adjacent but separate (Phase 6j Wave 1 territory if at all).
- Scale-invariance / unimodular gravity DE proposals — already partly absorbed by Phase 5y's q-theory unimodular realization.
- Dark-energy "modified gravity" routes (f(R), DGP, massive gravity) — outside SK-EFT substrate scope.

**Phase 5y relationship.** Phase 6m *extends* Phase 5y's methodology to three explicitly-deferred mechanism families. Phase 5y modules are not modified; Phase 6m adds new modules and extends `ClassificationTableDark.lean`. The closure verdict of Phase 5y on Volovik-family q-theory is preserved.

**Phase 6c.1 relationship.** Phase 6c.1's Zhitnitsky topological-DE absorption is currently the project's only viable DE mechanism (within ≤3 orders of observed Λ, no free parameters). Phase 6m's three new mechanism families either (a) fail (NO-GO), preserving the single-DE-mechanism commitment from 6c.1, or (b) survive (PARTIAL-VIABLE), creating a multi-mechanism landscape that requires re-examination of 6c.1's combined-mechanism falsifier.

---

## Track A: Causal-Set Theory Dark Energy

### Wave 1a — Round 1: Causal-Set DE Landscape Survey [Pipeline: Stages 1–7] **[SHIPPED 2026-04-30]**

**Goal.** Deep-research synthesis of all known causal-set-derived DE mechanisms; enumerate candidate realizations; first-pass filter against the four-factor orthogonality decomposition.

**Prerequisites:** Phase 5y modules read; `ARCHITECTURE_SCOPE.md` read.

**Module structure:**
- Deep-research dossier `Lit-Search/Tasks/complete/Phase6m_TA_R1_causal_set_de_landscape.md` (dispatched 2026-04-28; returned 2026-04-30).
- Returned dossier `Lit-Search/Phase-6m/6m-Track A Round 1 — Causal-Set DE Landscape.md.md`.
- Working doc: `SK_EFT_Hawking/temporary/working-docs/phase6m_TA_R1_synthesis.md`.

**Headline content:** Sorkin everpresent-Λ (Phys. Rev. D 36, 1731, 1987; Sorkin-Surya 2004; Ahmed-Dowker-Surya 2017); causal-set "atomicity" → discrete fluctuations of Λ; Bombelli-Lee-Meyer-Sorkin causal-set kinematics (PRL 59, 521, 1987); BDG action-fluctuation DE (Moradi-Yazdi-Zilhão CQG 42, 045017, 2025).

**Output (R1 verdict):** 5 mechanisms enumerated; 3 CLEARED → R2 (Sorkin everpresent-Λ Models 1+2 + BDG); 1 NO-GO (causal-set d'Alembertian — DM not DE + 4D instability); 1 OPEN-AT-FRONTIER (Sorkin-Surya 2004 reference identification needed). Phase 5y GD obstruction structurally inapplicable to causal-set DE class.

---

### Wave 1b — Round 2: Top-Survivor Detailed Analysis [Pipeline: Stages 1–7] **[SHIPPED 2026-04-30]**

**Goal.** Detailed quantitative analysis of R1 survivors against DESI DR2 (w₀, w_a) and beyond-DESI signatures.

**Module structure:**
- Deep-research dossier `Lit-Search/Tasks/complete/Phase6m_TA_R2_top_survivor_dive.md` (dispatched 2026-04-30; returned 2026-04-30).
- Returned dossier `Lit-Search/Phase-6m/Phase 6m Track A — Round 2- Top‑Survivor Detailed Analysis.md`.
- Synthesis working doc `SK_EFT_Hawking/temporary/working-docs/phase6m_TA_R2_synthesis.md`.

**Output (R2 verdict):** 0 CLEARED-R2, 3 NEEDS-R3 (all R1 survivors), 1 NO-GO-R2 reconfirmed. Four convergent structural gaps prevented R2 clearance: (i) no published DESI DR2 ensemble fit; (ii) Barrow-bound evasion prescription-dependent (publishable structural caveat); (iii) BDG first-principles σ_Λ propagation through Friedmann unfinished; (iv) c_s² = 1 by prescription, not derived. R1 GD-inapplicability finding reinforced under R2 across all admissible prescription branches.

---

### Wave 1c — Round 3: Gibbs-Duhem Filter [Pipeline: Stages 1–7] **[SHIPPED 2026-04-30]**

**Goal.** Apply the Gibbs-Duhem obstruction (Phase 5y `GibbsDuhemTheorem`) to surviving realizations across all admissible covariant/local prescription branches. Causal-set DE typically does NOT have a single-scalar field structure (it's discrete-causet kinematic), so Gibbs-Duhem may not apply; R3 *confirms* this across local Barrow-restored, covariant Zwane-Afshordi-Sorkin, spatially-homogeneous, and per-PLC fluctuating prescriptions.

**Module structure:**
- Deep-research dossier `Lit-Search/Tasks/complete/Phase6m_TA_R3_gibbs_duhem_filter_plus_quantitative.md` (dispatched 2026-04-30; returned 2026-04-30).
- Returned dossier `Lit-Search/Phase-6m/Phase 6m Track A Round 3 — Gibbs-Duhem Filter + Quantitative Closure.md`.
- Synthesis working doc `SK_EFT_Hawking/temporary/working-docs/phase6m_TA_R3_synthesis.md`.

**Output (R3 verdict):** 0 CLEARED-R3, 3 NEEDS-R4 (structural), 1 NO-GO-R2 reaffirmed. All three R2 NEEDS-R3 candidates carry forward to R4 on STRUCTURAL grounds — physically excluded by joint DESI+σ₈+ISW at ≳5σ. R4 carry-forward driven by: (i) **publishable Barrow-bound prescription-dependence short-paper** (Barrow ≲ 3×10⁻⁶ on per-PLC prescription; ZAS-2018 covariant prescription lifts ~3 orders of magnitude — non-uniqueness publishable structural caveat at CQG/JCAP Letter); (ii) BDG action-fluctuation σ_Λ ~ α_BDG/√V structurally reproduces Sorkin heuristic with α_BDG = √(K(M)/V) computable from MYZ 2025 bi-action integrals (ε first-principles open R4+); (iii) c_s² = 1 by prescription, not derived. **GD inapplicability robust across all 4 admissible prescriptions** — first publishable structural result of Phase 6m Track A R3.

---

### Wave 1d — Round 4: c_s² Stability Filter [Pipeline: Stages 1–7] **[SHIPPED 2026-04-30; combined dispatch returned same day]**

**Goal.** Sound-speed-squared positivity (avoid catastrophic gradient instability, the same filter that killed vestigial-EOS natural-branch in Phase 5y).

**Module structure:**
- **Combined dispatch dossier `Lit-Search/Tasks/Phase6m_R4_cs_squared_stability_filter_combined.md`** (consolidated 2026-04-30 post-R3 — Track-A R4 scope reduced post-R3 §6 c_s² status survey to BDG-MYZ-K-kernel derivation only).
- Per-track prompt `Phase6m_TA_R4_cs_squared_stability_filter.md` retained for traceability; superseded by combined dispatch.

**Headline R4 questions (Track A scope):** (a) BDG c_s² derivation from MYZ K-kernel structure (highest-leverage; 3 outcomes per derivation result); (b) per-PLC fluctuating Barrow branch sub-Hubble inconsistency check (c_s² counterpart to R3 §4 short-paper); (c) sanity-check NO-GO-R2 d'Alembertian as c_s² < 0 instance (unified c_s² language).

**Output:** survivors after stability filter.

---

### Wave 1e — Round 5: DESI DR2 (w₀, w_a) Comparison [Pipeline: Stages 1–7] **[SHIPPED 2026-04-30; combined dispatch returned same day]**

**TA R5 outcome:** 3 NO-GO-R5 phenomenological (Sorkin Models 1+2 + BDG); causet d'Alembertian NO-GO-R2 reaffirmed (not in R5 pool). f_DESI < 10⁻⁵ at 95% C.L. post-Tier-(4). Three publishable structural caveats survive (GD-inapplicability across prescriptions; Barrow-bound prescription-dependence; BDG σ_Λ = α_BDG/√V first-principles). DR3 forecast: no re-entry. See `phase6m_R5_synthesis.md` §1.

**Goal.** For each surviving causal-set DE realization, compute predicted (w₀, w_a) and compare to DESI DR2 1σ band.

**Module structure:**
- Deep-research dossier `Lit-Search/Tasks/Phase6m_TA_R5_desi_dr2_comparison.md` (dispatched 2026-04-30 in parallel with R3+R4).

**Headline R5 questions:** (a) per-realization w(z) ensemble extraction + CPL projection; (b) multi-tier conditioning hierarchy (raw / SN-Ia / Planck low-ℓ ISW / σ₈); (c) BDG-specific (w₀, w_a) by L_corr regime; (d) phantom-crossing topology vs quantitative DESI match; (e) DESI DR3 forecast.

**DESI DR2 reference contour:** w₀ = −0.838 ± 0.055, w_a = −0.62 (+0.22/−0.19) [DESI+CMB+Pantheon+, 2.8σ]; alternative SN compilations give 3.8-4.2σ. Phantom crossing at z ≈ 0.5 robust feature.

**Output:** DESI-compatible survivors (if any). Per anchoring choice (floating-r_d vs fixed-r_d Planck).

---

### Wave 1f — Round 6 + Lean Closure: `CausalSetDarkEnergy.lean` [SHIPPED 2026-04-30] [Pipeline: Stages 1–13]

**Outcome:** `lean/SKEFTHawking/CausalSetDarkEnergy.lean` SHIPPED — 15 substantive thms / 0 sorry / 0 new axioms / library 8507 PASS. Encodes Track A's three NO-GO-R5 phenomenological verdicts (Sorkin Models 1+2 + BDG) plus the d'Alembertian NO-GO-R2 reaffirmation, AND the three publishable structural caveats independent of DESI: (i) GD-inapplicability robust under all 4 sprinkling prescriptions (CSDE5); (ii) Barrow-bound prescription dependence with quantitative 40%+ gap (CSDE6, CSDE6′); (iii) BDG σ_Λ = α_BDG/√V first-principles decomposition with monotone-decreasing-in-V property (CSDE7-8). Sharpened f_DESI < 10⁻⁵ Tier-4 conditioning bound encoded as norm_num inequality (CSDE1-3). Causal-set d'Alembertian c_s² < 0 4D gradient instability (CSDE4). Per-candidate R5 verdicts CSDE9-12. Phantom-crossing topology weak (ρ² ≤ 5%) CSDE13. Track A fully NO-GO at R5 closure summary CSDE14.


**Goal.** Final round + Lean formalization of the verdict (NO-GO with obstruction theorem, or PARTIAL-VIABLE with substrate-realization conditions, or VIABLE with prediction band).

**Module structure:**
- `lean/SKEFTHawking/CausalSetDarkEnergy.lean` — new module, ~14 substantive theorems target.
- `src/dark_energy/causal_set_de.py` — numerical Λ from causal-set everpresent fluctuations.
- `tests/test_causal_set_de.py` — DESI-comparison + everpresent-Λ tests; 10+ tests.
- `figures/fig_causal_set_de_verdict.{png,html}`.

**Headline theorems (one branch fires):**

**Branch NO-GO:**
1. `causal_set_de_no_go_under_<filter>` — formalizes which Phase 5y filter kills causal-set DE.
2. `everpresent_lambda_fails_desi_compatibility` — Sorkin everpresent-Λ predicts time-evolving Λ but with magnitude / amplitude mismatching observation.
3. `classification_table_dark_appends_causal_set_no_go` — extends `ClassificationTableDark.lean`.

**Branch PARTIAL-VIABLE:**
1. `causal_set_de_viable_under_substrate_condition_<X>` — explicit substrate-condition theorem.
2. `causal_set_de_open_for_phase_<future>` — opens a new chain.

**Strengthening checklist:**
- (P5 trivial-discharge): if branch NO-GO fires, the obstruction theorem must be falsifiable (a counterexample causal-set realization would falsify the theorem).
- (Quantitative): (w₀, w_a) closed-form values vs DESI 1σ band.

**Stage 13 anchors:**
- Sorkin, PRD 36, 1731 (1987); Mod. Phys. Lett. A 9, 3119 (1994).
- Bombelli, Lee, Meyer, Sorkin, PRL 59, 521 (1987).
- Ahmed, Dowker, Surya, CQG 34, 124002 (2017).
- DESI Collaboration, arXiv:2503.14738 (2025).

**Deliverables.** `CausalSetDarkEnergy.lean`; numerical module; figure suite; section in flagship paper.

---

## Track B: Entropic-Gravity Dark Energy

### Waves 2a–2f — Six rounds, parallel structure to Track A

**Round 1 (2a) [SHIPPED 2026-04-30]:** Entropic-gravity DE landscape — Verlinde 2011 (JHEP 04 029); Verlinde 2017 (SciPost Phys. 2 016) emergent-DE in de Sitter spacetime; Padmanabhan thermodynamic-GR overlaps. **Outcomes:** 3 FALSIFIED at 2.8-4.2σ (Verlinde 2017, Padmanabhan/CosMIn, Hossenfelder-Verlinde — all predict exact ΛCDM); 1 NOT a DE candidate (Verlinde 2011); 5 MARGINAL → R2 (Cadoni-Tuveri DEC, HDE event-horizon, Tsallis HDE, Barrow HDE, Odintsov-D'Onofrio-Paul 4-param). Returned dossier at `Lit-Search/Phase-6m/6m-Track B Round 1 — Entropic-Gravity Dark-Energy Landscape.md`. Synthesis at `SK_EFT_Hawking/temporary/working-docs/phase6m_TB_R1_synthesis.md`.

**Round 2 (2b) [SHIPPED 2026-04-30]:** Top-survivor detailed analysis. **Outcomes:** 0 CLEARED-R2, **4 NO-GO-R2** (Cadoni-Tuveri DEC inherits Verlinde 2017 CMB/Bullet-Cluster issues; HDE event-horizon forces w_a > 0 opposite sign of DESI; Tsallis HDE Δlog 𝓑 ≈ −8 to −13 Occam-driven; Barrow HDE equivalent to Tsallis under Δ ↔ 2(δ−1)); 1 NEEDS-R3 (Odintsov-D'Onofrio-Paul). r_d-anchoring rescue partially restores ΛCDM-class candidates statistically (2.8-4.2σ → 1-2σ) but doesn't fix CMB/dwarf-galaxy issues. Tsallis/Barrow Bayesian disfavor is r_d-anchoring-INDEPENDENT. Luciano-Saridakis vs Tyagi-Haridasu-Basak conflict resolved. Class-(d) HDE-class taxonomy refinement introduced. Returned dossier at `Lit-Search/Phase-6m/6m-Round 2 Quantitative Analysis of Five Marginal-Survivor Entropic-Gravity Dark-Energy Candidates.md`. Synthesis at `SK_EFT_Hawking/temporary/working-docs/phase6m_TB_R2_synthesis.md`.

**Round 3 (2c) [SHIPPED 2026-04-30]:** Gibbs-Duhem filter applied. **Outcomes: 8 NO-GO-R3 unanimous — first complete-mechanism-family NO-GO closure in Phase 6m.** Verlinde 2017 / Padmanabhan / Hossenfelder-Verlinde NO-GO via CMB Boltzmann + Bullet-Cluster (r_d-independent; Yoon-Guha 2304.07301 confirms dS attractor stability via matter+radiation but ΛCDM-equivalence at observable scales). Cadoni-Tuveri DEC strengthened on three structural grounds: GD theorem forces w_DE = −1 at FLRW, GCG-class CMB Sandvik et al. 2004 falsification (99.999% of α>0 ruled out), Bullet-Cluster ≳5σ tension. Li 2004 HDE event-horizon: w_a > 0 sign mismatch vs DESI w_a < 0. Tsallis/Barrow HDE: Δlog 𝓑 ≈ −8 to −13 Occam parameter-volume (Tyagi-Haridasu-Basak 2504.11308; Luciano-Paliathanasis-Saridakis 2506.03019 confirms BH limit). Odintsov-D'Onofrio-Paul: predicted Δlog 𝓑 ≈ −15 to −17 by extrapolation (Adhikary-Das-Odintsov-Paul 2507.15273 reports goodness-of-fit only). r_d-anchoring rescue partial. **Track B closes structurally.** Returned dossier at `Lit-Search/Phase-6m/6m-Track B Round 3 — Gibbs-Duhem Filter + Odintsov-D'Onofrio-Paul Closure.md`. Synthesis at `SK_EFT_Hawking/temporary/working-docs/phase6m_TB_R3_synthesis.md`.

**Round 4 (2d) [SHIPPED 2026-04-30, combined dispatch returned]:** c_s² filter informational only — Track B closed structurally at R3 with 8 NO-GO-R3 unanimous. **R2 §5(c) Hossenfelder-Verlinde dS-instability claim explicitly SUPERSEDED by Yoon-Guha 2304.07301 (2023)** — matter+radiation FLRW backgrounds stabilize dS attractor as smooth attractor in matter-radiation-imposter system; imposter-mass parameter λ² ∈ [1.85×10⁴, 2.26×10⁴] reproduces q ∈ [-0.95, -0.55]. HDE-class PPF c_s² = 1 + DEC GCG hydrodynamic c_s² > 0 + Verlinde 2017/Padmanabhan c_s² undefined — all confirmation-diagnostic only. Forward-pointer for future entropic-gravity DE proposals beyond the 8 closed candidates. Combined dispatch returned at `Lit-Search/Phase-6m/ 6m Round 4 (Combined) — c_s² Stability Filter.md` (Part B). Synthesis at `phase6m_R4_synthesis.md` §2.

**Round 5 (2e) [SHIPPED 2026-04-30, combined dispatch returned same day]:** **8 NO-GO-R5 unanimous CONFIRMED — first complete-mechanism-family NO-GO closure in Phase 6m.** DR2-specific Bayesian evidence: Tyagi-Haridasu-Basak 2504.11308 (PRD 113, 063507, 2026) gives \|log 𝓑\| ∼ 6.2 disfavor for Tsallis HDE; Luciano-Paliathanasis-Saridakis 2506.03019 (JHEAp 49, 100427, 2026) factor 5-6 disfavor for Barrow HDE; Hossenfelder-Verlinde dS-instability NO LONGER load-bearing per Yoon-Guha 2304.07301. 7-of-8 candidates have r_d-independent NO-GO. Paper-45 framing locked. See `phase6m_R5_synthesis.md` §2.

**Round 6 + Lean Closure (2f) [SHIPPED 2026-04-30]:** `EntropicGravityDarkEnergy.lean` — verdict module.

**Outcome:** 14 substantive thms / 0 sorry / 0 new axioms / library 8507 PASS. Encodes the **first complete-mechanism-family NO-GO closure in Phase 6m**: 8 candidates (Verlinde 2017, Padmanabhan/CosMIn, Hossenfelder-Verlinde post-Yoon-Guha, Cadoni-Tuveri DEC, Li 2004 HDE, Tsallis HDE, Barrow HDE, Odintsov-D'Onofrio-Paul) all NO-GO with quantitative |log 𝓑| / σ thresholds exceeding Jeffreys-decisive (5). Theorems EGDE1-EGDE12: per-candidate norm_num bounds (Verlinde ≥ 5σ; Tsallis ≥ 6.2; Barrow ≥ 5.5; Odintsov ∈ [15, 17]); structural flags (no scalar perturbation theory for CosMIn; dS-instability superseded for Hossenfelder-Verlinde; w_DE = -1 for DEC); r_d-anchoring partial-rescue does not save Class (b) or (d) (EGDE9, EGDE9′); 8/8 unanimous closure (EGDE10, EGDE10′); classification-table append (EGDE11); aggregate quantitative bound theorem (EGDE12).

**Lean module (Wave 2f):**
- `lean/SKEFTHawking/EntropicGravityDarkEnergy.lean` — 14 theorems shipped (target was ~12).
- Verlinde-2017 emergent-Λ closed-form; Gibbs-Duhem application; DESI comparison; classification-table extension.

**Stage 13 anchors:**
- Verlinde, JHEP 04 029 (2011), arXiv:1001.0785.
- Verlinde, SciPost Phys. 2, 016 (2017), arXiv:1611.02269.
- Padmanabhan, Rep. Prog. Phys. 73, 046901 (2010).

---

## Track C: Jacobson-Thermodynamic-GR Dark Energy

### Waves 3a–3f — Six rounds, parallel structure

**Round 1 (3a) [SHIPPED 2026-04-30]:** Jacobson-thermodynamic-GR DE landscape — Jacobson 1995 (PRL 75, 1260); Padmanabhan thermodynamic-GR; Eling-Guedens-Jacobson 2006 nonequilibrium thermodynamics; recent work by Cai-Cao on F(R) thermodynamic gravity. **Outcomes:** 9 mechanisms enumerated; 2 ELIMINATED (Verlinde 2010 entropic, EFS — locality/Lorentz tension); 6 SURVIVORS → R2 (M1 Jacobson, M2/M7 Padmanabhan/CosMIn, M3 EGJ f(R), M4 Cai-Cao Lovelock subset, M8 KSS Lorentz-violating superfluid, M9 Volovik-Jannes substrate). **Phase 6e cross-bridge anchor:** Λ_J ≠ Λ_HK in general — substrate-dependent. Returned dossier at `Lit-Search/Phase-6m/6m-Track C Round 1 — Jacobson-Thermo-GR DE Landscape.md.md`. Synthesis at `SK_EFT_Hawking/temporary/working-docs/phase6m_TC_R1_synthesis.md`.

**Round 2 (3b) [SHIPPED 2026-04-30]:** Top-survivor detailed analysis. **Outcomes:** **5 CLEARED-R2** (M1 Jacobson, M2/M7 Padmanabhan/CosMIn, M3 Eling-Guedens-Jacobson f(R), M4 Pure Lovelock, M9 Volovik-Jannes); 1 NEEDS-R3 (M8 KSS — Lorentz-violation incompatible with Jacobson's SO(3,1) Rindler horizons at EFT level; δQ = T δS imposed only on SO(3)-aligned horizons insufficient to recover Einstein equations). **Three publishable structural findings:** (i) **Sakharov-induced-gravity criterion** (4 conditions: fermionic-node existence, universal coupling, tr(I)≠0, IR Lorentz-invariance recovery) — first systematic Λ_J vs Λ_HK comparison on common substrate in literature; (ii) Volovik-Jannes ³He-A explicit numerics (λ = Δ₀⁴/(6π²ℏ³), Δ₀ ≈ 1.6 mK ≈ 2×10⁻⁷ eV, tr(I) = 4 on 4-Weyl-fermion bundle, anisotropy c_⊥0/c_∥ ∼ 10⁻³, graviton-mass ratio ζ = 2); (iii) **unimodular reformulation as Λ_HK escape route** admits M1, M2/M7, M3, M4, M9 (not M8 — its Weinberg-evasion mechanism requires vacuum energy to couple to gravity). M3 Plaza-Kraiselburd 2504.05432: "very strong" Bayesian preference for Starobinsky-DE/Exp/ArcTanh f(R) over ΛCDM under DESI DR2 + PPS + CC; Feng et al. 2510.23105 b ≈ 0.21. CosMIn = 4π is postulate (Padmanabhan: "needs new fundamental principle") — must not be credited as predictive content. Returned dossier at `Lit-Search/Phase-6m/6m-Track C Round 2 — Jacobson Phase 6e Cross-Bridge + Survivor Analysis.md`. Synthesis at `SK_EFT_Hawking/temporary/working-docs/phase6m_TC_R2_synthesis.md`.

**Round 3 (3c) [SHIPPED 2026-04-30]:** Gibbs-Duhem filter applied. **Outcomes: 4 CLEARED-R3 + 1 NEEDS-R4 (M8 PARTIAL) + 1 NO-GO-R3 likely (M4).** M1 Jacobson 1995 CLEARED-R3 (class (b) GD inapplicable, fixed-r_d 1σ, Sakharov criterion all hold). M2/M7 Padmanabhan/CosMIn CLEARED-R3 with epistemic flag (CosMIn = 4π postulate explicitly NOT credited as predictive content; class (b′), native unimodular). M3 EGJ f(R) CLEARED-R3 conditional on fixed-r_d projection — Plaza-Kraiselburd "very strong" preference projected to weaken to "strong" (ΔAIC, ΔBIC 6-10) under Planck-DR3 r_d prior. M4 Pure Lovelock NO-GO-R3 likely; monitor DR3 — causality-bounded |α̃₂|_max ≈ 0.15 (CEMZ; Brigante-Liu-Myers-Shenker-Yaida) puts (w₀, w_a) ≈ (−0.99, −0.05) at edge of Quintom-B 1σ box, not robustly inside. **M8 KSS NEEDS-R4 (PARTIAL closure via path (a))** — SO(3)-restricted Jacobson recovers ADM Hamiltonian + momentum constraints (literature analog: Arata-Liberati-Neri 2603.28851 covariant phase space, April 2026), NOT full Einstein dynamics; path (b) self-defeating (loses Weinberg evasion); path (c) genuinely OPEN research. M9 Volovik-Jannes CLEARED-R3 — anchors cross-bridge as sole substrate where Λ_J = Λ_HK rigorously demonstrated. Sakharov criterion systematic comparison delivered (³He-A vs SM-as-topological-medium vs Weyl semimetals vs acoustic BEC) — first systematic comparison in literature. **Two parallel publishable short-note opportunities surface:** (a) Sakharov-induced-gravity criterion systematic Λ_J vs Λ_HK comparison (CQG/PRD); (b) [Track A] Barrow-bound prescription-dependence (CQG/JCAP Letter). Returned dossier at `Lit-Search/Phase-6m/Phase 6m Track C Round 3 — Gibbs–Duhem Filter + KSS Lorentz-Violating-Jacobson Closure.md`. Synthesis at `SK_EFT_Hawking/temporary/working-docs/phase6m_TC_R3_synthesis.md`.

**Round 4 (3d) [SHIPPED 2026-04-30, combined dispatch returned]:** c_s² filter substantive verdicts. Pure-Λ class (M1, M2/M7, M9) CLEARED-R4 vacuous (w_DE = -1; no δΛ at linear level). **M3 EGJ f(R) per-variant at DESI b ≈ 0.21** (Plaza-Kraiselburd 2504.05432 best-fits: Hu-Sawicki b ≲ 0.11 upper / Starobinsky 0.827 / Exp 1.020 / ArcTanh 1.750; Feng et al. 2510.23105 combined b = 0.206): **Hu-Sawicki NO-GO-R4** (parameter range narrow; ΔBIC = +10.088 disfavored; chameleon trivializes to ΛCDM in b → 0 limit). **Starobinsky-DE marginal CLEARED-R4** (ΔBIC = -14.476). **Exponential CLEARED-R4 (strongest-of-any-track)** (ΔBIC = -21.894; exp(-19.05) ≈ 5.3×10⁻⁹ exponential x₀ suppression). **ArcTanh / Hyp Tangent CLEARED-R4 (strongest-of-any-track)** (ΔBIC = -20.899; sech²(19.05) ≈ 10⁻¹⁷ suppression). **M4 Pure Lovelock NO-GO-R4 reaffirmed** via combined CEMZ + Brustein-Sherf hyperbolicity |α̃₂|_max ≈ 0.15 + DESI Quintom-B 1σ box exclusion at ~3σ. **M8 KSS CLEARED-R4 conditional** via Arata-Liberati-Neri 2603.28851 path (a) PARTIAL closure (SO(3)-restricted Jacobson recovers ADM constraints; KSS Eqs. 5.10-5.30 anisotropic c_s²(k̂) ≥ 0 in pathology-free regime; Wald-second-law chain consistent). Wald-second-law chain coherent across TC M3 (f'(R) > 0 ⇒ κ_eff² > 0) and TB class-(d) HDE (Krishna-Mathew 2002.02121 confirms holographic equipartition for Kaniadakis/Tsallis). Unimodular ↔ GR perturbation invariance (Basak-Fabre-Shankaranarayanan 1511.01805) preserves c_s² for trace-free DOF. Combined dispatch returned at `Lit-Search/Phase-6m/ 6m Round 4 (Combined) — c_s² Stability Filter.md` (Part C). Synthesis at `phase6m_R4_synthesis.md` §3.

**Round 5 (3e) [SHIPPED 2026-04-30, combined dispatch returned same day]:** **5+ R5 survivors CONFIRMED — highest-survival track in Phase 6m.** Pure-Λ class (M1, M2/M7, M9) PARTIAL-VIABLE under fixed-r_d Planck DR3 prior (≲1.5σ); NEEDS-MONITORING under floating-r_d (2.8-4.2σ). **M3 EGJ f(R) strongest CLEARED-R5 of any track** — Plaza-Kraiselburd 2504.05432 (PRD 112, 023554, 2025): "very strong statistical evidence in favor of f(R) over ΛCDM" (ΔAIC ≃ ΔBIC ≳ 20). Per-variant: Exp + ArcTanh CLEARED (strongest); Starobinsky marginal; **Hu-Sawicki NO-GO-R5** via chameleon Solar-System constraint at b ≃ 0.21. M4 Pure Lovelock NO-GO-R5 reaffirmed: causality-respecting |α̃₂|_max ≃ 0.15 puts (w₀, w_a) ≃ (−0.99, −0.05) at 1σ-box edge. M8 KSS CLEARED-R5 conditional via R4 path-(a) Arata-Liberati-Neri 2603.28851; OPEN-R6+ via path-(c). M9 Volovik-Jannes CLEARED-R5 as structural cross-bridge anchor. **Phase 6e cross-bridge final closure:** Sakharov 4-condition criterion validated on ³He-A (Λ_J = Λ_HK ∼ Δ₀⁴/(6π²ℏ³)), falsified on FLS acoustic-BEC (condition (ii) fails). **First systematic Λ_J vs Λ_HK comparison on common substrate in literature.** Substrate-class assignment + unimodular Λ_HK escape route admits 5/6 (NOT M8). DR3 + Roman (~2030) forecast: f(R) Exp/ArcTanh ≳5σ; pure-Λ floating-r_d disfavor reaches >7σ; M4 still at 1σ-box edge. See `phase6m_R5_synthesis.md` §3+§4.

**Round 6 + Lean Closure (3f) [SHIPPED 2026-04-30]:** `JacobsonThermoGRDarkEnergy.lean` — verdict module.

**Outcome:** 12 substantive thms / 0 sorry / 0 new axioms / library 8507 PASS. Encodes Track C as highest-survival track (5+ R5 survivors) plus Phase 6e cross-bridge final closure. JTGR1: pure-Λ class fixed-r_d disfavor < floating-r_d (norm_num inequality). JTGR2: f(R) Exp+ArcTanh ΔAIC ≥ 2× Jeffreys-decisive (≳20). JTGR3: Hu-Sawicki best-fit b ≈ 0.21 > 100× Solar-System chameleon bound — no viable parameter window. JTGR4: Lovelock at 1σ-box edge |w₀+1| < 0.05 with |α̃₂|_max ≤ 0.15. JTGR5: KSS conditional via R4 path-(a). **JTGR6-JTGR8 Phase 6e cross-bridge closure:** Sakharov 4-criterion biconditional implication, ³He-A satisfies all 4, FLS BEC violates condition (ii). JTGR9: Volovik-Jannes substrate anchors Sakharov criterion. JTGR10: unimodular escape route admits 5/6 except KSS. JTGR11: ≥ 5 cleared-R5 (decided over 9 candidates). JTGR12: classification-table append.

**Lean module (Wave 3f):**
- `lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean` — 12 theorems shipped (3 are Phase 6e cross-bridge: JTGR6/JTGR7/JTGR8; total 12 substantive).

**Stage 13 anchors:**
- Jacobson, PRL 75, 1260 (1995), arXiv:gr-qc/9504004.
- Padmanabhan, Class. Quant. Grav. 21, 4485 (2004).
- Eling, Guedens, Jacobson, PRL 96, 121301 (2006), arXiv:gr-qc/0602001.

---

## Wave 4 — `DarkSectorClassificationExtension.lean` + ARCHITECTURE_SCOPE.md update [SHIPPED 2026-04-30] [6m.4] [Pipeline: Stages 1–13]

**Outcome:** `lean/SKEFTHawking/DarkSectorClassificationExtension.lean` SHIPPED — 10 substantive thms / 0 sorry / 0 new axioms. Encodes the unified Phase 6m 7-class GD taxonomy (Class 0 + (a) + (b) + (b′) + (b″) + (c) + (d)) as an inductive type, with 3-tier GD applicability gradient (Tier I outside-domain / Tier II inapplicable / Tier III applies / Tier S re-derive). DSCE1: Track A uniformly Class 0. DSCE2: Track B 3+1+4 split across (b)/(c)/(d). DSCE3: M8 KSS uniquely Class (a). DSCE4: Class 0 GD-inapplicability bridges to CSDE5. DSCE5: GD binds only for Class (c) and (d) (Tier-III ↔ classes-(c,d) iff). DSCE6: first complete-mechanism-family NO-GO closure cross-bridge (Track B). DSCE7: Track C highest-survival cross-bridge. DSCE8: unimodular escape admits all classes except (a). DSCE9: 17 Phase 6m mechanism count (8 + 9). DSCE10: every class admits a tier assignment. ARCHITECTURE_SCOPE.md update + paper-45 deferred (next session work).


**Goal.** Consolidate Tracks A/B/C verdicts into an extended dark-sector classification table; update `ARCHITECTURE_SCOPE.md` with the new verdicts. The Layer 3 dark-energy scope statement is sharpened: previously "Volovik-family mechanisms outside scope," now "Volovik-family + (NO-GO results from Tracks A/B/C) outside scope; (any PARTIAL-VIABLE/VIABLE results) opened as new chains."

**Prerequisites:**
- Tracks A/B/C all SHIPPED.

**Module structure:**
- `lean/SKEFTHawking/DarkSectorClassificationExtension.lean` — new module, ~10 theorems target (consolidates Tracks A/B/C verdicts as bridge theorems into existing `ClassificationTableDark.lean`).
- Extension to `ClassificationTableDark.lean` (additive, not editing).
- `docs/ARCHITECTURE_SCOPE.md` — append-only update with the new probe verdicts.

**Headline theorems:**
1. `causal_set_de_classified` — Tracks A's verdict as a structured Lean proposition.
2. `entropic_gravity_de_classified` — Track B's verdict.
3. `jacobson_thermo_de_classified` — Track C's verdict.
4. `architecture_scope_extended_2026Q3` — meta-theorem: `Layer3DarkEnergyScope = VolovikFamily ∪ {Track-A-NoGoPart, Track-B-NoGoPart, Track-C-NoGoPart}`.
5. `single_de_mechanism_commitment_holds_iff_no_partial_viable` — biconditional: Phase 6c.1's combined-mechanism falsifier remains in force IFF no Track A/B/C realization is partial-viable.

**Stage 13 anchors:** all primary sources from Waves 1f, 2f, 3f.

**Deliverables.** `DarkSectorClassificationExtension.lean`; `ARCHITECTURE_SCOPE.md` updated; flagship paper closure.

---

## Paper deliverable

**Paper 45** (target: Phys. Rep. or PRD): "Untested Dark-Energy Mechanisms on the SK-EFT Substrate: Causal-Set, Entropic, Jacobson-Thermodynamic Probes." 12–20 pages (review-paper-flavored). Structure:
- §2 Causal-set DE (Track A) — six-round summary + verdict.
- §3 Entropic-gravity DE (Track B) — six-round summary + verdict.
- §4 Jacobson-thermodynamic-GR DE (Track C) — six-round summary + verdict.
- §5 Classification table extension (Wave 4).
- §6 Updated architecture-scope statement.
- §7 What remains untested (next-generation candidates: tensor-network holographic codes, modified-gravity DE, ...).

**Submission readiness:** target Stage 13 closure ~16–24 weeks post-Wave 4 (heavy review-paper drafting).

---

## Cross-phase impact

- **Phase 5y**: Phase 6m extends but does not modify; Volovik-family closure preserved.
- **Phase 6c.1**: Phase 6m's verdicts on Tracks A/B/C either preserve 6c.1's single-DE-mechanism commitment (NO-GO branch) or break it (PARTIAL-VIABLE branch, requiring 6c.1 falsifier re-examination).
- **`ARCHITECTURE_SCOPE.md`**: Wave 4 updates this document.
- **`ClassificationTableDark.lean`**: Wave 4 extends this module additively.

---

## Total LOE estimate

- Track A (6 rounds + Lean closure): 4–6 PM (research-heavy)
- Track B (6 rounds + Lean closure): 4–6 PM
- Track C (6 rounds + Lean closure): 4–6 PM
- Wave 4 (consolidation): 2 PM
- Paper 45 drafting (review-flavored): 4–6 PM
- **Total: 18–26 PM** (~4.5–6.5 months at full intensity)

Tracks A/B/C can run in parallel after Gates M.1, M.2, M.3 are opened; serial execution is also acceptable.

---

*Last updated: 2026-04-30. Status: **Phase 6m FULLY CLOSED at the Lean-formalization scope** across all three tracks + Wave 4 consolidation. Net Lean closure: 4 new modules / 51 substantive thms / 0 sorry / 0 new axioms / library 8507 jobs PASS. Wave 1f shipped 15 thms (CausalSetDarkEnergy.lean: Track A 3 NO-GO + 3 publishable structural caveats + d'Alembertian reaffirmation); Wave 2f shipped 14 thms (EntropicGravityDarkEnergy.lean: first complete-mechanism-family NO-GO closure; 8/8 unanimous with quantitative Jeffreys-decisive bounds); Wave 3f shipped 12 thms (JacobsonThermoGRDarkEnergy.lean: Track C highest-survival + Phase 6e cross-bridge biconditional Sakharov criterion); Wave 4 shipped 10 thms (DarkSectorClassificationExtension.lean: unified 7-class GD taxonomy + 3-tier applicability gradient + per-track class assignments). **Remaining work:** ARCHITECTURE_SCOPE.md update with Phase 6m verdicts; paper-45 (Phys. Rep. or PRD review); two parallel short-note publications (Barrow prescription-dependence CQG/JCAP Letter outline at `short_note_barrow_prescription_dependence_outline.md`; Sakharov criterion systematic Λ_J vs Λ_HK comparison CQG/PRD outline at `short_note_sakharov_lambda_j_vs_lambda_hk_outline.md`).*
