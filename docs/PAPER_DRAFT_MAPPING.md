# SK-EFT Hawking — Paper Draft → Bundle Mapping

**Companion document to** `PAPER_STRATEGY.md`.

**Purpose:** Explicit per-draft assignment from the 32+ existing drafts in `papers/paperN_*/` to the 13 publication targets defined in the new strategy (1 flagship + 5 Tier 1 deep + 3 Tier 2 PRL + 2 Tier 3 infrastructure + 2 Tier 4 experimental).

**Created:** 2026-04-28.

**Conventions:**
- **Lift-section:** the existing draft's content (or major fraction) becomes a §section of a new bundle. Existing draft retired from publication track but retained in `papers/paperN_*/` as historical/source.
- **Lift-letter:** the existing draft's content fits a 4-page PRL splash; some content also lifts as §section of a deep paper.
- **Lift-companion:** the existing draft becomes a 2–3 page experimental letter, paired with a deep paper.
- **Lift-flagship:** the existing draft's content is summarized in the flagship review and also fully covered in a deep paper.
- **Retain-in-place:** the existing draft is structurally orthogonal to the new architecture and ships as-is on its current path (rare).
- **Retire:** the existing draft was a placeholder or has been fully superseded; no separate publication track. Content already absorbed elsewhere.

---

## 1. Per-existing-draft mapping

The 32 existing drafts in `papers/paperN_*/`. For each: title, status before strategy reframe, new destination(s), lift action.

| Existing draft | Working title | Prior target | New destination(s) | Lift action |
|---|---|---|---|---|
| `paper1_first_order` | First-order dissipative analog Hawking | PRL | **D1 §2** (BEC predictions + δ_diss) + **F §4** (summary) | Lift-section |
| `paper2_second_order` | Second-order SK-EFT | PRD | **D1 §3** (counting + parity alternation + ω³) + **F §4** | Lift-section |
| `paper3_gauge_erasure` | Gauge erasure | PRL | **D3 §3** (gauge erasure selection rule) + **F §3** | Lift-section |
| `paper4_wkb_connection` | Exact WKB connection | PRD | **D1 §4** (exact WKB + three non-perturbative effects) + **F §4** | Lift-section |
| `paper5_adw_gap` | ADW gap equation | PRD | **D3 §2** (ADW + tetrad gap + bifurcation) + **F §6** | Lift-section |
| `paper6_vestigial` | Vestigial gravity + MC | PRD | **D3 §10** (vestigial-MC status note, conditional on RHMC convergence at L≥8) + **F §6** | Lift-section (conditional) |
| `paper7_chirality_formal` | Chirality formal (GS no-go + TPF in Lean 4) | PRD/CPC | **D2 §4** (GS evasion + TPF) + **F §5** | Lift-section |
| `paper8_chirality_master` | Chirality master (three-pillar synthesis) | PRL | **D2 §4** (three-pillar synthesis as the integrating section) + **F §5** | Lift-section |
| `paper9_sm_anomaly_drinfeld` | SM anomaly + Drinfeld center | PRL | **D2 §3** (SM anomaly) + **D4 §4** (Drinfeld center) + **F §5, §7** | Lift-section (split) |
| `paper10_modular_generation` | Modular generation constraint (N_f ≡ 0 mod 3) | PRD | **L2** (4-page PRL splash) + **D2 §2** (full derivation + Ext computation) + **F §5** | Lift-letter |
| `paper11_quantum_group` | First quantum-group formalization | PRD | **D4 §2** (longest verified math chain) + **F §7** | Lift-section (this is the natural deep-paper kernel for D4) |
| `paper12_polariton` | Polariton analog Hawking | PRL | **D1 §6** (polariton platform) + **E1** (Paris-LKB cover letter) + **F §4** | Lift-section + Lift-companion |
| `paper14_braided_mtc` | Braided MTC + knot invariants | PRD | **D4 §3** (Ising MTC complete + trefoil = −1 + figure-eight) + **F §7** | Lift-section |
| `paper15_methodology` | Verification methodology | CPC | **I1** (Methodology paper expanded with worked cases) + **F §9** | Lift-section (substantially expanded for I1; F gets summary) |
| `paper16_graphene_sk_eft` | Graphene Dirac-fluid SK-EFT | PRD | **D1 §7** (graphene platform + 92% Lean theorem reuse + noise spectrum) + **E2** (Dean-Kim-Lucas cover letter) + **F §4** | Lift-section + Lift-companion |
| `paper16_wrt_tqft` | WRT TQFT pipeline formalization | PRD | **D4 §5** (TQFT partition functions + WRT surgery) + **F §7** | Lift-section (note: the directory naming clash with paper16_graphene is a project-internal issue; both are 'paper16' but distinguished by suffix) |
| `paper17_dark_sector` | Dark-sector connections | PRD | **D5 §2** (DM classification + SFDM forecast) + **D5 §3** (DE structural NO-GO architecture) + **F §8** | Lift-section |
| `paper18_doublon_gate` | Geometric quantum gate (Fermi-Hubbard) | PRX | **D4 §6** (doublon SWAP + Berry-phase + first sym-protected gate) + **F §7** | Lift-section |
| `paper20_scalar_rung` (Phase 5z W1) | Scalar rung (Higgs identification) | (draft) | **D3 §11** (scalar rung + Higgs mass band) + **F §6** | Lift-section |
| `paper21_majorana_rung` (Phase 5z W2) | Majorana rung (seesaw + BCS no-go) | (draft) | **D3 §12** (Majorana rung + BCS no-go) + **F §6, §10** | Lift-section |
| `paper22_ew_phase_transition` (Phase 5z W3) | EW phase transition | (draft) | **D3 §13** (EW transition + crossover-excludes-baryogenesis) + **F §6, §10** | Lift-section |
| `paper23_linearized_efe` (Phase 6a W1+W4) | Linearized EFE + FLRW | PRD | **D3 §5** (linearized EFE + FLRW) + **F §6** | Lift-section |
| `paper25_gravitational_waves` (Phase 6a W2) | GW170817 vs vestigial graviton | PRD | **L1** (PRL splash, voucher candidate) + **D3 §6** (GW propagation full content) + **F §6, §10** | Lift-letter |
| `paper26_bh_entropy` (Phase 6a W3) | BH entropy from MTC counting | Annals | **D3 §7** (Bekenstein-Hawking + Kaul-Majumdar) + **F §6** | Lift-section |
| `paper27_bh_four_laws` (Phase 6a W5) | BCH four laws by regime | PRD (submission-ready) | **L3** (PRL splash, ships first wave with L1) + **D3 §8** (BCH four laws + regime partition full content) + **F §6** | Lift-letter |
| `paper29_bbn` (Phase 6b W1) | BBN classification | (draft) | **D5 §4** (BBN classification of Phase 5x DM candidates) + **F §8** | Lift-section |
| `paper32_strong_cp_topological_de` (Phase 6c W1) | Strong-CP + topological DE | (draft) | **D5 §5** (Zhitnitsky topological-DE absorption + combined-mechanism falsifier) + **F §8, §10** | Lift-section |
| `paper34_equivalence_principle` (Phase 6c W3) | Equivalence-principle classification | (draft) | **D5 §6** (EP-violation matrix; vestigial-only verdict) + **F §8** | Lift-section |
| `paper35_qec_holography` (Phase 6c W4) | QEC-Holography bridge | (draft) | **D4 §7** (QEC + scrambling on horizon-MTC) + **D3 §9** (cross-bridge to BH entropy) + **F §6, §7** | Lift-section (split) |
| `paper36_confinement` (Phase 6d W1) | Confinement (center symmetry) | (draft) | **D3 §14** (confinement + Polyakov loop + Svetitsky-Yaffe) + **F §6** | Lift-section |
| `paper37_chiral_ssb_qcd` (Phase 6d W2) | Chiral SSB / GMOR | (draft) | **D3 §15** (chiral SSB + GMOR PDG-verified) + **F §6** | Lift-section |
| `paper38_cfl_color_flavor_locking` (Phase 6d W3) | CFL color-flavor locking | (draft) | **D3 §16** (CFL ℤ_3 ≡ QCD center-ℤ_3 first formalization) + **F §6** | Lift-section |
| `note_rt_ch_bounds` (Phase 6c W5) | RT / Casini-Huerta bounds | short note | **D4 §8** (RT/CH knife-edge biconditional + tracked Props) + **F §7** | Lift-section |
| `paper39_heat_kernel_expansion` (Phase 6e W1) | Heat-kernel a₀, a₂, a₄ from Christensen-Duff Dirac | Annals | **D3 §17** (heat-kernel calibration + Sakharov-Adler ↔ G_N_emerg) + **F §6** | Lift-section |
| `paper40_higher_curvature` (Phase 6e W2) | Higher-curvature Stelle-basis structure at order a₄ | (draft) | **D3 §18** (Stelle (α,β,γ) closed form + observational ceiling check) + **F §6** | Lift-section |
| `paper41_diff_invariance` (Phase 6e W3) | Nonlinear diff invariance order-by-order | (draft) | **D3 §19** (Decision Gate E.3: path-(b) invariance through a₄) + **F §6** | Lift-section |
| `paper42_nonlinear_efe` (Phase 6e W4) | Variational nonlinear EFE Decision Gate biconditional + multi-channel PPN | (draft) | **D3 §20** (trace-level EFE + emergent vs matter T_μν + multi-channel PPN signatures) + **F §6** | Lift-section |
| `paper42b_cc_emergent` (Phase 6e W5) | Cosmological constant in emergent form (Decision Gate E.4) | (draft) | **D3 §21** (Λ^emerg microscopic prediction + CC-problem reproduction) + **D5 §7** (CC-channel constraint: heat-kernel a₀ does not produce Λ_obs naturally) + **F §6, §8** | Lift-section (split) |
| `paper43_einstein_cartan` (Phase 6e W6) | Einstein-Cartan torsion from ADW spin current — observational-bound passage | (draft) | **D3 §22** (EC torsion microscopic prediction + Kostelecky/Hughes-Drever bound passage) + **F §6** | Lift-section |

**Total: 39 existing draft directories** mapping to 13 publication targets.

---

## 2. Per-bundle source map (inverse view)

For each new publication target, the existing-draft sources it consumes. Helps Stage-1 scoping per bundle.

### Tier 0 — Flagship

**F. Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey**

Sources: every existing draft (summary content + cross-reference). Plus:
- `RESEARCH_STATUS_OVERVIEW.md` — proven-chains + scope sections
- `ARCHITECTURE_SCOPE.md` — §2 + §10 lift verbatim
- `temporary/Research-Overview/research_overview_analysis.md` — strategic-narrative synthesis
- `WAVE_EXECUTION_PIPELINE.md` — methodology summary

### Tier 1 — Deep papers

**D1. Analog Hawking across three platforms**
Sources: paper1, paper2, paper4, paper12, paper16_graphene_sk_eft.
Plus Phase 5w + Phase 5d + Phase 5u material.

**D2. Anomaly constraints on SM particle content**
Sources: paper7, paper8, paper9 (anomaly portion), paper10 (full derivation as primary section).
Plus Phase 5b/5c/5q/5r/5h material.

**D3. Emergent gravity through BH thermodynamics** (heaviest deep paper; Phase 6e adds the §17–§22 nonlinear-effective-action chain through Einstein-Cartan)
Sources: paper3, paper5, paper6 (conditional), paper20, paper21, paper22, paper23, paper25, paper26, paper27, paper35 (cross-bridge portion), paper36, paper37, paper38, paper39 (heat-kernel calibration), paper40 (higher-curvature Stelle), paper41 (diff invariance), paper42 (nonlinear EFE + PPN), paper42b (CC reproduction; primary in D3 §21), paper43 (EC torsion + bound passage; primary in D3 §22).
Plus Phase 3 + Phase 5d + Phase 5f + Phase 5z + Phase 6a + Phase 6d + Phase 6e material.

**D4. Topological quantum computation foundations**
Sources: paper9 (Drinfeld center portion), paper11 (primary kernel), paper14, paper16_wrt_tqft, paper18, paper35 (QEC portion), note_rt_ch_bounds.
Plus Phase 5b–5p material.

**D5. Dark sector under substrate constraints**
Sources: paper17 (DM and DE classification), paper29, paper32, paper34, paper42b (CC-channel constraint contribution; primary in D3, secondary §7 here).
Plus Phase 5x + Phase 5y + Phase 6b + Phase 6c + Phase 6e Wave 5 + (when shipped) Phase 6m material.

### Tier 2 — PRL splashes

**L1. GW170817 / vestigial-graviton**
Source: paper25 (4-page PRL kernel).

**L2. Three generations from modular invariance**
Source: paper10 (4-page PRL kernel).

**L3. BCH four laws by regime**
Source: paper27 (4-page PRL kernel; already submission-ready).

### Tier 3 — Infrastructure

**I1. Verification methodology with worked cases**
Source: paper15 (substantially expanded).
Plus: WAVE_EXECUTION_PIPELINE.md content; curated reviewer-driven-correction trace; FirstOrderKMS Aristotle counterexample case study; gap-solution-bounded counterexample case study; chirality-wall axiom decomposition case study.

**I2. Verified statistical estimators + lean-tensor-categories**
Source: Phase 5c VerifiedJackknife material; Phase 5o Wave 4 lean-tensor-categories library + Wave 5 Mathlib upstream cycle (when first PR in review).

### Tier 4 — Experimental letters

**E1. Paris-LKB polariton letter**
Source: paper12 (companion content); Phase 5u Wave 21 cover letter draft.

**E2. Dean-Kim-Lucas graphene letter**
Source: paper16_graphene_sk_eft (companion content).

---

## 3. Per-bundle Stage-13 review scope

Each bundle gets at least one full-pass Stage 13 adversarial review before submission. The reviewer prompts (`physics-qa:claims-reviewer` + figure reviewer) need to know the *bundle* scope, not just the existing per-paper scope. Per-bundle review fingerprint:

- **L1, L2, L3:** stand-alone PRL review, single-paper depth. Each must pass without leaning on other bundles. Each carries a specific Stage-13 anchor (LIGO Δc/c bound for L1; Ext computation + 24 | c₋ chain for L2; Balbinot 2005 + Hawking 1975 for L3).
- **D1–D5:** deep-paper bundle review. Each bundle has 30+ source-claim sentences from contributing existing drafts; the bundle review confirms (a) no within-bundle inconsistency between lifted sections, (b) cross-bundle consistency with sibling bundles for any cross-bridge claim, (c) the architectural-scope sidebar is correctly slice-restricted. Bundles D3 and D5 are the largest, ~50pp each, and may need two Stage-13 passes.
- **F (flagship):** review-paper-style Stage-13 pass. Independent reviewer-anchored against `ARCHITECTURE_SCOPE.md`, `RESEARCH_STATUS_OVERVIEW.md`, and the shipped Tier 1 bundle published versions (the flagship cites the published forms, so it's reviewed *after* the Tier 1 papers are out).
- **I1, I2:** standard methods/software paper reviews; less stringent than physics-claim depth but still per-bundle.
- **E1, E2:** lightweight letter review, plus device-parameter audit pass for accuracy against the experimental team's published device specs.

---

## 4. Sentence-level provenance re-mapping

The Phase 5v / Phase 6i sentence-state infrastructure (`prose_state.json`, `audit_log.jsonl`) tracks every sentence of every existing draft to its claim cluster + primary source + Lean theorem. **Phase 6i Wave 7** wires the bundle re-mapping into this infrastructure:

1. Each existing-draft sentence acquires a `bundle_destination` field (e.g., `"D3:§5"` or `"L1"` or `"E1"`).
2. Sentences whose lift action is **Lift-section** carry their `claim_cluster` ID into the bundle; cross-bundle clusters reform automatically via the Phase 5v cluster-detection script.
3. Sentences whose action is **Lift-letter** carry into both the splash bundle and the deep bundle; the Phase 5v cross-paper-consistency check enforces that the splash's claim is consistent with the deep paper's claim.
4. Sentences whose action is **Retire** are tombstoned in `prose_state.json` with `tombstoned_reason: "consolidated_into_bundle"`.
5. The `Phase6i_Roadmap.md` Wave 7 deliverable adds a `bundle_destination` to the v2 schema and produces the migration script that reads `PAPER_DRAFT_MAPPING.md` (this document) as the source of truth.

---

## 5. Decision points still open

These decisions are deferred to per-bundle Stage 1 scoping or to user authorization. They do not block the strategy.

- **Should D4 split into D4a (math-physics, *Comm. Math. Phys.*) + D4b (quantum computation, *PRX Quantum*)?** Decision: deferred to D4 Stage 1 scoping; recommended single-paper unless reviewer strongly prefers split.
- **Should paper6 (vestigial MC) lift as a section of D3 §10 unconditionally, or only if RHMC convergence at L≥8 lands?** Decision: conditional on RHMC outcome. If convergence positive, becomes D3 §10. If convergence negative, becomes a stand-alone "publishable negative result" *PRR* paper plus a §10 brief in D3 noting the redirect.
- **Should D5 ship before Phase 6m closure, in a "Volovik-only" form?** Decision: prefer to wait for Phase 6m; D5 is much stronger as a closed predictive-scope statement. Acceptable fallback: ship D5 as Volovik-only with a planned Phase 6m extension paper.
- **Should I1 explicitly name the cases where Aristotle / Stage 13 caught errors?** Decision: yes — without concrete worked cases, I1 is a process essay rather than an empirical argument. The user / PI needs to authorize the case-disclosure (e.g., FirstOrderKMS counterexample is now public via Phase 1 Aristotle run; gap-solution-bounded counterexample is in Phase 5d Aristotle run; chirality-wall axiom decomposition is in Phase 5h history). All are already in the project record.
- **What's the arXiv-submission identity?** The PI's institutional affiliation determines first-submission eligibility. arXiv voucher is per-author. L1 carries the PI as sole author or co-author with collaborators TBD. Discussion item.

---

*Created 2026-04-28. Companion to `PAPER_STRATEGY.md`. Sentence-level re-mapping wired by `roadmaps/Phase6i_Roadmap.md` Wave 7.*
