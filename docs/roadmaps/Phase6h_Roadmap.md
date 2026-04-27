# Phase 6h: Substrate Phase Diagram and Symmetric Mass Generation

## Technical Roadmap — April 2026

*Prepared 2026-04-27 | **Conditional phase** — activates only on positive close of **Phase 5z Wave 4** (`MajoranaRungSMG.lean`) per Gate Z.4 of `Phase5z_Roadmap.md`. Sources: `Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` (Hasenfratz-Witzel SMG, Razamat-Tong, Catterall), `Lit-Search/Phase-5b/Formalizing bidirectional anomaly constraints in theoretical physics.md` (Catterall-KD ↔ ℤ₁₆), `Lit-Search/Phase-5z/Phase 5z Wave 2a — Majorana-Channel Projection of the Tetrad Gap Equation.md` (BCS no-go ⇒ SMG alternative), `Lit-Search/Phase-3/The ADW mean-field gap equation for tetrad condensation with emergent Dirac fermions.md` (substrate HS gap remains unwritten in primary literature).*

**Trigger condition (Gate Z.4 of Phase 5z):** Phase 5z Wave 4 ships positively, meaning:
- `MajoranaRungSMG.lean` builds clean with 10–14 substantive theorems, zero sorry, zero new axioms
- Hasenfratz-Witzel-anchored Λ_SMG → M_R lands in the 10⁹–10¹⁵ GeV seesaw band under documented substrate-parameter assumptions
- The SMG branch is shown structurally distinct from the BCS branch (does NOT require lepton-number violation) AND is shown structurally consistent with the ℤ₁₆ singlet-branch via the Catterall 16-Weyl-per-generation lattice manifestation
- Wave 4 deep-research return (`Lit-Search/Tasks/complete/Phase5z_W4_smg_substrate_phase_diagram.md`) confirms the ADW substrate plausibly sits in or near the Hasenfratz-Witzel SMG window

**Status update (2026-04-27):** **Gate Z.4 closed NEGATIVE.** The Wave 4 deep research returned OPEN-AT-LITERATURE-FRONTIER on all three sub-questions, with Vladimirov-Diakonov's own mean-field tilting NEGATIVE (chiral-SSB phase, no SMG). Phase 5z Wave 4 shipped as a **second structural no-go** parallel to Wave 2's BCS no-go. **Phase 6h has NOT activated.** The roadmap stays in this file as a documented latent option.

**Concrete activation criteria — published-research events that flip Gate Z.4 positive:** Per Wave 4 deep research §6 falsifier list (`Lit-Search/Tasks/complete/Phase5z_W4_smg_substrate_phase_diagram.md`), Phase 6h becomes ship-eligible if any one of the following published research events occurs:

- **(F-a-1) Lattice MC of V&D 8-coupling action identifies a chirally symmetric massive phase.** A 4D lattice Monte Carlo simulation of the Vladimirov-Diakonov (PRD 86 104019, 2012) 8-fermion action — currently un-simulated in any published work — finds a chirally-symmetric massive phase with a 2nd-order transition into the massless phase. Most direct positive-closure path. Requires substantial computational effort but no obstacle in principle. *If this lands*, Phase 6h activates with the `H_SubstrateNearSMGFixedPoint` tracked hypothesis (currently OPEN-W4-1) promoted to a derived theorem, and OPEN-6h-1 (Wave 1 of Phase 6h) closes positively from the start.

- **(F-a-3) Kähler-Dirac extension of V&D reduces to KD SMG.** A theoretical demonstration that the V&D substrate, after augmentation to a full Kähler-Dirac multiplet (vertex + edge + face + tetrahedron + 4-cell components per Catterall-Laiho-Unmuth-Yockey PRD 98 114503, 2018), reduces to two copies of the Kähler-Dirac SMG action of Butt-Catterall-Pradhan-Toga (PRD 104 094504, 2021) in some limit. Establishes SMG eligibility of ADW indirectly through the K-D bridge. *If this lands*, Phase 6h Waves 2 (`SymmetricMassGeneration`) and 3 (`MajoranaRungSMG` extension + PMNS via Catterall-Pati-Salam) become directly executable with Catterall's framework as the substrate-derived (not substrate-postulated) anchor.

- **(F-c-1) 4D analog of Fidkowski-Kitaev rigour for 16-Majorana SMG.** A 4D analog of the Fidkowski-Kitaev rigorous proof (PRB 81 134509, 2010) — currently the only rigorous mirror-decoupling proof, valid only in 2D — that proves 16-Majorana SMG gapping is rigorous in 4D rather than merely conjectural (Catterall arXiv:2311.02487 §4 explicitly conjectures this). Central open problem in lattice chiral gauge theory. *If this lands*, the `H_CatterallMirrorDecoupling` tracked hypothesis (Wave 3) promotes to theorem, the Pati-Salam emergence at the continuum limit becomes a theorem rather than a conjecture, and Phase 6h's flagship paper (Wave 3) acquires a rigorous foundation. This is the highest-impact closure path but the lowest probability per current literature.

**Secondary closure paths** (Wave 4 deep research §6, would partial-close Gate Z.4 sub-questions):

- **(F-a-2) FRG of V&D substrate finds merged UV-IR fixed point** (analog of Hasenfratz-Witzel for V&D action) — would close the SMG-window question via functional-RG rather than lattice MC. Difficulty medium.
- **(F-a-4) Direct anomaly-matching argument for V&D-Razamat-Tong compatibility** — would close the Spin × ℤ₄ symmetry mismatch concern. Difficulty medium-high.
- **(F-b-1) Lattice MC measures Λ_SMG / a⁻¹ on V&D** — would tighten the c_SMG band from `[10⁻¹², 10⁻³]` (broad NJL envelope) to a substrate-derived value. Difficulty: same as F-a-1 (paired observable from same lattice study).
- **(F-b-2) Bilocal-NJL Hill-style closed-form Λ_SMG = f(λ_1,…,λ_8, Λ_UV)** — would replace the project-internal Fierz-translation with a literature-derived closed form. Difficulty medium.
- **(F-c-2) Razamat-Tong on emergent-Lorentz substrate** — addresses risk axis R4 (emergent vs background Spin(4)). Difficulty medium-high.
- **(F-c-3) Lattice MC of Catterall Pati-Salam mirror model demonstrates 4D mirror decoupling** — partial-closure of (F-c-1) at the empirical level. Difficulty: substantial computational effort.

Any combination of (F-b-1)+(F-b-2) plus one of (F-a-1)/(F-a-3)/(F-c-1) would constitute full closure. A single F-a-1 / F-a-3 / F-c-1 alone is sufficient to flip Gate Z.4 positive.

**Project-internal calculation routes** (alternatives to waiting for external publication):

- **NJL Fierz-complete RG analysis on V&D 8-coupling action** (extending Braun-Leonhardt-Pospiech I/II/III to 8 channels) — most tractable internal route per Wave 4 deep research §8 closing remark. Would yield F-a-2 directly. Difficulty: a substantial Phase-5d-style continuation; would likely become its own phase (5z.5 or 6i) with ~6–12 PM scope.
- **Augmented V&D action with Kähler-Dirac multiplet** (testing F-a-3 via internal calculation) — algebraic/representation-theoretic; would yield F-a-3 via theorem rather than conjecture. Difficulty medium.

**If Phase 5z Wave 4 ships negatively (second no-go):** Phase 6h does not activate. Instead, the Phase 5z `MajoranaRung.lean` paper is upgraded to a strengthened obstruction note covering both BCS *and* SMG branches, and the substrate-bridge derivation closes as impossible-in-current-substrate-models. Phase 6h remains a documented latent option for a future substrate model that escapes both no-gos. **This is the current state as of 2026-04-27.**

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **VERIFY THE TRIGGER:** Before any Phase 6h work begins, verify Gate Z.4 of `docs/roadmaps/Phase5z_Roadmap.md` was passed. Read `lean/SKEFTHawking/MajoranaRungSMG.lean` (must exist) and the Wave 4 closure status update at top of `Phase5z_Roadmap.md`. If `MajoranaRungSMG.lean` does not exist or Wave 4 ship date is missing, **STOP** — Phase 6h has not activated; flag to user and ask whether Wave 4 is on the immediate path.
> 2. **Mandatory project bootstrap (CLAUDE.md §"Mandatory References"):**
>    - `CLAUDE.md`
>    - `SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md`
>    - `SK_EFT_Hawking/SK_EFT_Hawking_Inventory_Index.md`
>    - `SK_EFT_Hawking/README.MD`
>    - `temporary/working-docs/brainstorm/20260413-context-lean-dev/Lean-Development-Optimization.txt`
>    - `SK_EFT_Hawking/docs/references/Theorm_Proving_Aristotle_Lean.md`
> 3. Read this roadmap end-to-end before claiming any wave assignment.
> 4. Read **`docs/roadmaps/Phase5z_Roadmap.md` Wave 4 section** in full — Phase 5z Wave 4 *is* Phase 6h's structural foundation; Phase 6h Wave 3 promotes it.
> 5. **Critical deep-research dossiers (read directly, not via subagent — per CLAUDE.md):**
>    - `Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` — Hasenfratz-Witzel SMG, Razamat-Tong s-confinement, Wan-Wang K-gauge TQFT tables, Catterall-KD ↔ ℤ₁₆ unit, Wang Ultra-Unification scenario 1c
>    - `Lit-Search/Phase-5b/Formalizing bidirectional anomaly constraints in theoretical physics.md` — Catterall Kähler-Dirac → Pati-Salam from SMG mirror decoupling (§6); Drinfeld-center / SymTFT context (§3)
>    - `Lit-Search/Phase-5z/Phase 5z Wave 2a — Majorana-Channel Projection of the Tetrad Gap Equation.md` — BCS no-go (Scenario B); SMG positioned as Scenario D alternative; Braun-Leonhardt-Pawlowski Fierz-complete machinery
>    - `Lit-Search/Phase-5/Phase_5_follow-up_Effective nearest-neighbor action in ADW tetrad condensation after SO(4) Haar integration.md` — Vladimirov-Diakonov 5 8-fermion + 3 4-fermion couplings; Peter-Weyl decomposition; ε-tensor "baryonic" SO(4) sector
>    - `Lit-Search/Phase-3/The ADW mean-field gap equation for tetrad condensation with emergent Dirac fermions.md` — Hubbard-Stratonovich landscape; Maitiniyazi-Matsuzaki-Oda-Yamada irreversible-vierbein-postulate (PRD 109 106018, 2024)
>    - `Lit-Search/Phase-5f/Two-loop NJL gap equation for tetrad condensation.md` — strict-NLO vs CJT scheme dependence; structural advantages of the tetrad channel
>    - `Lit-Search/Phase-1-and-Background/Tier-2/The fermion bootstrap problem in emergent gravity.md` — Vergeles-style fundamental-Grassmann route vs emergent-fermion route; SMG's relation to vestigial gravity
>    - `Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for the Majorana Rung.md` — Embedding III context for the seesaw target
> 6. **Key external papers (titles + arXiv IDs; fetch via WebFetch at Stage 13 verification):**
>    - Hasenfratz & Witzel, arXiv:2412.10322 (2024); arXiv:2511.22678 (2025) — SMG SU(3) N_f=8 lattice evidence, continuum-limit confirmation
>    - Catterall, arXiv:2311.02487, SciPost Phys. 16 108 (2024) — Pati-Salam from KD on lattice
>    - Razamat & Tong, PRX 11 011063 (2021) — s-confinement gaps 16 Weyl preserving Spin × ℤ₄
>    - Wan & Wang, arXiv:2512.25038 (2025) — K-gauge TQFT anomaly tables
>    - Braun, Leonhardt & Pospiech I/II/III, PRD 96 076003 (2017); PRD 97 076010 (2018); PRD 101 036004 (2020) — Fierz-complete FRG-NJL with diquark channels
>    - Vladimirov & Diakonov, PRD 86 104019 (2012) — 4D simplicial ADW lattice with 8 dimensionless couplings
>    - Maitiniyazi, Matsuzaki, Oda, Yamada, PRD 109 106018 (2024) — irreversible-vierbein-postulate; closest published HS realization
> 7. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to Hasenfratz-Witzel band, Vladimirov-Diakonov coupling space, Λ_QCD/Λ_SMG/Λ_UV hierarchies); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check; (5) defining-the-conclusion check. End-of-wave strengthening pass should produce ≤ 2 retroactive theorems (per Phase 6c.4/6c.5 trend; Phase 6b.1 baseline of 5).
> 8. **Do not delegate Lean theorem proving to subagents.** Phase 6h is hard theorem proving; subagents lose tactic-level detail per CLAUDE.md.

**Entry state (calibration, 2026-04-27 inventory snapshot):** ~4225 thms, 179 modules, 0 sorry, 1 axiom (`gapped_interface_axiom`). On Phase 5z Wave 4 close: ~4235–4239 thms, 180 modules.

**Anchors carried forward into Phase 6h:**
- `MajoranaRungSMG.lean` (Phase 5z Wave 4) — structural foundation; promoted to Phase 6h Wave 3
- `MajoranaRung.lean` (Phase 5z Wave 2) — BCS branch; co-existence with SMG branch is the *disjointness* content of `smg_and_BCS_apply_in_distinct_substrate_regimes`
- `MajoranaRungDecoupling.lean` (Phase 5z Wave 2b) — Appelquist-Carazzone IR-equivalence framework
- `Z16AnomalyComputation.lean` + `HiddenSectorClassification.lean` (Phase 5x) — ℤ₁₆ singlet-branch infrastructure; Catterall 16-Weyl unit cross-bridges into Phase 6h via lattice manifestation
- `WetterichNJL.lean` + `BHLGaugeEmbedding.lean` (Phase 5z Waves 1/1b) — Fierz-complete substrate-channel infrastructure; Braun-Leonhardt-Pawlowski transplant template
- `TetradGapEquation.lean` + `ADWMechanism.lean` (Phase 3/5d) — substrate gap-equation infrastructure; Vladimirov-Diakonov 4D simplicial lattice background
- Bonn Massot↔Rothgang Mathlib differential-geometry branch (Phase 6f context) — *not* a load-bearing dependency for Phase 6h, but waves touching the substrate's lattice geometry may benefit downstream

**Thesis.** If Symmetric Mass Generation is the substrate's mechanism for fermion mass generation, the consequences extend far beyond `M_R`: the substrate phase diagram acquires an SMG window with a continuous-fixed-point structure (Hasenfratz-Witzel merged UV-IR fixed point), the ℤ₁₆ singlet-branch acquires a lattice manifestation via Catterall-KD, the SM fermion mass hierarchy acquires a possible explanation via proximity-to-SMG-fixed-point physics, the Pati-Salam SU(4) × SU(2)_L × SU(2)_R structure emerges from Catterall mirror decoupling, and the EW baryogenesis chain (Phase 6c.2, currently OPEN) acquires a microscopic mechanism. Phase 6h ships these consequences as five waves of formal verification + one paper.

**Correctness-push framing.** Phase 6h's correctness-push anchors are quantitative and lattice-anchored: (i) substrate phase diagram → identifies the SMG window in (Λ_UV, λ_1, ..., λ_8) parameter space; (ii) hierarchy from fixed-point proximity → predicts m_e/m_t ratio from substrate parameters within an order of magnitude; (iii) Pati-Salam emergence → predicts (4,2,1) ⊕ (4̄,1,2) matter content under documented mirror-decoupling assumptions. Each is falsifiable against PDG 2024 + Hasenfratz-Witzel band + Catterall lattice scaling.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6h:**
- Substrate phase-diagram formalization: BCS / SMG / vestigial / disordered partition
- SMG mechanism in Lean: Hasenfratz-Witzel continuum-limit fixed point, Razamat-Tong s-confinement gaps 16 Weyl preserving Spin × ℤ₄
- Catterall Kähler-Dirac ↔ ℤ₁₆ unit lattice manifestation; Pati-Salam emergence from mirror decoupling
- Promoted `MajoranaRungSMG` (Phase 5z W4) + extension to PMNS structure via Catterall-Pati-Salam representation theory
- Light-fermion mass hierarchy from proximity to SMG fixed point (m_t ~ 1 from in-window, m_e ~ 10⁻⁶ from edge-of-window)
- Bridge to Phase 6c.2 (EW baryogenesis ↔ chirality wall): SMG provides microscopic mechanism for chirality wall generation

**OUT OF SCOPE for Phase 6h (deferred or other phases):**
- Full lattice MC simulation of ADW substrate near SMG window — separate computational effort; Phase 6h Lean ships the predicates and theorems, lattice MC is a follow-up project (potential Phase 5d/5w-style continuation)
- 4D rigorous proof of mirror decoupling — Catterall conjectures it; proven only in 2D via Fidkowski-Kitaev. Phase 6h treats 4D mirror decoupling as a tracked hypothesis.
- Direct connection to gravity sector — Phase 6e (nonlinear gravity) territory; Phase 6h focuses on fermion-mass-generation mechanism only
- Vergeles unitarity-proof-style UV completion — fundamental-Grassmann route is structurally distinct from emergent-fermion SMG route; Phase 6h does NOT attempt a Vergeles-style proof for the SMG substrate

**Phase 5z relationship:** Phase 6h is Phase 5z's natural escalation if Wave 4 closes positively. Phase 6h does not reopen Phase 5z; it builds *on* the shipped Phase 5z waves.

**Phase 5x relationship:** Catterall's lattice manifestation of ℤ₁₆ unit (via Kähler-Dirac on cubic lattice) is the structural bridge from Phase 5x (anomaly-classification dark sector) to Phase 6h (substrate-mechanism mass generation). Phase 6h does NOT modify Phase 5x's dark-matter classification; it adds a co-located mechanism for ℤ₁₆ saturation via SMG rather than via fundamental sterile neutrinos.

**Phase 6c relationship:** Phase 6c.2 (EW baryogenesis ↔ chirality wall, currently OPEN) is the natural downstream consumer of Phase 6h Wave 5. Phase 6h Wave 5 ships the SMG-instantiated chirality wall; Phase 6c.2 then uses it as input.

---

## Wave 1 — `SubstratePhaseDiagram.lean` [6h.1] [Pipeline: Stages 1–8 + 10]

**Goal:** Formalize the substrate's phase diagram in (Λ_UV, λ_1, ..., λ_8) Vladimirov-Diakonov coupling space, partitioning it into BCS, SMG, vestigial-metric, and disordered phases. Identify the SMG window via Hasenfratz-Witzel continuum-limit anchors.

**Prerequisites:**
- Phase 5z Wave 4 (`MajoranaRungSMG.lean`) — structural foundation, must be SHIPPED
- Phase 3/5d `TetradGapEquation.lean` + `ADWMechanism.lean` — substrate gap-equation infrastructure
- Phase 5z Wave 1/1b `WetterichNJL.lean` + `BHLGaugeEmbedding.lean` — Fierz-complete coupling structure
- Deep-research dossier `Lit-Search/Phase-5/Phase_5_follow-up_Effective nearest-neighbor action in ADW tetrad condensation after SO(4) Haar integration.md` (read directly)

**Module structure:**
- `lean/SKEFTHawking/SubstratePhaseDiagram.lean`
  - `structure SubstrateCouplings` — Vladimirov-Diakonov 8 dimensionless couplings (3 four-fermion + 5 eight-fermion) plus Λ_UV; positivity / hierarchy constraints
  - `inductive SubstratePhase` — `BCS | SMG | VestigialMetric | Disordered`
  - `def H_PhaseAssignment (s : SubstrateCouplings) (φ : SubstratePhase) : Prop` — tracked-hypothesis predicate that substrate parameters land in phase `φ`. Non-vacuous via:
    - `BCS_phase_window`: explicit characterization via `H_LeptonNumberViolated G_LV ≠ 0` AND `G_M > G_c` (BCS supercriticality from `MajoranaRung.H_MR_FromADWSubstrate_BCS_LNV`)
    - `SMG_phase_window`: explicit characterization via Hasenfratz-Witzel band — strong-coupling region with merged UV-IR fixed point, characterized by `c_SMG ∈ [0.1, 1.0]` from `MajoranaRungSMG.H_SubstrateNearSMGFixedPoint`
    - `VestigialMetric_phase_window`: per Volovik 2024 — ⟨Ê^a_μ⟩ = 0 but ⟨Ê^a_μ Ê^b_ν⟩ ≠ 0; characterized by 4-fermion condensation without 2-fermion order
    - `Disordered_phase_window`: complement of all three above
  - **Phase-disjointness theorem:** `theorem substrate_phases_partition_param_space` — the four `*_phase_window` predicates are pairwise disjoint and (under documented coverage assumptions) jointly exhaustive
  - **Bridge theorem to Wave 2 (Phase 5z) BCS branch:** `theorem BCS_phase_implies_BCS_substrate_bridge` — if substrate is in BCS phase, Wave 2's `H_MR_FromADWSubstrate_BCS_LNV` applies. Cross-bridge call.
  - **Bridge theorem to Wave 4 (Phase 5z) SMG branch:** `theorem SMG_phase_implies_SMG_substrate_bridge` — if substrate is in SMG phase, Wave 4's `H_MR_FromSMGGap` applies. Cross-bridge call.
  - **Falsifiability witness for Phase 6h:** `theorem substrate_phase_predicts_M_R_consistent_with_NuFit` — under documented phase assignment, predicted `M_R` lands in NuFit-6.0 seesaw band (10⁹–10¹⁵ GeV per `MAJORANA_PARAMS`). Quantitative `norm_num`-backed comparison.
  - **Phase-transition theorem (Vladimirov-Diakonov-flavor):** `theorem second_order_transition_at_phase_boundary` — the BCS-SMG and SMG-disordered phase boundaries are second-order continuous transitions (as in Vladimirov-Diakonov PRD 86 104019, 2012).
  - `def H_SubstrateInSMGWindow (s : SubstrateCouplings) : Prop` — load-bearing tracked hypothesis for Phase 6h consumption: substrate parameters explicitly in SMG window. Conditional on lattice-MC verification (OPEN-6h-1).
  - `def Wave1OpenManifest_6h` — non-vacuous bundle of OPEN-6h-{1,2,3}: lattice MC of ADW substrate near Hasenfratz-Witzel parameters; phase-boundary identification on simplicial lattice; ε-tensor "baryonic" SO(4) sector contribution
- Target: **14–18 substantive theorems**, 0 sorry, 0 new axioms

**Python side:**
- `src/substrate_phase_diagram/__init__.py`
- `src/substrate_phase_diagram/phase_classifier.py` — given (Λ_UV, λ_1, ..., λ_8), predict phase via documented coupling-window thresholds
- `src/substrate_phase_diagram/hasenfratz_witzel_anchor.py` — convert SU(3) N_f=8 lattice anchors to substrate-parameter ranges
- `src/core/formulas.py` additions: `substrate_phase_classifier(couplings)`, `smg_window_band_lower(N_f)`, `smg_window_band_upper(N_f)`
- `tests/test_substrate_phase_diagram.py` — ~15 pytest

**Bridges:**
- Depends on Phase 5z W2 + W4 + Phase 5z W1/1b
- Feeds Phase 6h W2-W5 (all downstream Phase 6h waves)
- Feeds Phase 6c.2 (EW baryogenesis) — phase classification as input

**Deliverables:**
- Module zero-sorry, building clean
- 14–18 theorems
- Python `src/substrate_phase_diagram/` (3 modules)
- ~15 pytest in `tests/test_substrate_phase_diagram.py`
- Figure: `fig_substrate_phase_diagram` in `visualizations.py` — 2D projection of phase boundaries in (Λ_UV / M_Pl, G_c) plane with SMG window highlighted; Hasenfratz-Witzel anchor point marked
- Inventory update: +14–18 theorems, +1 Lean module, +1 Python subpackage, +1 figure

**Estimated LOE:** **3–5 person-months**
**Risk:** Medium. Phase-window characterizations are tracked hypotheses (not derived); the load-bearing physics is in the deep-research substrate parameter mappings.

**Correctness-push.** Identifies the SMG window in substrate parameter space and confirms it includes a Hasenfratz-Witzel-compatible region. If the SMG window is empty or inaccessible to ADW substrate parameters, Phase 6h closes early as a strengthened no-go.

---

## Wave 2 — `SymmetricMassGeneration.lean` [6h.2] [Pipeline: Stages 1–8 + 10]

**Goal:** Formalize the SMG mechanism itself: Hasenfratz-Witzel continuum-limit fixed point structure, Razamat-Tong s-confinement-gaps-16-Weyl-preserving-Spin × ℤ₄ theorem, Catterall Kähler-Dirac ↔ ℤ₁₆ unit lattice manifestation. Build the cross-bridge from SMG to the Phase 5x ℤ₁₆ classification.

**Prerequisites:**
- Wave 1 (`SubstratePhaseDiagram.lean`) complete
- Phase 5x `Z16AnomalyComputation.lean` + `HiddenSectorClassification.lean` (cross-bridge target)
- Phase 5z W4 `MajoranaRungSMG.lean`

**Module structure:**
- `lean/SKEFTHawking/SymmetricMassGeneration.lean`
  - `structure SMGContinuumFixedPoint` — Hasenfratz-Witzel merged UV-IR fixed point: `(Λ_strong, η_SMG, ν_SMG)` with critical exponents
  - `def H_HasenfratzWitzelContinuumLimit (s : SubstrateCouplings) : Prop` — tracked hypothesis that substrate continuum limit exhibits the Hasenfratz-Witzel SMG fixed point. Non-vacuous: requires N_f-anchor consistent with SU(3) N_f=8 lattice scaling.
  - `def H_RazamatTongSConfinement (s : SubstrateCouplings) : Prop` — tracked hypothesis that substrate's s-confinement gaps 16 Weyl fermions while preserving Spin × ℤ₄ (Razamat-Tong PRX 11 011063 2021).
  - **Razamat-Tong 16-Weyl theorem:** `theorem s_confinement_gaps_sixteen_weyl_preserving_spin_z4` — under `H_RazamatTongSConfinement`, exactly 16 Weyl fermions are gapped per generation while Spin × ℤ₄ symmetry is preserved. Cross-bridge to `Z16AnomalyComputation.three_nu_R_cancel_three_gen` via the explicit 16-count.
  - **Catterall lattice manifestation theorem:** `theorem catterall_kd_realizes_z16_unit` — Kähler-Dirac on cubic lattice with 4 reduced fields gives 16 Weyl in continuum; this is the lattice instantiation of the Phase 5x ℤ₁₆ unit. Calls `HiddenSectorClassification.three_singlets_satisfy_hidden_sector` to close the bridge.
  - **No-LNV-required theorem:** `theorem smg_mechanism_does_not_require_LNV` — promoted from Phase 5z W4's `smg_route_does_not_require_LNV`; restated at the mechanism level (not just the M_R derivation level).
  - **Z_4 preservation theorem:** `theorem smg_preserves_z4_x` — Razamat-Tong's preservation of Spin × ℤ₄ implies preservation of Z_{4,X} = 5(B-L) - 4Y; this means SMG is consistent with Wang Ultra-Unification scenario 1c (Wang 2008.06499) WITHOUT requiring Z_{4,X} to be broken.
  - **Wan-Wang K-gauge TQFT compatibility:** `theorem smg_compatible_with_K_gauge_TQFT_extension` — the SMG mechanism is structurally compatible with Wan-Wang's K-gauge TQFT anomaly-trivialization construction (arXiv:2512.25038); SMG and K-gauge-TQFT are *parallel* mechanisms for the same ℤ₁₆ deficit, not competing.
  - `def H_MergedUVIRFixedPoint (s : SubstrateCouplings) : Prop` — load-bearing for Wave 4 (hierarchy): substrate continuum limit has the merged UV-IR fixed-point structure (Hasenfratz-Witzel arXiv:2511.22678 EPS-HEP2025).
  - **Falsifiability witness:** `theorem smg_window_falsified_if_no_strong_coupling_phase` — if the substrate's strong-coupling regime does NOT exhibit a continuum limit (Λ_strong = 0 or undefined), the SMG mechanism is structurally falsified for that substrate.
- Target: **12–16 substantive theorems**, 0 sorry, 0 new axioms

**Python side:**
- `src/smg/__init__.py`
- `src/smg/hasenfratz_witzel.py` — continuum-limit fixed-point parameters; SU(3) N_f=8 anchor; merged UV-IR fixed-point critical exponents
- `src/smg/razamat_tong.py` — s-confinement 16-Weyl-counting verification
- `src/smg/catterall_kd.py` — Kähler-Dirac on lattice; 4-reduced-field-to-16-Weyl scaling
- `src/core/formulas.py` additions: `hasenfratz_witzel_lambda_strong(N_f)`, `razamat_tong_weyl_count(s_confinement_data)`, `catterall_kd_continuum_count(reduced_fields)`
- `tests/test_smg_mechanism.py` — ~14 pytest

**Bridges:**
- Depends on Wave 1 (Phase 6h)
- Cross-bridges to Phase 5x `HiddenSectorClassification.lean`, `Z16AnomalyComputation.lean`
- Feeds Phase 6h Wave 3 (`MajoranaRungSMG` extension to PMNS), Wave 4 (hierarchy from fixed-point proximity), Wave 5 (chirality wall instantiation)

**Deliverables:**
- Module zero-sorry, building clean
- 12–16 theorems, 0 new axioms
- Python `src/smg/` (4 modules)
- ~14 pytest
- Figure: `fig_smg_mechanism_landscape` — Hasenfratz-Witzel SMG + Razamat-Tong s-confinement + Catterall-KD as three structurally compatible realizations of the same SMG mechanism, with cross-bridges marked
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python subpackage, +1 figure

**Estimated LOE:** **3–4 person-months**
**Risk:** Medium. The cross-bridge theorems to Phase 5x infrastructure are structurally tight (Catterall's KD-on-lattice → 16-Weyl is rigorous); the open hypothesis content is the substrate-parameter-to-SMG-mechanism mapping.

**Correctness-push.** First formalization of the SMG mechanism in any proof assistant, with explicit cross-bridges to anomaly-classification machinery. Per Phase 6f.3 precedent (first formalization of energy conditions across all proof assistants).

---

## Wave 3 — `MajoranaRungSMG.lean` extension + PMNS via Catterall-Pati-Salam [6h.3] [Pipeline: Stages 1–8 + 10]

**Goal:** Promote the Phase 5z Wave 4 `MajoranaRungSMG.lean` and extend it with PMNS structure via Catterall mirror-decoupling Pati-Salam SU(4) × SU(2)_L × SU(2)_R representation theory. Provides the first formal-verification PMNS prediction from a substrate mechanism.

**Prerequisites:**
- Wave 1 + Wave 2 (Phase 6h) complete
- Phase 5z Wave 4 `MajoranaRungSMG.lean` SHIPPED (this wave promotes it)
- Phase 5z Wave 2 `NeutrinoMixing.lean` (PMNS structure note baseline)

**Module structure:**
- **Promote** `lean/SKEFTHawking/MajoranaRungSMG.lean` — Phase 5z W4 module, augmented with Phase 6h cross-bridges to `SubstratePhaseDiagram.lean` and `SymmetricMassGeneration.lean`
- **Extend** `lean/SKEFTHawking/NeutrinoMixingSMG.lean` — Pati-Salam representation theory + PMNS prediction
  - `structure PatiSalamFermionContent` — the (4,2,1) ⊕ (4̄,1,2) representation under SU(4) × SU(2)_L × SU(2)_R from Catterall mirror decoupling
  - `def H_CatterallMirrorDecoupling (s : SubstrateCouplings) : Prop` — tracked hypothesis: Catterall's mirror-decoupling-via-SMG yields Pati-Salam matter content. **Conjectural in 4D** (proven only in 2D via Fidkowski-Kitaev for 8 Majorana per Catterall arXiv:2311.02487 §4).
  - **Pati-Salam emergence theorem:** `theorem catterall_decoupling_yields_pati_salam` — under `H_CatterallMirrorDecoupling`, the light fermion content is exactly (4,2,1) ⊕ (4̄,1,2). Cross-bridge to `Wave2.NeutrinoMixing.PMNSMatrix` via the SU(2)_L doublet structure.
  - **PMNS-from-Pati-Salam theorem:** `theorem pmns_emerges_from_pati_salam_structure` — the PMNS rotation between flavor and mass eigenstates emerges from the SU(4) × SU(2)_L × SU(2)_R rotation between Pati-Salam basis and Standard Model basis.
  - **μ-τ symmetry from Pati-Salam:** `theorem pmns_mu_tau_symmetry_from_pati_salam_su4` — the substrate μ-τ symmetry hypothesis (`NeutrinoMixing.H_PMNSAnglesFromExactSubstrate` from Phase 5z W2) is inherited from the Pati-Salam SU(4) symmetry under specific decoupling assumptions. **This addresses the Phase 5z Wave 2a accuracy round's WAVE2-OPEN-2** (PMNS-from-substrate-symmetry derivation): Pati-Salam SU(4) is the substrate symmetry, μ-τ row equality follows from SU(4)-block structure.
  - **NuFit-6.0 quantitative anchor:** `theorem catterall_pati_salam_predicts_theta_23_near_45` — under exact Pati-Salam SU(4) (idealized limit), θ_23 = π/4 exactly; with the Wave 2a tolerance-parameterized form (`H_PMNSAnglesFromSubstrate_eps`), the empirical θ_23 = 49.1° is recovered for documented `ε ≈ 0.07`.
  - **Falsifiability:** `theorem pati_salam_falsified_if_theta_23_far_from_pi_4` — if NuFit data ever shifts to θ_23 ≪ 45° or θ_23 ≫ 60°, Pati-Salam-via-SMG is falsified.
- Target: **14–18 substantive theorems** (across both modules), 0 sorry, 0 new axioms

**Python side:**
- `src/majorana_rung/smg.py` extension — Pati-Salam predicted PMNS angles
- `src/neutrino_mixing/pati_salam.py` — Pati-Salam representation theory + PMNS rotation
- `src/core/formulas.py` additions: `pati_salam_pmns_prediction(decoupling_data)`, `theta_23_from_su4_block(epsilon)`
- `tests/test_pmns_pati_salam.py` — ~12 pytest

**Bridges:**
- Promotes Phase 5z W4
- Depends on Phase 6h W1 + W2
- Cross-bridges to Phase 5z W2 `NeutrinoMixing.lean` (PMNS structure note)
- Cross-bridges to Phase 5x `HiddenSectorClassification.lean` (Catterall-KD ↔ ℤ₁₆ at the Pati-Salam-decoupling level)

**Deliverables:**
- 2 Lean modules: promoted `MajoranaRungSMG.lean` + new `NeutrinoMixingSMG.lean`
- 14–18 theorems total
- Python `src/neutrino_mixing/pati_salam.py` + `src/majorana_rung/smg.py` extension
- ~12 pytest in `tests/test_pmns_pati_salam.py`
- Figure: `fig_pmns_pati_salam_prediction` — predicted vs NuFit-6.0 mixing angles with Pati-Salam-band overlay
- Paper: `papers/paper40_smg_pmns_majorana/paper_draft.tex` — "PMNS Mixing and Majorana Mass from Symmetric Mass Generation on the SK-EFT Substrate" (PRD format, target 6–8 pages)
- Inventory update: +14–18 theorems, +1 new Lean module + 1 promoted, +1 Python subpackage, +1 paper, +1 figure

**Estimated LOE:** **4–6 person-months**
**Risk:** Medium-high. The Pati-Salam-via-Catterall-mirror-decoupling bridge depends on the conjectural 4D mirror decoupling. Wave 3 ships under tracked-hypothesis `H_CatterallMirrorDecoupling`; if a future result proves or disproves 4D mirror decoupling, the wave's quantitative predictions land or fail accordingly.

**Correctness-push.** First formal-verification PMNS prediction from substrate symmetry. Closes (under tracked hypothesis) Phase 5z Wave 2's WAVE2-OPEN-2.

---

## Wave 4 — `LightFermionHierarchyFromSMG.lean` [6h.4] [Pipeline: Stages 1–8 + 10]

**Goal:** Predict the SM light-fermion mass hierarchy (12 orders of magnitude from m_e to m_t) from proximity-to-SMG-fixed-point physics. Hasenfratz-Witzel's merged UV-IR fixed point provides the structural mechanism: m_f / Λ_UV ~ exp(-distance(f, fixed-point)) with documented distance metric.

**Prerequisites:**
- Wave 1 + Wave 2 (Phase 6h) complete
- Wave 3 (Phase 6h) preferred but not strictly required

**Module structure:**
- `lean/SKEFTHawking/LightFermionHierarchyFromSMG.lean`
  - `structure FixedPointDistance` — distance from SM fermion f to the Hasenfratz-Witzel merged UV-IR fixed point in coupling-constant space; per-fermion measure `δ_f`
  - `def H_HierarchyFromFixedPointProximity (s : SubstrateCouplings) (δ : Fin n_fermions → ℝ) : Prop` — tracked hypothesis: SM fermion masses scale as `m_f / Λ_UV ~ exp(-δ_f / α_∗)` with `α_∗` the merged-fixed-point critical-exponent ratio.
  - **Hierarchy-from-distance theorem:** `theorem hierarchy_quantitative_from_fixed_point_distance` — under `H_HierarchyFromFixedPointProximity` with documented `δ_f` for each SM fermion, the predicted m_f's land within an order of magnitude of PDG values. Quantitative `norm_num` comparisons with PDG 2024.
  - **Top-as-natural theorem:** `theorem top_yukawa_natural_in_smg_window` — m_t ~ Λ_UV / strong_coupling_factor ≈ O(100 GeV) is the *natural* outcome when the top fermion sits near the SMG-window center (δ_t ≈ 0). Cross-bridge to Phase 5z Wave 1's correctness-push framing of m_H prediction.
  - **Electron-as-edge theorem:** `theorem electron_yukawa_from_smg_window_edge` — m_e ~ Λ_UV · exp(-δ_e / α_∗) ≈ O(0.5 MeV) for documented δ_e at the edge of the SMG window. Recovers Froggatt-Nielsen-like exponential suppression as a *consequence* of fixed-point proximity rather than as a fitted U(1)_FN charge.
  - **Quark-lepton asymmetry theorem:** `theorem quark_lepton_mass_asymmetry_from_pati_salam` — under Wave 3's Pati-Salam structure, the m_t/m_τ ≈ 100 ratio emerges from SU(4) breaking by SMG ordering. Cross-bridge to Wave 3.
  - **Falsifiability:** `theorem hierarchy_falsified_if_smg_window_inaccessible` — if Wave 1 returns no SMG window, this Wave 4 prediction is structurally falsified (cascade no-go from earlier waves).
- Target: **10–14 substantive theorems**, 0 sorry, 0 new axioms

**Python side:**
- `src/light_fermion_hierarchy/__init__.py`
- `src/light_fermion_hierarchy/fixed_point_distance.py` — δ_f computation per SM fermion under documented Hasenfratz-Witzel-style distance metric
- `src/light_fermion_hierarchy/yukawa_prediction.py` — predicted m_f from substrate parameters; comparison to PDG 2024
- `src/core/formulas.py` additions: `yukawa_from_fixed_point_proximity(delta_f, alpha_star, Lambda_UV)`
- `tests/test_light_fermion_hierarchy.py` — ~12 pytest covering hierarchy predictions for all 12 charged SM fermions

**Bridges:**
- Depends on Phase 6h W1 + W2 (preferred W3)
- Feeds Phase 6h W5 (chirality wall via SMG)
- Cross-bridges to Phase 5z W1 (`ScalarRungInterpretation`, m_H prediction) — top Yukawa is the load-bearing connection

**Deliverables:**
- Module zero-sorry, building clean
- 10–14 theorems
- Python `src/light_fermion_hierarchy/` (3 modules)
- ~12 pytest
- Figure: `fig_smg_hierarchy_prediction` — predicted vs PDG fermion masses on log-scale, with ±1σ Hasenfratz-Witzel-band overlay
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 figure

**Estimated LOE:** **3–5 person-months**
**Risk:** High. The distance metric `δ_f` is itself a structural postulate; if no documented Hasenfratz-Witzel-style metric reproduces the SM hierarchy, this wave fails to deliver quantitative content. Falls back to structural-only ("hierarchy from fixed-point proximity is qualitatively consistent").

**Correctness-push.** If the SM mass hierarchy emerges quantitatively from documented substrate parameters, this is a structural achievement comparable to grand unification. If the wave delivers only qualitative structure, that itself sets the floor for future quantitative work.

---

## Wave 5 — `SMGChiralityWall.lean` [6h.5] [Pipeline: Stages 1–8 + 10]

**Goal:** Bridge Phase 6h SMG mechanism to Phase 6c.2 (EW baryogenesis ↔ chirality wall). SMG provides the microscopic mechanism for chirality wall generation: the SMG-gapped mirror sector provides the chirality asymmetry that EW baryogenesis requires.

**Prerequisites:**
- Wave 1 + Wave 2 (Phase 6h) complete
- Phase 6c.2 stub (open in Phase 6c roadmap)
- Phase 5z Wave 3 `EWPhaseTransition.lean` (transition-order input)

**Module structure:**
- `lean/SKEFTHawking/SMGChiralityWall.lean`
  - `structure ChiralityWallFromSMG` — chirality wall as the SMG-mirror-decoupling boundary
  - `def H_SMGGeneratesChiralityWall (s : SubstrateCouplings) : Prop` — tracked hypothesis: SMG mirror decoupling produces a chirality wall with documented profile
  - **Wall-from-mirror-decoupling theorem:** `theorem chirality_wall_emerges_from_mirror_decoupling` — under `H_CatterallMirrorDecoupling` (Wave 3) + `H_SMGGeneratesChiralityWall`, an explicit chirality wall emerges in the substrate. Cross-bridge to Phase 6c.2's chirality wall predicate.
  - **EW baryogenesis bridge:** `theorem smg_chirality_wall_supplies_baryogenesis_input` — the SMG-generated chirality wall provides the chirality asymmetry that Phase 5z W3's first-order EW phase transition would need for baryogenesis. Closes (under tracked hypothesis) Phase 5z W3's `crossover_excludes_baryogenesis` exclusion theorem by routing baryogenesis through SMG-leptogenesis instead of EW-baryogenesis.
  - **Quantitative anchor:** `theorem smg_baryogenesis_compatible_with_observed_eta_b` — the predicted baryon asymmetry η_B from SMG-routed leptogenesis under documented substrate parameters lands in the observed band (η_B ≈ 6 × 10⁻¹⁰). `norm_num`-backed comparison with WMAP/Planck.
  - **Falsifiability:** `theorem smg_baryogenesis_falsified_if_no_mirror_decoupling` — if Wave 3's `H_CatterallMirrorDecoupling` falsifies (4D mirror decoupling proven impossible), this wave's baryogenesis route is structurally cut off.
- Target: **10–14 substantive theorems**, 0 sorry, 0 new axioms

**Python side:**
- `src/smg/chirality_wall.py` — chirality-wall profile + leptogenesis-asymmetry predictor
- `src/core/formulas.py` additions: `eta_baryon_from_smg_chirality_wall(substrate_params)`
- `tests/test_smg_chirality_wall.py` — ~10 pytest

**Bridges:**
- Depends on Phase 6h W1 + W2 (preferred W3)
- Closes Phase 6c W2 (EW baryogenesis ↔ chirality wall) — provides the microscopic chirality-wall mechanism
- Cross-bridges to Phase 5z W3 (`EWPhaseTransition.lean`) — reroutes baryogenesis around its crossover exclusion

**Deliverables:**
- Module zero-sorry, building clean
- 10–14 theorems
- Python `src/smg/chirality_wall.py`
- ~10 pytest
- Figure: `fig_smg_chirality_wall_eta_b` — predicted baryon asymmetry from SMG-leptogenesis vs observation
- Closes Phase 6c W2 (cross-roadmap update)
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python module, +1 figure

**Estimated LOE:** **4–6 person-months**
**Risk:** High. Closes a Phase 6c.2 stub that has been open since Phase 6c was opened; the leptogenesis-from-SMG mechanism is novel and not extensively explored in primary literature. Wave 5 may need to file its own deep-research task.

**Correctness-push.** Closes Phase 6c W2 and provides EW baryogenesis a microscopic mechanism that bypasses Phase 5z W3's SM-crossover exclusion. If validated, this unifies fermion mass generation, neutrino mass, and baryogenesis under a single substrate mechanism.

---

## Decision Gates

**Gate H.1 — before Wave 1 begins:** Phase 5z Wave 4 SHIPPED (Gate Z.4 of Phase 5z passed)? If NOT → Phase 6h does not activate; STOP.

**Gate H.2 — after Wave 1 (`SubstratePhaseDiagram`) ships:** Does the substrate's natural parameter range include an accessible SMG window? If YES → proceed to W2-W5. If NO → Phase 6h closes early as a strengthened Wave-1-only no-go ("substrate-mechanism SMG predicted but window inaccessible").

**Gate H.3 — after Wave 2 (`SymmetricMassGeneration`) ships:** Are the cross-bridges to Phase 5x ℤ₁₆ infrastructure clean (Catterall-KD ↔ Z16AnomalyComputation)? If YES → proceed to W3-W5. If NO → re-scope or file deep-research task on Catterall-Phase-5x bridge before W3.

**Gate H.4 — after Wave 3 (`MajoranaRungSMG` extension + PMNS) ships:** Is the Catterall mirror-decoupling-Pati-Salam bridge load-bearing (i.e., does the PMNS prediction depend on the conjectural 4D mirror decoupling)? Document explicitly. If 4D mirror decoupling is proven elsewhere during W3 execution → upgrade tracked hypothesis to theorem; if disproven → W3 retracts to structural-only.

**Gate H.5 — after Wave 4 (`LightFermionHierarchyFromSMG`) ships:** Does the substrate parameter map reproduce the SM hierarchy quantitatively (within an order of magnitude per fermion)? If YES → flagship paper. If NO → ship structural-only and flag hierarchy-derivation as continuing open question.

**Gate H.6 — after Wave 5 (`SMGChiralityWall`) ships:** Does the predicted η_B match observation (6 × 10⁻¹⁰)? If YES → close Phase 6c W2 (cross-roadmap update). If NO → ship structural-only and flag η_B-derivation as continuing open question; Phase 6c W2 remains open.

---

## Dependencies

```
Phase 6h.1 (SubstratePhaseDiagram) — depends on Phase 5z W2 + W4 + W1/1b
  ↓
Phase 6h.2 (SymmetricMassGeneration) — depends on 6h.1 + Phase 5x Z16 infrastructure
  ↓
Phase 6h.3 (MajoranaRungSMG promote + NeutrinoMixingSMG) — depends on 6h.1 + 6h.2 + Phase 5z W2 NeutrinoMixing
  ↓
Phase 6h.4 (LightFermionHierarchyFromSMG) — depends on 6h.1 + 6h.2 (preferred 6h.3)
  ↓
Phase 6h.5 (SMGChiralityWall) — depends on 6h.1 + 6h.2 (preferred 6h.3); closes Phase 6c W2

Parallelism:
  6h.1 then 6h.2 (serial)
  6h.3, 6h.4, 6h.5 can run in parallel after 6h.2
```

---

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| **Gate H.1** | Verify Phase 5z W4 shipped | — | Phase 5z W4 | **TRIGGER** |
| 6h.1 | `SubstratePhaseDiagram.lean` + Python phase classifier + figure | 3–5 | Phase 5z W2 + W4 + W1/1b | **TIER 0 — foundational** |
| 6h.2 | `SymmetricMassGeneration.lean` + Python SMG mechanism + figure | 3–4 | 6h.1 | **TIER 0 — mechanism** |
| 6h.3 | `MajoranaRungSMG.lean` (promoted) + `NeutrinoMixingSMG.lean` + paper 40 + figure | 4–6 | 6h.1 + 6h.2 + Phase 5z W2 NeutrinoMixing | **TIER 1 — flagship paper** |
| 6h.4 | `LightFermionHierarchyFromSMG.lean` + Python hierarchy + figure | 3–5 | 6h.1 + 6h.2 (preferred 6h.3) | **TIER 1 — hierarchy** |
| 6h.5 | `SMGChiralityWall.lean` + Python η_B predictor + figure; closes Phase 6c W2 | 4–6 | 6h.1 + 6h.2 (preferred 6h.3) | **TIER 1 — baryogenesis bridge** |

**Total Phase 6h LOE:** **17–26 person-months**. 6h.1 + 6h.2 serial (6–9 PM), then 6h.3 + 6h.4 + 6h.5 parallel: wall-clock 11–17 months minimum.

**Deliverables cumulative:**
- 5 new Lean modules (one promoted from Phase 5z W4): `SubstratePhaseDiagram`, `SymmetricMassGeneration`, `MajoranaRungSMG` (promoted), `NeutrinoMixingSMG`, `LightFermionHierarchyFromSMG`, `SMGChiralityWall`
- 5 new Python subpackages
- 1 flagship paper (Paper 40, PRD/Annals format) + 1 §-extension to Paper 21 (already shipped in Phase 5z W4) + 1 closure of Phase 6c W2
- 5 new figures
- ~60–80 new theorems; zero sorry target; zero new axioms target
- Closes Phase 6c W2 (EW baryogenesis ↔ chirality wall) — cross-roadmap update

---

## Open Questions

**O-6h.1 — LOAD-BEARING.** Does the ADW substrate (Vladimirov-Diakonov 4D simplicial action with 8 dimensionless couplings) admit an SMG window? Lattice MC required; deep-research task to be filed pre-Wave-1: `Lit-Search/Tasks/Phase6h_W1_substrate_smg_window.md`.

**O-6h.2 — LOAD-BEARING — RESOLVED 2026-04-27 (negative-tilt OPEN).** What is the analog of Hasenfratz-Witzel's Λ_D for the ADW substrate? **Verdict (deep research at `Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate Phase Diagram.md` §2):** no closed form exists in published literature. Project-internal NJL-scaling envelope is `c_SMG = Λ_SMG/Λ_UV ∈ [10⁻¹², 10⁻³]` (broad) or `[10⁻¹⁰, 10⁻⁴]` (seesaw-restricted, requires fine-tuning of (λ_i) of order 10–30%). Closure paths: see "Concrete activation criteria" near top of this roadmap — F-b-1 (lattice MC of V&D action), F-b-2 (bilocal-NJL Hill-style closed form), F-b-3 (large-N expansion). Phase 6h Wave 1 ships with the broad-band NJL envelope as the canonical anchor and a tracked hypothesis at the seesaw-restricted band.

**O-6h.3 — RESOLVED 2026-04-27 (NEGATIVE — conjectural in 4D).** Is 4D mirror decoupling (Catterall arXiv:2311.02487 §4) provable? **Verdict (deep research §3.2):** rigorous only in 2D via Fidkowski-Kitaev (PRB 81 134509, 2010); 4D version is explicitly conjectural in Catterall's own paper. No literature through April 2026 closes this gap. **Concrete positive-closure path (F-c-1) listed near top of roadmap.** Phase 6h Wave 3 ships `H_CatterallMirrorDecoupling` as a tracked hypothesis flagged conjectural; if F-c-1 publishes, the hypothesis promotes to a theorem.

**O-6h.4.** Distance metric `δ_f` for Wave 4 — what's the documented Hasenfratz-Witzel-style metric? May need its own deep-research task.

**O-6h.5.** Does SMG-leptogenesis admit a quantitative η_B prediction? Affects Wave 5. May need its own deep-research task.

---

## What Success Looks Like

**Per wave:**
- 6h.1: Substrate phase-diagram partition + SMG-window identification; cross-bridges to BCS-and-SMG branches of Phase 5z W2/W4
- 6h.2: SMG mechanism formalized with cross-bridges to Phase 5x ℤ₁₆ infrastructure; first formalization across all proof assistants
- 6h.3: PMNS prediction from substrate Pati-Salam structure; flagship paper 40
- 6h.4: SM mass hierarchy quantitatively from fixed-point proximity (within an order of magnitude per fermion) OR documented structural-only fallback
- 6h.5: Closes Phase 6c W2 with SMG-routed leptogenesis as the microscopic baryogenesis mechanism

**Cumulative:**
- 5 new Lean modules + 1 promoted, ~60–80 new theorems, zero sorry target
- 1 flagship paper + 1 §-extension + 1 cross-roadmap closure
- **Program-level value:** unifies fermion mass generation, neutrino mass, light-fermion hierarchy, Pati-Salam emergence, and EW baryogenesis under a single substrate mechanism. This is the program-level payoff that Phase 5z's Wave 2 BCS no-go opens up via the SMG alternative.

---

## Cross-References

**Prior phases this extends / harvests from:**
- Phase 3/5d (TetradGapEquation, ADWMechanism) — substrate gap-equation infrastructure
- Phase 5x Wave 2 (Hidden-Sector Classification) — ℤ₁₆ singlet branch; Catterall-KD cross-bridge target
- Phase 5z Wave 2 + Wave 4 (MajoranaRung, MajoranaRungSMG) — structural foundation
- Phase 5z Wave 1/1b (ScalarRungInterpretation, BHLGaugeEmbedding) — Fierz-complete substrate-channel infrastructure
- Phase 5z Wave 3 (EWPhaseTransition) — first-order/crossover transition input to baryogenesis chain

**Parallel phases (unaffected by Phase 6h activation):**
- Phase 5w, 5y, 6a (linearized gravity), 6b (cosmological perturbations), 6f (classical-GR Lean infrastructure) — independent
- Phase 5x dark-matter waves — Phase 6h adds an SMG mechanism layer but does not modify dark-matter classification

**Downstream phases this feeds:**
- Phase 6c W2 (EW baryogenesis ↔ chirality wall) — Phase 6h Wave 5 closes this stub
- Phase 6e (nonlinear gravity) — Phase 6h does NOT directly feed; substrate-mechanism scope is fermion-mass-generation, gravity-side is 6e territory

**Source documents:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) — overarching program scope
- `Lit-Search/Phase-5z/Phase 5z Wave 2a — Majorana-Channel Projection of the Tetrad Gap Equation.md` (2026-04-25) — BCS no-go that motivated SMG pivot
- `Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` (2026-04-16) — Hasenfratz-Witzel + Razamat-Tong + Catterall context

**Correctness-push highlights from strategy doc §12 (cumulative through Phase 6h):**
- 6h.1: SMG window identification (substrate phase diagram)
- 6h.4: SM hierarchy quantitatively from fixed-point proximity
- 6h.5: η_B from SMG-leptogenesis closes Phase 6c W2 baryogenesis stub

---

*Phase 6h roadmap. Prepared 2026-04-27 conditional on Phase 5z Wave 4 positive close (Gate Z.4 of Phase 5z). Five waves: substrate phase diagram (6h.1), SMG mechanism (6h.2), MajoranaRungSMG promotion + PMNS via Catterall-Pati-Salam (6h.3), light-fermion hierarchy from fixed-point proximity (6h.4), SMG-instantiated chirality wall closing Phase 6c W2 (6h.5). Five correctness-push anchors. One flagship paper. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 17–26. **Activation gate: Phase 5z Wave 4 must ship positively first.** If Phase 5z Wave 4 ships negatively (second no-go), Phase 6h does not activate; substrate-bridge derivation closes as impossible-in-current-substrate-models.*
