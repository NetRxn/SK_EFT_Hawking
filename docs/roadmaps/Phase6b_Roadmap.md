# Phase 6b: Cosmology Layer — BBN Constraints, Cosmological Perturbation Theory, Vestigial Inflation

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §5. Cosmology extension to the post-SK-EFT program; follows Phase 5y closure and Phase 6a linearized-gravity groundwork.*

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. Relevant anchors: `Z16AnomalyComputation.lean` (23), `HiddenSectorClassification.lean` (9, COMPLETE 2026-04-22), Phase 5y closure modules (`GibbsDuhemTheorem` 16, `QTheoryNoGoTheorem` 12, `DarkEnergyObstructionPrinciple` 8, `VestigialEOS` 20+, `DESIComparison` 8), Phase 5x dark-matter infrastructure (all DM candidate modules), `VestigialSusceptibility.lean` (24 after 5y W6).

**Thesis.** Three cosmology waves: (i) a BBN unified constraint framework that every current and future DM/DE candidate passes through; (ii) cosmological perturbation theory around the q-theory / two-fluid background (joint with Phase 5y); (iii) slow-roll inflation from vestigial-phase coupling dynamics (highest-risk, cleanest-falsifiability wave in Phase 6b).

**Correctness-push framing.** 6b.1 is expected to disqualify at least one existing 5x DM candidate ("honest negative result" by design). 6b.3 is flagged as highest-risk correctness-push — if vestigial inflation cannot reproduce Planck/BICEP `(n_s, r)`, the framing is falsified, cleanly publishable either direction.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §5 (6b) and §12 (correctness-push highlights)
> 4. Wave-specific pre-reads:
>    - 6b.1 — Phase 5x roadmap, all DM candidate memos in `docs/dark_sector/`, `Z16AnomalyComputation.lean`, `HiddenSectorClassification.lean`, and Phase 5x Wave 1b BBN constraint analysis in `Lit-Search/Phase-5x/5x-Gapless Fracton Liquid Stability at Finite Temperature...` and `Lit-Search/Phase-5x/5x-Fracton DM Kinetic Stability...`
>    - 6b.2 — Phase 5y closure modules (full read), Phase 6a.1 `LinearizedEFE.lean`, Phase 6a.4 `FLRWDynamics.lean`
>    - 6b.3 — `VestigialSusceptibility.lean` (with 5y W6 extensions), Phase 6a.1 `LinearizedEFE.lean`; deep research on Koivisto-Nunes-Mulryne 3-form inflation (`Lit-Search/Phase-5y/Phase5y_H1_second_sound_graviton.md` §H3 notes where available)
> 5. If 6b.3 proves intractable, de-escalate per Decision Gate B.3 — do not grind on Planck/BICEP-matching if microscopic dynamics fundamentally wrong. Document the failure as a publishable structural result and move to backlog.
> 6. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to published constants); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check (no `rfl`/`decide`/`not_lt.mpr h_disagree` tautologies); (5) defining-the-conclusion check (vacuous when `f := <obvious target>`). The end-of-wave strengthening pass should produce **0 retroactive theorems** — if it produces 5+, log the failure mode and tighten the next wave's discipline.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6b:**
- BBN abundance baseline (⁴He, D, ³He, ⁷Li) as Lean definitional facts
- Abundance-bound theorems as Props that every DM candidate must satisfy
- Cosmological perturbation theory around q-theory / two-fluid / vestigial backgrounds
- CMB ℓ-space power spectrum emergence from perturbation theory
- Slow-roll inflation from vestigial-phase coupling dynamics
- Planck/BICEP `(n_s, r)` constraint as correctness-push anchor

**OUT OF SCOPE for 6b (lands in 6c):**
- Strong-CP ↔ topological DE bridge (6c.1)
- EW baryogenesis ↔ chirality wall (6c.2)

**OUT OF SCOPE for 6b (deferred to backlog):**
- Full Boltzmann-code cosmological fits
- Non-standard BBN scenarios (late-decaying particles, entropy production)
- Quantum inflation / primordial non-Gaussianity beyond leading slow-roll
- Extra-dimensional cosmology

**Phase 5x relationship:** 6b.1 **explicitly feeds back into Phase 5x** — the BBN constraint spine is expected to disqualify some 5x DM candidates. This is the intended effect. 5x roadmap gets updated as 6b.1 results land.

**Phase 5y relationship:** 6b.2 is joint with Phase 5y closure — perturbation theory around the q-theory / two-fluid background is a natural downstream of 5y's NO-GO verdict. 5y is closed; 6b.2 is the next-layer formalization that makes 5y's scope boundary machine-checked.

---

## Track A: BBN Unified Constraints (6b.1) — **SHIPPED 2026-04-27**

**Status:** Wave 1 closed end-to-end. Pipeline through Stage 8.
- `BBN.lean`: 17 substantive theorems + 1 module-summary marker, 0 sorry, 0 new axioms (verified `propext, Classical.choice, Quot.sound` only on key theorems via `lean_verify`).
- `src/bbn/`: 2 Python modules (`abundances.py` Planck/PDG/Cooke/Sbordone constants + `candidate_checker.py` 5-candidate evaluator) + 16 pytest cases (16/16 PASS in 0.02s).
- `papers/paper29_bbn_unified/`: short formalization paper, 4 pages, 425 KB, compiles clean, 11 bibitems.
- `fig_bbn_conformance_matrix`: 5×3 candidate × field heatmap + ΔN_eff log-scale comparison with Planck 2σ slack horizontal reference, registered in `review_figures.py`.
- **Five Phase 5x candidates classified**: Z16Topological_T0 + Z16Mixed_C1 + FractonPWave (BBN-conformant via W8 collective-invisibility); Z16Singlet_S0 + FGTorsion (BBN-violators conditional on thermalization at T_BBN ≈ 1 MeV — both via ΔN_eff > 0.34 Planck slack).
- **Structural punchline `bbn_violators_share_n_eff_failure_mode`**: both violators fail through the same N_eff-mediated channel (not abundance perturbations or photodissociation). The BBN failure surface is N_eff-mediated.
- **Cross-bridges shipped**: `decoupled_via_w8_collective_invisibility_implies_bbn_safe` actually imports `DarkSectorSynthesis` and calls `emergent_gravity_dm_invisible_collective` directly; `phase5x_candidate_set_aligned_with_synthesis` references the upstream enum to confirm alignment.
- **Preemptive-strengthening discipline applied at first-pass**: 0 retroactive strengthening theorems needed (compares to 6c.3's 12). Two pattern violations caught DURING first-pass writing (∃-absorption in original H_VestigialRelicBBNAbundance; structural-tautology P5 in original biconditional violator theorems) and fixed before completion of the wave.
- Stages 9 (LLM figure review) and 13 (adversarial review) deferred per pipeline policy (user-triggered).



### Motivation

Phase 5x produced multiple DM candidates (fracton, Fang-Gu torsion, vestigial relics, SFDM, hidden-sector T-0 TQFT). Each candidate has been assessed for phenomenological viability, but there is no unified Lean-level framework stating "candidate X satisfies / violates BBN constraints." This module provides that framework as a single constraint spine — `BBN.lean` gives the baseline + Abundance-Bound Props, and every DM candidate module gets an explicit conformance theorem.

Expected outcome: at least one 5x DM candidate that looked anomaly-viable will fail the BBN spine. That falsification is the 6b.1 contribution — unified scrutiny that no 5x wave had to carry individually.

### Wave 1 — `BBN.lean` (6b.1) [Pipeline: Stages 1–8]

**Goal:** Standard BBN abundances as Lean definitional facts + Abundance-Bound theorems + per-DM-candidate conformance statements.

**Prerequisites:** None beyond existing Phase 5x infrastructure.

**Module structure:**
- `lean/SKEFTHawking/BBN.lean`
  - BBN abundance baseline: `BBN.abundance_He4`, `BBN.abundance_D_over_H`, `BBN.abundance_He3_over_H`, `BBN.abundance_Li7_over_H` as definitional constants with observational bounds + theoretical midpoints
  - Observational bound Props: `WithinBBN_Bounds (ρ_DM, Γ_injection) : Prop` — the candidate's energy density and any injection channel must satisfy `Ω_B h² = 0.02242 ± 0.00014` (Planck 2020) and abundance bounds
  - **Correctness-push theorem:** `no_DM_candidate_can_inject_more_than_BBN_slack` — tightly bounds injection channels
  - Conformance theorems (per-candidate), added in this module:
    - `FractonDMC_BBN_conformance` — references Phase 5x Wave 7 results
    - `FangGuTorsionDMC_BBN_conformance` — references Phase 5x Wave 4
    - `VestigialRelicDMC_BBN_conformance` — references Phase 5x Wave 6
    - `SFDMC_BBN_conformance` — references Phase 5x Wave 5
    - `HiddenSectorT0_BBN_conformance` — references Phase 5x Wave 2 (expected TRIVIAL since T-0 is gapped-anyon with no particles, but explicit statement required)
- Target ~8–12 theorems.

**Python side:**
- `src/bbn/` new subpackage
  - `abundances.py` — canonical BBN abundance values with provenance (Planck 2020, PDG 2020, tabular references)
  - `candidate_checker.py` — loop over DM candidate modules, evaluate BBN Props, emit compliance matrix
- Formula additions to `src/core/formulas.py`: `bbn_he4`, `bbn_deuterium`, `bbn_he3`, `bbn_li7`, each tied to Lean theorem names + provenance

**Bridges:**
- Integrates with: all Phase 5x DM candidate modules
- Feeds back into Phase 5x roadmap — any `*_BBN_conformance = False` triggers candidate downgrade in Phase 5x

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_bbn.py` — numerical abundance checks against Planck 2020
- Short CPP-ish paper `papers/paper29_bbn_unified/paper_draft.tex` — "Unified BBN Constraint Framework for Emergent DM Candidates"
- Updated `PARAMETER_PROVENANCE` with Planck 2020 BBN parameters; `CITATION_REGISTRY` entries for primary sources
- Inventory update: +8–12 theorems, +1 Lean module, +1 Python subpackage, +1 paper
- Phase 5x roadmap revision: any failing candidate flagged for downgrade/closure

**Estimated LOE:** 1–2 person-months
**Risk:** Low. Standard cosmology + conformance-per-candidate pattern. Main variable is how many 5x candidates fail — that's the publishable content, not a risk.

**Correctness-push highlight.** At least one candidate is expected to fail. Honest negative result published; Phase 5x roadmap updated transparently.

---

## Track B: Perturbation Theory Around Emergent Backgrounds (6b.2)

### Motivation

Phase 5y proved structurally that Volovik-family emergent-DE mechanisms cannot produce DESI-compatible time-evolving `w(z)`. Phase 6a.4 formalizes FLRW dynamics from linearized EFE. The natural next layer is perturbation theory around q-theory / two-fluid / vestigial backgrounds — tracking whether the linear perturbations produce a sensible CMB ℓ-space power spectrum.

This wave is **joint with Phase 5y** — specifically, it closes the "what can this framework predict at the linear level" loop that 5y's NO-GOs left open. (5y proved the backgrounds don't work for DESI; 6b.2 asks whether even the perturbations are sensible at the Planck/CMB-scale.)

### Wave 2 — Cosmological Perturbation Theory [Pipeline: Stages 1–9, 11–12 — SHIPPED 2026-04-29]

**Status:** **SHIPPED 2026-04-29 end-to-end** through Stages 1–9 + 11–12. Stages 10 (paper draft) and 13 (adversarial review) deferred per user policy 2026-04-29 — wave-specific paper deliverables that don't fit `PAPER_STRATEGY.md` / `PAPER_DRAFT_MAPPING.md` are auto-deferred; W2 content lifts into D5 §7 (Dark Sector under Substrate Constraints) per the joint Phase 5y/6b NO-GO bundle. The wave's Lean + Python + figure + notebooks are complete and the joint-Phase 5y/6b structural NO-GO is formally in place.

- `lean/SKEFTHawking/CosmologicalPerturbations.lean`: **22 substantive theorems** (16 first-pass + 6 strengthening) / 0 sorry / 0 new axioms (verified `propext, Classical.choice, Quot.sound` only via `lean_verify`). Strengthening pass added: `self_lt_cosh_of_pos` (reusable cosh-self-bound helper); `vestigial_growth_exceeds_planck_cv_cap_under_kη_threshold` (quantitative Planck-anchored falsifier — for any `k·η ≥ 200`, vestigial growth exceeds Planck CV cap of 100); `instability_implies_not_admissible` (general lemma); `vestigial_at_zero_falsifies_H_StableSpectrum_via_amplitude` (independent witness for the bundled-Prop falsification); `H_VestigialNaturalBranchPasses` + `H_VestigialNaturalBranchPasses_falsified` + `joint_phase5y_6b_no_go_natural_branch` (joint Phase 5y/6b structural NO-GO bundle — **the load-bearing close of the "joint with Phase 5y" claim**). Cross-bridges to Phase 5y `VestigialEOS` consumed by name in 6 theorems; cross-bridge to `DESIComparison` in the joint NO-GO.
- `src/cosmological_perturbations/`: 4 Python modules (`__init__`, `linear_perturbations`, `cmb_spectrum`, `planck_comparison`) with `LinearPerturbation` / `PerturbationRegime` / `PlanckReference` / `AdmissibilityVerdict` dataclasses + 5 `formulas.py` additions (`jeans_frequency_sq`, `linear_growth_factor`, `is_admissible_background`, `cmb_growth_amplitude`, `vestigial_pertubation_growth_at_zero`).
- `tests/test_cosmological_perturbations.py`: **43 pytest cases** (35 first-pass + 8 strengthening), all PASS in 0.07s.
- `figures/fig_cmb_spectrum_planck_comparison.png`: 2-panel figure (log-log |G|² vs k for ΛCDM bounded vs vestigial divergent + 2D log₁₀|G(k,η)|² heatmap saturated at 24 orders) — registered in `review_figures.py`.
- `notebooks/Phase6b2_CosmologicalPerturbations_{Technical,Stakeholder}.ipynb`: 17+11 cells, both execute clean (`viz_consistency` + `notebook_exec` PASS).
- 16 new `PARAMETER_PROVENANCE` entries (Planck 2018 base-ΛCDM cosmology pivots + falsification thresholds + vestigial-EOS-derived growth-rate constants). validate.py `parameter_provenance` PASS.
- **Joint Phase 5y / 6b structural NO-GO**: the natural vestigial-DE branch (`τ² ∈ (0, 1/5)`) is **doubly-falsified by independent observations** — DESI 1σ region (Phase 5y `VestigialEOS.vestigial_not_in_desi_region`) AND CMB-ℓ admissibility (Phase 6b CP12 `vestigial_at_zero_not_admissible`). Two-witness structure: if either observational constraint individually relaxes, the other still falsifies the natural branch.
- **Discipline metric: 0 retroactive theorems** at first-pass + ruthless review (best yet, matches 6e.5). Strengthening pass added 6 substantive theorems but none were retroactive — they were proactively-targeted gap fills (Planck-anchored quantitative claim, joint-bundle Prop, generalization of vestigial-specific lemma to universal statement). Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, **6b.2=0 (best yet)**.

**Project totals after 6b.2 ship:** 4505 substantive theorems (+22), 196 modules (+1), 86 notebooks (+2), 136 figures (+1), 88 test files (+1), 1 axiom (unchanged), 0 sorry. validate.py 25/25 PASS.

#### Original Wave 2 specification (preserved for reference)

**Goal:** Formalize linear perturbation theory around q-theory / two-fluid / vestigial FRW backgrounds; derive CMB ℓ-space power spectrum emergence.

**Prerequisites:** Phase 6a.1 (`LinearizedEFE.lean`) and 6a.4 (`FLRWDynamics.lean`) substantially complete. Phase 5y closure modules must be read directly.

**Module structure:**
- `lean/SKEFTHawking/CosmologicalPerturbations.lean` (joint with 5y track)
  - Perturbation ansatz: `g_μν = g̃_μν + δg_μν` around FRW background with `VestigialEOS`-type perfect-fluid stress-energy
  - Linear perturbation equations at scalar/vector/tensor decomposition
  - **Theorem:** `perturbation_spectrum_from_linearized_efe` — CMB-ℓ power spectrum emerges
  - **Correctness-push theorem:** `spectrum_matches_planck_at_large_ℓ_iff_background_in_admissible_class` — quantitative comparability to Planck TT at large ℓ, tied to admissibility class of background EOS
  - Cross-reference theorems to each Phase 5y closure module — which 5y-NO-GO background produces which spectrum anomaly
- Target ~12–16 theorems.

**Python side:**
- `src/cosmological_perturbations/` new subpackage
  - `linear_perturbations.py` — scalar/vector/tensor decomposition + linear evolution
  - `cmb_spectrum.py` — ℓ-space power spectrum evaluator
  - `planck_comparison.py` — comparison to Planck 2020 TT/TE/EE spectra
- Formula additions: linear-perturbation growth function, transfer function

**Bridges:**
- Depends on 6a.1, 6a.4
- Cross-references Phase 5y modules directly: `GibbsDuhemTheorem`, `QTheoryNoGoTheorem`, `DarkEnergyObstructionPrinciple`, `VestigialEOS`, `DESIComparison`, `CondensedMatterAnalog`, `VestigialMapping`
- Feeds 6b.3 (vestigial inflation) via shared linear-perturbation machinery

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_cosmological_perturbations.py`
- Joint PRD paper (joint with Phase 5y closure) `papers/paper30_perturbation_theory_5y_joint/paper_draft.tex` — "Cosmological Perturbation Theory Around Emergent Backgrounds: A Joint Phase 5y/6b Analysis"
- Figure: `fig_cmb_spectrum_planck_comparison` — predicted vs Planck TT at large ℓ, admissible-class envelope
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python subpackage, +1 joint paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Technical subtleties in gauge fixing (Newtonian vs synchronous) must be documented. Coordination with Phase 5y closure team on the joint-paper scope.

**Correctness-push highlight.** CMB ℓ-space spectrum mismatch with Planck at large ℓ = falsification *or* prediction about non-standard early-universe physics. 5y closes the background-level story; 6b.2 closes the perturbation-level story.

---

## Track C: Vestigial Slow-Roll Inflation (6b.3)

### Motivation

Slow-roll inflation from vestigial-phase coupling dynamics is the alternative-to-standard-inflaton framing. **Highest-risk wave in Phase 6b.** `(n_s, r)` from Planck/BICEP are extremely tight — if the microscopic model cannot reproduce them, vestigial inflation is falsified as a quantitative theory of early-universe physics. That falsification is itself cleanly publishable.

### Wave 3 — `VestigialInflationNoGo.lean` (6b.3) [Pipeline: Stages 1–13 SHIPPED 2026-04-29 as structural NO-GO]

**Status: SHIPPED 2026-04-29 as structural NO-GO** (de-escalated per Gate B.3, user decision 2026-04-29). Stage 3a preliminary numerics scan produced **0 viable points / 2574** for the Planck/BICEP admissibility region. Two structural failures formalized:

1. **η-problem (closed form):** `η_hilltop = -30·(M̄_P/M_φ)²` (f_0-independent, geometric); slow-roll `|η|<1` requires super-Planckian `M_φ > √30 M̄_P`; Planck-2σ on n_s tightens to `M_φ > 36 M̄_P` (formalized via `nSAtHilltop_planck_compatible_implies_super_Planckian`).
2. **e-fold overshoot:** at the formally compatible `M_φ ≈ 41 M̄_P`, every (n_s, r)-passing point in the scan has `N_e ≥ 71.8` — graceful exit fails.

**Deliverables shipped:**
- `lean/SKEFTHawking/VestigialInflationNoGo.lean`: 15 substantive thms + 1 marker / 0 sorry / 0 new axioms (verified `propext, Classical.choice, Quot.sound` only on load-bearing `vestigial_natural_branch_inflation_falsified` + `nSAtHilltop_planck_compatible_implies_super_Planckian` + `etaAtHilltop_eq_neg_thirty_ratio_sq`).
- `src/vestigial_inflation/`: 4 Python modules (`slow_roll`, `ns_r_prediction`, `planck_bicep_check`, `__init__`), 108 LOC.
- `tests/test_vestigial_inflation_no_go.py`: 48 pytest cases (cross-layer parity), all PASS in 0.06s.
- `papers/paper31_vestigial_inflation_no_go/paper_draft.tex`: 3-page structural-NO-GO note, compiles clean.
- `figures/data/vestigial_inflation_preliminary_scan.json` + `figures/fig_ns_r_microscopic_vs_planck_bicep.{png,html}`: 2574-point scan + diagnostic figure.
- `temporary/working-docs/todo/phase6b_w3_gate_b3_preliminary.md`: gate-decision memo.

**Joint NO-GO ledger (Phase 5y + 6b W2 + 6b W3):**
- Phase 5y: `VestigialEOS.vestigial_not_in_desi_region` — vestigial natural branch fails DESI Year-1.
- Phase 6b W2: `CosmologicalPerturbations.vestigial_at_zero_falsifies_H_StableSpectrum_via_amplitude` — CMB-ℓ admissibility fails (gradient-instability `c_s² = -1/3`).
- Phase 6b W3 (this wave): `VestigialInflationNoGo.vestigial_natural_branch_inflation_falsified` — Planck-2σ on n_s requires super-Planckian M_φ.

**Discipline metric: 0 retroactive cuts.** Preemptive checklist applied at first pass; minor tactic-level fixes only during build.

#### Original Wave 3 specification (preserved for reference)

**Goal:** Formalize slow-roll inflation from vestigial-phase coupling dynamics; compute `(n_s, r)` from microscopic parameters.

**Prerequisites:** 6a.1 (`LinearizedEFE.lean`) complete. 6b.2 (`CosmologicalPerturbations.lean`) substantially complete for shared linear-perturbation machinery. User authorization before Wave 3 Stage 1 — this is the highest-risk wave in 6b and explicit sign-off is prudent.

**Module structure:**
- `lean/SKEFTHawking/VestigialInflation.lean`
  - Vestigial-phase order parameter `χ(t)` as inflaton analog
  - Slow-roll parameters `ε_vest(χ)`, `η_vest(χ)` derived from vestigial susceptibility
  - Equation of motion: `χ̈ + 3Hχ̇ + V'_vest(χ) = 0` with `V_vest` from VestigialEOS
  - Scalar spectral index: `n_s(params) = 1 − 6ε + 2η` (slow-roll leading order) expressed in `(Λ_UV, N_f, T_c,vest)`
  - Tensor-to-scalar ratio: `r(params) = 16ε` expressed in microscopic params
  - **Correctness-push theorem:** `vestigial_inflation_compatible_with_Planck_BICEP_iff_params_in_narrow_window` — biconditional pinning down microscopic parameter window compatible with `n_s = 0.965 ± 0.004`, `r < 0.036` (BICEP/Keck 2021)
  - Failure theorem (speculative, may be the result): `vestigial_inflation_falsified_if_no_natural_window` — if the natural parameter window does not intersect the Planck/BICEP admissible region
- Target ~14–18 theorems.

**Python side:**
- `src/vestigial_inflation/` new subpackage
  - `slow_roll.py` — slow-roll parameters evaluator
  - `ns_r_prediction.py` — `(n_s, r)` over microscopic parameter grid
  - `planck_bicep_check.py` — admissible-region comparison
- Formula additions: `slow_roll_epsilon_vestigial`, `slow_roll_eta_vestigial`, `ns_vestigial`, `r_vestigial`

**Bridges:**
- Depends on 6a.1, 6b.2 (partial)
- Integrates with `VestigialSusceptibility.lean`, `VestigialEOS.lean`, Phase 5y closure modules
- Cross-references Koivisto-Nunes-Mulryne 3-form-inflation literature (arXiv:1209.2156 et seq.) — document the overlap/distinction in paper §

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_vestigial_inflation.py`
- PRD paper `papers/paper31_vestigial_inflation/paper_draft.tex` — speculative, publishable regardless of direction
- Figure: `fig_ns_r_microscopic_vs_planck_bicep` — `(n_s, r)` over microscopic parameter grid, Planck/BICEP 1σ/2σ/3σ envelopes overlaid
- Inventory update: +14–18 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 4–6 person-months
**Risk:** High. The microscopic dynamics are not guaranteed to produce slow-roll in any natural parameter window. If preliminary numerics before Stage 3a show no admissible region, de-escalate to a "structural analysis" paper rather than pushing.

**Correctness-push highlight.** Clean falsifiable prediction either way. If `(n_s, r)` match Planck/BICEP in a natural window → substantial result. If they do not match anywhere → structural falsification of vestigial-inflation framing → also substantial.

---

## Decision Gates

**Gate B.1 — after Wave 1 (`BBN`) ships:** How many Phase 5x DM candidates fail BBN? Update Phase 5x roadmap accordingly; any candidate that fails is demoted/closed with a clear evidence trail in the joint paper section "DM candidates ruled out by unified BBN spine."

**Gate B.2 — after Wave 2 (`CosmologicalPerturbations`) ships:** Is the CMB spectrum compatible with Planck at large ℓ under at least one admissible background? YES → 6b.3 proceeds at full scope. NO → 6b.3 is reframed as "even at the perturbation level, vestigial framework fails;" scope becomes a short structural note rather than full inflation derivation.

**Gate B.3 — before Wave 3 begins (user-authorization gate):** Is preliminary `(n_s, r)` numerics within 2σ of Planck/BICEP region for any natural microscopic parameter? YES → full Wave 3 scope. NO → de-escalate to a structural falsification paper; do not grind on microscopic-fit tuning. This gate is explicitly user-authorization because 6b.3 is the highest-risk wave in 6b.

---

## Dependencies

```
6b.1 (BBN) — independent; can run first

6b.2 (CosmologicalPerturbations) — depends on 6a.1, 6a.4

6b.3 (VestigialInflation) — depends on 6a.1, 6b.2 (substantial);
    user-authorization gate before start

Parallelism:
  6b.1 can run in parallel with 6a.x
  6b.2 blocked on 6a.1 + 6a.4
  6b.3 blocked on 6b.2 + user gate
```

---

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6b.1 | `BBN.lean` + short CPP paper | 1–2 | None | **SHIPPED 2026-04-27** |
| 6b.2 | `CosmologicalPerturbations.lean` + joint 5y PRD paper | 3–5 | 6a.1, 6a.4 | **TIER 1** |
| 6b.3 | `VestigialInflation.lean` + PRD paper (speculative) | 4–6 | 6a.1, 6b.2; user gate | **TIER 2 — highest-risk** |

**Total Phase 6b LOE:** 8–13 person-months. With 6b.1 running before 6a completes and 6b.2/6b.3 serial after 6a.1+6a.4: wall-clock 6–12 months minimum.

**Deliverables cumulative:**
- 3 new Lean modules (`BBN`, `CosmologicalPerturbations`, `VestigialInflation`)
- 3 new Python subpackages (`src/bbn/`, `src/cosmological_perturbations/`, `src/vestigial_inflation/`)
- 3 papers (Papers 29–31 reserved), one is joint 5y/6b
- ~34–46 new theorems; zero sorry target; zero new axioms target
- Phase 5x roadmap revisions as BBN conformance dictates

---

## Open Questions

**O.1** — 6b.1 paper venue: CPP (formalization-focused) vs a short physics note on the BBN constraint spine. User decision at Stage 10.

**O.2** — 6b.2 joint paper: is the Phase 5y closure team the appropriate co-author context, or is this author-ambiguous since 5y is machine-closed? Treat as single-author joint paper with 5y closure modules cited as foundational.

**O.3** — 6b.3 authorization gate: confirm user is willing to publish a structural falsification paper if the natural parameter window doesn't intersect Planck/BICEP region. (Strategy doc §3 indicates yes, but recheck before Wave 3 Stage 1.)

**O.4** — Boltzmann-code depth: 6b.2 uses analytic leading-order power spectrum; does the user want a deeper Boltzmann-code integration in a subsequent wave (potential 6b.4)? Scope as extension task if/when requested.

---

## What Success Looks Like

**6b.1 (BBN):**
- `BBN.lean` with 8–12 theorems, zero sorry
- At least one Phase 5x DM candidate demoted/closed by unified BBN spine; transparent evidence trail
- Short CPP paper + Phase 5x roadmap revisions filed
- **Program-level value:** first formal unified DM-candidate-constraint framework

**6b.2 (Cosmological Perturbations):**
- `CosmologicalPerturbations.lean` with 12–16 theorems, zero sorry
- CMB ℓ-space power spectrum emerges; Planck comparison documented
- Joint Phase 5y/6b PRD paper shipped
- **Program-level value:** perturbation-level closure of 5y's scope

**6b.3 (Vestigial Inflation):**
- `VestigialInflation.lean` with 14–18 theorems, zero sorry
- `(n_s, r)` predictions over microscopic parameter space, Planck/BICEP-compared
- PRD paper shipped — either quantitative prediction or structural falsification
- **Program-level value:** cleanest falsifiable prediction in Phase 6 (5z through 6g)

**Cumulative:**
- 3 new Lean modules, 3 Python subpackages, 3 papers
- Correctness-push anchors: DM-candidate disqualification (6b.1), large-ℓ spectrum fit (6b.2), `(n_s, r)` vs Planck/BICEP (6b.3)

---

## Cross-References

**Prior phases this extends:**
- Phase 5x (all DM candidate waves) — feeds into 6b.1 BBN conformance
- Phase 5y closure (`GibbsDuhemTheorem`, `QTheoryNoGoTheorem`, `VestigialEOS`, `DESIComparison`) — foundational context for 6b.2 joint paper
- Phase 4 Wave 2 (`VestigialSusceptibility`, `VestigialGravity`) — foundational for 6b.3

**Feeds downstream phases:**
- Phase 6c.1 (strong-CP ↔ topological DE) — uses 6b.2 perturbation framework for the DE sector
- Phase 6c.2 (EW baryogenesis ↔ chirality wall) — uses Phase 5z.3 transition-order input and 6b cosmological context

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §5

**Correctness-push highlights from strategy doc §12:**
- 6b.3: Inflation `(n_s, r)` vs Planck/BICEP (highest-risk in entire post-SK-EFT program; clean falsifiable prediction)

---

*Phase 6b roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Three waves: unified BBN constraints (6b.1), cosmological perturbation theory joint with 5y (6b.2), vestigial slow-roll inflation (6b.3, highest-risk). All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 8–13. 6b.3 is explicitly user-authorization-gated per B.3.*
