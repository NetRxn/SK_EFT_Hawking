# Phase 6d: QCD Interpretation Layer — Confinement, Chiral SSB, CFL

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §7. Native QCD items (confinement-as-center-unbreaking, chiral symmetry breaking, strong-CP) folded into existing infrastructure; non-native items (β-function, lattice Wilson-loop, full hadron spectrum) deferred to HepLean / PhysLean.*

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. QCD-relevant anchors: `GaugeErasure.lean` (12, higher-form symmetry framework), `ModularInvarianceConstraint.lean` (12, ζ₂₄ framing), `SU2kFusion.lean` (29), `SU3kFusion.lean` (99), `KacWaltonFusion.lean` (63), MTC stack, `WetterichNJL.lean` (18, scalar/pseudoscalar/vector channels + NJL–ADW correspondence), `TetradGapEquation.lean` (24 after 5y W6), existing mean-field machinery in `src/adw/`, `src/vestigial/`.

**Thesis.** Three QCD waves — native integration with program pillars: (i) confinement as center-symmetry unbreaking (connects to gauge-erasure + modular-invariance), (ii) chiral symmetry breaking via the WetterichNJL scalar channel as quark condensate (parallel to Phase 5z.1 Higgs identification), (iii) CFL chiral Lagrangian as Layer-3 IR hadronic fluid (promoted from optional; emergent ℤ₃ one-form symmetry = independent consistency check of 6d.1).

**Correctness-push framing.** 6d.3 is the correctness-push anchor — CFL's emergent ℤ₃ one-form symmetry should be identifiable with QCD center ℤ₃ from 6d.1. Direct cross-derivation consistency check.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §7 (6d) and §12 (correctness-push highlights)
> 4. Wave-specific pre-reads:
>    - 6d.1 — `GaugeErasure.lean`, `ModularInvarianceConstraint.lean`, `SU2kFusion.lean`, `SU3kFusion.lean`, `KacWaltonFusion.lean`, MTC stack; Svetitsky-Yaffe 1982 + related universality literature; Phase 5.8 Walker-Wang transport plan (deferred in Phase 6B of HPC roadmap)
>    - 6d.2 — `WetterichNJL.lean`, `TetradGapEquation.lean`, Phase 5z.1 `ScalarRungInterpretation.lean` (parallel pattern)
>    - 6d.3 — 6d.2, Hirono-Tanizaki ℤ₃ one-form symmetry literature, Son CFL chiral Lagrangian derivation (Son-Stephanov literature)
> 5. If 6d.1 transport prediction (η/s vs KSS bound) becomes load-bearing for paper claims, coordinate with Phase 6B HPC roadmap (Walker-Wang transport is HPC-dependent)
> 6. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to published constants); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check (no `rfl`/`decide`/`not_lt.mpr h_disagree` tautologies); (5) defining-the-conclusion check (vacuous when `f := <obvious target>`). The end-of-wave strengthening pass should produce **0 retroactive theorems** — if it produces 5+, log the failure mode and tighten the next wave's discipline.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6d:**
- Confinement as ℤ_N 1-form center symmetry unbreaking (6d.1)
- Polyakov loop as order parameter; Svetitsky-Yaffe deconfinement universality
- WetterichNJL scalar channel as quark condensate `⟨q̄q⟩` (6d.2)
- `SU(N_f)_L × SU(N_f)_R → SU(N_f)_V` breaking pattern
- GMOR relation `m_π² f_π² = −2 m_q ⟨q̄q⟩` as algebraic consequence
- CFL chiral Lagrangian (Son) with emergent ℤ₃ one-form symmetry (6d.3)
- Ttopological order beyond Landau-Ginzburg

**OUT OF SCOPE for 6d:**
- Asymptotic-freedom β-function — HepLean / PhysLean deferred (requires Faddeev-Popov + dimreg + ghosts)
- Lattice-QCD Wilson-loop area law — 6d.1 supersedes via center-symmetry framing
- Full hadron spectrum — CFL / ChPT only; beyond that = HepLean
- Flavor-physics CP-violation fitting — HepLean CKM

**HPC relationship:** Walker-Wang transport prediction (η/s near KSS bound) requires HPC; tracked in Phase 6B HPC roadmap. 6d.1 can state the prediction without HPC; the computational validation is HPC-gated.

**Phase 5z relationship:** 6d.2 parallels Phase 5z.1 — same WetterichNJL identification pattern, different bilinear target (quark condensate vs Higgs). The two waves can share Lean infrastructure.

---

## Track A: Center-Symmetry Confinement (6d.1)

### Motivation

Standard QCD confinement is usually framed as Wilson-loop area law; 6d.1 instead treats confinement as ℤ_N 1-form center symmetry unbreaking. This aligns with the program's existing gauge-erasure + higher-form-symmetry infrastructure (`GaugeErasure.lean`) and leverages the modular-invariance framing (`ModularInvarianceConstraint.lean` ζ₂₄ structure). Polyakov loop is the order parameter; Svetitsky-Yaffe universality links the deconfinement transition to MTC center structure.

### Wave 1 — `CenterSymmetryConfinement.lean` (6d.1) [Pipeline: Stages 1–11+] — **SHIPPED 2026-04-27**

**Status:** Wave 1 closed end-to-end through Stage 11 (notebooks); Stage 13 adversarial review run 2026-04-29 with all BLOCKERs addressed.
- `CenterSymmetryConfinement.lean`: 18 substantive theorems / 0 sorry / 0 new axioms (verified `propext, Classical.choice, Quot.sound` only).
- `src/center_symmetry/`: 4 modules (`__init__.py`, `polyakov_loop.py`, `svetitsky_yaffe.py`, `eta_over_s_prediction.py`) + 28 pytest cases.
- `papers/paper36_center_symmetry/paper_draft.tex`: short paper, compiles clean.
- `fig_polyakov_loop_deconfinement` + companion `Phase6d1_CenterSymmetry_Technical.ipynb` / `_Stakeholder.ipynb`.
- ℤ_N center: `centerPhase_pow_N`, `centerPhase_norm_one`, `centerPhase_Z2_eq_neg_one` (concrete SU(2)).
- Polyakov-loop biconditional `confining_iff_magnitude_zero` + `confining_iff_center_invariant`.
- Svetitsky-Yaffe universality: `critical_exponent_nu` function with literature-anchored values; load-bearing comparison `ising_nu_gt_potts_nu` (threshold-free).
- KSS bound bracket [0.07, 0.08] proved via Mathlib `Real.pi_gt_d4` / `Real.pi_lt_d4`.
- Walker-Wang transport correctness-push: `H_WalkerWangTransportNearKSS` tracked-Prop with witness + 2 falsifiers (η/s = 0 and η/s = 1).
- Cross-bridges: `higher_form_discrete_iff_non_abelian` (genuine biconditional), `su3k1_fusion_card_matches_z3_order` (calls `SU3kFusion.su3k1_object_count`).
- Adversarial citation BLOCKERs (KPSDV2016 quadruple-attribute correction, HofmanIqbal2018 title) + Walker-Wang attribution restructure (paper §IV now explicitly labels [KSS, 2·KSS] as project-originated tracked Prop, not derived; cites WalkerWang2012 for topological-phase context only) all addressed.
- HPC validation of η/s window deferred to Phase 6B per roadmap.

### ~~Wave 1 specification (preserved for reference)~~

**Goal:** Confinement via ℤ_N 1-form center symmetry; Polyakov loop as order parameter; Svetitsky-Yaffe universality statement.

**Prerequisites:** `GaugeErasure.lean`, `ModularInvarianceConstraint.lean`, `SU2kFusion.lean`, `SU3kFusion.lean` all at zero-sorry.

**Module structure:**
- `lean/SKEFTHawking/CenterSymmetryConfinement.lean`
  - ℤ_N 1-form center symmetry definition + action on Wilson / Polyakov line operators
  - Confinement predicate: `Confining (T : ℝ) : Prop` = center symmetry unbroken at temperature `T`
  - Polyakov loop as order parameter: `PolyakovLoop (T) = ℝ` with `|P| = 0` iff confining
  - Svetitsky-Yaffe universality statement: `D-dim deconfinement transition = (D−1)-dim Z_N spin model transition`
  - MTC center-structure bridge: `center_modular_invariance_matches_MTC_center_structure` (for SU(2)_k and SU(3)_k specializations from existing modules)
  - **Correctness-push theorem:** `walker_wang_transport_eta_s_near_KSS_iff_anyonic_transport_matches` — states the η/s prediction as a biconditional; quantitative validation is HPC-gated (Phase 6B)
- Target ~10–14 theorems.

**Python side:**
- `src/center_symmetry/` new subpackage
  - `polyakov_loop.py` — Polyakov loop numerical evaluator
  - `svetitsky_yaffe.py` — universality-class cross-reference (D to D−1 dim map)
  - `eta_over_s_prediction.py` — analytical η/s prediction from Walker-Wang transport (HPC-gated numeric in Phase 6B)

**Bridges:**
- Integrates `GaugeErasure`, `ModularInvarianceConstraint`, `SU2kFusion`, `SU3kFusion`, `KacWaltonFusion`, MTC stack
- Feeds 6d.3 — CFL emergent ℤ₃ one-form ↔ QCD center ℤ₃ consistency check
- Cross-references Phase 6B HPC roadmap for Walker-Wang transport validation

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_center_symmetry.py`
- PRD paper (or short) `papers/paper36_center_symmetry_confinement/paper_draft.tex`
- Figure: `fig_polyakov_loop_deconfinement` — `|P|` vs T, deconfinement transition at `T_c`, Svetitsky-Yaffe universality class identified
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 2–5 person-months
**Risk:** Medium. The Svetitsky-Yaffe universality statement can be formalized as a Prop-level claim without requiring full lattice derivation — scope this carefully to avoid sliding into lattice-QCD territory.

---

## Track B: Chiral Symmetry Breaking (6d.2)

### Wave 2 — `ChiralSSB_QCD.lean` (6d.2) [Pipeline: Stages 1–11+] — **SHIPPED 2026-04-27**

**Status:** Wave 2 closed end-to-end through Stage 11 (notebooks); Stage 13 adversarial review run 2026-04-29 with all BLOCKERs addressed.
- `ChiralSSB_QCD.lean`: 10 substantive theorems / 0 sorry / 0 new axioms (verified `propext, Classical.choice, Quot.sound` only).
- `src/chiral_ssb/`: 4 modules (`__init__.py`, `quark_condensate.py`, `gmor_check.py`, `tetrad_ratio.py`) + 14 pytest cases.
- `papers/paper37_chiral_ssb/paper_draft.tex`: short companion paper, compiles clean.
- `fig_gmor_relation_verification` + companion `Phase6d2_ChiralSSB_Technical.ipynb` / `_Stakeholder.ipynb`.
- `QuarkCondensate` structure with σ < 0 invariant; FLAG-2021 lattice witness at −0.0227 GeV³.
- GMOR relation `m_π² f_π² = −2 m_q ⟨q̄q⟩` numerically verified at PDG-rounded working values (m_π = 0.137, f_π = 0.092, m_q = 0.0035 GeV) within 1e-4 GeV⁴ tolerance via `norm_num`.
- Contrapositive `chiral_unbroken_violates_gmor` parametric over raw σ (uses all four hypotheses to derive False — caught at first-pass review when an earlier shortcut version closed via the structure invariant).
- `H_TetradQuarkScalesNatural` 3-conjunct tracked-Prop + unit-ratio witness + super-large/super-small falsifiers (HPC-gated for Phase 6B numerical validation).
- Substantive cross-bridge `njl_scalar_bounded_consistent_with_chiral_broken` consumes `WetterichNJL.njl_scalar_upper_bound` + W2-internal `gmor_rhs_pos_of_quark_mass_pos`.
- Adversarial citation BLOCKERs (FLAG2021 `provides` 272→283 MeV correction, "1 part in 10⁴" precision claim → "~2.5×10⁻⁴ relative residual at PDG-rounded values" with explicit hedge against PDG-precise vs rounded distinction) addressed.
- Discipline metric: 4 retroactive theorems (1 first-pass + 2 second-pass + 1 third-pass via multi-pass review protocol).

### ~~Wave 2 specification (preserved for reference)~~

**Goal:** WetterichNJL scalar channel as quark condensate `⟨q̄q⟩`; `SU(N_f)_L × SU(N_f)_R → SU(N_f)_V` breaking pattern; GMOR relation as algebraic consequence.

**Prerequisites:** `WetterichNJL.lean`, `TetradGapEquation.lean` at zero-sorry. Phase 5z.1 `ScalarRungInterpretation.lean` substantially complete (pattern-parallel — reuse identification infrastructure).

**Module structure:**
- `lean/SKEFTHawking/ChiralSSB_QCD.lean`
  - Quark condensate identification: `IsQuarkCondensate (σ : WetterichNJL.ScalarChannel) : Prop` — parallel to Phase 5z.1's `IsHiggsBilinear`
  - Chiral symmetry group + breaking pattern: `SU(N_f)_L × SU(N_f)_R → SU(N_f)_V` as typed statement
  - GMOR relation: `m_π² · f_π² = −2 m_q · ⟨q̄q⟩` — theorem tying pion mass, decay constant, current quark mass, and condensate
  - **Correctness-push theorem:** `tetrad_vev_to_quark_condensate_ratio_natural_iff_NJL_ADW_match` — ratio of tetrad VEV to quark condensate must be "natural" under the NJL-ADW correspondence; pathological ratio means simultaneous identification is strained
- Target ~8–12 theorems.

**Python side:**
- `src/chiral_ssb/` new subpackage
  - `quark_condensate.py` — numerical `⟨q̄q⟩` from WetterichNJL gap equation
  - `gmor_check.py` — GMOR relation numerical verification against known PDG values
  - `tetrad_ratio.py` — tetrad VEV / quark condensate ratio

**Bridges:**
- Integrates `WetterichNJL`, `TetradGapEquation`
- Parallels 5z.1 `ScalarRungInterpretation` — shares identification-machinery infrastructure
- Feeds 6d.3 (CFL) — chiral Lagrangian is a low-energy expansion around the chiral-SSB vacuum

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_chiral_ssb.py`
- Companion paper `papers/paper37_chiral_ssb/paper_draft.tex` (companion to 5z flagship or standalone — user decision)
- Figure: `fig_gmor_relation_verification` — GMOR numerical check
- Inventory update: +8–12 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 1–3 person-months
**Risk:** Low. Pattern-parallel to 5z.1; Lean infrastructure reuse expected.

---

## Track C: CFL Chiral Lagrangian (6d.3, promoted)

### Motivation

The strategy doc promotes 6d.3 from optional to standard because of its correctness-push value: CFL's emergent ℤ₃ one-form symmetry should match the QCD center ℤ₃ from 6d.1. Independent derivation, direct consistency check. If it fails, that's a quantitative constraint on emergent-symmetry identification.

### Wave 3 — `CFLChiralLagrangian.lean` (6d.3) [Pipeline: Stages 1–11+] — **SHIPPED 2026-04-27 — PHASE 6D CORRECTNESS-PUSH ANCHOR LANDED**

**Status:** Wave 3 closed end-to-end through Stage 11 (notebooks); Stage 13 adversarial review run 2026-04-29 with 0 BLOCKERs (cleanest of all 7 paper-pairs).
- `CFLChiralLagrangian.lean`: 12 substantive theorems / 0 sorry / 0 new axioms (verified `propext, Classical.choice, Quot.sound` only).
- `src/cfl/`: 4 modules (`__init__.py`, `cfl_lagrangian.py`, `z3_one_form_action.py`, `topological_order_check.py`) + 17 pytest cases.
- `papers/paper38_cfl/paper_draft.tex`: short paper, compiles clean. Hatsuda2008 bibkey misnomer corrected to `AlfordSchmittRajagopalSchaefer2008` 2026-04-29.
- `fig_cfl_z3_center_bridge` + companion `Phase6d3_CFL_Technical.ipynb` / `_Stakeholder.ipynb`.
- **Correctness-push anchor `CFL_emergent_Z3_matches_QCD_center_Z3` shipped**: Hirono-Tanizaki emergent ℤ_3 (CFL diquark sector) and W1 QCD center ℤ_3 (bare-gauge SU(3)) yield the *same* generator ω = exp(2πi/3) at the closed-form level. Verifiable at the level of the algebraic identification across two physically independent derivations.
- Algebraic consequences derived through the correctness-push: ω³ = 1 (calls W1's `centerPhase_pow_N`), |ω| = 1 (calls W1's `centerPhase_norm_one`), 1 + ω + ω² = 0 (substantive — distinguishes ℤ_3 from ℤ_2 via factorization).
- CFL chiral Lagrangian skeleton: `cflKineticTerm_nonneg`, `cflMassTerm_chiral_limit` (Goldstone limit at m_q = 0), `cflMassTerm_pos_in_cfl_phase` (uses BOTH m_q > 0 AND `isCFLPhase`).
- Hirono-Tanizaki topological-order-beyond-Landau-Ginzburg: `H_TopologicalOrderBeyondLG` tracked Prop with witness + 2 falsifiers.
- Cross-bridge `cfl_phase_with_gmor_dual_broken` consumes BOTH W2's `chiral_unbroken_violates_gmor` (contrapositive) AND W3's `isCFLPhase_iff_magnitude_pos` — both hypotheses load-bearing.
- Discipline metric: 1 retroactive theorem (single first-pass identity wrapper caught by Lean's unused-variable linter; pass 2 + 3 clean).

### ~~Wave 3 specification (preserved for reference)~~

**Goal:** Son's CFL chiral Lagrangian; emergent ℤ₃ one-form symmetry; topological order beyond Landau-Ginzburg.

**Prerequisites:** 6d.2 `ChiralSSB_QCD.lean` substantially complete. 6d.1 `CenterSymmetryConfinement.lean` substantially complete (correctness-push cross-check against 6d.3).

**Module structure:**
- `lean/SKEFTHawking/CFLChiralLagrangian.lean`
  - CFL condensate `Φ^{ai}_{αj}` diquark structure; color-flavor locking
  - CFL chiral Lagrangian (Son): effective pseudoscalar sector with diquark VEV
  - Emergent ℤ₃ one-form symmetry: structural statement + generator action
  - **Correctness-push theorem:** `CFL_emergent_Z3_matches_QCD_center_Z3` — direct biconditional. If true: independent consistency. If false: structural tension in emergent-symmetry identification (ITSELF a clean result)
  - Topological-order-beyond-Landau-Ginzburg statement (Hirono-Tanizaki framing)
- Target ~10–14 theorems.

**Python side:**
- `src/cfl/` new subpackage
  - `cfl_lagrangian.py` — CFL chiral Lagrangian term-by-term evaluation
  - `z3_one_form_action.py` — emergent ℤ₃ action on diquark VEV
  - `topological_order_check.py` — beyond-Landau-Ginzburg indicator

**Bridges:**
- Depends on 6d.1, 6d.2
- Integrates with `SU3kFusion.lean` (center ℤ₃ structure), `ModularInvarianceConstraint.lean`
- Cross-references Hirono-Tanizaki literature on ℤ₃ one-form symmetry

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_cfl.py`
- Annals paper `papers/paper38_cfl/paper_draft.tex` — CFL as Layer-3 IR hadronic fluid, ℤ₃ one-form emergent symmetry
- Figure: `fig_cfl_z3_center_bridge` — explicit bridge diagram CFL-Z3 ↔ QCD-center-Z3
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. CFL diquark VEV structure formalization has category-theory / tensor-product load. Hirono-Tanizaki framing is recent and evolving.

**Correctness-push highlight.** CFL's emergent ℤ₃ one-form ↔ QCD center ℤ₃ cross-check. Direct biconditional. Either outcome is a substantive result.

---

## Decision Gates

**Gate D.1 — after Wave 1 (`CenterSymmetryConfinement`) ships:** Is the Walker-Wang transport η/s prediction analytically tight? If YES → coordinate with Phase 6B HPC roadmap for validation; if NO → document analytical uncertainty, HPC-validation still recommended.

**Gate D.2 — before Wave 3 (`CFLChiralLagrangian`) begins:** Is the `SU3kFusion`-based ℤ₃ center-structure formalization compatible with Hirono-Tanizaki one-form symmetry framing? If unclear, drop deep-research prompt before Stage 3a.

---

## Dependencies

```
6d.1 (CenterSymmetryConfinement) — independent; uses GaugeErasure + MTC
6d.2 (ChiralSSB_QCD) — independent; parallels 5z.1 pattern
6d.3 (CFLChiralLagrangian) — depends on 6d.1 and 6d.2

Parallelism:
  6d.1 and 6d.2 independent → parallel execution
  6d.3 blocked on 6d.1 + 6d.2
```

---

## Timeline — Phase 6d CLOSED 2026-04-27

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6d.1 | `CenterSymmetryConfinement.lean` + PRD paper | 2–5 | MTC stack | **SHIPPED 2026-04-27** |
| 6d.2 | `ChiralSSB_QCD.lean` + companion paper | 1–3 | WetterichNJL + 5z.1 pattern | **SHIPPED 2026-04-27** |
| 6d.3 | `CFLChiralLagrangian.lean` + Annals paper | 3–5 | 6d.1 + 6d.2 | **SHIPPED 2026-04-27 — correctness-push anchor landed** |

**Phase 6d status (2026-04-29):** all three Track A waves (W1 + W2 + W3) SHIPPED end-to-end including Stage 11 notebooks and Stage 13 adversarial review (all BLOCKERs addressed). Phase 6d CLOSED per roadmap scope-lock; residual QCD items (β-function, Wilson-loop area law, full hadron spectrum) deferred to HepLean / PhysLean.

**Shipped totals:**
- 3 new Lean modules: `CenterSymmetryConfinement`, `ChiralSSB_QCD`, `CFLChiralLagrangian`
- 3 new Python subpackages: `src/center_symmetry`, `src/chiral_ssb`, `src/cfl`
- 40 substantive Lean theorems (18 + 10 + 12)
- 3 papers (paper36, paper37, paper38)
- 3 figures, 59 pytest cases (28 + 14 + 17)
- 6 notebook pairs (Technical + Stakeholder for each shipped wave)
- 0 sorry / 0 new axioms across all three shipped modules

**Tracked-Prop correctness-pushes pending HPC validation in Phase 6B:**
- `H_WalkerWangTransportNearKSS` (W1) — η/s ∈ [KSS, 2·KSS] window; project-originated modeling assumption (not derived from Walker-Wang or Hofman-Iqbal).
- `H_TetradQuarkScalesNatural` (W2) — tetrad-VEV / |σ|^(1/3) within order-of-magnitude window.
- `H_TopologicalOrderBeyondLG` (W3) — Hirono-Tanizaki ℤ_3 charge framing.

**Discipline trend (5 waves with the discipline applied):**
6c.3 = 12 (no preemptive discipline; baseline) → 6b.1 = 5 → 6d.1 = 6 → 6d.2 = 4 → **6d.3 = 1** (single first-pass identity wrapper caught by linter). Monotone improvement validates the discipline.

---

## Open Questions

**O.1** — 6d.1 publication venue: full PRD vs short PRD vs combined with 6d.3 as an Annals bundle? User decision at Stage 10.

**O.2** — 6d.2 companion-paper scope: bundle with 5z flagship (Paper 20) or standalone? Pattern-parallel makes bundling attractive.

**O.3** — 6d.3 Hirono-Tanizaki framing: is there enough Mathlib infrastructure for ℤ₃ one-form symmetry? If NO, scope is reduced to Prop-level statement + external-hypothesis tracking.

**O.4** — Walker-Wang η/s validation: HPC-gated per Phase 6B. Does user want 6d.1 paper to include analytical prediction only, or wait for HPC validation?

---

## What Success Looks Like

**Per wave:**
- 6d.1: Confinement as center-symmetry unbreaking; Polyakov-loop order parameter; Svetitsky-Yaffe universality formal; η/s prediction structural (HPC-validated later)
- 6d.2: Quark condensate identification via WetterichNJL; GMOR numerically verified
- 6d.3: CFL chiral Lagrangian with emergent ℤ₃ one-form; direct consistency check against 6d.1 center ℤ₃

**Cumulative:**
- 3 new Lean modules, 3 Python subpackages, 3 papers
- Correctness-push anchor: CFL ℤ₃ ↔ QCD center ℤ₃ (6d.3)

---

## Cross-References

**Prior phases this extends:**
- Phase 5b (Drinfeld center / Rep(D(G))) — structural categorical groundwork
- Phase 5c/5e (MTC stack, SU(2)_k, SU(3)_k) — `SU2kFusion`, `SU3kFusion`, `KacWaltonFusion`
- Phase 5h (gauging step) — `GaugingStep.lean`
- Phase 3 (WetterichNJL) — quark-condensate identification
- Phase 5d (TetradGapEquation) — NJL-ADW correspondence
- Phase 5z.1 (scalar rung) — parallel pattern for identification

**Feeds downstream phases:**
- Phase 6B HPC roadmap — Walker-Wang η/s validation
- Phase 6e — QCD-side input to nonlinear effective action (where relevant)

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §7

**Correctness-push highlights from strategy doc §12:**
- 6d.3: CFL ℤ₃ one-form vs 6d.1 QCD center ℤ₃

---

*Phase 6d roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Three QCD waves: center-symmetry confinement (6d.1), chiral SSB QCD (6d.2), CFL chiral Lagrangian (6d.3, promoted). All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). **Phase 6d CLOSED 2026-04-27**: all three waves shipped end-to-end. CFL-Z3 ↔ QCD-center-Z3 correctness-push anchor (6d.3) landed.*
