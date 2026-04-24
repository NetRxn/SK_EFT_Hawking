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

### Wave 1 — `CenterSymmetryConfinement.lean` (6d.1) [Pipeline: Stages 1–12]

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

### Wave 2 — `ChiralSSB_QCD.lean` (6d.2) [Pipeline: Stages 1–8]

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

### Wave 3 — `CFLChiralLagrangian.lean` (6d.3) [Pipeline: Stages 1–12]

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

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6d.1 | `CenterSymmetryConfinement.lean` + PRD paper | 2–5 | MTC stack | **TIER 1** |
| 6d.2 | `ChiralSSB_QCD.lean` + companion paper | 1–3 | WetterichNJL + 5z.1 pattern | **TIER 1** |
| 6d.3 | `CFLChiralLagrangian.lean` + Annals paper | 3–5 | 6d.1 + 6d.2 | **TIER 1 (promoted)** |

**Total Phase 6d LOE:** 6–13 person-months. Full parallelism 6d.1 + 6d.2, then 6d.3 after: wall-clock 6–9 months minimum.

**Deliverables cumulative:**
- 3 new Lean modules
- 3 new Python subpackages
- 3 papers (Papers 36–38 reserved)
- ~28–40 new theorems; zero sorry target

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

*Phase 6d roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Three QCD waves: center-symmetry confinement (6d.1), chiral SSB QCD (6d.2), CFL chiral Lagrangian (6d.3, promoted). All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 6–13. 6d.3 is the correctness-push anchor via CFL-Z3 ↔ QCD-center-Z3 cross-check.*
