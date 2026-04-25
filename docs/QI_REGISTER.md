# Meta-process Quality Improvement Register

**Auto-generated:** 2026-04-25T03:38:53+00:00
**Generator:** `scripts/qi_register.py`
**Reads from:** current ReviewFinding graph nodes + this file's `## Closed Items` section for status continuity

This is the Stage 14 (advisory) register. Each QI item is a **process-level** issue — a failure class that has affected multiple papers or indicates a pipeline gap — not a paper-local issue. Stage 13 (adversarial review) surfaces paper-level issues; Stage 14 aggregates those into process improvements. Stage 14 never blocks submission; items here feed remediation waves.

## Summary

- **107** ReviewFinding nodes currently in the graph
- **8** QI items detected
- **8** open, **0** closed

## Open Items

### qi-assumptiondisclosure — Recurring AssumptionDisclosure findings across 4 papers

- **Gate affected:** `AssumptionDisclosure`
- **Occurrences:** 6 findings across 4 papers
- **Affected papers:** paper10_modular_generation, paper12_polariton, paper17_dark_sector, paper20_scalar_rung
- **Severity mix:** 3 advisory, 2 major, 1 critical
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-25-0135-internal-adversarial
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:6.3` — 6.3 Paper 10: Spin manifold/cobordism assumption undis (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:7.5` — 7.5 "Modular invariance rooted in Dedekind eta studied (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:9.2` — 9.2 Paper 12 strategic reframing for collaboration (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:6.1` — 6.1 🟡 REQUIRED — Hypothesis `H_MixedChannelZ16Cancels` (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)
- `review:2026-04-25-0135-internal-adversarial:paper20_scalar_rung:3.1` — 3.1 🔴 BLOCKER — Paper cites removed Lean predicate `Is (papers/AutomatedReviews/2026-04-25-0135-internal-adversarial/paper20_scalar_rung.md)

### qi-citationintegrity — Recurring CitationIntegrity findings across 12 papers

- **Gate affected:** `CitationIntegrity`
- **Occurrences:** 41 findings across 11 papers
- **Affected papers:** paper10_modular_generation, paper12_polariton, paper17_dark_sector, paper18_doublon_gate, paper1_first_order, paper20_scalar_rung, paper3_gauge_erasure, paper5_adw_gap, paper7_chirality_formal, paper8, paper9_sm_anomaly_drinfeld
- **Severity mix:** 20 advisory, 16 critical, 3 major, 2 minor
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-26-0130-citation-verification
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:5.5` — 5.5 Missing journal for `[BeaudryCampbell]` (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:6.1` — 6.1 Fidkowski-Kitaev 2010 (required for ℤ₁₆ in class D (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:6.2` — 6.2 di Francesco et al. (CFT textbook) for Casimir ene (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:6.3` — 6.3 Freed-Hopkins (for framing anomaly and spin manifo (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:6.4` — 6.4 Wang 2024 is cited once but drives almost everythi (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)

### qi-computationcorrectness — Recurring ComputationCorrectness findings across 3 papers

- **Gate affected:** `ComputationCorrectness`
- **Occurrences:** 5 findings across 2 papers
- **Affected papers:** paper10_modular_generation, paper17_dark_sector
- **Severity mix:** 4 advisory, 1 major
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-23-1500-internal-adversarial
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:7.4` — 7.4 "Quaternionic structure of spinors" as causal orig (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:7.6` — 7.6 E8 "lattice" vs. E8 "manifold" conflation (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:8.2` — 8.2 `dai_freed_spin_z4` is discharged as `Equiv.refl` (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:9.3` — 9.3 "First formally verified X in any proof assistant" (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:7.1` — 7.1 🟡 REQUIRED — 11 inline count-literals flagged by ` (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)

### qi-countfreshness — Recurring CountFreshness findings across 3 papers

- **Gate affected:** `CountFreshness`
- **Occurrences:** 4 findings across 2 papers
- **Affected papers:** paper18_doublon_gate, paper20_scalar_rung
- **Severity mix:** 2 advisory, 2 major
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-25-0135-internal-adversarial
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:4.1` — 4.1 Module count discrepancy (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-23-2153-internal-adversarial:paper18_doublon_gate:9.1` — 9.1 🟡 REQUIRED — Two raw count literals outside the ma (papers/AutomatedReviews/2026-04-23-2153-internal-adversarial/paper18_doublon_gate.md)
- `review:2026-04-25-0135-internal-adversarial:paper20_scalar_rung:7.2` — 7.2 🟡 REQUIRED — Definition count inconsistent: paper  (papers/AutomatedReviews/2026-04-25-0135-internal-adversarial/paper20_scalar_rung.md)
- `review:2026-04-25-0135-internal-adversarial:paper20_scalar_rung_REINVOCATION:C7` — C7 Count Freshness (3/3 closed) (papers/AutomatedReviews/2026-04-25-0135-internal-adversarial/paper20_scalar_rung_REINVOCATION.md)

### qi-crosspaperconsistency — Recurring CrossPaperConsistency findings across 3 papers

- **Gate affected:** `CrossPaperConsistency`
- **Occurrences:** 6 findings across 2 papers
- **Affected papers:** paper17_dark_sector, paper7_chirality_formal
- **Severity mix:** 4 advisory, 1 minor, 1 critical
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-26-0130-citation-verification
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:3.3` — 3.3 The Fractional Central Charge Argument (`c_- = 15/ (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:3.4` — 3.4 "Without ν_R, N_f = lcm(16,3) = 48 provides formal (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:2.1` — 2.1 Paper 7 calls the construction "Tong-Preskill-Fidk (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:9.1` — 9.1 Papers 7 and 8 contradict each other on author nam (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:2.2` — 2.2 🔵 RECOMMENDED — Paper 17 is the sole citer of 4 hi (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)

### qi-leanproofsubstance — Recurring LeanProofSubstance findings across 4 papers

- **Gate affected:** `LeanProofSubstance`
- **Occurrences:** 6 findings across 3 papers
- **Affected papers:** paper15_methodology, paper17_dark_sector, paper20_scalar_rung
- **Severity mix:** 3 advisory, 1 critical, 1 minor, 1 major
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-25-0135-internal-adversarial
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:4.3` — 4.3 `sixteen_convergence_full` — tautological structur (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:8.1` — 8.1 `sixteen_convergence_full` is a structural tautolo (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:8.4` — 8.4 Paper 15 module/theorem counts are stale (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:5.1` — 5.1 🔴 BLOCKER — `fracton_bullet_sigma_zero` is `rfl` o (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:7.2` — 7.2 🔵 RECOMMENDED — `placeholdertheorems=99` not surfa (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)

### qi-narrativegrounding — Recurring NarrativeGrounding findings across 5 papers

- **Gate affected:** `NarrativeGrounding`
- **Occurrences:** 6 findings across 4 papers
- **Affected papers:** paper17_dark_sector, paper18_doublon_gate, paper20_scalar_rung, paper6_vestigial
- **Severity mix:** 2 advisory, 3 major, 1 critical
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-25-0135-internal-adversarial
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:3.1` — 3.1 The "16 Convergence" Section: Four Claims, Two Wro (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:6.5` — 6.5 Paper 6: Monte Carlo claim unsupported (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:8.1` — 8.1 🟡 REQUIRED — Paper claims "Monte Carlo evidence" v (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)
- `review:2026-04-23-2153-internal-adversarial:paper18_doublon_gate:5.1` — 5.1 🟡 REQUIRED — W8e statement does not prove "Berry p (papers/AutomatedReviews/2026-04-23-2153-internal-adversarial/paper18_doublon_gate.md)
- `review:2026-04-25-0135-internal-adversarial:paper20_scalar_rung:3.4` — 3.4 🔴 BLOCKER — Paper claims a Yukawa-overlap "orthogo (papers/AutomatedReviews/2026-04-25-0135-internal-adversarial/paper20_scalar_rung.md)

### qi-parameterprovenance — Recurring ParameterProvenance findings across 4 papers

- **Gate affected:** `ParameterProvenance`
- **Occurrences:** 7 findings across 3 papers
- **Affected papers:** paper12_polariton, paper17_dark_sector, paper20_scalar_rung
- **Severity mix:** 3 advisory, 3 major, 1 minor
- **First observed:** 2026-04-12
- **Last observed:** 2026-04-25-0135-internal-adversarial
- **Owner:** _(unassigned)_
- **Target date:** _(unset)_

**Representative findings:**

- `review:2026-04-12:Paper 10 Deep Review — Modular Generation Constraint:4.4` — 4.4 The Ext computation claim (papers/AutomatedReviews/2026-04-12/Paper 10 Deep Review — Modular Generation Constraint.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:4.1` — 4.1 Speed of sound c_s wrong by 25% (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-12:SK_EFT_Hawking — Master Systematic Update Checklist:4.4` — 4.4 Dispersive parameter D likely underestimated (papers/AutomatedReviews/2026-04-12/SK_EFT_Hawking — Master Systematic Update Checklist.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:3.1` — 3.1 🟡 REQUIRED — No `PARAMETER_PROVENANCE` entries fou (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)
- `review:2026-04-23-1500-internal-adversarial:paper17_dark_sector:3.2` — 3.2 🟡 REQUIRED — `T_dS = 2 · T_GH` numeric interpretat (papers/AutomatedReviews/2026-04-23-1500-internal-adversarial/paper17_dark_sector.md)

## Closed Items

_(none yet)_
---

## Manual fields

The following fields are preserved across regenerations by matching on QI item `id`:

- `owner` — person responsible
- `target_date` — ISO 8601
- `status` — `open` / `in-progress` / `closed`
- `evidence_on_close` — commit hash or wave reference that remediated the pattern

To assign fields for a QI item, edit the item section inline. The generator does NOT overwrite manual fields (it matches on `id`). (Current generator is auto-regen-only; manual-field persistence is a follow-up.)
