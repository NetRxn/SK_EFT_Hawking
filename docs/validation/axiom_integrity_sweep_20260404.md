# Axiom Integrity Sweep Report

**Date:** 2026-04-04
**Trigger:** Discovery and correction of 4 problematic axioms
**Scope:** All documents, papers, indices, notebooks, and source files in SK_EFT_Hawking

---

## Ground Truth (verified from Lean source)

| Metric | Value | Verification command |
|--------|-------|---------------------|
| Theorems | 900 | `grep -c "^theorem" lean/SKEFTHawking/*.lean` (sum across 57 files with theorems) |
| Axioms | 2 | `grep -rn "^axiom" lean/SKEFTHawking/*.lean` |
| Lean modules | 58 | `ls lean/SKEFTHawking/*.lean` (57 with theorems + Basic.lean) |
| Sorry | 6 (Wave 3 draft only) | `lake build 2>&1 \| grep sorry` -- all in DrinfeldDoubleAlgebra.lean |
| Aristotle-proved | 254 (251 machine + 3 manual) | ARISTOTLE_THEOREMS in constants.py |

### Remaining 2 axioms

| Axiom | Module | Status |
|-------|--------|--------|
| `non_abelian_center_discrete` | GaugeErasure.lean:80 | Encodes standard Lie theory |
| `gs_nogo_axiom` | GoltermanShamir.lean:427 | Encodes GS no-go theorem (1993) |

### 4 axioms removed

| Former axiom | Module | Problem | Resolution |
|-------------|--------|---------|------------|
| `z16_classification` | Z16Classification | Tautological: `exists (phi : ZMod 16 equiv ZMod 16), Bijective phi` -- trivially true | Discharged to theorem |
| `dai_freed_spin_z4` | Z16AnomalyComputation | Tautological: same structure as z16_classification | Discharged to theorem |
| `chiral_central_charge_coeff` | GenerationConstraint | Tautological: `forall N_f, exists c, c = 8*N_f` -- witness: `8*N_f` | Discharged to theorem |
| `modular_invariance_constraint` | GenerationConstraint | **FALSE**: claimed `forall c, (exists N_f, c = 8*N_f) -> 24 divides c`. Counterexample: N_f=1, c=8, 24 does not divide 8. | REMOVED. Comment in GenerationConstraint.lean explains. |

**None of the 4 removed axioms were used in any proof.** The generation_mod3_constraint theorem was always correct -- it takes `24 | 8*N_f` as a hypothesis.

### Per-module theorem count changes

| Module | Before | After | Reason |
|--------|--------|-------|--------|
| Z16Classification | 21 thm + 1 ax | 22 thm + 0 ax | Axiom discharged to theorem |
| Z16AnomalyComputation | 21 thm + 2 ax | 23 thm + 0 ax | 2 axioms discharged to theorems |
| GenerationConstraint | 12 thm + 2 ax | 13 thm + 0 ax | 1 axiom discharged to theorem, 1 removed |

---

## Files Fixed

### Core indices (3 files)

| File | Changes |
|------|---------|
| `SK_EFT_Hawking_Inventory_Index.md` | Counts table: 900+2ax, 58 modules. Module rows: Z16Classification 22, Z16AnomalyComputation 23, GenerationConstraint 13. |
| `SK_EFT_Hawking_Inventory.md` | Summary line, header (900+2ax, 58 modules), module table (axiom section: 2 axioms), status line updated to 2026-04-04. |
| `README.md` | Header (900+2ax, 58 modules), tree annotations, theorem inventory table (all module rows), section header. |

### Python source (3 files)

| File | Changes |
|------|---------|
| `src/__init__.py` | Docstring: 900+2ax, 58 modules |
| `src/core/constants.py` | Verification breakdown comment: 2 axioms, discharged/removed listed |
| `src/core/visualizations.py` | fig_chirality_wall_three_pillars summary bar: 900+2ax, 58 modules, 254 Aristotle |

### Papers (3 files)

| File | Changes |
|------|---------|
| `papers/paper7_chirality_formal/paper_draft.tex` | Abstract, figure caption, conclusion: 900+2ax, 58 modules |
| `papers/paper8_chirality_master/paper_draft.tex` | Abstract, intro, figure caption, summary table, "What is proved/axiomatized", conclusion: 900+2ax, 2 axioms |
| `papers/paper9_sm_anomaly_drinfeld/paper_draft.tex` | Abstract, generation constraint section (13 thm 0 ax), Z16AnomalyComputation (23 thm 0 ax), conclusions (900+2ax, explicit axiom names) |

### Documentation (5 files)

| File | Changes |
|------|---------|
| `docs/roadmaps/Phase5b_Roadmap.md` | Axiom index completely rewritten: 2 axioms, 4 discharged/1 removed detailed. Entry state annotated. "from first principles" -> "conditional on 2 axioms". |
| `docs/stakeholder/companion_guide.md` | Status table: 900+2ax, 58 modules |
| `docs/stakeholder/Phase5a_Implications.md` | Status line annotated, Z16 axiom row updated (22 thm, 0 ax, discharged), A(1) Steenrod description updated |
| `docs/Fluid-Based Approach to Fundamental Physics  Feasibility Study.md` | Validation table: 900+2ax, 58 modules. Section 6.3 status: updated counts. |
| `docs/Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md` | Multiple sections: verdict (900+2ax), chirality row (900+2ax), section 5.1 (900+2ax), table row, section 8.2, section 9 claims. |

### Notebooks (3 files)

| File | Changes |
|------|---------|
| `notebooks/Phase5b_SMAnomalyDrinfeld_Technical.ipynb` | Lean summary table: Z16AnomalyComputation 23/0, GenerationConstraint 13/0. Total line: 900+2ax, 58 modules. |
| `notebooks/Phase5b_SMAnomalyDrinfeld_Stakeholder.ipynb` | Verification status: 900+2ax, 58 modules, conditional on 2 axioms. |
| `notebooks/Phase5a_GTChiralFermion_Stakeholder.ipynb` | Intro: 900 theorems. Print statement: 900+2ax, 58 modules. |

---

## Files NOT fixed (correctly stale or generated)

| File | Reason |
|------|--------|
| `papers/paper7_chirality_formal/claims_review.json` | Generated by claims-reviewer tool. Contains stale "748 theorems + 3 axioms" from review date. Will be regenerated on next review run. |
| `papers/paper8_chirality_master/claims_review.json` | Same -- generated file, stale counts. |
| `papers/paper9_sm_anomaly_drinfeld/claims_review.json` | Same -- generated file, stale "877 theorems + 7 axioms". |
| `docs/stakeholder/Phase5a_Strategic_Positioning.md` | Historical Phase 5a snapshot (675 -> 748). Correctly documents state at that time. |
| `docs/roadmaps/Phase5a_Roadmap.md` | Historical snapshot. "748/49" was correct at Phase 5a completion. |
| `.superpowers/brainstorm/*/content/*.html` | Generated brainstorm artifacts, not part of project. |

---

## Overclaiming check

Searched for "from first principles" across the project. Most uses are physics-appropriate ("computed from first principles" meaning "derived from the SK-EFT framework"). One instance in Phase5b_Roadmap.md was changed from "from first principles" to "conditional on 2 axioms".

The project does NOT claim "formally verified from first principles" in any paper. All paper conclusions now explicitly state the axiom count and names.

---

## Verification

- `grep -rn "^axiom" lean/SKEFTHawking/*.lean`: confirms exactly 2 axioms
- `grep -c "^theorem" lean/SKEFTHawking/*.lean` (summed): confirms 900 theorems
- `lake build 2>&1 | grep sorry`: 6 sorry all in DrinfeldDoubleAlgebra.lean (Wave 3 draft)
- No remaining instances of "888 theorems", "877 theorems", "6 axioms", or "7 axioms" in .md/.tex/.py files
- `modular_invariance_constraint` appears only in: GenerationConstraint.lean (removal comment), Phase5b_Roadmap.md (REMOVED section), constants.py (REMOVED comment), Inventory Index (removal note), and generated claims_review.json files

---

## Additional finding

The Inventory Index row for VecGMonoidal still says "(1 sorry -- Lean heartbeat)" but `lake build` does not flag any sorry in VecGMonoidal.lean -- only in DrinfeldDoubleAlgebra.lean. This may indicate the VecGMonoidal sorry was resolved since the text was written. Not addressed in this sweep (pre-existing, unrelated to axiom correction).

---

## Summary

17 files fixed across indices, Python source, papers, documentation, and notebooks. All stale axiom counts (3, 6, or 7) updated to 2. All stale theorem counts (748, 877, 888) updated to 900. All stale module counts (49, 56, 57) updated to 58. The false axiom `modular_invariance_constraint` is documented as removed in all relevant files. No overclaiming found in papers.

Three generated claims_review.json files contain stale counts but are excluded from manual fixes (will be regenerated by the claims-reviewer tool on next run).
