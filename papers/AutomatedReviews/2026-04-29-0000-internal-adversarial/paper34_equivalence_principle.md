---
paper: paper34_equivalence_principle
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-29T00:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper34_equivalence_principle

## Summary

Re-scan after strengthening pass. **Prior REQUIRED 3.1** (`step_target_can_test_vestigial_relics` self-equality tautology) is **resolved**: theorem removed from `EquivalencePrinciple.lean` (verified absent via `grep -n "step_target_can_test_vestigial_relics" → no matches`). **Prior RECOMMENDED 3.2** (`module_summary_marker : True := trivial`) is **resolved**: declaration removed (verified absent). **Prior RECOMMENDED 5.1** (abstract "within reach" feasibility claim unsupported) is **partially resolved**: abstract line 41 now reads "sub-MICROSCOPE and at the projected design sensitivity discussed for STEP-class satellite missions" — the appropriate hedge from "within reach" → "projected design sensitivity". **Prior RECOMMENDED 6.1** (first conjunct `rfl` bookkeeping) is **resolved**: docstring at lines 376-381 now explicitly acknowledges "The first conjunct closes by `rfl` (a bookkeeping consistency check on the `ClassificationTableDark` enumeration); the substantive content lives in the second conjunct, which decides via the EP-violation enumeration." Counts macro `\epThms` resolves to 25 (verified `grep -cE "^theorem " EquivalencePrinciple.lean = 25`); `\epTests` to 38. **One new RECOMMENDED finding (5.1 below): residual "within reach" prose at line 114 was not hedged in §II body** — abstract was hedged but §II-Mechanism-enumeration body retains the un-hedged phrase.

## Findings

### 5.1 — 🔵 RECOMMENDED — residual "within reach of next-generation satellite tests" at §II body line 114 escaped the abstract-only hedge

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `paper34_equivalence_principle/paper_draft.tex:113-115`
- **Observed:** Abstract (line 41) was hedged from "within reach" → "at the projected design sensitivity discussed for STEP-class satellite missions" — good. But §II "Vestigial relics" paragraph at line 114-115 still reads "This is sub-MICROSCOPE but **within reach** of next-generation satellite tests (STEP-class, $\eta \sim 10^{-18}$ target)." The body retains the un-hedged feasibility-claim phrase that the abstract removed; semantic drift between abstract and body.
- **Evidence:** `grep -n "within reach" paper_draft.tex` returns line 114 only (the §II body usage); abstract uses the hedged form.
- **Expected:** Either (a) propagate the abstract's hedge to §II ("...sub-MICROSCOPE; at the $\eta \sim 10^{-18}$ projected design sensitivity discussed for STEP-class satellite missions"), or (b) accept the §II "within reach" as informal expository prose given that the abstract already establishes the formal hedged claim.
- **Fix:** At line 114, replace "within reach of next-generation satellite tests (STEP-class, $\eta \sim 10^{-18}$ target)" with "at the projected $\eta \sim 10^{-18}$ design sensitivity of STEP-class satellite missions." One-line edit; preserves the body's parallel structure with the abstract.
- **Why not BLOCKER/REQUIRED:** The abstract carries the formal claim; this is a body inconsistency rather than a falsifiable-claim problem. RECOMMENDED for cleanup before submission.

## Verification of strengthening-pass changes

### Class 3 — `step_target_can_test_vestigial_relics` removed

- `grep -n "step_target_can_test_vestigial_relics" lean/SKEFTHawking/EquivalencePrinciple.lean` → no matches ✓
- Paper `paper_draft.tex` no longer cites this theorem (verified — only `vestigial_phase_eta_violates_microscope_bound` and `vestigial_relics_below_microscope_bound` remain in the §III bullet list at lines 178-182).

### Class 3 — `module_summary_marker` removed

- `grep -n "module_summary_marker" lean/SKEFTHawking/EquivalencePrinciple.lean` → no matches ✓

### Class 5 — `vestigial_microscope_violation_consistent` docstring updated

- File: `lean/SKEFTHawking/EquivalencePrinciple.lean:376-381`
- Docstring now reads: "The first conjunct closes by `rfl` (a bookkeeping consistency check on the `ClassificationTableDark` enumeration); the substantive content lives in the second conjunct, which decides via the EP-violation enumeration. The bridge is therefore non-trivial only on the second conjunct — the first is a sanity check that the two modules' enumerations agree on the vestigial mechanism's row." ✓ explicit acknowledgment of `rfl` discharge.

### Class 5 — abstract feasibility-claim hedge

- `paper_draft.tex:40-42`: "vestigial relics, which predict a residual $\eta \sim 10^{-18}$ from defect remnants in a full-tetrad phase, sub-MICROSCOPE and **at the projected design sensitivity discussed for STEP-class satellite missions**." ✓ hedged.
- See finding 5.1 above for residual body usage.

### Class 7 — counts macros

- `\epThms{}` → 25 — matches `grep -cE "^theorem " EquivalencePrinciple.lean = 25` ✓
- `\epTests{}` → 38 — matches `tests/test_equivalence_principle.py` ✓
- No "Undefined control sequence" in `paper_draft.log`. ✓

## Class 1 cache-skip summary (unchanged)

All four bibitems are major published works:
- `Will2018` — Cambridge UP textbook 2nd ed. — `cache-skip`
- `Touboul2017` — arXiv:1712.01176, PRL 119, 231101 (2017) — `cache-skip`
- `Pretko2017` — arXiv:1604.05329, PRB 95, 115139 (2017) — `cache-skip`
- `Berezhiani2015` — arXiv:1507.01019, PRD 92, 103510 (2015) — `cache-skip`

## Class 4 cross-paper consistency

No bibkeys shared with the other six papers in this batch. No contradictions.
