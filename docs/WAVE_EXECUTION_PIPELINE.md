# Wave Execution Pipeline

**Authoritative reference for executing any wave of work in the SK-EFT Hawking project.**

Every wave — whether adding new physics, extending formalization, or producing experimental predictions — follows these 12 stages in strict order. Each stage has a gate that must pass before proceeding. Skipping stages or reordering causes rework and allows errors to propagate downstream.

---

## Pipeline Overview

```
Stage 1:  CONSTANTS & PARAMETERS     → Gate: imports succeed
Stage 2:  FORMULAS                   → Gate: every function has Lean ref
Stage 3:  LEAN THEOREMS (sorry stubs)→ Gate: lake build compiles
Stage 4:  ARISTOTLE                  → Gate: all sorrys filled, lake build clean
Stage 5:  LEAN BUILD VERIFICATION    → Gate: zero sorry, counts match
Stage 6:  PYTHON TESTS               → Gate: all tests pass
Stage 7:  CROSS-LAYER VALIDATION     → Gate: validate.py all checks pass
Stage 8:  VISUALIZATIONS             → Gate: all PNGs generated
Stage 9:  FIGURE REVIEW              → Gate: LLM review all PASS
Stage 10: PAPER DRAFT                → Gate: paper_provenance check passes
Stage 11: NOTEBOOKS                  → Gate: notebook_exec + viz_consistency pass
Stage 12: DOCUMENT SYNC              → Gate: full validate.py passes, counts consistent
```

---

## Stage 1: CONSTANTS & PARAMETERS

**Purpose:** Establish the single source of truth for all physics values.

**Actions:**
- Add new physical constants to `src/core/constants.py`
- Add new experimental parameters to the `EXPERIMENTS` dict
- Add new Aristotle run IDs to `ARISTOTLE_THEOREMS` as they are obtained (Stage 4)

**Rules:**
- `constants.py` is the ONLY place experimental parameters live
- No other file may hardcode physical constants or experimental values
- All other modules import from `constants.py`

**Provenance Requirements:**
- Every value in EXPERIMENTS, ATOMS, and POLARITON_PLATFORMS MUST have a
  corresponding entry in `PARAMETER_PROVENANCE` (in `src/core/provenance.py`)
- Each provenance entry MUST specify: value, unit, tier, source, detail,
  llm_verified_date, human_verified_date
- Tier must be one of: MEASURED, EXTRACTED, DERIVED, PROJECTED, THEORETICAL
- PROJECTED parameters must be clearly labeled — they represent estimates for
  experiments that have not been performed
- Parameters from deep research (LLM outputs) enter as `llm_verified_date: None`
  and must be LLM-verified against the primary source before the Stage 1 gate passes
- See the [Deep Research Reconciliation Protocol](#deep-research-reconciliation-protocol) below

**Gate:** `python -c "from src.core.constants import *"` succeeds without error
**AND** `python scripts/validate.py --check parameter_provenance` passes
(all LLM-verified, zero MISSING, zero NULL values).

**Paper Submission Gate:** `python scripts/validate.py --check parameter_provenance --strict`
passes (all parameters human-verified). Checked before arXiv/journal submission, not at Stage 1.

---

## Stage 2: FORMULAS

**Purpose:** Implement canonical physics formulas with provenance tracking.

**Actions:**
- Add formula implementations to `src/core/formulas.py`
- Each function MUST have a docstring containing:
  - The mathematical formula in plain text
  - `Lean: <theorem_name>` — the exact name of the Lean theorem (must exist in a .lean file or be a planned sorry stub)
  - `Aristotle: <run_id>` — the Aristotle run that proved it, or `manual` for hand proofs, or `pending` for unproved stubs
  - `Source: <citation>` — for physics formulas derived from published work: paper citation + equation number (e.g., `Source: Corley & Jacobson, PRD 54, 1568 (1996), Eq. (4.2)`). Pure math identities and project-original results may omit this.
- Domain-specific modules (`src/<domain>/`) import from `formulas.py` — they NEVER reimplement formulas

**Rules:**
- `formulas.py` is the ONLY place physics formulas live
- If a domain module needs a formula, it must be in `formulas.py` first
- Every function must reference a Lean theorem — no unformalized formulas

**Gate:** Every function has a `Lean:` reference. Grep confirms each referenced Lean name exists in `lean/SKEFTHawking/*.lean` (as a theorem, def, or sorry stub).

---

## Stage 3: LEAN THEOREMS

**Purpose:** Formalize physics results as machine-checkable proofs.

**Actions:**
- Write theorem statements in `lean/SKEFTHawking/<Module>.lean` with `sorry` placeholders
- Add `import SKEFTHawking.<Module>` to the root `lean/SKEFTHawking.lean`
- Register each sorry stub in `src/core/aristotle_interface.py` as `SorryGap(filled=False)`

**Theorem Quality Requirements:**
- Every theorem must encode actual physics — no tautologies (`1 = 1`, `x = x`)
- Hypotheses must be load-bearing, not vacuously satisfied
- Beware Lean's total division convention (`0/0 = 0`): add strengthened variants where κ > 0 or c_s ≠ 0 is genuinely used in the proof
- When in doubt, state the theorem in the strongest form possible; Aristotle can find the proof

**Gate:** `cd lean && lake build` compiles successfully (sorry warnings are expected, zero errors).

---

## Stage 4: ARISTOTLE

**Purpose:** Fill sorry gaps with machine-verified proofs. Strengthen manual proofs.

**Pre-requisite:** Read `docs/archive/references/Theorm_Proving_Aristotle_Lean.md` before every Aristotle session.

**Actions:**

1. **Submit sorry gaps:**
   ```bash
   uv run python scripts/submit_to_aristotle.py --priority 1 --integrate
   ```

2. **For manual proofs — attempt strengthening:**
   ```bash
   uv run python scripts/submit_to_aristotle.py --target <theorem_name> --integrate
   ```

3. **Retrieve results:**
   ```bash
   uv run python scripts/submit_to_aristotle.py --retrieve <ID> --integrate
   ```

4. **Resume OUT_OF_BUDGET runs:**
   ```bash
   uv run python scripts/submit_to_aristotle.py --resume <ID>
   ```

5. **After integration — verify quality:**
   - Review the diff: does the proof actually exercise the hypotheses?
   - Check for trivial proofs (e.g., `simp` that works because of total division)
   - If strengthening is needed: stop, explain to user, prepare correction
   - Only after quality is verified, proceed to registration

6. **Register the proof:**
   - Update `SorryGap(filled=True)` in `src/core/aristotle_interface.py`
   - Add Aristotle run ID to `ARISTOTLE_THEOREMS` in `src/core/constants.py`
   - Update `formulas.py` docstrings: change `Aristotle: pending` to `Aristotle: <run_id>`

**Gate:** All sorry gaps filled (or documented as manual with explanation). `lake build` clean with zero sorry.

---

## Stage 5: LEAN BUILD VERIFICATION

**Purpose:** Confirm the formalization is complete and counts are consistent.

**Actions:**
```bash
cd lean && lake build                    # Must complete with zero sorry, zero errors
grep -c "^theorem " SKEFTHawking/*.lean  # Count theorems per module
grep -c "^axiom " SKEFTHawking/*.lean    # Count axioms
```

- Verify total theorem count matches the header comment in `constants.py`
- Verify `ARISTOTLE_THEOREMS` count + manual count = total theorem count

**Gate:** Zero sorry. Zero errors. Theorem count matches documentation exactly.

---

## Stage 6: PYTHON TESTS

**Purpose:** Validate all computations, including physical reasonableness.

**Actions:**
- Write tests in `tests/test_<domain>.py` for every new `src/` module
- Required test categories:
  - **Correctness:** Computed values match expected results
  - **Edge cases:** Boundary conditions, zero inputs, limiting cases
  - **Physical bounds:** `assert 0 < delta_diss < 1` for every perturbative correction
  - **Cross-module consistency:** Same quantity computed by different modules agrees
  - **Sanity bounds:** If δ < 10^-3, then shots_needed > 10^4 (small corrections need many shots)

```bash
uv run python -m pytest tests/ -v
```

**Gate:** All tests pass. Every `src/` module has a corresponding test file.

---

## Stage 7: CROSS-LAYER VALIDATION

**Purpose:** Verify consistency across Python, Lean, notebooks, and papers.

**Actions:**
```bash
uv run python scripts/validate.py
```

**Checks (14 total):**
1. `formulas` — Python formulas reference valid Lean theorems
2. `numerical` — Experimental parameters match reference values
3. `identities` — Mathematical identities and boundary conditions
4. `paper_table` — Paper 1 Table 1 values match solver output
5. `theorems` — Theorem registry is self-consistent
6. `notebooks` — Notebooks import physics from src.core, no re-implementation
7. `lean_source` — Key theorem names found in Lean source files
8. `cgl_fdr` — CGL FDR derivation produces correct results
9. `lean_build` — Lean project builds cleanly
10. `viz_consistency` — Notebook viz uses imported physics, consistent style
11. `notebook_exec` — All notebooks execute without errors
12. `physical_bounds` — All computed quantities within physical bounds
13. `cross_path_consistency` — Different code paths agree within 0.5%/1%
14. `paper_provenance` — Paper numerical claims trace to computations within 0.5%

**Gate:** ALL checks pass (not just advisory warnings). Report archived to `docs/validation/reports/`.

---

## Stage 8: VISUALIZATIONS

**Purpose:** Create publication-quality figures derived from validated computations.

**Actions:**
- Implement figure functions in `src/core/visualizations.py`
- Each function: `def fig_<name>() -> go.Figure`
- Register in `scripts/review_figures.py` (FigureSpec + func_map)

**Rules:**
- `visualizations.py` is the ONLY place figure functions live
- Functions MUST import data from `formulas.py` / `constants.py` / domain modules
- NEVER hardcode physics values in figure functions
- Use `COLORS` dict from `visualizations.py` — never hardcode hex values
- Use `stakeholder=True` parameter for tech/stakeholder figure variants

```bash
uv run python scripts/review_figures.py
```

**Gate:** All PNGs generated with zero failures. All registered figures have corresponding functions.

---

## Stage 9: FIGURE REVIEW

**Purpose:** Catch rendering issues that automated tests cannot detect.

**Actions:**
- Run LLM figure review agent (physics-figure-review plugin or general-purpose agent with review prompt)
- Fix ALL issues flagged as FAIL or MINOR in `visualizations.py`
- Regenerate PNGs, re-review until ALL PASS
- Report saved to `figures/figure_review_report.json`

**Gate:** All figures PASS LLM review. No FAIL, no MINOR remaining.

---

## Stage 10: PAPER DRAFT

**Purpose:** Write the paper with full provenance for every claim.

**Actions:**
- Copy validated PNGs to `papers/paper<N>_<name>/figures/`
- Write/update `.tex` with `\includegraphics` — NEVER use `\fbox` placeholders
- Every numerical claim must trace to `formulas.py` or `constants.py`
- Every "formally verified" claim must cite specific Lean theorem names
- Every Aristotle reference must include run ID
- Use phrasing: "X theorems in Y.lean, verified by `lake build` (zero sorry). Z filled by the Aristotle automated prover [run IDs]."
- Qualitative claims (feasibility, detectability) must be supported by computed quantities — no hallucinated optimism
- No hardcoded numbers in tex that aren't also in the computation pipeline

**Gate:** `validate.py --check paper_provenance` passes for this paper.

---

## Stage 11: NOTEBOOKS

**Purpose:** Create reproducible computational narratives.

**Actions:**
- **Technical notebook:** Matches paper structure, imports all physics from `src/` modules
- **Stakeholder notebook:** Accessible language, same physics imports, teaching-oriented
- Tag all figure cells with `# viz-ref: fig_<name>` matching `visualizations.py` function names
- Import `COLORS` from `src.core.visualizations` (NOT `src.core.constants`)
- No inline physics redefinition (CHECK 6 catches this)
- No evaluative print statements in code cells (commentary goes in markdown cells)
- Narrative text must be consistent with computed values displayed in the notebook

**Naming convention:** `Phase<N><letter>_<Topic>_Technical.ipynb` / `_Stakeholder.ipynb`
- Example: `Phase3b_GaugeErasure_Technical.ipynb`

**Gate:** `validate.py --check notebook_exec` and `--check viz_consistency` pass.

---

## Stage 12: DOCUMENT SYNC

**Purpose:** Ensure all project documentation reflects the current state.

**Actions — update these files:**

| Category | Files | What to update |
|----------|-------|---------------|
| **Code** | `src/__init__.py` | Docstring: theorem count, module count, phase summary |
| **Code** | `src/core/constants.py` | Header comment: total theorems, modules |
| **Code** | `scripts/validate.py` | Expected counts in CHECK 5 |
| **Root** | `README.MD` | Theorem table, project tree, test/figure/module counts |
| **Root** | `SK_EFT_Hawking_Inventory.md` | Summary table |
| **Root** | `CLAUDE.md` (repo root) | Architecture, module count, Lean table |
| **Stakeholder** | `docs/stakeholder/companion_guide.md` | Status table + content synthesis |
| **Stakeholder** | `docs/stakeholder/Phase<N>_Implications.md` | Content for this phase |
| **Stakeholder** | `docs/stakeholder/Phase<N>_Strategic_Positioning.md` | Content for this phase |
| **Reference** | `docs/Fluid-Based...Feasibility Study.md` | SK-EFT row in validation table |
| **Reference** | `docs/Fluid-Based...Critical Review v3.md` | SK-EFT row in evidence table |
| **Inventory** | `SK_EFT_Hawking_Inventory.md` | All sections (see Inventory_Index.md for what to update) |
| **Inventory Index** | `SK_EFT_Hawking_Inventory_Index.md` | Counts table + section→update mapping |

**Content must be consistent across all documents.** This means: physics descriptions match the code, phase boundaries match computed values, feasibility claims are supported by calculations, and all narratives reflect the current state of the research. Count agreement (theorems, tests, figures, etc.) is a secondary mechanical check — content accuracy is the primary concern.

### Inventory Maintenance Protocol

The Inventory (`SK_EFT_Hawking_Inventory.md`) is the comprehensive source of truth. The Index (`SK_EFT_Hawking_Inventory_Index.md`) is the LLM-friendly quick reference.

**Before updating:** Read `SK_EFT_Hawking_Inventory_Index.md` to understand which sections need updates and the verification commands for each count.

**Update procedure:**
1. Run the verification commands from the Index's "Counts" table to get ground truth
2. Update the Inventory's relevant sections (the Index tells you which sections to update for each type of change)
3. Update the Index's "Counts" table
4. Update the Index's "Last synced" date
5. Spot-check: read 3 random sections of the Inventory and verify they match the current codebase

**Common staleness patterns to watch for:**
- New modules added but not listed in Section 1
- New Lean theorems but Section 2 table not updated
- New Aristotle runs but Section 3 table not updated
- New notebooks/papers but Sections 4-5 not updated
- Formula changes in formulas.py but Section 10 not updated
- Test count changes but Section 6 not updated
- Descriptions that reference old behavior (e.g., "hardcoded constants" after consolidation)

### Validation Reports

- `docs/validation/reports/` — Timestamped archives from `validate.py` (auto-generated, no maintenance needed)
- `docs/validation/lean_quality_audit.md` — Manual audit snapshots. Create new ones per wave; do not update old ones in place.
- `docs/validation/VALIDATION_REPORT.md` — Deprecated; superseded by `validate.py` automated checks. Kept for historical reference only.

**Gate:** `validate.py` full suite passes. Manual spot-check of 3 count-sensitive files confirms consistency.

---

## Pipeline Invariants

These must hold at ALL times, not just at wave completion:

1. **`formulas.py` is canonical.** It is the ONLY place physics formulas live. All other code imports from it. No domain module reimplements a formula.

2. **`constants.py` is canonical.** It is the ONLY place experimental parameters and the Aristotle theorem registry live. No other file hardcodes physical constants.

3. **`visualizations.py` is canonical.** It is the ONLY place figure functions live. Notebooks reference figures via `# viz-ref:` tags, never reimplementing figure logic.

4. **Every formula has a Lean theorem.** Every Lean theorem has a proof (zero sorry). No unformalized formulas in the computation pipeline.

5. **Every computed quantity has bounds.** Physical bounds are tested in the test suite and enforced by CHECK 12.

6. **Every paper claim traces to computation.** Numerical claims match `formulas.py` output within 0.5%. Enforced by CHECK 14.

7. **Narrative derives from data.** Feasibility claims, detectability statements, and experimental reach assessments must be supported by computed quantities. "Within reach" means the computed shot count is < 10^6 and feasible=True.

8. **Every experimental parameter has verified provenance.** Each value in EXPERIMENTS, ATOMS, and platform dicts traces to a specific published source (paper, table/figure, page) via `PARAMETER_PROVENANCE` in `src/core/provenance.py`. Parameters from LLM research outputs are not considered verified until LLM reads the primary source. Paper submission requires human verification via the provenance dashboard. Enforced by CHECK 15.

---

## Deep Research Reconciliation Protocol

When incorporating results from deep research (LLM-generated analysis in `Lit-Search/`):

1. **Extract claims.** List every factual claim: parameter values, paper citations, experimental status assertions.

2. **Classify each claim:**
   - **VERIFIABLE:** cites a specific paper + location (table, equation, figure)
   - **PLAUSIBLE:** consistent with known physics but no specific citation
   - **CONFLICTING:** disagrees with another deep research result or the codebase
   - **UNVERIFIABLE:** no citation, or citation is vague ("well-known result")

3. **For VERIFIABLE claims:** Add to `PARAMETER_PROVENANCE`. LLM fetches the cited paper and extracts the value + excerpt → `llm_verified_date` set. Code values can update after LLM verification. Human verification via dashboard gates paper submission.

4. **For CONFLICTING claims:** Document BOTH values + excerpts in `PARAMETER_PROVENANCE` notes. LLM recommends resolution based on source quality (e.g., "Table I" beats "estimated from figure"). Code uses the LLM-recommended value. Human resolves via dashboard before paper submission.

5. **For PLAUSIBLE/UNVERIFIABLE claims:** Can add to `constants.py` with `tier: 'PROJECTED'` and `llm_verified_date: None`. Clearly labeled as estimates. CHECK 15 flags these as advisory warnings, not hard failures (PROJECTED params are expected to lack primary sources).

6. **Verification tasks** go in the roadmap under a "Primary Source Verification" section.

**Rule:** Deep research claims can update code parameters after LLM verification against primary sources. Paper SUBMISSION is gated on human verification via the provenance dashboard.

---

## Quick Reference: Commands

```bash
# Full validation (run from SK_EFT_Hawking/ root)
uv run python -m pytest tests/ -v                    # All tests
uv run python scripts/validate.py                    # All 15 checks
uv run python scripts/review_figures.py              # Generate figures + structural checks
cd lean && lake build                                 # Lean build

# Aristotle (read docs/archive/references/Theorm_Proving_Aristotle_Lean.md first!)
uv run python scripts/submit_to_aristotle.py --priority 1 --integrate
uv run python scripts/submit_to_aristotle.py --retrieve <ID> --integrate
uv run python scripts/submit_to_aristotle.py --resume <ID>

# Individual validation checks
uv run python scripts/validate.py --check physical_bounds
uv run python scripts/validate.py --check cross_path_consistency
uv run python scripts/validate.py --check paper_provenance
uv run python scripts/validate.py --check parameter_provenance  # CHECK 15
uv run python scripts/validate.py --list              # List all available checks

# Provenance command center (human verification dashboard)
uv run python scripts/provenance_dashboard.py         # Opens localhost:8050
```
