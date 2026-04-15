# Wave Execution Pipeline

**Authoritative reference for executing any wave of work in the SK-EFT Hawking project.**

Every wave — whether adding new physics, extending formalization, or producing experimental predictions — follows these 12 stages in strict order. Each stage has a gate that must pass before proceeding. Skipping stages or reordering causes rework and allows errors to propagate downstream.

---

## Pipeline Overview

```
Stage 1:  CONSTANTS & PARAMETERS           → Gate: imports succeed
Stage 2:  FORMULAS                         → Gate: every function has Lean ref
Stage 3a: LEAN — INTERACTIVE MCP LOOP      → Gate: proof closes OR decomposed to sector stubs
Stage 3b: LEAN — SORRY REGISTRATION        → Gate: lake build compiles, SORRY_GAPS accurate
Stage 4:  ARISTOTLE (FALLBACK)             → Gate: residual sorrys filled, lake build clean
Stage 5:  LEAN BUILD VERIFICATION          → Gate: zero sorry, counts match
Stage 6:  PYTHON TESTS                     → Gate: all tests pass
Stage 7:  CROSS-LAYER VALIDATION           → Gate: validate.py all checks pass
Stage 8:  VISUALIZATIONS                   → Gate: all PNGs generated
Stage 9:  FIGURE REVIEW                    → Gate: LLM review all PASS
Stage 10: PAPER DRAFT                      → Gate: paper_provenance check passes
Stage 11: NOTEBOOKS                        → Gate: notebook_exec + viz_consistency pass
Stage 12: DOCUMENT SYNC                    → Gate: full validate.py passes, counts consistent
Stage 13: ADVERSARIAL REVIEW               → Gate: fresh-context Opus sweep shows zero BLOCKERs
Stage 14: META-PROCESS QI                  → Advisory: systemic findings logged to QI register
```

**Stage 3 is split into 3a (interactive MCP proving via `lean-lsp-mcp`) and 3b (sorry registration for residual gaps).** Most proofs should close in 3a. Stage 4 (Aristotle) is reserved for (i) sorries that survive interactive iteration with decomposition, or (ii) batch submissions in future phases where MCP iteration is impractical. See the "Lean interactive tooling (MCP)" section of `CLAUDE.md` for dev-loop details.

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

This stage is now split into two phases: **3a (statement + first-pass proof attempt via interactive MCP tools)** and **3b (sorry registration + scaffolding for any remaining gaps)**. Most proofs should close in 3a. Stage 4 (Aristotle) is now a *fallback* for sorries that survive both.

### 3a. Statement + Interactive Proof Attempt

**Actions:**
- Write theorem statements in `lean/SKEFTHawking/<Module>.lean` with `sorry` placeholders
- Add `import SKEFTHawking.<Module>` to the root `lean/SKEFTHawking.lean`
- **Before leaving a sorry in place, make a serious interactive proof attempt using the `lean-lsp-mcp` tools** (see CLAUDE.md "Lean interactive tooling (MCP)" section).

**Required interactive loop per sorry:**
1. `lean_file_outline` — orient in the file
2. `lean_goal` at the `sorry` position — read the actual goal state
3. Identify the proof strategy from any relevant deep research in `Lit-Search/Phase-5*/`. For non-trivial proofs (quantum groups, tensor products, bidegree decompositions, etc.), **read the relevant research document directly, in full**, before iterating on tactics. Agent-summarized research loses tactic-level detail and has caused session failures.
4. `lean_multi_attempt` with a battery of 4–6 candidate tactic sequences. Start with simpler tactics (`noncomm_ring`, `abel`, `aesop`) and escalate to explicit rewrite chains only if needed.
5. Iterate: read the resulting goal state for each attempt, pick the winner, write it to the file, re-inspect.
6. If the proof requires a large decomposition (e.g., bidegree sectors, case splits), **pre-decompose into sub-lemmas with `have` statements** so each sub-goal is small (ideally ≤12 terms). Close each sub-lemma interactively via step 4.

**Theorem Quality Requirements:**
- Every theorem must encode actual physics — no tautologies (`1 = 1`, `x = x`)
- Hypotheses must be load-bearing, not vacuously satisfied
- Beware Lean's total division convention (`0/0 = 0`): add strengthened variants where κ > 0 or c_s ≠ 0 is genuinely used in the proof
- When in doubt, state the theorem in the strongest form possible

**Antipatterns (do NOT do these — every one has been documented to fail or corrupt sessions):**
- `set_option maxHeartbeats N` or `synthInstance.maxHeartbeats N` in any proof body (`theorem`, `lemma`, `example`, `def` with tactic-generated body). Heartbeat overrides in proofs indicate a proof-architecture problem, not a compute problem — decompose into `have` sub-lemmas. **Pipeline invariant #10.** (The `ExtractDeps.lean` metaprogram is exempt — see invariant #10 for the precise scope.)
- `ring` / `ring_nf` on non-commutative rings (`Uqsl2Aff`, `Uqsl3`, `RingQuot`-based types). Use `noncomm_ring` or explicit rewrites.
- Monolithic `simp` / `simp_rw` calls that try to expand and regroup 50+ terms in one pass. Always decompose via `have` sub-lemmas first.
- `simp_rw` with rules that can form a cycle (e.g., Serre relation in both directions) — leads to infinite loops.
- `match_scalars` at the wrong level of decomposition (when cancellation is inter-atom rather than per-atom) — produces unprovable `⊢ 1 = 0`.
- Blind iteration via `lake build` for hard proofs. The MCP loop is ~1000× faster and gives live goal state. If MCP is not yet installed, installing it is ALWAYS cheaper than grinding on `lake build`.

**Axiom Classification:** New axioms MUST have an entry in `AXIOM_METADATA` (in `src/core/constants.py`) with `eliminability` (eliminable/hard/unknown) and `reason` fields. This surfaces in the Proof Architecture dashboard tab and claims-reviewer agent.

**Gate (3a):** Either the proof closes interactively and `lake build` is clean for this theorem, OR the proof has been decomposed into sub-lemmas with thorough `PROVIDED SOLUTION` comments and is ready for Stage 3b.

### 3b. Sorry registration (only if 3a left residual gaps)

**Actions:**
- Register each remaining sorry stub in `src/core/aristotle_interface.py` as `SorryGap(filled=False)` with a precise `strategy_hint` that names the sub-lemmas, helper theorems, and coefficient identities needed
- Add `PROVIDED SOLUTION` comments inline at each `sorry` site, referencing any relevant `Lit-Search/Phase-5*/` deep research document by path
- Keep the `SORRY_GAPS` registry in sync: one entry per actual `sorry` in the source (not per "group" of sorries — Aristotle needs granular targets)

**Gate (3b):** `cd lean && lake build` compiles successfully (sorry warnings are expected, zero errors). `SORRY_GAPS` registry matches the lake build output exactly.

---

## Stage 4: ARISTOTLE (FALLBACK)

**Purpose:** Fill sorry gaps that Stage 3a's interactive MCP loop could not close. Also used for cross-cutting batch submissions in future phases where interactive iteration is impractical.

**When to use Stage 4:**
- Stage 3a's interactive MCP loop on `lean_multi_attempt` has been fully exhausted for the remaining sorries
- The remaining sorries have been pre-decomposed into sector/sub-lemma `have` targets (≤12 terms each) — Aristotle can handle granular targets much better than monolithic 50+ term goals
- Every sorry has a thorough `PROVIDED SOLUTION` comment referencing relevant deep research
- Registry in `src/core/aristotle_interface.py` is accurate (no stale `filled=False` entries for theorems that are actually filled)
- **User has explicitly authorized the submission.** Each Aristotle batch submits the whole project and takes ~1 day to return.

**When NOT to use Stage 4:**
- When Stage 3a hasn't been seriously attempted (MCP loop gives 1000× speedup vs. `lake build` iteration)
- When re-submitting a previously-failed batch without a **materially changed state** — Aristotle failing the same cubic and then being resubmitted on the same state produces the same failure. Insanity is doing the same thing and expecting different results.
- When some sorries in the batch are still monolithic (50+ terms) — decompose first via Stage 3a scaffolding, THEN submit

**Pre-requisite:** Read `docs/references/Theorm_Proving_Aristotle_Lean.md` before every Aristotle session. It covers Aristotle's capabilities, prompt strategies, and project-specific integration behavior.

### 4a. Submit

**One job at a time.** Every submission sends the entire Lean project — parallel jobs duplicate work. The script blocks submission if a job is already running.

**Priority batching:** When there are many sorry gaps across multiple modules, group them into priority batches and submit sequentially (highest priority first). Each batch should contain related modules so Aristotle can leverage shared context. Register all sorry gaps with priorities in `SORRY_GAPS` (in `aristotle_interface.py`) before submitting. See `docs/references/aristotle_batch_plan.md` for the current batch plan.

```bash
# Preview what would be submitted:
uv run python scripts/submit_to_aristotle.py --dry-run

# Submit with priority (1=highest, 3=lowest):
uv run python scripts/submit_to_aristotle.py --submit --priority 1

# For custom prompts targeting specific modules, use the CLI directly:
cd lean && source ../.env && export ARISTOTLE_API_KEY
uv run aristotle submit "Fill sorry gaps in [Module1.lean] and [Module2.lean]. [Strategy hints.]" \
  --project-dir . --priority 1
```

Do not pass `--integrate` at submission time — integration is a separate step (4c). Ensure every sorry theorem has a `PROVIDED SOLUTION` hint in its docstring before submitting.

### 4b. Monitor

```bash
# Source .env for the CLI key, then check status:
source .env && export ARISTOTLE_API_KEY && uv run aristotle list --limit 5
```

Move on to non-dependent work while waiting. Do NOT submit additional jobs while one is running.

### 4c. Retrieve and Review

Retrieve first, review the diff, then integrate selectively.

```bash
# 1. Retrieve (no --integrate)
uv run python scripts/submit_to_aristotle.py --retrieve <UUID>

# 2. Review the diff
cat docs/aristotle_results/run_<timestamp>/diff.patch

# 3. If clean: re-run with --integrate
uv run python scripts/submit_to_aristotle.py --retrieve <UUID> --integrate

# 3. If regressions: manually copy only the filled proof blocks
```

See the [Aristotle reference doc](references/Theorm_Proving_Aristotle_Lean.md#project-integration) for details on `--integrate` behavior and regression risks.

### 4d. Resume OUT_OF_BUDGET runs

```bash
uv run python scripts/submit_to_aristotle.py --resume <UUID>
```

### 4e. Verify quality

- Does the proof exercise the hypotheses? Check for trivial proofs (total division, vacuous satisfaction).
- `lake build` — zero errors, sorry warnings only for genuinely unfilled gaps.
- If strengthening is needed: stop, explain to user, prepare correction.

### 4f. Register

- Update `SorryGap(filled=True)` in `src/core/aristotle_interface.py`
- Add run UUID to `ARISTOTLE_THEOREMS` in `src/core/constants.py`
- Update `formulas.py` docstrings: `Aristotle: pending` → `Aristotle: <run_id>`

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

**Checks (16 total):**
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
15. `parameter_provenance` — All parameters have verified provenance
16. `graph_integrity` — Knowledge graph integrity: orphans, conflicts, broken chains, axiom classification, PG+AGE sync

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
- Run LLM figure review agent (`physics-qa:figure-reviewer` plugin agent)
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

**Paper Claims Review (`physics-qa:claims-reviewer` — runs after Stage 10, before Stage 11):**

After writing or updating a paper draft, run the paper claims reviewer agent
(`physics-qa:claims-reviewer` plugin). This is analogous to the figure reviewer
(`physics-qa:figure-reviewer`) in Stage 9 — an LLM sweep that checks content
accuracy, not just formatting.

The agent reads each paper's `.tex` and cross-references against:
1. `PAPER_DEPENDENCIES` in `provenance.py` — declared formulas, Lean modules, key claims
2. `formulas.py` — recomputes numerical values and compares to paper tables
3. `PARAMETER_PROVENANCE` — checks all referenced parameters are verified
4. `CITATION_REGISTRY` — checks all cited papers have valid DOIs
5. `ARISTOTLE_THEOREMS` — checks "formally verified" claims match actual proof status

The agent reports:
- **FAIL**: numerical value in paper disagrees with computation by >0.5%
- **FAIL**: "formally verified" claim but theorem not in Lean or has sorry
- **FAIL**: cited reference DOI doesn't resolve or is wrong paper
- **WARN**: parameter referenced but not human-verified (blocks submission)
- **WARN**: qualitative claim without computed support
- **PASS**: claim verified against computation pipeline

Results saved to `papers/paper<N>/claims_review.json`.

**Gate:** `validate.py --check paper_provenance` passes for this paper
AND paper claims review has zero FAIL.

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

**Actions — run the automated pipeline, then update content-sensitive docs:**

```bash
# Step 1: Run validate.py (triggers lean_deps.json refresh automatically if stale)
uv run python scripts/validate.py

# Step 2: Generate counts.json + counts.tex (single source of truth)
uv run python scripts/update_counts.py
```

**Lean dependency extraction** is managed by `scripts/extract_lean_deps.py`, which:
- Hashes all `.lean` source files to detect changes
- Only re-runs `ExtractDeps.lean` when the hash differs from cached
- Writes output to `lean/lean_deps.json` with a hash file at `lean/lean_deps.json.hash`
- Is called automatically by `validate.py --check graph_integrity`

`docs/counts.json` is the authoritative source for ALL project counts.
`docs/counts.tex` provides LaTeX macros (\totaltheorems, \sorrycount, etc.) for papers.

**Content-sensitive docs (NOT automated — require human/LLM judgment):**

| Category | Files | What to update |
|----------|-------|---------------|
| **Code** | `src/__init__.py` | Phase summary (not counts — use counts.json) |
| **Code** | `src/core/constants.py` | Phase summary in header |
| **Root** | `README.MD` | Project tree, architecture description |
| **Root** | `SK_EFT_Hawking_Inventory.md` | Module descriptions, section content |
| **Root** | `CLAUDE.md` (repo root) | Architecture, conventions |
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

## Stage 13: ADVERSARIAL REVIEW

**Purpose:** Catch every failure class that Stages 1–12 cannot detect by construction — wrong-target citations, parameter drift from primary sources, Lean theorems cited as "verified" but discharged as placeholders, cross-paper contradictions, narrative overclaims, and production-run claims without backing evidence.

This stage exists because the April 2026 external adversarial-review round found a 13-dimension problem space that slipped through the 12-stage internal pipeline. The detail is in `docs/READINESS_GATES.md` — the canonical definition of the 11 readiness gates this stage backstops.

**Actions:**

1. Ensure Stages 1–12 are all green (`validate.py` passes). Stage 13 is meaningful only on a codebase that passes its own internal checks.
2. Invoke the `adversarial-reviewer` agent (`.claude/plugins/physics-qa/agents/adversarial-reviewer.md`) with the target paper key:
   > "Run the adversarial-reviewer on `paper<N>_<name>`"
3. The agent runs in a fresh-context Opus window and works 8 finding-classes in order (one per readiness gate). It emits a structured markdown report at:
   ```
   papers/AutomatedReviews/{YYYY-MM-DD-HHMM}-internal-adversarial/{paper_key}.md
   ```
4. Findings are auto-picked up by `scripts/build_graph.extract_review_finding_nodes` on next graph build — each finding becomes a `ReviewFinding` node with `FLAGS` edges to the paper; `BLOCKER` findings also flip the affected `ReadinessGate` to `blocked`.
5. Re-run `validate.py --check readiness_submission_gate` — the paper's aggregate state surfaces in the summary (green / yellow / red).

**Rules:**

- One agent invocation = one paper per report file. Do not batch across papers.
- Citation findings of any kind are **BLOCKER** at submission time, no exceptions. The `docs/citation_verifications.jsonl` cache + `scripts/citation_cache.py` helpers amortize re-fetch cost across rounds so every arXiv / DOI resolve gets verified at most once per 90 days per (bibkey, bibitem_hash) pair.
- Findings marked `fixed` by the author must pass a **re-invocation** showing no new BLOCKERs in the affected class before the gate flips back to `passed`. "The author says it's fixed" is not evidence; the re-run is evidence.
- If the agent surfaces a systemic finding (a failure class that affects multiple papers or indicates a pipeline gap), it emits a `## QI Candidate` section — that feeds Stage 14.

**Gate:** Every paper marked "submission-pending" has ZERO `BLOCKER` findings under `papers/AutomatedReviews/` with `status != fixed`. `validate.py --check readiness_submission_gate` shows no RED papers among submission candidates.

**Do NOT use Stage 13 to fix issues.** The agent output is findings-only. The author fixes; the author re-invokes. Separation of the fix-and-review roles is the whole reason the agent exists.

---

## Stage 14: META-PROCESS QUALITY IMPROVEMENT (advisory)

**Purpose:** Surface systemic issues — recurring failure classes across papers or evidence of pipeline gaps — and track them as improvement items with owners and deadlines. Stage 13 catches paper-level issues; Stage 14 catches process-level issues.

**Actions:**

1. Scan `ReviewFinding` nodes across all papers for patterns: findings with the same `pattern_class` appearing in ≥2 papers, or findings that indicate a gate the pipeline can't enforce automatically.
2. Emit QI items to `docs/QI_REGISTER.md` (auto-generated). Each item carries: id, pattern summary, first_observed_date, occurrence_count, pipeline_stage_affected, owner, target_date, status, evidence_on_close.
3. User-facing report emitted to `docs/QI_REGISTER_{date}.md` on each Stage 14 run (timestamped snapshot).
4. Dashboard "Process Health" tab surfaces open QI items + trend of findings-per-category over time.

**Rules:**

- Stage 14 is **advisory** — it never blocks submission. Its purpose is feeding pipeline improvements back into Phase 5v+ work.
- If a QI item's `severity == critical` (indicates a gate that allowed a correctness violation to ship), the item gets escalated to a Phase 5w+ remediation wave. Example: the April round's 13-dimension problem space is captured as the QI register's seed data.
- Closed QI items have an `evidence_on_close` field pointing to the commit or wave that remediated the pattern.

**Gate (advisory, no blocking):** QI register exists, is regenerated on Stage 14 runs, and is linked from the dashboard Process Health tab.

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

9. **Placeholder theorems are non-load-bearing.** Theorems proved as `True := trivial` encode no mathematical content and MUST NOT be referenced by any other proof, formula, or paper claim. They are documentation markers only. Tracked in `PLACEHOLDER_THEOREMS` in `constants.py`. Substantive theorem count = total - placeholders. Paper claims MUST cite substantive count, not total.

10. **No heartbeat overrides in proof bodies.** No `set_option maxHeartbeats` or `set_option synthInstance.maxHeartbeats` in any `theorem`, `lemma`, `example`, or `def`/`noncomputable def` whose body is produced by tactics. Proof bodies that hit the heartbeat limit are evidence that the proof architecture is wrong — the fix is `have` sub-lemma decomposition, not raising the budget. Expensive typeclass synthesis is resolved via `@[local instance]` caching, not heartbeat increases.

    **Exception — metaprograms.** Lean metaprograms whose work is intrinsically O(project size) may set unlimited heartbeats in their local `CoreM` / `MetaM` options when no proof-decomposition equivalent exists. The distinguishing test: the work scales with **number of declarations processed**, not with **complexity of a single proof goal**. A proof can always be decomposed into smaller goals; an environment walker cannot be decomposed into "walk fewer declarations" because the requirement is that it walks all of them.

    `ExtractDeps.lean` is currently the only such file in this project. It walks all 2,237+ declarations in the `SKEFTHawking` namespace, runs `collectAxioms` on each to compute transitive axiom closures, and pretty-prints every type signature — total work is O(declarations × per-declaration metadata cost), intrinsically exceeding the default 200K heartbeat budget. Its `maxHeartbeats := 0` lives in the `Lean.Core.Context` for its own `IO Unit` main function and does not leak to any theorem or proof in the project (it is a separate `lean_exe`, not part of `lean_lib SKEFTHawking`).

    Any new file claiming this exception must: (a) be a metaprogram, not contain tactic-generated proofs; (b) demonstrate that its work is intrinsically project-size-bound; (c) justify why no decomposition is possible. If uncertain, assume the rule applies and do not add the override.

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
uv run python scripts/validate.py                    # All 16 checks
uv run python scripts/review_figures.py              # Generate figures + structural checks
cd lean && lake build                                 # Lean build

# Aristotle (read docs/references/Theorm_Proving_Aristotle_Lean.md first!)
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
