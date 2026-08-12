# Wave Execution Pipeline

**The authoritative process for executing any wave of work in the SK-EFT Hawking project.**

Every wave — new physics, extended formalization, experimental predictions — runs Stages 1 through
14 in order. Each stage has a gate that must pass before the next begins. Skipping or reordering
stages lets errors propagate downstream, where they cost more to find.

This document states the rules. **Why** a rule exists lives in
[WAVE_PIPELINE_RATIONALE.md](WAVE_PIPELINE_RATIONALE.md) — read it when a rule looks arbitrary or
you are considering an exception. You do not need it to follow the pipeline.

**Stage numbers are load-bearing and must never be renumbered.** They are consumed by
`paper_tables/sources.py`, `gate_precheck.py`, the `stage{9,10,13}_status` metadata fields, and
every document citing a stage by number. New review steps become sub-gates of an existing stage,
never new numbers.

---

## Pipeline Overview

```
Stage 1:  CONSTANTS & PARAMETERS           → Gate: imports succeed, provenance verified
Stage 2:  FORMULAS                         → Gate: every function has a Lean ref
Stage 3a: LEAN — INTERACTIVE MCP LOOP      → Gate: proof closes OR decomposed to sector stubs
Stage 3b: LEAN — SORRY REGISTRATION        → Gate: lake build compiles, SORRY_GAPS accurate
Stage 4:  ARISTOTLE (FALLBACK)             → Gate: residual sorrys filled, gauntlet passed
Stage 5:  LEAN BUILD VERIFICATION          → Gate: zero sorry, counts match
Stage 6:  PYTHON TESTS                     → Gate: all tests pass
Stage 7:  CROSS-LAYER VALIDATION           → Gate: validate.py all checks pass
Stage 8:  VISUALIZATIONS                   → Gate: all PNGs generated, figure adequacy met
Stage 9:  FIGURE REVIEW                    → Gate: LLM review all PASS, verdict recorded
Stage 10: PAPER DRAFT                      → Gate: provenance + claims + length + read-through
Stage 11: NOTEBOOKS                        → Gate: notebook_exec + viz_consistency pass
Stage 12: DOCUMENT SYNC                    → Gate: full validate.py passes, counts consistent
Stage 13: ADVERSARIAL REVIEW               → Gate: fresh-context sweep shows zero BLOCKERs
Stage 14: META-PROCESS QI                  → Advisory: systemic findings logged
```

Most proofs close in **3a** (interactive MCP). **Stage 4 (Aristotle) is a fallback**, for sorries
that survive 3a with decomposition. See CLAUDE.md, "Lean development — MCP-first loop".

---

## Stage 1: CONSTANTS & PARAMETERS

**Purpose:** Establish the single source of truth for all physics values.

**Actions:**
- Add physical constants to `src/core/constants.py`; experimental parameters to `EXPERIMENTS`
- Add Aristotle run IDs to `ARISTOTLE_THEOREMS` as they are obtained (Stage 4)

**Rules:**
- `constants.py` is the ONLY place experimental parameters live. No other file hardcodes them.
- Every value in `EXPERIMENTS`, `ATOMS`, and `POLARITON_PLATFORMS` has an entry in
  `PARAMETER_PROVENANCE` (`src/core/provenance.py`) specifying value, unit, tier, source, detail,
  `llm_verified_date`, `human_verified_date`.
- Tier is one of `MEASURED`, `EXTRACTED`, `DERIVED`, `PROJECTED`, `THEORETICAL`. `PROJECTED`
  parameters are estimates for experiments not yet performed and must be labeled as such.
- Parameters from deep research enter with `llm_verified_date: None` and must be LLM-verified
  against the primary source before this gate passes. See
  [Deep Research Reconciliation](#deep-research-reconciliation-protocol).

**New bibitems.** Run `scripts/extract_missing_bibkeys.py`, then
`scripts/back_fill_primary_sources.py --fetch`, then `scripts/promote_primary_sources.py`. See
Invariant 11.

**Bundle target.** A wave producing paper-shaped output (new draft, section addition, notebook
companion) identifies its target bundle here — one of the codes in `validate.BUNDLE_CODES`, the
roster's single source of truth — and records it in `docs/PAPER_DRAFT_MAPPING.md` at Stage 12.
See Invariant 14.

**Gate:** `python -c "from src.core.constants import *"` succeeds **AND**
`validate.py --check parameter_provenance` passes (all LLM-verified, zero MISSING, zero NULL).

**Submission gate (not Stage 1):** `validate.py --check parameter_provenance --strict` — all
parameters human-verified. Checked before arXiv/journal submission.

---

## Stage 2: FORMULAS

**Purpose:** Implement canonical physics formulas with provenance.

**Actions:** Add implementations to `src/core/formulas.py`. Each docstring contains:
- the mathematical formula in plain text
- `Lean: <theorem_name>` — exact name of a real, non-placeholder Lean declaration
- `Aristotle: <run_id>` — the proving run, or `manual`, or `pending`
- `Source: <citation>` — paper citation plus equation number for formulas from published work
  (e.g. `Corley & Jacobson, PRD 54, 1568 (1996), Eq. (4.2)`). Pure math identities and
  project-original results may omit it.

**Rules:**
- `formulas.py` is the ONLY place physics formulas live. Domain modules import from it and never
  reimplement.
- Every function references a Lean theorem. No unformalized formulas.

**Gate:** Every function has a `Lean:` reference that resolves to a real declaration in
`lean/SKEFTHawking/*.lean`.

---

## Stage 3: LEAN THEOREMS

**Purpose:** Formalize physics results as machine-checkable proofs.

### 3a. Statement + interactive proof attempt

Write statements in `lean/SKEFTHawking/<Module>.lean` with `sorry` placeholders and add
`import SKEFTHawking.<Module>` to `lean/SKEFTHawking.lean`. **Make a serious interactive attempt
before leaving any sorry in place.**

**Required loop per sorry:**
1. `lean_file_outline` — orient in the file
2. `lean_goal` at the `sorry` — read the actual goal state
3. Identify the strategy from relevant deep research in `Lit-Search/Phase-*/`. For non-trivial
   proofs (quantum groups, tensor products, bidegree decompositions), **read the research document
   directly and in full.** Agent-summarized research loses tactic-level detail and has caused
   session failures.
4. `lean_multi_attempt` with 4–6 candidate tactic sequences. Start simple (`noncomm_ring`, `abel`,
   `aesop`); escalate to explicit rewrite chains only if needed.
5. Read the resulting goal state, pick the winner, write it, re-inspect.
6. For large decompositions, **pre-decompose into `have` sub-lemmas** so each sub-goal is small
   (ideally ≤12 terms), and close each interactively.

**Theorem quality:**
- Every theorem encodes actual physics. No tautologies.
- Hypotheses are load-bearing, not vacuously satisfied.
- Lean's total division convention (`0/0 = 0`) means a theorem can hold vacuously; add
  strengthened variants where `κ > 0` or `c_s ≠ 0` is genuinely used.
- State the theorem in the strongest form available.

**Preemptive-strengthening checklist — run on every statement before writing it.** If you cannot
satisfy all five, fix the statement first.

1. **Bundle redundancy.** "If I drop any conjunct, does it still mean the same thing?" If yes, drop
   it. A bundle whose conjuncts are algebraically equivalent is one theorem dressed as three.
2. **Quantitative connection.** If the statement mentions a constant declared elsewhere
   (`MICROSCOPE_BOUND`, `LIGO_TAU`), the numerical relationship belongs in the theorem body. Write
   the `norm_num`-backed comparison
   (`vestigial_phase_eta_violates_microscope_bound : (1.0 : ℝ) > 1.0e-15`), not a qualitative
   `*_violates_*` claim alone. The numerical assertion is what makes it falsifiable.
3. **Cross-module bridge integrity.** If the docstring references another module's theorem,
   `import` that module and *call* the theorem in the body. An uncalled cross-reference rots.
4. **Trivial discharge.** Could this be closed by `rfl`, `decide`, or `0 ≤ C` for any positive `C`?
   If so, either the substantive content is elsewhere or you are shipping a tautology.
5. **Defining the conclusion.** If defining the function as the obvious target makes the theorem
   trivial, the substantive load is in the *definition*. Say so in the docstring, and either push
   the content elsewhere or commit to a concrete model and document the assumption.

A ruthless post-wave strengthening review remains mandatory; the checklist reduces its cost but
does not replace it.

**Antipatterns — do not do these:**
- `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` in any proof body (Invariant 10)
- `ring` / `ring_nf` on non-commutative rings (`Uqsl2Aff`, `Uqsl3`, `RingQuot`-based types) — use
  `noncomm_ring` or explicit rewrites
- monolithic `simp` / `simp_rw` over 50+ terms; `simp_rw` with rules that can cycle
- `match_scalars` at the wrong decomposition level
- blind `lake build` iteration on hard proofs — use the MCP loop

**New axioms require explicit user sign-off** and an `AXIOM_METADATA` entry. See Invariant 15.

**Gate (3a):** the proof closes and `lake build` is clean for this theorem, OR it is decomposed
into sub-lemmas with thorough `PROVIDED SOLUTION` comments and is ready for 3b.

### 3b. Sorry registration (only if 3a left gaps)

- Register each remaining sorry in `src/core/aristotle_interface.py` as `SorryGap(filled=False)`
  with a `strategy_hint` naming the sub-lemmas, helper theorems and coefficient identities needed
- Add `PROVIDED SOLUTION` comments at each `sorry` site, referencing any relevant
  `Lit-Search/Phase-*/` document by path
- Keep `SORRY_GAPS` at one entry per actual `sorry` — Aristotle needs granular targets

**Gate (3b):** `cd lean && lake build` compiles (sorry warnings expected, zero errors), and
`SORRY_GAPS` matches the build output exactly.

---

## Stage 4: ARISTOTLE (FALLBACK)

**Purpose:** Fill sorry gaps that Stage 3a could not close.

Stage 4 uses **safe partial submission plus verify-then-graft** (ADR-006). All steps use the
subcommand CLI `scripts/submit_to_aristotle.py`, a thin wrapper over `src/core/aristotle_submit.py`.
The pre-ADR-006 flag interface is archived and **must not be re-enabled**.

**Pre-requisite:** read `docs/references/Theorm_Proving_Aristotle_Lean.md` before every session.

**Use Stage 4 when:**
- the 3a interactive loop is fully exhausted for the remaining sorries
- those sorries are pre-decomposed into sector/sub-lemma targets (≤12 terms each)
- every sorry has a thorough `PROVIDED SOLUTION` comment
- **the user has explicitly authorized the submission** (enforced by `--yes-i-authorize`)

**Do NOT use Stage 4 when:** 3a has not been seriously attempted; a previously-failed target has
no materially changed state (manifest dedup refuses an identical closure without `--force`); or
some sorries are still monolithic — decompose first.

Submission is **async and non-blocking**, which is what lets Stage 4 run inside a `/goal` loop
without the loop blocking on Aristotle's return.

### 4a. Stage + submit

Submission uploads ONLY the target's transitive `SKEFTHawking` import closure, never the full
project. A target is a module (`SKEFTHawking.Foo`), a path, a `*.lean` name, or a bare leaf.

```bash
uv run python scripts/submit_to_aristotle.py sorries [<target>...]        # current gaps
uv run python scripts/submit_to_aristotle.py stage <target>...            # stage, no submit
uv run python scripts/submit_to_aristotle.py submit <target>... --yes-i-authorize
```

### 4b. Monitor

```bash
uv run python scripts/submit_to_aristotle.py status
source .env && export ARISTOTLE_API_KEY && uv run aristotle list --limit 5
```

### 4c. Retrieve and review

```bash
uv run python scripts/submit_to_aristotle.py retrieve <job_id>            # no integration
uv run python scripts/submit_to_aristotle.py graft <extracted_dir> <target>...   # review diff
```

### 4d. Graft + verify (auto-revert)

```bash
uv run python scripts/submit_to_aristotle.py graft <extracted_dir> <target>... --apply
```

`--apply` grafts ONLY the target file(s), refusing if Aristotle touched any non-target closure
file, then runs the **verification gauntlet**: `lake build` (zero sorry) → fresh ExtractDeps →
kernel-purity/axiom audit of the target declarations → `validate.py`
(`axiom_closure_allowlist`, `native_decide_regression`) → tests. It **keeps the graft on pass and
auto-reverts on failure**, so the tree is never left worse than found. Standalone gauntlet:
`... verify <target>...`.

The proof must exercise its hypotheses (no vacuous or total-division proofs) and be kernel-pure:
no new `sorry`, no `native_decide` regression, no un-signed-off axiom.

### 4e. Register (only after a graft is kept)

- Add the run UUID to `ARISTOTLE_THEOREMS` (`src/core/constants.py`) and bump the
  `assert ARISTOTLE_PROVED_COUNT == <N>` in that same file, in the same commit. **That assert is
  the only pin — do not add a second.** A wrong count raises `AssertionError` from the first
  check body that imports `constants` (checks import it lazily, and the runner catches), so it
  surfaces as a check-level failure, not an import error.
- Set `SorryGap(filled=True)` in `src/core/aristotle_interface.py` — append or update, never
  delete; the registry is provenance
- Run `scripts/update_counts.py`; `scripts/aristotle_usage_by_bundle.py` re-derives per-bundle
  disclosure; reconcile `ATTRIBUTION.md`
- Update `formulas.py` docstrings: `Aristotle: pending` → `Aristotle: <run_id>`

**Gate:** all sorry gaps filled or documented as manual; `lake build` clean with zero sorry; the
verification gauntlet passed.

---

## Stage 5: LEAN BUILD VERIFICATION

**Purpose:** Confirm the formalization is complete and counts are consistent.

```bash
cd lean
lake build                               # library only; must complete clean
lake build SKEFTHawking.ExtractDeps      # + ExtractDeps.olean (graph_integrity, counts_fresh)

# Trustworthy but slow clean baseline (after toolchain or structural changes):
rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps
```

**Use exactly that rebuild command.** A bare `lake build` leaves `ExtractDeps.olean` missing and
breaks `graph_integrity` and `counts_fresh`; `lake build extractDeps` fails the macOS
argument-length link limit. Clean rebuilds are rare — reserve them for pin bumps and structural
refactors, and use incremental `lake build` otherwise.

Verify the total theorem count matches the `constants.py` header, and that
`ARISTOTLE_THEOREMS` count plus manual count equals the total.

**Gate:** zero sorry, zero errors, theorem count matches documentation exactly.

---

## Stage 6: PYTHON TESTS

**Purpose:** Validate all computations, including physical reasonableness.

Write tests in `tests/test_<domain>.py` for every new `src/` module, covering:
- **Correctness** — computed values match expected results
- **Edge cases** — boundary conditions, zero inputs, limiting cases
- **Physical bounds** — e.g. `assert 0 < delta_diss < 1` for every perturbative correction
- **Cross-module consistency** — the same quantity from different modules agrees
- **Sanity bounds** — e.g. if δ < 10⁻³ then shots_needed > 10⁴

```bash
uv run python -m pytest -q          # both suites: repo tests + skeft-qa plugin guards
uv run python -m pytest tests/ -v   # repo only
```

**Gate:** all tests pass; every `src/` module has a corresponding test file.

---

## Stage 7: CROSS-LAYER VALIDATION

**Purpose:** Verify consistency across Python, Lean, notebooks and papers.

```bash
uv run python scripts/validate.py          # --list enumerates the authoritative roster
```

**`validate.py --list` is the authoritative roster** of checks; do not maintain a second list.
The core cross-layer checks are `formulas`, `numerical`, `identities`, `paper_table`, `theorems`,
`notebooks`, `lean_source`, `cgl_fdr`, `lean_build`, `viz_consistency`, `notebook_exec`,
`physical_bounds`, `cross_path_consistency`, `paper_provenance`, `parameter_provenance` and
`graph_integrity`. The suite is substantially larger, covering the bundle, citation and freshness
families as well as the substrate gates below.

**Substrate integrity gates (ADR-004) — semantic presence, not merely syntactic:**

| Check | Enforces |
|---|---|
| `formula_grounding` | every `formulas.py` `Lean:` ref resolves to a real, non-placeholder theorem (Inv. 4) |
| `proxy_body_audit` | no structurally-named theorem is closed by a trivial defining-the-conclusion body, unless disclosed in `MODELING_ASSUMPTION_THEOREMS` |
| `tracked_hypothesis_ledger` | every consumed tracked-hypothesis Prop is registered (Inv. 16) |
| `tracked_hypotheses_fresh` | `PERMANENT_TRACKED_HYPOTHESES.md` matches the registry (auto-regenerates) |
| `placeholder_not_cited` | no paper presents a placeholder as formally verified (Inv. 9) |
| `nogo_substrate_integrity` | every provably-false no-go has a live, kernel-pure, non-vacuous backing theorem (Inv. 17) |
| `native_decide_regression` | the `native_decide` declaration closure does not grow past `NATIVE_DECIDE_DECL_CLOSURE_CEILING` (ADR-002; also Stage 5) |

**Gate:** ALL checks pass, not merely advisory warnings. Report archived to
`docs/validation/reports/`.

---

## Stage 8: VISUALIZATIONS

**Purpose:** Create publication-quality figures derived from validated computations.

- Implement figure functions in `src/core/visualizations.py` as `def fig_<name>() -> go.Figure`
- Register in `scripts/review_figures.py` (`FigureSpec` + `func_map`)

**Rules:**
- `visualizations.py` is the ONLY place figure functions live
- Figures import data from `formulas.py` / `constants.py` / domain modules. **Never hardcode
  physics values in a figure function.**
- Use the `COLORS` dict; never hardcode hex values. Plotly only, colorblind-accessible blue/amber.
- `stakeholder=True` selects the stakeholder variant

```bash
uv run python scripts/review_figures.py
```

**Figure adequacy.** A bundle must carry the figures its tier owes a reader:
`validate.py --check bundle_figure_adequacy`. A figure that is planned but not yet drawn is
declared with `\figuredeferred{id}{reason}`, never omitted silently.

**Gate:** all PNGs generated with zero failures; all registered figures have functions; figure
adequacy met.

---

## Stage 9: FIGURE REVIEW

**Purpose:** Catch rendering issues that automated tests cannot detect.

- Run the `skeft-qa:figure-reviewer` agent
- Fix ALL issues flagged FAIL or MINOR in `visualizations.py`, regenerate, re-review until all PASS
- Report saved to `figures/figure_review_report.json`

**Record the verdict with the script, never by hand:**

```bash
uv run python scripts/record_review.py --bundle <X> --stage 9 --verdict green --doc <report>
```

**Gate:** all figures PASS. No FAIL, no MINOR remaining, verdict recorded.

---

## Stage 10: PAPER DRAFT

**Purpose:** Write the paper with full provenance for every claim.

**"Stage 10" names the whole stage — drafting and its review sub-gates.** The stage does not close
until they are clean. There is no Stage 10a and no renumbering.

**Two paradigms:**
- **Phase ≤ 6X** (per-paper drafts in `papers/paperN_*/`): the actions below are canonical.
- **Phase 7+** (bundle drafts in `papers/<bundle>/`): Stage 10 is implemented by
  `docs/BUNDLE_LIFT_PROCEDURE.md`, the canonical 14-step lift procedure. The actions below remain
  the substrate it draws from. Late-arriving Phase 6X waves are absorbed via
  `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` (Stages A–G, branches D.0–D.4).

**Actions:**
- Copy validated PNGs to the paper's `figures/`; use `\includegraphics`, never `\fbox` placeholders
- Every numerical claim traces to `formulas.py` or `constants.py`
- Every "formally verified" claim cites specific Lean theorem names; every Aristotle reference
  includes its run ID
- Qualitative claims (feasibility, detectability) are supported by computed quantities
- No hardcoded numbers in the `.tex` that are not also in the computation pipeline
- Standard phrasing for a verification claim: "X theorems in `<Module>.lean`, verified by
  `lake build` (zero sorry). Z filled by the Aristotle automated prover [run IDs]."

**Drafting guidance** is the `skeft-qa:paper-authoring` skill. It and the `skeft-qa:prose-reviewer` agent
read the same `references/prohibited-patterns.md`, so a rule cannot mean one thing while writing
and another while reviewing.

Draft either in-context or by dispatching `skeft-qa:paper-drafter`, one agent per **disjoint**
section, each with a brief. The lead owns the outline, the argument's spine and integration. A
drafted section that cites, quotes **or characterizes** prior work is written against that work
**read first** — the full text of every section, table and equation carrying the claim being made,
never an abstract in place of one. No layer below catches misrepresented prior art, because each
checks that a source resolves, never that the prose is faithful to it. This outranks the brief: a
brief that asks for a section faster than the reading allows does not license drafting ahead of it.

### Sub-gate: read-through (runs first)

The `skeft-qa:prose-reviewer` agent reads the draft start to finish as a referee at its named venue, and
returns a restructuring instruction. It runs at `BUNDLE_LIFT_PROCEDURE.md` §7.5 — **before the
claims review and before Stage 9.**

### Sub-gate: claims review

Run `skeft-qa:claims-reviewer`. It cross-references the `.tex` against, by source file:

| source | registries read |
|---|---|
| `src/core/formulas.py` | the canonical evaluators, for recomputation |
| `src/core/constants.py` | `ARISTOTLE_THEOREMS`, `PLACEHOLDER_THEOREMS`, `HYPOTHESIS_REGISTRY`, `AXIOM_METADATA`, `EXPERIMENTS` |
| `src/core/provenance.py` | `PARAMETER_PROVENANCE`, `PAPER_DEPENDENCIES` |
| `src/core/citations.py` | `CITATION_REGISTRY` |
| `lean/lean_deps.json` | live declaration registry (theorem-name resolution) |

Listed by file, so that adding a registry the reviewer reads means adding it to that file's
row — not deciding whether the file is already "covered".

- **FAIL** — a numerical value disagrees with computation by >0.5% (Class IA)
- **FAIL** — a "formally verified" claim whose theorem is missing or has a `sorry` (Class TN)
- **FAIL** — a "formally verified" claim citing a **placeholder** theorem, or a result presented as
  kernel-verified that is only a concrete-instance or statement-level stub (Invariant 9; Class PC,
  keyed on `PLACEHOLDER_THEOREMS`)
- **FAIL** — a cited DOI that does not resolve, or resolves to the wrong paper
- **FAIL** — a toolchain pin quoted in prose that disagrees with `lean-toolchain` / `lakefile.toml`
  (Class TP)
- **FAIL** — a tracked hypothesis carried by a cited result but not disclosed in the draft
  (Class HD, keyed on `HYPOTHESIS_REGISTRY`)
- **FAIL** — a prose cardinality that disagrees with the structured object it describes (Class SD)
- **WARN** — a parameter referenced but not human-verified (blocks submission)
- **WARN** — a qualitative claim without computed support

Results saved to `papers/<key>/claims_review.json`.

### Reader-facing voice

Two prohibitions apply to every draft, both deterministic and both enforced:

- **No em-dash in prose a reader will see** (`bundle_prose_em_dash_free`). The target is zero.
  Removing one is a *rewrite*, not a substitution. **`--` is a different character and is
  mandatory** (`Bose--Einstein`, `Schwinger--Keldysh`, page ranges); the check cannot see a broken
  en-dash, so that rule lives in the authoring reference.
- **A fix may not narrate itself** (`bundle_reader_facing_voice`). The manuscript states what is
  true. It does not report what an earlier draft said, when it was corrected, or which review round
  caught it. That history belongs in `change_log.md` and the supersession ledger.

Everything else about prose — length, structure, whether the argument carries — belongs to the
read-through reviewer, not to a check.

### Manuscript length

A bundle declares the size its venue requires in `bundle_metadata.json.length_target` (schema:
`docs/BUNDLE_DIRECTORY_SCHEMA.md`), and `bundle_manuscript_length` measures the **compiled**
article against it. Both bounds are load-bearing: the ceiling catches a letter that became a
monograph, the floor catches a container declared as a deep paper whose content is a letter.

`length_target: null` is legitimate for a bundle whose venue is still open, and reads
**UNMEASURED, never PASS** — as does a draft with no compiled PDF, or one whose PDF is older than
its own input closure. Re-targeting a bundle is an edit to that field and its `source`: the target
is data with provenance, not a constant.

**Gate:** `validate.py --check paper_provenance` passes **AND** claims review has zero FAIL
**AND** the read-through's restructuring instruction is resolved **AND**
`--check bundle_manuscript_length` reports the bundle inside its declared band, or records by name
why it could not be measured.

---

## Stage 11: NOTEBOOKS

**Purpose:** Create reproducible computational narratives.

- **Technical notebook** mirrors paper structure; **stakeholder notebook** uses accessible language.
  Both import all physics from `src/`.
- Tag figure cells `# viz-ref: fig_<name>` matching the `visualizations.py` function
- Import `COLORS` from `src.core.visualizations`, not `src.core.constants`
- No inline physics redefinition; no evaluative print statements in code cells (commentary goes in
  markdown); narrative text must agree with the computed values displayed

**Naming:** `Phase<N><letter>_<Topic>_Technical.ipynb` / `_Stakeholder.ipynb` — for example
`Phase3b_GaugeErasure_Technical.ipynb`.

**Gate:** `validate.py --check notebook_exec` and `--check viz_consistency` pass.

---

## Stage 12: DOCUMENT SYNC

**Purpose:** Ensure all documentation reflects the current state.

```bash
uv run python scripts/validate.py           # refreshes lean_deps.json if stale
uv run python scripts/update_counts.py      # counts.json + counts.tex
uv run python scripts/render_paper_tables.py
```

Or run the whole mechanical sync in one command with the `skeft-qa:sync` skill.

`docs/counts.json` is authoritative for ALL project counts; `docs/counts.tex` provides the LaTeX
macros. Theorem censuses are author-written-scoped and must agree across every artifact that
publishes one — `validate.py --check theorem_census_agrees` enforces both that and the rule that
every `kind == "theorem"` filter goes through `validate_helpers.autogen_index`, the single owner
of "is this compiler-generated". Lean dependency extraction is managed by `scripts/extract_lean_deps.py`, which re-runs
`ExtractDeps.lean` only when the source hash changes. **Never delete `lean_deps.json.hash` to
force a refresh** — run `update_counts.py`.

**Paper tables.** Each paper with autogenerated tables declares its data sources in
`papers/<key>/tables.py` using the `Col` + `TABLES` spec format. `render_paper_tables.py` renders
each spec to `papers/<key>/tables/<spec_id>.tex`, and the paper body `\input{}`s it, so tabular
numerical claims are structurally fresh. `tables_fresh` auto-regenerates stale tables;
`numerical_literals` flags inline literals outside `\input{}` blocks.

To add a table: pick a row generator in `scripts/paper_tables/sources.py` (or add one), add the
spec entry, replace the inline rows in `paper_draft.tex` with `\input{tables/<spec_id>.tex}`
(keeping the `\begin{table}` caption envelope), and run
`render_paper_tables.py --paper <key>`.

**Content-sensitive documents require judgment and must stay in sync:**

| Category | File | What to update |
|---|---|---|
| Code | `src/__init__.py`, `src/core/constants.py` | phase summary in header (not counts) |
| Root | `README.md` | project tree, architecture description |
| Root | `SK_EFT_Hawking_Inventory.md` | module descriptions, section content |
| Root | `CLAUDE.md` | bootstrap map, Lean rules, invariants, conventions |
| Root | `../CLAUDE.md` (workspace) | workspace layout, public/private boundary |
| Docs | `docs/RESEARCH_STATUS_OVERVIEW.md` | proof chains, strategic situation |
| Stakeholder | `docs/stakeholder/companion_guide.md` | status table + content synthesis |
| Stakeholder | `docs/stakeholder/Phase<N>_Implications.md` | content for this phase |
| Stakeholder | `docs/stakeholder/Phase<N>_Strategic_Positioning.md` | content for this phase |
| Reference | `docs/Fluid-Based...Feasibility Study.md` | SK-EFT row in the validation table |
| Reference | `docs/Fluid-Based...Critical Review v3.md` | SK-EFT row in the evidence table |
| Inventory | `SK_EFT_Hawking_Inventory_Index.md` | counts table, section→update mapping |

**Content accuracy is the primary concern; count agreement is a secondary mechanical check.**
Physics descriptions must match the code, phase boundaries must match computed values, and
feasibility claims must be supported by calculations.

**Inventory maintenance.** Read `SK_EFT_Hawking_Inventory_Index.md` first to learn which sections a
given change touches. Then: run the Index's verification commands for ground truth → update the
Inventory's sections → update the Index's counts table and "Last synced" date → spot-check three
recently altered sections against the codebase.

Watch for: new modules absent from Section 1; new theorems missing from the Section 2 table; new
Aristotle runs missing from Section 3; new notebooks or papers missing from Sections 4–5; formula
changes absent from Section 10; and descriptions that still reference superseded behavior.

**Validation reports.** `docs/validation/reports/` is auto-generated and needs no maintenance.
`docs/validation/lean_quality_audit.md` holds manual audit snapshots — create a new one per wave,
never update an old one in place. `docs/validation/VALIDATION_REPORT.md` is deprecated, superseded
by `validate.py`, and kept only for historical reference.

**Gate:** full `validate.py` passes; manual spot-check of three count-sensitive files confirms
consistency.

---

## Stage 13: ADVERSARIAL REVIEW

**Purpose:** Catch the failure classes Stages 1–12 cannot detect by construction — wrong-target
citations, parameter drift, placeholder theorems cited as verified, cross-paper contradictions,
narrative overclaims, and production-run claims without backing evidence.

`docs/READINESS_GATES.md` is the canonical definition of the 11 readiness gates this stage
backstops.

**Actions:**

0. **Stages 9 and 10 must be GREEN first.** `scripts/record_review.py` refuses to record a
   Stage-13 green while either prerequisite is unfinished, and
   `validate.py --check bundle_reviewer_stage_ordering` catches a hand edit that bypasses it. A
   Stage-13 verdict also requires `--kind`; only `full-adversarial` earns a green.
0b. **A draft carrying an unresolved work marker may not be green.** Drafting with
   `% TODO:` notes is normal and permitted; recording a completed review over content the
   author has flagged as unwritten is not. `validate.py --check bundle_todo_free_before_green`
   enforces it, keyed on markers inside LaTeX comments only — `placeholder` in reader-facing
   prose is a disclosed technical term this pipeline *requires* drafts to name.
0c. **Compiler-trust debt must be disclosed and may not grow.** If a bundle's declared-apex
   closure contains `native_decide`, its draft has to say so;
   `validate.py --check bundle_native_decide_debt` enforces disclosure and ratchets the
   per-bundle count in `NATIVE_DECIDE_BUNDLE_DEBT` downward only. Zero is *asserted*, so a wave
   that routes compiler trust into a clean bundle fails here rather than at a referee.
1. Ensure Stages 1–12 are green. Stage 13 is meaningful only on a codebase passing its own checks.
2. Invoke the `skeft-qa:adversarial-reviewer` agent with the target key. It runs in a fresh context
   and works the finding classes in order, emitting
   `papers/AutomatedReviews/{YYYY-MM-DD-HHMM}-internal-adversarial/{key}.md`.
3. Findings are picked up by `scripts/build_graph.py`'s `extract_review_finding_nodes` on the next
   graph build.
   Each becomes a `ReviewFinding` node with `FLAGS` edges to the paper; `BLOCKER` findings flip the
   affected `ReadinessGate` to `blocked`.
4. Re-run `validate.py --check readiness_submission_gate`.

**Rules:**
- One invocation = one paper per report file. Do not batch across papers.
- **Citation findings of any kind are BLOCKER at submission time, no exceptions.**
- A finding marked `fixed` by the author must pass a **re-invocation** showing no new BLOCKERs in
  that class before the gate flips back to `passed`. "The author says it's fixed" is not evidence;
  the re-run is evidence.
- **A closure is recorded with `scripts/close_finding.py`, never by hand.** It mints the finding id
  with the same function the extractor uses, so a record naming no finding cannot be produced.
- **The closure bar applies at every severity**, not only blocking ones. `docs/READINESS_GATES.md`
  owns the contract — status is `open` until the ledger says otherwise, and what a record must
  carry. Read it there rather than here; one owner per fact.
- **Do NOT use Stage 13 to fix issues.** The output is findings-only. The author fixes, the author
  re-invokes. Separating the fix and review roles is the whole reason the agent exists.
- A systemic finding (a class affecting multiple papers, or a pipeline gap) is emitted as a
  `## QI Candidate` section, feeding Stage 14.

**Bundle-level review.** Stage 13 may be invoked at the bundle level. `skeft-qa:claims-reviewer`
and `skeft-qa:figure-reviewer` accept a `bundle_target` and execute the per-bundle profile from
`docs/agents/claims-reviewer-bundle-prompts.md`:

| Tier | Bundles | Profile |
|---|---|---|
| 0 | F | review-paper style: verify cited published claims against the citation cache |
| 1 | D1–D12 | intra-bundle consistency across lifted sections + cross-bundle bridge checks |
| 2 | L1–L3 | stand-alone PRL depth; do not penalize absent broader scope |
| 3 | I1–I3 | software/methodology: each worked case traces to a reproducible run ID or pinned counterexample |
| 4 | E1, E2 | lightweight letter review + device-parameter audit |

`scripts/review_runner.py --bundle <target> --prep-brief` emits the review-prep brief; the review
document goes to `papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md`. Aggregated readiness
is in `docs/BUNDLE_READINESS_HEATMAP.md` (regenerated by `scripts/bundle_readiness.py`);
cross-bundle consistency is enforced by
`validate.py --check bundle_consistency`; bundle source freshness by `--check
bundle_source_freshness`.

**Gate:** every paper marked submission-pending has ZERO `BLOCKER` findings with `status != fixed`,
and `--check readiness_submission_gate` shows no RED papers among submission candidates.

---

## Stage 14: META-PROCESS QUALITY IMPROVEMENT (advisory)

**Purpose:** Surface systemic issues — a failure class recurring across papers, or evidence of a
gap the pipeline cannot enforce. Stage 13 catches paper-level issues; Stage 14 catches
process-level ones.

**Actions:**
1. Scan `ReviewFinding` nodes for patterns: the same `pattern_class` in ≥2 papers, or findings
   indicating a gate that cannot be automated.
2. Emit QI items to `docs/QI_REGISTER.md`, each carrying id, pattern summary, first-observed date,
   occurrence count, pipeline stage affected, owner, target date, status, evidence on close.
3. Emit the timestamped snapshot `docs/QI_REGISTER_{date}.md`.
4. The dashboard "Process Health" tab surfaces open items and the findings-per-category trend.

**Rules:**
- Stage 14 is **advisory** and never blocks submission.
- A `severity == critical` item (a gate that allowed a correctness violation to ship) escalates to
  a remediation wave.
- Closed items carry `evidence_on_close` pointing to the commit or wave that remediated the pattern.

**Closure pathways.** A QI item closes by one or more of:

1. **Per-finding supersession** — every underlying `ReviewFinding` gets a record in
   `docs/review_finding_supersessions.json` flipping `meta.status` to `fixed` or `accepted`.
2. **Structural prevention** — a wave installs durable infrastructure that prevents the class from
   recurring. Recorded by moving the item to `## Closed Items` with `evidence_on_close` naming the
   new infrastructure.
3. **No-applicable-scope acceptance** — the finding's body is itself a PASS-verification or a scope
   disclosure, accepted via supersession with no content fix.

**Any class with a live generator may close ONLY via structural prevention.** This covers the
proof-substance and assumption-disclosure families (`qi-leanproofsubstance`,
`qi-assumptiondisclosure`, `qi-gate-5-self-audit-blind-spot-on-sibling-tautologies`, and any
successor whose pattern recurs in new modules as they ship). Per-finding supersession fixes the
catalogued instances and leaves the generator alive.

**The supersession ledger is append-only.** Never remove an entry from
`review_finding_supersessions.json`; `_introduced_by` and `superseded_by` preserve the audit trail.

⚠️ **One in-place edit is permitted, and was performed once (2026-08-12): re-keying a record whose
`finding_id` matches no minted node.** Such a record closes nothing — it is inert, indistinguishable
from absent — so correcting its key adds information rather than removing any, and the former key is
preserved in `notes`. Two candidates were **skipped** because their corrected key already carried a
record: the reader is last-wins, so re-keying onto an occupied id would have made one of the pair
silently do nothing. Records are otherwise written only by `scripts/close_finding.py`.

**Gate (advisory):** the QI register exists, is regenerated on Stage 14 runs, and is linked from
the dashboard.

---

## Pipeline Invariants

These hold at ALL times, not only at wave completion. **They are cited by number across the
codebase and must not be renumbered.**

1. **`formulas.py` is canonical.** The ONLY place physics formulas live. No domain module
   reimplements a formula.

2. **`constants.py` is canonical.** The ONLY place experimental parameters and the Aristotle
   registry live. No other file hardcodes physical constants.

3. **`visualizations.py` is canonical.** The ONLY place figure functions live. Notebooks reference
   figures via `# viz-ref:` tags.

4. **Every formula is content-grounded on a real, non-placeholder Lean theorem**, and every Lean
   theorem has a proof (zero sorry). A `Lean:` reference must resolve to a declaration that is not
   a `True`/placeholder stub — a formula may not be grounded on a theorem that proves nothing.
   Enforced by `formula_grounding` across all references (hard-fail on placeholder-grounded refs,
   advisory on dangling stale names).

5. **Every computed quantity has bounds**, tested in the suite and enforced by `physical_bounds`.

6. **Every paper claim traces to computation** — numerical claims match `formulas.py` within 0.5%.
   Enforced by `paper_provenance`.

7. **Narrative derives from data.** Feasibility, detectability and experimental-reach statements
   are supported by computed quantities. "Within reach" means the computed shot count is < 10⁶ and
   `feasible=True`.

8. **Every experimental parameter has verified provenance** — traced to a specific published source
   via `PARAMETER_PROVENANCE`. LLM verification unblocks computation; human verification unblocks
   submission. Enforced by `parameter_provenance`.

9. **Placeholder theorems are non-load-bearing.** A theorem proved `True := trivial` encodes no
   content and MUST NOT be referenced by any proof, formula or paper claim; it is a documentation
   marker. Tracked in `PLACEHOLDER_THEOREMS`. Substantive count = total − placeholders, and paper
   claims cite the substantive count. The registry must be complete: every on-disk `True := trivial`
   declaration is registered with a `lean_name` and `category`, and `PLACEHOLDER_TOTAL_COUNT`
   matches `theorems_placeholder` in `docs/counts.json`. Enforced by `placeholder_not_cited`
   plus claims-reviewer Class PC; the "not referenced by a proof or formula" clause by
   `formula_grounding` and the graph builder's placeholder exclusion.

10. **No heartbeat overrides in proof bodies.** No `set_option maxHeartbeats` or
    `synthInstance.maxHeartbeats` in any `theorem`, `lemma`, `example`, or `def` whose body is
    tactic-produced. Hitting the limit is evidence the proof architecture is wrong; the fix is
    `have` decomposition. Expensive typeclass synthesis is resolved with `@[local instance]`
    caching, not a larger budget.

    **Exception — metaprograms.** A metaprogram whose work is intrinsically O(project size) may set
    unlimited heartbeats in its local `CoreM`/`MetaM` options. `ExtractDeps.lean` is currently the
    only such file. A new file claiming this exception must (a) be a metaprogram containing no
    tactic-generated proofs, (b) demonstrate that its work is project-size-bound, and (c) justify
    why no decomposition is possible, with user approval. When in doubt, the rule applies.

11. **Every external bibitem has a primary-source cache file.** Each non-`inprep` entry in
    `CITATION_REGISTRY` carries a `primary_source_path` under
    `Lit-Search/Phase-X/primary-sources/<bibkey>.{pdf,abstract.txt,json}`. Populated by
    `scripts/back_fill_primary_sources.py` (sidecar state
    `docs/primary_sources_state.json`) and promoted into the registry by
    `scripts/promote_primary_sources.py`. Enforced by `citation_primary_sources_present`, mandatory
    at every Stage 13. **Exempt:** in-prep self-cites
    (`inprep: True`), and canonical-textbook or pre-DOI references (entries with
    `primary_source_path`, `doi` and `arxiv` all `None`) verified via secondary academic citations.

12. **Provenance DOIs resolve to the registry.** Every DOI in a `PARAMETER_PROVENANCE` source
    resolves to a `CITATION_REGISTRY` bibkey, and every bibkey in a `cited_bibkeys` field exists.
    Enforced by `provenance_doi_in_registry` — advisory by default, hard-fail under `--strict`,
    which is mandatory at the submission gate.

13. **The QI register is auto-regenerated and manually curated, never wiped.**
    `scripts/qi_register.py` emits an item to **Open Items** only when its `qi-<gate>` ID is not
    already under **Closed Items** and the underlying findings have `meta.status == 'open'`. The
    curated `## Closed Items` block is preserved verbatim across regenerations.

14. **Every paper-shaped output lifts into a bundle.** Every new draft, section addition or
    notebook companion identifies its target — one of the codes in `validate.BUNDLE_CODES`, the
    roster's single source of truth — at Stage 1 and records it in `docs/PAPER_DRAFT_MAPPING.md`
    (append-only) at Stage 12. **No new stand-alone drafts are created without explicit user
    authorization** to add a target beyond the current roster. `docs/PAPER_STRATEGY.md` carries the
    per-target charters. The assignment propagates to every prose-state sentence via
    `scripts/sentence_state.py` (`bundle_destination`, `bundle_section_hint`, `lift_action`);
    `scripts/bundle_migration.py` provides the migration and `scripts/bundle_clusters.py` projects
    per-paper assignments onto claim clusters at `papers/cluster_bundle_index.json`.

15. **Every new project-local `axiom` requires explicit user sign-off.** A deep-research
    recommendation to ship an axiom is **advisory only**. Every new axiom ships with either (a) a
    discharge plan in the wave roadmap, or (b) a documented argument that no constructive proof is
    feasible in current Mathlib. The posture is that **axioms are temporary scaffolding, not
    permanent commitments.** Every axiom also requires an `AXIOM_METADATA` entry with
    `eliminability`, `discharge_wave` and `discharge_estimate_loc`, consumed by the dashboard's
    Proof Architecture tab and by Stage 13.

16. **Every consumed tracked-hypothesis Prop is in the single registry.** A tracked hypothesis (a
    Prop-valued `def`/`structure` named `H_*` / `*Conjecture` / `*Hypothesis` encoding an
    undischarged claim) consumed as a binder by any theorem MUST be in `HYPOTHESIS_REGISTRY` — the
    single source of truth for the tracked-assumption surface — or listed in
    `TRACKED_HYPOTHESIS_NON_LOAD_BEARING` with a reason. Each entry carries `tier`, `statement`,
    `status`, `source`, `risk` and a publication-facing `prose`.
    `docs/PERMANENT_TRACKED_HYPOTHESES.md` is an **auto-generated view**
    (`scripts/render_tracked_hypotheses.py`), **never hand-edited.**
    Enforced by `tracked_hypothesis_ledger` and `tracked_hypotheses_fresh`.
    **Scope limit:** Prop-valued struct *fields* are not auto-enumerated and are covered case by
    case. General auto-detection is tracked debt.

17. **Every provably-false settled no-go has a live, kernel-pure, non-vacuous backing theorem.**
    The negative-front mirror of 16. Each kernel-no-go fork in `docs/dev-loops/SETTLED_FORKS.md`
    is encoded in `KERNEL_NOGO_REGISTRY` with `fork_id`, `backing_theorems`, `nogo_kind`
    (`refutation` / `structural_forcing` / `counterexample`) and a one-line `false_statement`.
    Each backing theorem must exist in `lean_deps.json`, be kernel-pure
    (`{propext, Classical.choice, Quot.sound}`) and be non-vacuous — a self-discharging no-go
    blocks nothing. Enforced by `nogo_substrate_integrity`.
    **Scope: provably-false no-gos ONLY.** Policy, route and preference bans are not false, cannot
    be kernel-encoded, and stay in `SETTLED_FORKS.md` prose.
    **Encode-on-settle:** discovering a kernel-checkable no-go lands its backing theorem and
    registry entry in the settling turn. Recording such a fork in prose alone is itself a finding.

---

## Deep Research Reconciliation Protocol

When incorporating results from deep research in `Lit-Search/`:

1. **Extract every factual claim** — parameter values, citations, experimental-status assertions.
2. **Classify each:**
   - **VERIFIABLE** — cites a specific paper and location (table, equation, figure)
   - **PLAUSIBLE** — consistent with known physics, no specific citation
   - **CONFLICTING** — disagrees with another result or the codebase
   - **UNVERIFIABLE** — no citation, or a vague one ("well-known result")
3. **VERIFIABLE** → add to `PARAMETER_PROVENANCE`; fetch the cited paper, extract the value and an
   excerpt, set `llm_verified_date`. Code values may update after LLM verification.
4. **CONFLICTING** → document BOTH values with excerpts in the provenance notes and recommend a
   resolution based on source quality ("Table I" beats "estimated from figure"). Code uses the
   recommended value; the human resolves via the dashboard before submission.
5. **PLAUSIBLE / UNVERIFIABLE** → may enter `constants.py` with `tier: 'PROJECTED'` and
   `llm_verified_date: None`, clearly labeled as estimates. These are advisory warnings, not
   failures.
6. **Verification tasks** go in the roadmap under "Primary Source Verification".

**Rule:** deep research may update code parameters after LLM verification against primary sources.
Paper **submission** is gated on human verification via the provenance dashboard.

---

## Quick Reference

```bash
# Run from the SK_EFT_Hawking/ root
uv run python -m pytest -q                      # both suites (repo + plugin guards)
uv run python scripts/validate.py               # whole suite (--list to enumerate)
uv run python scripts/validate.py --check <name>
uv run python scripts/review_figures.py         # figures + structural checks
cd lean && lake build                           # Lean build

# Aristotle — subcommand CLI (read docs/references/Theorm_Proving_Aristotle_Lean.md first)
uv run python scripts/submit_to_aristotle.py sorries [<target>...]
uv run python scripts/submit_to_aristotle.py stage <target>...
uv run python scripts/submit_to_aristotle.py submit <target>... --yes-i-authorize
uv run python scripts/submit_to_aristotle.py status
uv run python scripts/submit_to_aristotle.py retrieve <job_id>
uv run python scripts/submit_to_aristotle.py graft <extracted_dir> <target>... --apply

# Provenance dashboard (human verification)
uv run python scripts/provenance_dashboard.py   # localhost:8050
```
