# Paper Readiness Gates — Canonical Definitions

This document is the **source of truth** for the 11 readiness gates that every paper in this project must satisfy before submission. It defines the gates, their priorities, pass/fail criteria, and the evidence each gate consumes. All other documents — the pipeline doc, the adversarial-reviewer agent, the dashboard surface, `validate.py` CHECK 18 — reference this document, not the other way around.

**Implementation:** `scripts/readiness_gates.py` evaluates these gates against the knowledge graph. `validate.py --check readiness_submission_gate` aggregates per-paper state. The dashboard renders the 15 × 11 heatmap at `localhost:8050/?tab=readiness`.

**Status model:**
- `passed` — gate evaluator confirms all required conditions
- `blocked` — at least one required condition failed; paper cannot advance
- `needs-recheck` — conditions have changed upstream; re-evaluation required
- `in-review` — human review in progress (dashboard write-back, Phase 5v Wave 3c)
- `open` — insufficient data to evaluate

**Paper aggregate:**
- **RED** — any gate is `blocked`
- **YELLOW** — all gates `passed` except ≥1 `needs-recheck` / `open`
- **GREEN** — all 11 gates `passed`

Submission gate: a paper MAY NOT be submitted unless it is GREEN. There are no exceptions for any gate, P1 or P2. Credibility is the project's primary asset; every gate exists because a real failure class has passed through the internal pipeline in the past.

---

## Priority 1 — Correctness gates (8)

### Gate 1 — CitationIntegrity

**Intent:** Every bibliographic reference resolves to the paper the bibitem claims it does. Title, authors, arXiv ID, DOI, journal/volume/page all match the primary source.

**Evaluator input:** Each `\bibitem{key}` in `paper_draft.tex`, plus the `CITATION_REGISTRY` entry for that key in `src/core/citations.py`.

**Passes iff:**
- Every bibkey in the `.tex` has a matching `CITATION_REGISTRY` entry
- Every registry entry has `arxiv_verified == True` AND `doi_verified == True` (where applicable)
- Bibitem author strings match the registry's author list (order-insensitive)
- Bibitem title matches the registry title (exact or registry's known-aliases list)
- Journal/volume/page/year in bibitem matches registry (for published refs)

**Blocks on any:**
- A bibkey that is not in the registry
- A registry entry whose `arxiv_verified` is `False` or stale (hash mismatch vs. last fetch)
- Mismatch between bibitem metadata and registry truth
- Wrong-target arXiv ID (fetched title unrelated to what bibitem claims)

**Escalation:** All CitationIntegrity findings are `blocked` at submission time. Pre-submission drafts may carry findings as `needs-recheck` but submission requires full pass.

### Gate 2 — CrossPaperConsistency

**Intent:** Companion papers agree with each other on facts they share.

**Evaluator input:** Cross-paper CONTRADICTS edges; parallel REPORTS edges (same metric, different papers, different values); shared bibkeys (same key used in two papers must resolve the same way).

**Passes iff:**
- No CONTRADICTS edges touch this paper
- No other paper reports a different value for any `CountMetric` this paper also reports
- Every shared bibkey points at the same `arxiv_id` across papers

**Blocks on any:**
- A CONTRADICTS edge
- Two papers reporting different `paper_value` for the same metric
- A bibkey whose `arxiv_id` differs across papers that cite it

### Gate 3 — ParameterProvenance

**Intent:** Every experimental parameter has a traceable primary source and has been verified by a human against that source.

**Evaluator input:** The `DEPENDS_ON` edges from the Paper node to `Parameter` nodes, and the `PARAMETER_PROVENANCE` metadata on each parameter.

**Passes iff:**
- Every parameter the paper depends on has `llm_verified_date` AND `human_verified_date` set
- Every non-`PROJECTED` parameter has a primary-source citation that resolves (via Gate 1)

**Blocks on any:**
- A dependent parameter without `human_verified_date`
- A parameter whose primary source is itself flagged by Gate 1

**Note:** `PROJECTED` parameters are allowed (pre-experiment theoretical proposals) but must be clearly labeled as projections in the paper prose.

### Gate 4 — ComputationCorrectness

**Intent:** Every formula the paper makes claims from has at least one test that asserts **correctness**, not just **boundedness**. Bounds-only coverage is how silent formula bugs ship (a formula wrong by orders of magnitude can still fall inside a sanity-bound check).

**Evaluator input:** Formulas the paper `GROUNDED_IN`; their incoming `VERIFIES` edges from `PythonTest` nodes; each edge's `test_kind` attribute.

**Passes iff:**
- Every grounded formula has ≥1 VERIFIES edge where `test_kind ∈ {golden, identity, roundtrip}`

**Blocks on any:**
- A grounded formula with no VERIFIES edges
- A grounded formula whose VERIFIES edges are all `test_kind ∈ {bounds, unknown}`

**test_kind definitions:**
- `golden` — asserts numeric equality to a hardcoded reference value (`assertAlmostEqual`, `assert_allclose`, `pytest.approx`, `math.isclose`)
- `identity` — asserts equality between two independently-computed quantities (`==`)
- `bounds` — asserts inequalities only (`<`, `>`, `<=`, `>=`, range checks)
- `roundtrip` — forward/inverse or serialize/deserialize consistency
- `unknown` — complex assertions that don't match the above patterns

### Gate 5 — LeanProofSubstance

**Intent:** Every Lean theorem the paper cites as "verified" has a body that encodes mathematical content. Placeholder bodies (`rfl`, `Equiv.refl`, `trivial`) on non-trivial statements, or tautological constructions where a hypothesis appears in the conclusion, are both disallowed.

**Evaluator input:** Lean theorems cited in the paper (via `VERIFIED_BY` edges on grounded Formulas, or directly via `\texttt{theorem_name}` in prose); the `PlaceholderMarker` nodes extracted in Wave 2b.

**Passes iff:**
- No cited theorem has a matching `PlaceholderMarker` node
- No cited theorem has a body whose only tokens reproduce a hypothesis of the theorem

**Blocks on any:**
- A cited theorem flagged as a `PlaceholderMarker` (syntactic red flag: `rfl` / `Equiv.refl` / `trivial` on non-trivial claim)
- A cited theorem whose proof is structurally tautological (semantic check — primary responsibility of the adversarial reviewer, not the syntactic extractor)

### Gate 6 — AssumptionDisclosure

**Intent:** Every hypothesis that a cited theorem depends on (via `ASSUMES` edges, structure-field constraints, or inline `private abbrev` / deep-research assumptions) is named in the paper so readers know what the result is conditional on.

**Evaluator input:** `ASSUMES` edges from cited theorems to `Hypothesis` nodes; structure-field constraints in referenced Lean structures; paper `.tex` text.

**Passes iff:**
- For every hypothesis a cited theorem assumes, the hypothesis key or human-readable name appears in the paper's prose, assumptions section, or theorem-statement context

**Blocks on any:**
- An assumed hypothesis that is load-bearing for a cited result but does not appear in the paper

### Gate 7 — NarrativeGrounding

**Intent:** Every "interesting" claim in paper prose (abstract, intro, conclusion) has a formal artifact backing it — either a Lean theorem, a measured-and-verified parameter, a successful production run, or an explicit interpretive tag acknowledging the claim is intuition rather than proof.

**Evaluator input:** `ProseClaim` nodes flagged `interesting=true` for this paper; their `SUPPORTS` edges to formal artifacts.

Interesting-claim heuristic tags:
- `first-claim` — "first in any proof assistant", "first formally verified", etc.
- `unification-claim` — "all the same X", "converge to", "rooted in"
- `attribution-claim` — historical attribution of an idea or technique
- `feasibility-claim` — "within reach", "programmable", "tunable"
- `simulation-evidence-claim` — "Monte Carlo evidence", "numerical evidence"

**Passes iff:**
- Every interesting ProseClaim has ≥1 SUPPORTS edge to a formal artifact, OR is explicitly tagged interpretive in the prose

**Blocks on any:**
- An interesting ProseClaim with no SUPPORTS edge and no interpretive disclaimer

### Gate 8 — ProductionRunHealth

**Intent:** If the paper claims evidence from a numerical simulation (MC, RHMC, any production run), a successful `ProductionRun` node must be linked to the claim via a `PRODUCES` edge.

**Evaluator input:** `ProductionRun` nodes linked to this paper's claims via `PRODUCES`; `.tex` prose scan for "Monte Carlo evidence", "numerical evidence", or similar.

**Passes iff:**
- Every linked ProductionRun has `status == 'success'`
- Any "evidence from simulation" claim in prose has ≥1 successful ProductionRun backing

**Blocks on any:**
- A linked ProductionRun with status ∈ {crashed, out_of_budget, sign_problem, terminated, unknown}
- A prose claim of numerical evidence with no successful backing run

---

## Priority 2 — UX / trust gates (3)

### Gate 9 — NumericalFreshness

**Intent:** Every numerical claim in the paper reflects the current canonical pipeline output, not a snapshot from a past commit. Covers both count-style literals ("N theorems") and quantity-style literals ("c_s = 0.548 mm/s"). A paper is fresh iff every numerical value it reports — in prose, tables, or figures — comes from the canonical source (`counts.tex` macros, `tables/<id>.tex` autogen files, or `formulas.py` computations verified by CHECK 14).

**Evaluator input:**
- `REPORTS` edges from Paper to `CountMetric` nodes (each edge carries `paper_value`, `canonical_value`, `delta_pct`, `stale`)
- `validate.py --check count_literals` — WARN on count literals outside `\input{counts.tex}` macros
- `validate.py --check tables_fresh` — FAIL if any `tables/*.tex` is stale vs sources
- `validate.py --check numerical_literals` — WARN on unit-bearing numerical literals outside `\input{tables/*.tex}` blocks
- `validate.py --check paper_provenance` — FAIL on >0.5% drift between any paper numerical claim and its pipeline value

**Passes iff:**
- No REPORTS edge has `stale == True` (drift > 0.5%)
- `tables_fresh` passes (all autogen tables current vs source inputs)
- `numerical_literals` and `count_literals` are WARN-acceptable at draft stage; FAIL at submission once retrofit is complete
- `paper_provenance` passes

**Blocks on any:**
- A stale REPORTS edge
- A stale `tables/*.tex` file (tables_fresh would auto-regen; blocked only if regen fails)
- `paper_provenance` drift
- At submission: any remaining inline literal flagged by `count_literals` or `numerical_literals`

**Remediation:**
- Counts: retrofit paper with `\input{../../docs/counts.tex}` + `\totaltheorems{}` / `\leanmodules{}` / etc. macros
- Tables: write `papers/<paper>/tables.py` spec; replace inline data rows with `\input{tables/<id>.tex}`; `render_paper_tables.py` regenerates automatically via `tables_fresh`
- Inline prose literals: move quotable values into the same `\input{}` chain, or tag with a `\pipelinevalue{...}` macro that expands to the canonical value at compile time

**Why this gate name changed (Phase 5v).** Originally "CountFreshness" — expanded to "NumericalFreshness" when the `tables.py` spec framework landed, because the same anti-drift principle applies to all numerical content, not just counts. The ReadinessGate dashboard cell for this gate now evaluates both count-level and table-level freshness in a single pass.

### Gate 10 — FirstClaimVerification

**Intent:** "First in any proof assistant" / "first formally verified X" claims are ledger-backed — someone confirmed no prior Lean / Mathlib / Agda / Coq / Rocq formalization of this result exists before the claim was made.

**Evaluator input:** ProseClaim nodes tagged `first-claim`; (future) `FirstClaimLedger` node type or equivalent.

**Passes iff:**
- Every `first-claim`-tagged ProseClaim has a corresponding ledger entry confirming prior-work search

**Blocks on any:**
- A first-claim without a ledger entry

**Status:** The ledger node type is not yet implemented. Until it lands, this gate is `needs-recheck` for every paper with a first-claim — advisory only, but surfaces the obligation.

### Gate 11 — FixPropagation

**Intent:** When a ReviewFinding (from any adversarial review round, Perplexity or internal Stage 13) flags this paper, the fix has been applied AND propagated to every other paper the same issue affects.

**Evaluator input:** `ReviewFinding` nodes with `FLAGS` edges to this paper; each finding's `status` (open / fixed / accepted-with-note); `SUPERSEDES` edges closing older findings.

**Passes iff:**
- Every FLAGS incoming to this paper has `status != 'open'`
- Every finding marked `fixed` has a SUPERSEDES edge to the finding that confirmed the fix (or a documented commit reference)

**Blocks on any:**
- An open finding
- A `fixed` finding without a SUPERSEDES / commit reference

---

## Changing or adding a gate

Gates in this document are load-bearing: the evaluator, dashboard, pipeline, and adversarial agent all reference them by name. To modify:

1. Update this doc first (the canonical definition)
2. Update `scripts/readiness_gates.py` evaluator for the affected gate
3. Update `.claude/plugins/physics-qa/agents/adversarial-reviewer.md` finding classes to match
4. Update `scripts/templates/partials/readiness_tab.html` GATES array (ordering + priority)
5. Run `validate.py --check readiness_submission_gate` to confirm new gate state surfaces

To add a 12th+ gate: same sequence. Dashboard heatmap auto-grows. Bump the document title.

---

## Why these 11 and not more/fewer

The 11 gates were consolidated from the 13-dimension problem taxonomy that emerged from the April 2026 external adversarial review round. Two pairs were merged:
- `SourceFidelity` folded into `CitationIntegrity` (both are primary-source correspondence)
- `TestCoverageShape` folded into `ComputationCorrectness` (shape is a sub-check)

Every gate traces to a specific past failure class that passed through the 12-stage pipeline. The gate set is additive as new failure classes surface — a new gate is cheaper than repeatedly catching the same issue in adversarial rounds.
