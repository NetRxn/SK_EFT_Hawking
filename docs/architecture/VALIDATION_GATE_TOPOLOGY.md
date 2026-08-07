# Validation gate topology — what runs when, what it blocks, what each gate computes

**Living document.** Start at [`README.md`](README.md). States no counts — the gate and
check rosters are in [`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md).

**Companions:** [`VALIDATION_ARCHITECTURE.md`](VALIDATION_ARCHITECTURE.md) (how the suite is
built) · [`CHECK_AUTHORING_GUIDE.md`](CHECK_AUTHORING_GUIDE.md) (what a new check owes) ·
[`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) (the quality layer's interior) ·
`docs/WAVE_EXECUTION_PIPELINE.md` (the process law).

---

## 1. The tiers

| tier | trigger | what runs | blocks? |
|---|---|---|---|
| **0 — commit** | every `git commit` | leak/IP guard (staged diff) · `pre-commit-notebooks.sh` (**only staged `.ipynb`**) · `pre-commit-sync.sh`: incremental `lake build` if `.lean` staged, then a **short named list** of checks | **fail-open**; hard-blocks on `main` only |
| **1 — reviewer prechecks** | before dispatching an LLM reviewer | `gate_precheck.py s9` · `s10` | yes — do not spend reviewer budget on a stale tree |
| **2 — wave close (paper)** | `/skeft-qa:wave-close` | `sync.py --full`, then `gate_precheck.py s13` = **full suite + `--force-latex`** | yes — no Stage-13 dispatch on a red tree |
| **2 — wave close (Lean)** | same, for a wave that touched no `papers/` | `gate_precheck.py s13-lean` = the **same suite**, exit code scoped to the substrate | yes, on substrate reds only |
| **3 — submission** | before arXiv/journal | `gate_precheck.py submission` = full suite **+ the `--strict` legs** | yes |
| **— CI** | *none* | deliberately no scheduled runner | n/a |

**Tier 0 never runs the full suite** — it runs a named list, all Lean/substrate-side, so a
red caused by paper content cannot block a commit. The list is in `pre-commit-sync.sh`; it
is short by design and deliberately not restated here.

## 2. The question this document exists to answer

> *Will a red caused by paper content block routine Lean development?*

**At tier 0: no.** See above.

**At tier 2: use `s13-lean`.** `gate_precheck s13` runs the *whole* suite, so closing a
**pure-Lean wave** is blocked by paper-corpus state the wave never touched. Whenever any
corpus-wide red is open, plain `s13` cannot pass for **any** wave, Lean or paper.

`s13-lean` runs the **identical** suite and prints the **identical** failures; only the exit
code is scoped, via `validate.py --scope substrate`. Nothing is skipped and nothing is
hidden. Use plain `s13` for a wave that touched `papers/`, and wherever the corpus itself is
the deliverable.

⚠️ **`--scope` is deliberately absent from `submission`.** That gate is scope-blind by
design: nothing ships while any part of the tree is red. And the flag scopes only what
BLOCKS — a flag that scoped what is *measured* would be the defect this suite exists to
catch wearing a convenience label, which is why `test_ci_mode.py::TestScopeSubstrate`
asserts that a substrate failure still blocks and that non-blocking failures are still
reported.

**For the live red set, run the suite.** A list of currently-failing checks in a document is
a snapshot that rots; `uv run python scripts/validate.py` prints it, partitioned into
SUBSTRATE and PAPER CORPUS, which is the same partition this section is about.

## 3. Flags

| flag | effect | who passes it |
|---|---|---|
| `--strict` | promotes the submission advisories to hard failures; **implies `--no-memo`** | `gate_precheck submission` only |
| `--scope substrate` | paper-corpus failures still run and print, but do not set the exit code | `gate_precheck s13-lean` |
| `--force-latex` | recompiles every bundle draft, bypassing the per-draft cache | `gate_precheck s13` / `submission` |
| `--no-memo` | re-measures the memoized Lean checks | manual, or implied by `--strict` |
| `--ci` | skips the mtime regenerators + `notebook_exec`; enforces the coverage floor; never archives | nothing today |
| `--force-notebooks` | bypasses the notebook skip-cache | manual, after a kernel/dependency change |

`--strict` is passed only by the submission gate, and the reason is concrete:
`bundle_source_freshness` WARNs whenever a source paper moved after its last bundle lift —
the **normal** state of an in-progress bundle. A strict wave-close gate would go red on
correct work mid-wave, and **a gate that fires on correct work gets switched off.**

⚠️ **No invariant scopes `--strict` suite-wide.** The scoping is a property of
`gate_precheck.py`, which passes `--strict` at `submission` and nowhere else. Pipeline
Invariant #12 mandates `--strict` at the Paper Submission Gate for
`provenance_doi_in_registry` specifically — a rule scoped to that single check, not a global policy.

## 4. What each readiness gate actually computes

The roster and priorities are in [`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md#readiness-gates).
What matters here is the gap between a gate's *name* and its *computation*.

| gate | P | can block? | what it actually computes |
|---|---|---|---|
| `CitationIntegrity` | 1 | ✅ | `\bibitem{}` keys ⊆ `PrimarySource` nodes. **Registry coverage only** — no DOI/title/author match, contra its doc |
| `CrossPaperConsistency` | 1 | ✅ | `CONTRADICTS` edges (**no emitter**) + cross-paper `REPORTS` value disagreement |
| `ParameterProvenance` | 1 | ✅ | every `DEPENDS_ON → param:*` has `human_verified_date` |
| `ComputationCorrectness` | 1 | ✅ | grounded formulas have a non-`{bounds,unknown}` `VERIFIES` edge |
| `LeanProofSubstance` | 1 | ✅ | cited theorems ∌ `PlaceholderMarker` |
| `AssumptionDisclosure` | 1 | ✅ | each consumed hypothesis appears as a lowercased substring of the tex (heuristic by design) |
| `NarrativeGrounding` | 1 | ✅ | every `interesting` ProseClaim has ≥1 `SUPPORTS` (**no emitter**) — so it blocks only papers carrying such a claim and passes vacuously for the rest |
| `ProductionRunHealth` | 1 | ✅ | linked runs not failed (**via `PRODUCES`, no emitter**); plus a prose regex for MC evidence, which is the leg that actually fires |
| `NumericalFreshness` | 2 | ❌ | stale `REPORTS`, inline literals, table mtimes → **only ever `needs-recheck`** |
| `FirstClaimVerification` | 2 | ❌ | counts `first-claim` tags; the ledger node type **does not exist** |
| `FixPropagation` | 2→**1** | ✅ | open blocking findings; **self-promotes to P1 when blocking** |

⚠️ **The edge types marked *no emitter* above are queried and never produced**, so
they return verdicts they did not compute. Guarded by
`validate.py --check gate_edge_types_are_emitted`, which derives both populations from the
AST and fails on any dead type not disclosed there. `READINESS_GATES.md` still documents the
P2 gates as blocking; they cannot.

An evaluator that **raises** records `state='blocked'`, not `open`. This matters because
`open` aggregates to YELLOW: a crashed gate recorded as `open` is indistinguishable from a
mild advisory.

## 5. Enforcement reality — what actually blocks

**The architecture implies far more enforcement than exists.** Three tiers:

**Blocks.** The commit gate runs its short named list and only hard-blocks on `main`; it
exits 0 in a worktree, on missing `uv`, and on any check crash. `.git/hooks/pre-commit` is
local-only and uncommitted, so **a fresh clone has no mechanical gate at all.** The
web-egress guard is the one unambiguously fail-closed control in the system.

**Reports but never blocks.** A small set of checks are advisory *by design*, each with a
stated reason and dispositioned individually in ADR-009 §Deferred. Their population is
frozen by `tests/test_cannot_measure_baseline.py`, which fails in **both** directions — a
new silent PASS, or a converted one left stale in the baseline.

⚠️ **That population is a SYNTACTIC lower bound, not the truth.** It was produced by an AST
scan for a literal `passed=False`; a check can satisfy that scan while being unreachable in
every leg. A semantic-reachability re-measurement has never been run.

**Claims enforcement, has none.** `docs/AI-DEFECT-DEFENSE-LAYER.md` is headed *"Canonical
Specification"* and carries an **"Implementation:"** line naming `scripts/pre_commit_hook.sh`
and `scripts/install_pre_commit.sh`. **Both are absent**, and none of its named Tier-2 checks
was ever written. It is a **proposal that reads as a description** — committed once, as a
draft, and never built.

⚠️ It also declares its own **"Pipeline Invariant #16"**, which **collides** with the real
Invariant #16 (the tracked-hypothesis registry). Two different rules share one number across
two documents, and nothing in the pipeline law cites the AI-Defense document at all. Tracked
as **A2** in [`.working-docs/ARCHITECTURE_TODOs.md`](.working-docs/ARCHITECTURE_TODOs.md).

Also claiming enforcement and having none: **no gate or check reads `stage9_status` or
`stage10_status`.** They are not inert — `bundle_append.py` reads both and demotes a `green`
to `pending` when new content lands in the bundle — but nothing *gates* on them, so the
"Stages 9 and 10 before 13" rule has no enforcement point.

Nothing in the codebase writes any `stage*_status` to `green`; the only writers set
`"pending"`. Every green is therefore a hand edit, which is how a bundle can sit at
`stage13_status: green` with `stage9_status: not_started`.

## 6. Field ownership — who writes what

A recurring failure mode is a check telling you to run a script that cannot fix the field.

| field | written by | NOT written by |
|---|---|---|
| `blockers_open`, `advisories_open`, `open_findings`, `blocked_p1_gates`, `readiness` | `bundle_readiness.write_metadata_counts` | — |
| `stage13_status`, `stage9_status`, `stage10_status` | the **Stage-13/9/10 review cycle** (`BUNDLE_LIFT_PROCEDURE` §§8–10) | `bundle_readiness.py` |
| `freshness_stale` | `check_bundle_source_freshness.py` | `bundle_readiness.py` (deliberately — two writers made `validate.py` non-idempotent) |
| `apex_theorems` | a human, under ADR-010 §D5a's per-bundle context review | any script |
| `docs/counts.json` / `counts.tex` | `update_counts.py` | — |
| `lean/lean_deps.json` + `.hash` | `extract_lean_deps.py` | — |

So a `stage13_status='green'` contradicted by open blockers means **a past review has been
invalidated by newly-minted findings** — the fix is to re-run Stage 13, not the counts
writer.

## 7. Cost

The suite's cost concentrates in a couple of expensive checks, both now scoped to what changed:
`axiom_closure_allowlist` (input-fingerprint memo) and `paper_latex_compiles` (per-draft
content-hash cache). Everything else finishes fast. See
[`VALIDATION_ARCHITECTURE.md`](VALIDATION_ARCHITECTURE.md#5-change-scoping) for the caches
and the hazard they carry.

Measure rather than quote: `validate.py` prints its own elapsed time, and `--no-memo` gives
the cold number.

---

*Why there is no scheduled CI, and what a runner would have to fix first (mtime freshness is
meaningless on a fresh clone): `docs/audits/2026-08-04-qa-qi-infrastructure/CI_DEFAULTS_ASSESSMENT.md`.*
