# Architecture TODOs — remediation backlog

**Purpose.** Everything the architecture-accuracy pass found that is **a defect in the
system**, not in a document. Markdown fixes are made in place; anything requiring code,
infrastructure or a validation script is enumerated here and **deferred**.

**Standing constraint (operator, 2026-08-07):** *all* remediation on infrastructure and
papers is on hold until the architecture documents are at 100% accuracy. Nothing in this
file is authorized to be built yet.

**Status key:** `OPEN` — real, unfixed. `VERIFIED-OPEN` — re-measured during this pass and
confirmed still live. `WATCH` — not a defect today, but a shape that will become one.

---

## What the accuracy pass covered, and how

Every load-bearing claim in the seven architecture documents was checked **by reading the
implementation**, not by substring match. A prior attempt reported "100% verified" after
checking roughly a fifth of the surface, and one of its batches was a substring test dressed
as a check — asserting that `'SUPPORTS'` appears somewhere in an evaluator proves nothing
about the description of that evaluator. That failure is why the method is recorded here.

**Checked, in full:** the check-module roster · framework modules · `CheckResult` fields · the
four ADR-009 hazards and the test enforcing each · runtime flags · all five memo guards ·
every gate-semantics row against its evaluator source · the tier table against
`gate_precheck.STAGES` · field ownership against the writers · every staleness key in the
artifact table (mtime vs content-compare, individually) · the five silent-drop points · the
human-decision-point enforcement claims · both claim-lineage assertions · the Codex
out-of-scope claim · every cited file path · every relative link in all seven documents.

**Five document errors were found and corrected in place** — recorded in the documents
themselves where a future reader would otherwise re-introduce them. The largest: both maps
claimed bundle-level Stage-13 reviews reach no gate, which was **false and already stale when
written** — the extractor's heading regex had been widened before the maps were authored, and
bundle reviews are the largest source of `ReviewFinding` nodes in the graph.

**Standing risk this pass does not remove:** nothing mechanically verifies a *description*.
See **B2**.

---

## A. Defects the documents describe, confirmed still live

### A1. `harness_lock` contention silently yields stale derived artifacts — VERIFIED-OPEN

- **Where:** `scripts/harness_lock.py:103` `regen_lock()`
- **What:** bounded non-blocking poll, then `yield False` on contention. The context manager
  is correct and honest. The defect is in the **callers**: on `False` they SKIP the
  regeneration and proceed, so `load_lean_deps()` returns the existing file and downstream
  generators (`counts.json`, `counts.tex`, `atlas_view.json`) are written from stale input
  **and report success**.
- **Verified:** read `regen_lock` in full this pass. On an internal exception it yields
  `True` (proceed with the regen) — that direction is safe and must not be conflated with
  the contention path, which is the one that produces stale output.
- **Also:** the suite's auto-regenerating freshness checks shell out with **no lock at all**.
- **Documented in:** `QA_QI_INFRASTRUCTURE_MAP.md` §2, `CHECK_AUTHORING_GUIDE.md` §5.

### A2. AI-Defense Tier 1 names files that do not exist — VERIFIED-OPEN

- **Where:** `docs/AI-DEFECT-DEFENSE-LAYER.md` names `scripts/pre_commit_hook.sh` and
  `scripts/install_pre_commit.sh` as its Tier-1 implementation.
- **Verified this pass:** both **absent** from the tree.
- **Compounding:** Pipeline Invariant #16 cites that document as canonical, under a filename
  that is also wrong.
- **Documented in:** `VALIDATION_GATE_TOPOLOGY.md` §5, `CHECK_AUTHORING_GUIDE.md` §5.

---

## B. Found during this pass, not previously documented

### B1. The counts-ordering guard's population is hand-listed and incomplete — OPEN

- **Where:** `tests/test_validate_registry_contract.py:80` `_COUNTS_CONSUMERS`
- **What:** the tuple declares **two** consumers (`axiom_count_prose_consistency`,
  `inventory_index_autogen_fresh`), and `test_regenerators_precede_their_consumers` asserts
  `counts_fresh` precedes only those two. Measured this pass by AST over the registered
  checks, the actual readers of `docs/counts.json` are:

  | position | check | vs `counts_fresh` (31) |
  |---:|---|---|
  | 1 | `lean_zero_sorry` | **before** |
  | 10 | `native_decide_regression` | **before** |
  | 22 | `axiom_closure_allowlist` | **before** |
  | 58 | `axiom_count_prose_consistency` | after (declared) |
  | 59 | `prose_theorem_reference_coverage` | after |
  | 61 | `inventory_index_autogen_fresh` | after (declared) |

- **Consequence:** on a bare `validate.py` run over a tree whose Lean sources changed since
  the last counts regeneration, three checks — including the Invariant #4 gate — evaluate
  against the *previous* extraction.
- **Severity is bounded, and the bound must travel with the finding:** both real gates
  mitigate it. Tier 0 greps lake's own output with a quote-agnostic regex
  (`pre-commit-sync.sh`), independently of `counts.json`. Tier 2 runs `sync.py --full`,
  which regenerates counts, *before* `gate_precheck s13` invokes validate. The exposure is a
  bare mid-development `validate.py`, not a gate.
- **Why it is a defect anyway:** this is the failure mode
  `CHECK_AUTHORING_GUIDE.md` §6 lists as *"a hand-maintained list parallel to a registry"*,
  inside the test that enforces ADR-009 hazard H3.
- **Fix shape (not authorized yet):** derive the consumer set by AST rather than declaring
  it, exactly as `gate_edge_types_are_emitted` derives its two populations.

### B2. No mechanism verifies the *accuracy* of any architecture document — OPEN

- **What:** `validate.py --check architecture_inventory_fresh` gates two things: the census
  matches a fresh derivation, and no narrative states a census count. **Nothing verifies a
  description.** Every prose claim rests on its author having read the code.
- **Evidence this matters:** `QA_QI_INFRASTRUCTURE_MAP.md` drifted out of sync within days
  of being written and contradicted itself inside a single sentence, with a green suite
  throughout.
- **Candidate fix, cheapest first (not authorized yet):**
  1. Every backticked code reference in `docs/architecture/` must resolve to a real file,
     script, symbol, check name, gate name or test. Fully mechanical; catches the rename and
     deletion paths that actually rot these documents.
  2. Claim-level assertions for load-bearing findings.
- **Interim mitigation, in place:** this pass verifies each claim by direct read and records
  the verification method alongside it, so a later reader can re-run the same check.

---

### B3. `docs/READINESS_GATES.md` describes gates that cannot do what it says — OPEN

Not an architecture document, so corrected here rather than in place.

- **Gate 1 CitationIntegrity** (`:27`) states the intent as *"Title, authors, arXiv ID, DOI,
  journal/volume/page all match the primary source."* The evaluator performs
  **registry-coverage only** — `\bibitem` keys ⊆ `PrimarySource` nodes — and its own docstring
  says DOI fetch-and-verify is deferred to Stage 13. A reader takes the gate as verifying
  bibliographic content; it verifies registration.
- **Gates 9 and 10** (`NumericalFreshness`, `FirstClaimVerification`) each carry a
  **"Blocks on any:"** section. Verified by reading both evaluators: the only states either
  assigns are `needs-recheck` and `passed`. Neither can block.
- **Fix shape:** correct the prose to the computed behaviour, or raise the evaluators to the
  documented behaviour. The second is a scope decision, not a doc edit.

### B4. A discharged axiom and a FALSE theorem are still cited in chain-of-backing — OPEN

- **`gapped_interface_axiom`** — retired; the project's axiom count is **0** (verified in
  `docs/counts.json`). Still referenced **61 times across 14** `papers/*/claims_review.json`
  files (D2, D4, I1, L2, and nine legacy drafts).
- **`gap_solution_bounded`** — `lean/SKEFTHawking/TetradGapEquation.lean:320`, carrying the
  note at `:314` *"This theorem is FALSE as originally stated."* Still referenced **24 times
  across 2** files (I1, `paper5_adw_gap`). I1's citation is a **documented waiver** — it cites
  the theorem deliberately, as history. The others are not.
- **Why it matters:** these are sentence-level backing links, so a manuscript claim is resting
  on a retired axiom and a known-false theorem. Detected by
  `scripts/chain_canonicalize.py --report`; **nothing gates on it.**

### B5. `docs/WAVE_EXECUTION_PIPELINE.md` — the process LAW disagrees with the tree — OPEN

Each verified by direct read during this pass. The law is a mandatory-read bootstrap
document, so a reader is being handed five wrong facts before any work starts.

| line | says | actual |
|---|---|---|
| `:5` | *"follows these **12** stages in strict order"* | **14** `Stage` headings in the same file |
| `:317` | *"**Checks (16 total)**"* | the registry is far larger — see `SURFACE_INVENTORY.md` |
| `:689` | Invariant #14 enumerates `F, D1–D9, L1–L3, I1–I3, E1, E2` — *"18 targets as of the 2026-06-10 D9 authorization"* | the enum **cannot legally hold D10, D11 or D12**, which are on the live roster |
| `:191` | *"Aristotle runs Lean/Mathlib 4.28.0; **we run 4.29.1**"* | `lean/lean-toolchain` is `leanprover/lean4:v4.32.0` |
| `:529` | *"project guidance lives in the workspace CLAUDE.md; **no separate per-repo CLAUDE.md**"* | `SK_EFT_Hawking/CLAUDE.md` exists and is a bootstrap document |

- **The mechanism is the finding, not the five instances:** *a rule text that enumerates a
  roster is a hardcoded roster.* `bundle_registry_consistency` Leg C exists precisely because
  that pattern is known-bad **in code**; the same discipline has never been applied to prose.
- **Fix shape:** the same one this directory adopted — a rule should name the registry, not
  restate its contents. Tracked in ADR-010 §D7 as part of the roster change-set.

### B6. "Stage 10" names two different things — OPEN

- **`docs/WAVE_EXECUTION_PIPELINE.md:388`** — `## Stage 10: PAPER DRAFT`. Claims review is a
  **sub-step** described at `:407` as *"runs after Stage 10, before Stage 11"* — it is not a
  numbered stage in the law at all.
- **`docs/BUNDLE_LIFT_PROCEDURE.md:9`** — *"Stage 13 … may not be invoked until both Stage 9
  (figure review) AND **Stage 10 (claims review)** are GREEN."*
- **The machinery follows the bundle sense:** the `stage10_status` field in every
  `papers/*/bundle_metadata.json`, and `gate_precheck.py`'s `s10` stage.
- **Consequence:** a reader who learns the stage numbering from the law and then reads
  `stage10_status: skeleton` will believe it reports draft-writing progress. It reports claims
  review. The architecture documents now state which sense they use; the two source documents
  still disagree with each other.
- **Fix shape:** rename one of them, or have the law name claims review as its own stage.
  A decision, not a doc edit.

---

## C. Watch list

### C1. `lean_zero_sorry` reads a derived artifact rather than the extraction — WATCH

- **Where:** `scripts/validation/checks/lean_substrate.py`
- **What:** Invariant #4's gate reads `docs/counts.json` (`lean.sorry_declarations`) rather
  than `lean_deps.json` directly. It is correct and hard-failing given fresh counts, and
  returns `passed=True, measured=False` when counts are absent or unparseable — the
  documented cannot-measure contract. Coupled to **B1**.
- **Not a defect today:** tier 0 catches `sorry` independently from lake's own output.
