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

### A1. `harness_lock` contention silently yields stale derived artifacts — ✅ CLOSED

- **Where:** `scripts/harness_lock.py:103` `regen_lock()`
- **What:** bounded non-blocking poll, then `yield False` on contention. The context manager
  is correct and honest. The defect is in the **callers**: on `False` they SKIP the
  regeneration and proceed, so `load_lean_deps()` returns the existing file and downstream
  generators (`counts.json`, `counts.tex`, `atlas_view.json`) are written from stale input
  **and report success**.
- **Verified:** read `regen_lock` in full this pass. On an internal exception it yields
  `True` (proceed with the regen) — that direction is safe and must not be conflated with
  the contention path, which is the one that produces stale output.
- ✅ **CLOSED.** The lock was never the defect — it reports contention honestly. Fixed at both
  callers: `sync.py` now tracks skipped artifacts and prints `sync INCOMPLETE — N artifact(s)
  left stale`, naming them (exit code stays 0 by design: another process is doing the work);
  `load_lean_deps()` raises the skip from INFO to **WARNING** and names the blast radius —
  counts, atlas, graph and axiom closure for that run reflect the previous extraction.
- ⚠️ **Residue, unchanged:** the suite's auto-regenerating freshness checks shell out with
  **no lock at all**. Separate from A1's caller defect; not addressed here.
- **Documented in:** `QA_QI_INFRASTRUCTURE_MAP.md` §2, `CHECK_AUTHORING_GUIDE.md` §5.

### A2. AI-Defense Tier 1 names files that do not exist — ✅ CLOSED (editorial), 1 item BUILDABLE

✅ **Disposition taken: reframe + coverage-map + renumber.** Building the document as written
was rejected — most of it had already shipped by other names, so building it would have created
second mechanisms beside working ones (the exact failure the architecture rules exist to
prevent).

- Retitled **Design Proposal**, with a status admonition at the top saying it does not describe
  the running system and must not be cited as evidence a control exists.
- New **§Coverage** section measured against the live registry: `axiom_closure_allowlist`
  shipped verbatim; `bundle_lean_refs_resolve` → `prose_theorem_reference_coverage`;
  `bundle_latex_compile_clean_citations` → `paper_latex_compiles`; the `maxHeartbeats` and
  `native_decide` Tier-1 items are enforced by Invariant #10's ratchet and
  `native_decide_regression`. Partials and absences are marked as such.
- **Invariant collision removed.** The proposal's rule is now explicitly UNNUMBERED, with a note
  that numbers are allocated only in `WAVE_EXECUTION_PIPELINE.md` (#15 axiom sign-off, #16
  tracked-hypothesis registry, #17 kernel no-go).
- Fixed a dangling self-reference to `docs/AI_DEFECT_DEFENSE.md` (never existed) and a stale
  `physics-qa` plugin name (`skeft-qa`).

⚠️ **One item is genuinely unguarded and is a SOUNDNESS item, not a style one:** `@[csimp]`
without a justification comment. `csimp` appears **nowhere** in `scripts/` or `tests/`, and the
attribute can smuggle an axiom past the kernel's usual guarantees (`leanprover/lean4` #7463).
Two citation-metadata checks (`citation_bibkey_form_matches_metadata`, the author/venue half of
`bibitem_registry_character_match`) are the other real gaps. **These three are the entire
buildable residue** — carried forward as new work, not as this item.

**Superseded original text:**

- **Where:** `docs/AI-DEFECT-DEFENSE-LAYER.md` names `scripts/pre_commit_hook.sh` and
  `scripts/install_pre_commit.sh` as its Tier-1 implementation.
- **Verified this pass:** both **absent** from the tree.
- ❌ **CORRECTED 2026-08-07 — an inherited claim that was doubly false.** This read
  *"Pipeline Invariant #16 cites that document as canonical, under a filename that is also
  wrong."* Neither half holds: the real Invariant #16
  (`WAVE_EXECUTION_PIPELINE.md:695`) is the **tracked-hypothesis registry**, the pipeline law
  does **not reference the AI-Defense document under any name**, and the filename is correct.
- ✅ **The real compounding defect, verified:** the document declares its **own**
  `## Pipeline Invariant #16` (`:162`), colliding with the live Invariant #16. Two unrelated
  rules share one number across two documents. Also verified: all five of its named Tier-2
  checks (`threshold_arithmetic`, `theorem_quoted_bound_matches_lean_literal`,
  `bibitem_registry_character_match`, `citation_bibkey_form_matches_metadata`,
  `bundle_latex_compile_clean_citations`) appear in **zero** code files.
- **Git history:** committed exactly once, as `7530fc13 "AI-Defect Defense layer draft"`. It
  is a **proposal**, and its own header (*"Canonical Specification"*) plus an
  *"Implementation:"* line are what make it read as a description of a live system.
- **Disposition (research complete, aligned with intent):** do **not** build a parallel
  Tier-1 hook beside `pre-commit-sync.sh`. Its highest-value intents were independently
  implemented under other names — `axiom` → `AXIOM_METADATA` is Invariant #15 +
  `axiom_closure_allowlist`; `native_decide` is `native_decide_regression` (ADR-002). Re-frame
  the document as a proposal carrying a **coverage map** (intent → the existing machinery that
  already meets it, or "residue, unbuilt"), renumber its invariant, and implement only the
  genuine residue. The `csimp` guard has no coverage anywhere and is the clearest residue.
- **Documented in:** `VALIDATION_GATE_TOPOLOGY.md` §5, `CHECK_AUTHORING_GUIDE.md` §5.

---

## B. Found during this pass, not previously documented

### B1. The counts-ordering guard's population is hand-listed and incomplete — ✅ FIXED 2026-08-07

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
- ✅ **FIXED.** `_COUNTS_CONSUMERS` is replaced by `_counts_consumers()`, which derives the
  set by AST over the registered check bodies, and `counts_fresh` moved to the FRONT of
  `_CANONICAL_ORDER` so it precedes every reader. Production comment in `validate.py`
  corrected — it carried the same incomplete pair. Mutation-verified: restoring the old
  position fails the derived assertion, which the hand-written tuple could not see.
  Residual, stated in both the test and the production comment: a body reaching
  `counts.json` through a helper without naming it is invisible to the scan.

### B2. No mechanism verifies the *accuracy* of any architecture document — ✅ CLOSED

- **What:** `validate.py --check architecture_inventory_fresh` gates two things: the census
  matches a fresh derivation, and no narrative states a census count. **Nothing verifies a
  description.** Every prose claim rests on its author having read the code.
- **Evidence this matters:** `QA_QI_INFRASTRUCTURE_MAP.md` drifted out of sync within days
  of being written and contradicted itself inside a single sentence, with a green suite
  throughout.
- ✅ **Fix 1 BUILT** — `architecture_inventory_fresh` gained a `doc_refs_resolve` leg:
  every path-like backticked reference across the directory must resolve against the tree,
  with a reasoned exception set for documents that name an absent file deliberately.
  Mutation-verified both ways — a renamed script fails it, and shrinking the exception set
  below a still-absent reference fails it. Build trees (`.lake`) are excluded or the scan
  costs minutes instead of a second.
- ✅ **Fix 2 BUILT** — `tests/test_architecture_claims.py`, 10 executable assertions over the
  load-bearing claims. The design that made it tractable: **bind to the sentence AND the code
  fact**. Each test asserts its claim is still present verbatim *and* asserts the code fact;
  rewording the claim fails it, changing the code fails it. Mutation-verified both ways —
  `five` → `four` in the hazard sentence fails the doc leg; `.measured` → `.passed` in
  `_memo.py` fails the code leg.
  ⚠️ Two of the ten were written as PROXIES first (a text window around a constant; a
  line-shape scan for `--strict`) and both were WRONG — replaced by AST/table deciders. The
  file's own docstring carries that warning, because a proxy here manufactures errors rather
  than merely missing them.
  Coverage is partial by design: the claims a reader would act on.
- **The gap fix 1 left:** a reference that resolves but whose surrounding sentence is false.
  Every error found in the 2026-08-07 accuracy pass was of that kind, and fix 2 is the answer
  to it — for the claims it covers. Outside that set, direct reading remains the only guard.
- **Interim mitigation, in place:** this pass verifies each claim by direct read and records
  the verification method alongside it, so a later reader can re-run the same check.

---

### B3. `docs/READINESS_GATES.md` describes gates that cannot do what it says — ✅ CLOSED

Not an architecture document, so corrected here rather than in place.

- **Gate 1 CitationIntegrity** (`:27`) states the intent as *"Title, authors, arXiv ID, DOI,
  journal/volume/page all match the primary source."* The evaluator performs
  **registry-coverage only** — `\bibitem` keys ⊆ `PrimarySource` nodes — and its own docstring
  says DOI fetch-and-verify is deferred to Stage 13. A reader takes the gate as verifying
  bibliographic content; it verifies registration.
- **Gates 9 and 10** (`NumericalFreshness`, `FirstClaimVerification`) each carry a
  **"Blocks on any:"** section. Verified by reading both evaluators: the only states either
  assigns are `needs-recheck` and `passed`. Neither can block.
- ✅ **CLOSED — prose corrected to the computed behaviour** (raising the evaluators was not
  taken: `FirstClaimLedger` does not exist, and Gate 9's teeth already live in `tables_fresh`).
  Gate 1 now states that it is registry COVERAGE and carries a table routing each content
  claim to the check that verifies it (`bibitem_title_primary_source`,
  `citation_primary_sources_present`, `provenance_doi_in_registry`) or to Stage 13 where none
  does. Gates 9 and 10 disclose their reachable states (`passed` / `needs-recheck`). The
  submission section now separates the human GREEN policy from the narrower mechanized rule.
- **Superseded fix shape:** correct the prose to the computed behaviour, or raise the evaluators to the
  documented behaviour. The second is a scope decision, not a doc edit.

### B4. Chain-of-backing links name Lean targets that do not exist — ✅ GATED (backlog ratcheted)

✅ **Guard built:** `validate.py --check chain_backing_targets_resolve` (`reviews.py`),
production-seeded-mutation verified, registered in `MUTATION_VERIFIED` + `PRODUCTION_SEEDED`.
Ratchets the unresolved population at its live value so it can only shrink, and names the worst
papers every run.

⚠️ **Re-measurement changed this item materially — read this before quoting the numbers below.**

1. **The 61 and 24 were string counts, not links.** The chain-link population is **20** links
   naming these two declarations, of which 16 carry no `link_state` at all (4 are already
   marked `missing_target`).
2. **Neither name appears in any `.tex`.** The exposure is a fictitious audit trail, not a
   manuscript claim resting on a retired axiom. Where `paper5_adw_gap` mentions
   `gap_solution_bounded` in prose, it does so to report it *disproved by counterexample* —
   an honest negative claim.
3. **`gap_solution_bounded` is not a false theorem — it is not a declaration.** It sits inside
   a `/- … -/` comment block in `TetradGapEquation.lean`.
4. **The real defect is ~8× larger than this item described:** **156** unresolved
   theorem/axiom/lemma chain links, **114** distinct targets, **21** papers/bundles. A naive
   resolver reports 515; the difference is module targets, short names, Lean core axioms and
   hand-written notation variants, all legitimate.

**Remaining work (separate from this item):** the 156-link backlog is data remediation across
21 papers, not an infrastructure fix. It is bounded and visible now; clearing it means
retargeting or `missing_target`-labelling each link, and lowering the ceiling as it falls.

**Superseded original text:**

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

### B5. `docs/WAVE_EXECUTION_PIPELINE.md` — the process LAW disagrees with the tree — ✅ CLOSED

✅ All five corrected, each re-measured against the owning artifact first. Where a fact was a
census or a pin, the fix names the **owner** instead of copying the value — `validate.BUNDLE_CODES`
for the roster, `lean/lean-toolchain` for the pin, `validate.py --list` for the check roster — so
the same drift cannot recur. The stage count is now tied to the Stage headings that define it.
(The 16 enumerated check names were verified to still resolve; only the "(16 total)" framing was
wrong, so the list stayed and its claim to completeness went.) `CLAUDE.md`'s own "61 checks" was
the same class and was de-hardcoded in the same pass.

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

### B7. `SURFACE_INVENTORY.md`'s header overstates how its own tables are derived — ✅ CLOSED

**This is a doc-accuracy defect whose fix requires a CODE edit, so it is filed rather than
made.** The sentence is emitted by the generator, not written in the tracked file.

- **Where:** `scripts/architecture_inventory.py:289` emits
  *"Every table below is read from the artifact that owns the population — the check registry,
  the gate roster, the plugin manifest, the AST of the graph builder."*
- **Why it is wrong, in two ways:**
  1. **The named source list is incomplete.** Measured, the eight tables draw on six kinds of
     source: `validate._CHECKS`; `readiness_gates.GATES`; `build_graph.SHAPE_MAP` **plus** the
     AST of `build_graph.py` and of `readiness_gates.py`; the plugin `hooks/hooks.json`
     manifest plus git hooks on disk; agent/command `.md` frontmatter; module attribute probes;
     and `bundle_registry` plus `papers/*/bundle_metadata.json`.
  2. **"Every table" is false for the registries table.** `registries()` iterates a
     **hand-written `probes` list** of ten names. Its population is curated in the generator,
     not read from an owning artifact.
- **The curation is CORRECT and should not be "fixed" into a derivation.** Measured:
  `src/core/constants.py` holds **67** module-level uppercase collections; the other 60 are
  physics data (`A1_EXT_DIMENSIONS`, `ADW_2D_MODEL`, …), not registries. "Is this collection a
  registry?" is an editorial judgement, and the function's own docstring says so —
  *"HAND-MAINTAINED is the point."* Deriving it mechanically would flood the table with
  lattice-scan constants.
- **So the fix is to the SENTENCE, not the mechanism:** state that most tables are read from
  the artifact that owns the population, and that the registries table is a deliberately
  curated list of the hand-maintained surfaces worth tracking.
- **One genuine omission to consider while editing:** `citations.PAPER_TO_PHASE` is a
  module-level mapping not in the probe list. Whether it counts as a tracked registry is the
  same editorial call.
- ✅ **CLOSED.** The header now distinguishes VALUES (read from the owning artifact, all seven
  derivations) from MEMBERSHIP (derived in six, curated in one, and says which). Re-verified
  clause by clause; the exception count is measured. The curation itself was deliberately left
  alone — mechanising it would flood the table with lattice constants.

---

## C. Watch list

### C1. `lean_zero_sorry` reads a derived artifact rather than the extraction — WATCH

- **Where:** `scripts/validation/checks/lean_substrate.py`
- **What:** Invariant #4's gate reads `docs/counts.json` (`lean.sorry_declarations`) rather
  than `lean_deps.json` directly. It is correct and hard-failing given fresh counts, and
  returns `passed=True, measured=False` when counts are absent or unparseable — the
  documented cannot-measure contract. Coupled to **B1**.
- **Not a defect today:** tier 0 catches `sorry` independently from lake's own output.
