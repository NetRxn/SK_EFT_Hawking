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
4. **The real defect is larger than this item described, and the figure is now reconciled:**
   **121** unresolvable theorem/axiom/lemma chain links, **60** distinct targets, **25** papers —
   measured by `chain_canonicalize.canonicalize_link`, matching `--report`'s independent count.
   ⚠️ An earlier pass reported 156 from a resolver written locally in the check; that resolver
   was deleted and the check now calls the shared one. **Never quote 156.**

**Remaining work (separate from this item):** the 121-link backlog is data remediation across
25 papers, not an infrastructure fix. ⚠️ It is an **upper bound**: `canonicalize_link` counts
ambiguous short names (`zero` → 12 candidates) as `theorem-absent`, so part of the population is
a naming artifact. Clearing it means retargeting a citation or disambiguating a name, and
lowering the ceiling as it falls.

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

### B6. "Stage 10" names two different things — ✅ CLOSED

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
- ✅ **CLOSED — neither rename was needed; the premise was wrong.** Re-reading the law showed
  claims review is not a rival Stage 10 but a **sub-gate INSIDE** Stage 10: its sub-section at
  `:407` sits within the Stage-10 body, and Stage 10's own exit gate requires *"paper claims
  review has zero FAIL"*. So "Stage 10" in `BUNDLE_LIFT_PROCEDURE` and `gate_precheck s10` is
  the same stage narrowed to its exit condition — there is no second Stage 10 and nothing to
  renumber.
- Both documents now say so explicitly: a scope note under the law's Stage 10 heading, and a
  corrected cross-reference in `BUNDLE_LIFT_PROCEDURE` (whose `Stage 10 ↔ §9` line asserted an
  equivalence too narrow — §9 is the gate, §§3–7 are the drafting half).
- **Superseded fix shape:** rename one of them, or have the law name claims review as its own
  stage. Not required; the numbering was already consistent.

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

---

### D1. ~~Legacy drafts assert a retired axiom~~ — WITHDRAWN, no defect exists

Filed and withdrawn within the same pass. `paper18_doublon_gate` and `paper20_scalar_rung` both
carry *"since retired into the tracked Prop `TPFConjecture`"*; the qualifier follows a
`SPTClassification.lean` filename, and a regex that splits sentences on `.` truncates before it.
`validate.py --check axiom_count_prose_consistency` scans all 64 drafts against
`docs/counts.json` and reports **0 stale claims**. The check was right.

**Kept as an entry deliberately:** the next person to scan paper prose for Lean identifiers will
reach for the same sentence split. Cite the check's verdict instead of re-deriving one.

### D2. Chain-link scans must use the LaTeX-escaped identifier — OPEN (documentation of a trap)

- **What:** a draft writes `gapped\_interface\_axiom`, never the raw identifier. Any scan of
  `papers/**/*.tex` for a Lean name that does not unescape `\_` reports **zero hits and is
  wrong**. This produced a false claim in `QA_QI_INFRASTRUCTURE_MAP.md` (V8 atom Q10).
- **Who is exposed:** any future check or audit correlating Lean names with manuscript prose.
  `prose_theorem_reference_coverage` already handles verbatim forms — **verify it unescapes**
  before assuming the trap is closed there.
- **Fix shape:** a shared unescape helper for prose-vs-Lean correlation, so each new consumer
  does not rediscover this. Needs code.

### D3. `I1`'s line-number citation for the disproved stub is off — OPEN (minor)

- **Where:** `papers/I1/paper_draft.tex:494` and `:512` — *"a commented-out stub at
  lines~307--321"*, and `:493` — the live theorem at *"lines~329--345"*.
- **Actual:** the `/- … -/` block spans **311–325**; `gap_solution_monotone` is at **333**.
- **It is a systematic 4-line offset, not a typo** — both citations are short by exactly 4, so
  the file gained four lines above that point after I1 was written. Any other line-number
  citation into this file is likely off by the same amount.
- **Fix shape:** cite the block by declaration name rather than by line. A line number in prose
  is invalidated by any edit above it and nothing checks it. Paper content.

---

### D4. Ledger coverage — ✅ 100% (361/361). The residual risk is perishability, not coverage

Measured 2026-08-07, after V8. **This is the honest state of the accuracy effort**, replacing
the ledger's earlier unqualified "all seven VERIFIED".

- **Where:** `docs/architecture/.working-docs/ACCURACY_LEDGER.md` §Final state carries the
  per-document table and the measurement method.
- **The number:** ✅ **361 atom rows against 361** load-bearing sentences + table rows across the six
  prose documents. Every one has a row. Was 217 (60%) when first measured.
  Superseded count: 337 against 361 load-bearing sentences + table rows across the six
  prose documents (`SURFACE_INVENTORY.md` is generated and decided by regeneration+diff).
  V9 (END_TO_END_MAP §9) and V10 (VALIDATION_ARCHITECTURE remainder) closed 25 units.
- **It is an UPPER bound.** A compound sentence counts once in the denominator but owes one row
  per clause — the granularity failure this ledger exists to prevent. True coverage is lower.
- **The queue:** `CHECK_AUTHORING_GUIDE.md` 14 uncovered · `END_TO_END_MAP.md` 13 — the last
  two. **V9–V18 closed 120 units.** Fully enumerated (five of seven):
  `SURFACE_INVENTORY.md`, `VALIDATION_ARCHITECTURE.md`, `README.md`,
  `VALIDATION_GATE_TOPOLOGY.md`, `QA_QI_INFRASTRUCTURE_MAP.md`.
- ⚠️ **`END_TO_END_MAP.md` is the least verified, not the cleanest.** It records zero
  corrections over 34 atoms, which reads as health; it is 43% coverage of a document no other
  mechanism checks.

**Why this is not simply "finish the list."** V8 measured that a correction is as error-prone
as the prose it replaces: 5 of its 35 atoms were false, 4 of them written by the pass that had
just corrected other false claims. **Every edit creates unverified prose, including edits made
to fix unverified prose.** A pass that edits while it verifies does not converge.

**Fix shape — separate the two activities:**
1. a verify-only sweep that records atoms and files defects, changing no document;
2. a correction pass applying the filed defects;
3. a re-verify of exactly the sentences step 2 touched.
Steps 2 and 3 are small and bounded. Interleaving them, as every pass so far has done, is what
keeps the target moving. No code required — this is process, and it is why coverage stalled.

---

### D5. The bundle readiness signal is inverted — OPEN (CRITICAL)

Full analysis: [`docs/audits/2026-08-01-publication-readiness/`](../../audits/2026-08-01-publication-readiness/ADDENDUM-2026-08-07.md).

- **What:** `readiness` is GREEN iff 0 blockers ∧ ≤5 advisories ∧ a recorded Stage-13 review.
  Blockers derive from `ReviewFinding` nodes, which are minted by reviews. A bundle never
  reviewed has no findings and qualifies for GREEN.
- **Measured:** non-RED bundles average **31** sentences reviewed; RED bundles average **71**.
  The one GREEN bundle (D9) has **0**. The most-reviewed bundle (I1, 290) is RED.
- ⚠️ **Stated precisely:** the formula DOES guard the unreviewed case
  (`not review_recorded → YELLOW`) and withholds GREEN on a blocked or uncomputable P1 gate. The
  defect is that `review_recorded` does not discriminate review KIND — a 16-anchor attribution
  sweep satisfies `stage13_review_doc` exactly as a full adversarial pass does.
- **Also OPEN: transition 2 of the promotion path has no actor.** No code writes `"green"` to any
  `stage*_status`; reviewer agents have no write path. State machine now documented in
  `END_TO_END_MAP.md` §8. The status enum has drifted: 3 of 5 live values are undeclared.
- **Fix shape (needs code):** the bundle layer needs the distinction `CheckResult.measured`
  already gives the check layer (ADR-009 D2). A bundle with no `claims_review.json` must be
  UNMEASURED, never GREEN. Plus: a check that every bundle HAS a claims review; an enforcement
  point for Stage-9/10-before-13; `stage13_review_doc` recording the review KIND (a 16-anchor
  attribution sweep currently satisfies the same field as a full adversarial pass); and either
  writers for `stage*_status` or their removal.

### D6. Corpus-wide Lean pin drift in paper drafts — OPEN

⚠️ **A CHECK ALREADY MEASURES THIS — do not re-measure by hand.**
`validate.py --check paper_toolchain_pin_drift` (Class TP, advisory) resolves both the Lean
version *and* the Mathlib rev against `lean-toolchain` + `lakefile.toml`.

- **Measured by the check:** **29 pin-drift sites + 5 capability-claim sites across 65 drafts**,
  touching **11 bundles** — D2, D6, D9, D10, D11, D12, E1, E2, I1, I3, L2 — plus legacy drafts
  (`paper44`, `paper5`, `paper6`, `paper7`) and `phase6AA_qnetwork_preprint`.
- ⚠️ A hand scan on the Lean version string alone reports **8** bundles and misses every Mathlib
  rev (`c4843367`, `5e932f97`, `8850ed93`), because a hex scan collides with ISBNs and Aristotle
  run IDs. The check disambiguates; a manual scan cannot. **Never quote a hand count here.**
- **Capability claims are a distinct class the check separates:** a sentence asserting what the
  *pinned* Mathlib does or does not provide can be flipped by a pin bump — `D6:327`, `D6:787`.
- **Why it matters:** for bundles claiming reproducible kernel-checking, a wrong pin means a
  referee's reproduction fails and reads as a broken substrate.
- **The residue is not measurement, it is (a) gating** — the check is advisory, so nothing fails
  on pin drift — **and (b) prevention**: drafts should cite the pin through a generated macro as
  they already do for counts. Both need approval per §6a.

### D7. No mechanism assesses whether prose serves a reader — OPEN

- **Verified absent:** zero validation checks for readability/style, zero reviewer agents briefed
  on it, zero mentions in `WAVE_EXECUTION_PIPELINE.md`.
- **Measured consequences:** 171 sentences over 60 words across 21 drafts; 7 bundles contain a
  sentence over 100 words (max **179**); em-dash density spans **11×** within the corpus
  (L1 36/1000 → D9 391/1000) and the gradient tracks bundle recency.
- **Fix shape (needs code):** a readability ratchet in the house idiom calibrated against L1/D1;
  a `prose-reviewer` agent as the fourth reviewer; a gate before Stage 13.
- ⚠️ **The decider must not be the generator.** Metrics computed independently of the rewriter,
  and human calibration on a sample.

### D8. No required-content contract for the architecture documents — OPEN

- **What:** `README.md`'s ownership table declares which question each document must answer.
  Nothing verifies that it does. `README.md:14` assigns *"how does work get from a roadmap to a
  signed-off publication?"* to `END_TO_END_MAP.md`, which contained no promotion path at all
  until 2026-08-07 — while both documents were verified 100% accurate at assertion granularity.
- **Why the ledger cannot catch it:** assertion-granularity verification is a **soundness**
  check. It asks whether every sentence present is true; it cannot ask whether a required
  sentence is absent. A hard requirement can be wholly missing with the suite, the ledger and
  `architecture_inventory_fresh` all green.
- **Fix shape (needs code):** a fourth leg on `architecture_inventory_fresh` deriving the
  question→document map from `README.md`'s table and asserting each target document contains a
  section answering it — heading-level at minimum, so the check is structural rather than a
  keyword proxy. This is the missing completeness half of the doc-accuracy guard.

### D9. The AI-disclosure template asserts unbacked numerical traceability — OPEN (claim integrity)

- **Where:** `docs/DISCLOSURE_TEXT.md:27-29`, `:42-43`; carried by **11 drafts** (D1, D2, D3, D4,
  D5, D9, E1, L2 among them).
- **The claim:** *"all numerical claims trace to the repository's computation pipeline through its
  automated validation checks."*
- **The project's own checks contradict it:** `numerical_literals` = 116 inline literals,
  `count_literals` = 107 hard-coded counts across 64 papers; D9 has no `claims_review.json`.
- ⚠️ **Root cause of the worst instance:** `\substantivetheorems{}` is **project-scoped** and used
  as if **paper-scoped**, so D1's abstract states the whole library's theorem count as its own and
  *auto-inflates* as the library grows. The anti-drift macro is the overclaim's source.
- 📐 **Denominator corrected 2026-08-07.** This item read *"a 114-theorem chain (~230×)"*. The 114
  is **not D1's substrate** — it is the population of the nine 1+1D BEC modules over which §7.2's
  reuse fraction is computed, a different set for a different purpose. D1's substrate is its apex
  closure: **249 declarations**. Use that ratio; do not carry the old one forward.
- **Also in D1, same class:** the draft does not say which of the project's two counting
  conventions its `114` uses (source-level vs the `lean_deps` extraction, which additionally counts
  equation lemmas and gives 194 for the same modules). D11's draft discloses both explicitly and
  names the one it uses — borrow that sentence when fixing this item.
- **Fix shape:** template first (the traceability clause states only what is true), then per-bundle;
  and `\substantivetheorems{}` needs a per-bundle scoping — which is `SYNTHESIS.md` §6 Phase 0
  item 6, **withdrawn pending §6a approval**. Do not build it.
- Full working: `docs/audits/2026-08-01-publication-readiness/ADDENDUM-2026-08-07.md` §A5.

### D10. `_D11_MODULES` is hand-listed where the closure now derives it — OPEN (duplication)

- **Where:** `scripts/update_counts.py:398-406` hand-lists 22 module names to generate
  `\dxiModules`, `\dxiLines`, `\dxiTheorems`, `\dxiDefs`, `\dxiDepsTheorems` for D11's substrate
  paragraph.
- **What changed:** D11's apex closure (2026-08-07) reaches **exactly** those 22 modules — no
  module outside the list, no listed module unreached. The derived answer and the hand-maintained
  one now agree, which is the moment to delete the hand-maintained one.
- **Why it matters:** the roster is the same class of artifact the apex model exists to remove — a
  hand-listed set that silently goes stale when a module is added, renamed or split. A new D11
  module today would be counted by nobody and noticed by nothing.
- **Fix shape:** derive the module set from `bundle_closure.build_closures(...)["D11"].modules`.
  ⚠️ The *counting rule* must not change with it — the source-level rule (line-prefix, outside
  block comments, `abbrev` included) is stated in the draft's own prose and audited by its Stage-13
  history, and `lean_deps.json` counts differently on purpose (`\dxiDepsTheorems`).
- **Do not build without §6a approval.** Full working:
  `docs/audits/2026-08-07-d11-retrofit/FINDINGS.md` §2.

### D11. D11 §6.4 cites a conditional without its non-vacuity witness — OPEN (minor, prose)

- **Where:** `papers/D11/paper_draft.tex:462-464`.
- **The gap:** the Mexican-hat result is stated *at nonzero bias* and cites `bernal_mexicanHat`,
  which carries that hypothesis explicitly. `bernal_mexicanHat_witness` — the theorem showing the
  antecedent is inhabited — exists in `GrapheneBand/BernalBilayer` and is cited nowhere, so the
  draft leaves the conditional's non-vacuity unevidenced.
- **Why it is worth fixing:** §2.2 of the same draft is careful to state `latticeChern_Uwit`
  against the `latticeChern_trivial` fixture for exactly this reason. The discipline is the
  bundle's own; this is one place it lapsed.
- **Fix shape:** one clause in §6.4. Prose change — operator's call under ADR-010 C5.
- Full working: `docs/audits/2026-08-07-d11-retrofit/FINDINGS.md` §3.


### D12. D10 §4.2–§4.3 claim a first-ever DFT formalization over uninhabited structures — OPEN (CRITICAL, claim integrity)

- **Where:** `papers/D10/paper_draft.tex` abstract (`:39`) and §4.2–§4.3 (`:199-219`).
- **The gap:** `hohenberg_kohn_uniqueness`, `hohenberg_kohn_variational`, `levyLieb_functional`
  and `levyLieb_eq_HK_on_vrep` are stated over `GroundStateData`, `DensityVariational` and
  `LevyLiebData` — three structures with **no inhabitant anywhere in the tree** — and reduce to
  those structures' own fields (`ciInf_le` + `nondegen`; `rw; linarith` against `decomp`). The
  strict Rayleigh–Ritz inequalities of HK-I are **hypotheses**, not conclusions. Nothing connects
  any of them to §4.1's molecular Hamiltonian.
- **Why it is CRITICAL:** the abstract claims *"the first formalizations of … Hohenberg–Kohn/
  Levy–Lieb DFT … in any proof assistant"*. That is the sentence a referee tests first.
- ⚠️ **The Lean already discloses it and the paper does not.**
  `HohenbergKohnUniqueness.lean:19-21` names the variational inequalities as the load-bearing
  inputs; `HohenbergKohnVariational.lean:26-27` says the module is not connected to
  `molecularHamiltonian_essSelfAdjoint`. The defect is entirely in the manuscript.
- **Not a correctness defect.** Every theorem is true and kernel-pure, and §4.1's *unconditional*
  molecular self-adjointness is verified genuine (takes no analytic-hypothesis argument).
- ✅ **The fix template exists in the corpus.** D4 §5 handles the identical structural situation —
  a theorem whose content sits in a definition — and says so at the point of use: *"We **define**
  `WRTInvariant.wrtS2xS1` as `C.n` directly … the companion theorem `wrt_S2xS1_eq_rank` is a
  definitional sanity-check (`rfl` on the definitional unfolding), **not a proof of the
  Verlinde-formula chain**."* Copy that sentence's shape.
- **Fix shape, two options, prose-only vs. real work:** (1) narrow the claim — the layer is an
  axiomatized HK/Levy–Lieb interface plus its formal consequences; or (2) construct one
  `DensityVariational`/`GroundStateData` instance from §4.1's Hamiltonian, which would make the
  present claim true. Operator's call under ADR-010 C5. **The current prose is not a third option.**
- Full working: `docs/audits/2026-08-07-d10-retrofit/FINDINGS.md` §3.

### D13. D1 §3.1 mis-describes four `decide` proofs as `native_decide` — OPEN (minor, prose)

⚠️ **THIS ITEM WAS FILED WRONG ON 2026-08-07 AND IS RESTATED HERE. The original text claimed
`Lean.ofReduceBool` appears on ZERO declarations project-wide and concluded there is no
load-bearing `native_decide` anywhere, that F had the same defect, and that ADR-010's
`native_decide` posture item was thereby resolved. All three were false — see the correction
below before citing anything in this item.**

- **What survives, verified two ways:** `papers/D1/paper_draft.tex` §3.1 says the four counting
  theorems are *"independently closed by `native_decide`"*. They are proved **`by decide`**
  (`SecondOrderSK.lean:260, 272, 285, 937`), their docstrings say *"Use decide."*, and their
  `axiom_deps_project` is **empty** — no `._native.native_decide` marker. The sentence is wrong
  about those four theorems.
- **Why it still matters:** `decide` is kernel-checked, `native_decide` is not. D1 understates
  its own kernel purity in the place a referee looks.
- **Fix shape:** one sentence in §3.1. Prose-only.

#### ❌ Correction — the corpus-wide claim is WITHDRAWN

| withdrawn claim | measured truth | decider |
|---|---|---|
| *"`Lean.ofReduceBool` appears on zero declarations project-wide"* | the field `axiom_deps_core` contains **only** `propext`, `Quot.sound`, `Classical.choice` — it never records that axiom, so its absence measured nothing | enumerate every distinct name in `axiom_deps_core` |
| *"there is no load-bearing `native_decide` anywhere"* | **546 declarations** are in the `native_decide` closure | `validate.py --check native_decide_regression` — an **existing check** |
| *"F §7.2's `(native_decide)` annotation is false"* | **F is correct.** `FigureEightKnot.figure_eight_normalized` is literally `:= by native_decide` (`FigureEightKnot.lean:122`) and carries `…_native.native_decide.ax_1_1` in `axiom_deps_project` | read the source; read the right field |
| *"ADR-010's `native_decide` disclosure posture is resolved on the merits"* | **not resolved, and not mine to resolve** — it is an operator-owned open item, and the premise it was closed on was false | ADR-010 §Open |

**How the error was made, because the mechanism is reusable.** The project marks `native_decide`
in **`axiom_deps_project`** as `<decl>._native.native_decide.ax_N_M`, not in `axiom_deps_core` as
`Lean.ofReduceBool`. Probing the wrong field returned an absence that read as a measurement.

⚠️ **The project had already documented this exact trap.** `lean_statements.py:557-564` records
that *"`native_decide` axioms were STRIPPED from the project-axiom list before the test, so a
`native_decide`-backed refutation scored kernel-pure"*, and states the 546 figure in as many
words. **`native_decide_regression` measures this and was never run.** That is the goal's own
standing constraint — *before measuring anything, check whether a check already measures it* —
violated for the fifth time in this workstream.

- Full working: `docs/audits/2026-08-07-d1-retrofit/FINDINGS.md` §3 (corrected) and
  `docs/audits/2026-08-07-f-retrofit/FINDINGS.md` §4 (withdrawn).

### D14. D1's append log records four `Lift-section` events that inserted no content — OPEN

- **Where:** `papers/D1/append_log.json`, the four 2026-05-06 events sourcing
  `_phase6n_W1a_lean_only` (§3), `_phase6n_W2c_lean_only` (§5), `_phase6n_W2b_lean_only` (§6) and
  `_phase6o_W1a_lean_only` (§6).
- **What is in the manuscript:** four commented-out headings after `\end{thebibliography}`, each
  carrying `TODO: lift content` plus two further unresolved TODOs. Zero rendered words.
- **The named content is substantial:** a kinematic-dispersive geometric envelope with a
  closed-form `γ_n`; an LDP linear-response framework; a quantum-Crooks no-go landscape; boostless
  / Carrollian soft theorems with a Strominger-triangle closure.
- **Commenting the stubs out was correct** and is documented (2026-05-06 Session 2 — they were
  empty artefacts of `bundle_append.py`'s default insertion). The defect is that the **log still
  reads `Lift-section`**, so any count of absorptions taken from it over-counts D1 by four.
- ⚠️ **BROADENED 2026-08-07 — eleven events across two bundles.** D3's `append_log.json` records
  **seven** more empty `Lift-section` events (6n W1a → §6, 6n W2c → §3, 6o W1a → §3, 6o W1b → §6,
  6o W3b → §6, 6o W1c → §10, 6o W2a → §17), out of 26 `Lift-section` events total. **D2 adds two
  more** — *"SymTFT audit substrate"* and *"APS η-invariant cross-bridge to Z16 Dai-Freed"*, both
  commented-out stubs after its bibliography — and **D4 adds three more** (*SymTFT audit
  substrate*, *Lindbladian S-matrix axiomatization NO-GO*, *ETH-α productive-value refutation
  tableau*) — so the pattern spans **four** bundles. The named
  content is substantial and unpublished anywhere: a Kerr-Schild double-copy on Petrov-D acoustic
  geometry with a three-obstruction BCJ no-go, an APS η-invariant substrate for analog horizons,
  an Itô/LDP cross-bridge, and a dissipative-SK-EFT bootstrap-uniqueness no-go.
- ✅ **D3 handles the stubs better than D1, and the difference is the fix to copy.** Each D3 stub
  carries an in-line note — *"Lift body content remains pending; restore `\section` + `\label`
  once content lands"* — so a reader of the source knows the state. D1's say only that a
  bookkeeping anchor was preserved. **The log is wrong in both.**
- **Fix shape:** two parts, and they are different decisions. (a) Bookkeeping: the log needs a
  lift action that means *registered, not lifted* — a schema change, so §6a applies. (b) Content:
  whether to lift the eleven waves is an ADR-010 C5 scope call, and it bears on the
  charter-length shortfall in both bundles.
- Full working: `docs/audits/2026-08-07-d1-retrofit/FINDINGS.md` §4.

### D15. The flagship surveys a 17-bundle program; 21 exist — OPEN (CRITICAL, scope claim)

- **Where:** `papers/F/paper_draft.tex` — abstract, §1.1, §1.2, §9.4, §11.1, §11.2, §12.3. The
  claim is made seven times and consistently: *"the sixteen sibling-bundle threads"*, *"$17$
  publication targets"*, *"Tier 1 (8 deep papers): D1 … D8"*, *"citing all 16 siblings"*.
- **The fact:** the live roster is **21** bundles. **D9, D10, D11 and D12 appear nowhere in F.**
  Three of them now have declared apexes and measured closures.
- **Why CRITICAL:** this is not a stale count in a narrative — it is the paper's **scope**. A
  survey that enumerates its contents and omits four of them is wrong about what it surveys, and
  *"integrates the sixteen sibling threads into a single survey"* is its thesis.
- **§11.1 compounds it:** *"the substrate program has shipped 17 bundles to reviewer-triple-closed
  Stage-13 GREEN status."* Both halves fail — the roster is 21, and no bundle is submittable. F
  itself is `readiness: RED` with 23 open blockers.
- **§7's D6 checklist is stale in the other direction:** six boxes, all unchecked, including
  waves 6v.2 / 6v.5 / 6v.6 — all of which have shipped and appear in D6's own declared apexes.
  At least four of six are done.
- **Same item, smaller instances (§9 infrastructure prose), each re-derived not assumed:**
  *"29+ checks"* (live **66**) · *"Pipeline Invariants 1--14"* (they run to **#17**) ·
  *"`physics-qa:figure-reviewer`"* (plugin is **`skeft-qa`**) · *"branches D.1/D.2/D.3"*
  (branch **D.4** exists) · a hardcoded `$\sim 322$` where `\aristotleproved{}` is a macro in
  the `counts.tex` F already `\input`s — correct today, guaranteed to drift.
- ⚠️ **Two more instances found during the D3 retrofit (2026-08-07), and they point opposite ways.**
  (a) F **overstates**: its §6.3 bullet says the Vergeles triple *"discharges cleanly"* with no
  caveat, while F's own §10 register says *"on the substrate's tracked-hypothesis Prop record
  bundle"* and D3 §5.4 + §28.3 both record the one-loop calculation as OPEN. The flagship
  contradicts itself, and the honest version is the one in the cleared register.
  (b) F **understates**: §6.2 and §10 both call the factor-6000 Wen-ADW figure *"an informal
  extrapolation … not separately Lean-verified at the Newton-constant level"*, but D3 ships
  `EmergentGravityBounds.wen_adw_factor_6000`, a resolved kernel-pure theorem proving
  `1/6202 < G_Wen/G_c < 1/6000` for every nonzero cutoff. The hedge was true when written.
- **Fix shape:** F cannot be brought current by editing counts; the roster sections need
  rewriting against the live roster, and the §9 figures need to become macros or citations. This
  is content work under ADR-010 C5, and it is the strongest argument for retrofitting the
  remaining bundles **before** F is redrafted — F's job is to describe them.
- Full working: `docs/audits/2026-08-07-f-retrofit/FINDINGS.md` §2, §3, §5.

### D16. The program's central synthesis claim has no Lean witness — OPEN (CRITICAL, claim integrity)

- **The claim:** the `N_f` in the Sakharov coefficient `G_N = 12π/(N_f Λ²)` and the `N_f = 16`
  that fixes the Standard-Model anomaly classification are **the same `N_f`** — *"the substrate is
  one object; its faces are the sibling bundles' worth of predictive register."*
- **Where:** `papers/D3/paper_draft.tex` §1 and §28.1; `papers/F/paper_draft.tex` abstract, §1.4,
  §6.1 and §12.1 — where F elevates it to *"the synthesis claim NEW to this flagship, absent from
  any individual sibling bundle and load-bearing for the architectural argument."*
- ❌ **NARROWED 2026-08-07 after D2's retrofit — the original filing was too broad.** It said *"no
  D3 gravity-side declaration reaches the anomaly-side tree at all."* **False.** D2's closure makes
  it measurable: **D2 ∩ D3 = 3**, all in `SKEFTHawking.GenerationConstraint`
  (`div_24_8n_implies_div_3_n`, `div_3_n_implies_div_24_8n`, `generation_constraint_iff`), and a
  per-apex walk over all 89 of D3's apexes shows exactly one reaches them:
  **`horizon_wittTrivial_iff_three_generations`**. D3 §7.3's prose — *"ties the horizon boundary
  condition to the program's three-generation result through the same Witt invariant"* — **is
  witnessed.**
- **What still stands, and it is the claim this item should always have made:** the `N_f` in the
  **Sakharov coefficient** is a *Dirac-flavour count in a heat-kernel expansion*; the `N_f` in
  `c₋ = 8 N_f` is a *generation count*. **Those two are what F asserts to be identical, and that
  has no witness.** Measured: the Sakharov/heat-kernel chain (5 apexes → 19 declarations across
  `HeatKernelExpansion`, `LinearizedEFE`, `MicroscopicCoefficientMatch`, `EinsteinCartanExtension`)
  intersects D2's closure in **0** and never reaches `GenerationConstraint`. The bridge that exists
  runs through the horizon central charge, not through the Sakharov coefficient.
- **Also measured:** D3 ∩ D1 = 0; no declaration anywhere bridges the *Sakharov* `N_f` to an
  anomaly/modular/generation count (the three near-misses are lattice-signature and SymTFT theorems
  about `16 ∣ σ`, a different statement).
- ⚠️ **This does NOT say the claim is false.** Two formalizations of different facets of one
  physical object can have disjoint proof DAGs; a shared declaration is a sufficient witness for
  identity, not a necessary one. **It says the claim is unformalized in a corpus whose selling
  point is that its claims are formalized.**
- **D3 is the more careful of the two:** §1 attributes the identity to *"Bundle L2, lifting
  from [Roehm2026Modular]"* — a citation. F states it flatly and claims it as its own novelty.
- **Fix shape, and the choice matters:** (a) **formalize it** — a theorem tying the `N_f` of the
  heat-kernel calibration to the `N_f` of the anomaly classification would make the program's
  headline architectural claim machine-checked, and is the highest-value single theorem the
  substrate could ship; or (b) **scope the prose** to what is actually established: the same
  numeral appears in both derivations, and the identification is a modelling claim. Operator's
  call under ADR-010 C5.
- ✅ **Re-run at D2's retrofit, as this item required — and it changed the finding.** The lesson:
  a narrow probe (D3's *calibration* modules) was reported at wide scope (D3's *gravity side*).
  The probe was right; the sentence covering it was not. Full working:
  `docs/audits/2026-08-07-d2-retrofit/FINDINGS.md` §3.
- Full working: `docs/audits/2026-08-07-d3-retrofit/FINDINGS.md` §2.

### D17. D3's tracked-hypothesis registry contains two dangling `\ref`s — OPEN (minor)

- **Where:** `papers/D3/paper_draft.tex` — `sec:cfl-z3-matching` and `sec:singularity-thms` are
  referenced and never defined, so both render as `??` in the compiled PDF.
- **Why it is worth fixing despite being minor:** both live in **§28.3, the tracked-hypothesis
  registry** — the mechanism D3 offers as its accountability device, closing with *"A reader with
  auditing intent can resolve every open obligation in this list."* They are the pointers for
  `H_TopologicalOrderBeyondLG` and `IsADWPenroseApplicable`. §24.3 uses the second one again.
- **Fix shape:** repoint to `sec:cfl` and `sec:penrose`, the sections that carry the content.
  Prose-only.
- Full working: `docs/audits/2026-08-07-d3-retrofit/FINDINGS.md` §3.
