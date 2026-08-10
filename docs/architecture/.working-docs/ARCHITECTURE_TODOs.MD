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

### D2. Chain-link scans must use the LaTeX-escaped identifier — ✅ DONE 2026-08-09

> **The entry says to VERIFY `prose_theorem_reference_coverage` unescapes before assuming the trap is
> closed there. Verified: it does** — `\texttt{gapped\_interface\_axiom}` extracts as
> `gapped_interface_axiom`.
>
> ⚠️ **And the trap had already been rediscovered twice**, which is what the entry predicted would
> keep happening: `prose_lean_refs._PROSE_UNESCAPE_RE` (unescape, then match) and
> `lean_substrate._tex_name_pattern` (build an escape-tolerant pattern) are two independently-correct
> solutions to one problem in two modules.
>
> **Both shapes now live in `validation/_tex.py`** — `unescape_tex_identifier` and
> `tex_escaped_name_pattern` — because the two directions are genuinely different (name→prose vs
> prose→name), with the false-claim history (ledger V8 atom Q10) recorded at the definition. Both
> call sites delegate; 101 tests pass and both checks stay green.
>
> **Residue, stated rather than overclaimed:** a loose scan flags nine further scripts that read
> `.tex` and handle identifiers. That scan is a weak instrument and I did **not** audit all nine —
> two were read properly and both were already correct. A third consumer now inherits the helper
> instead of re-deriving it, which is what this entry asked for.

- **What:** a draft writes `gapped\_interface\_axiom`, never the raw identifier. Any scan of
  `papers/**/*.tex` for a Lean name that does not unescape `\_` reports **zero hits and is
  wrong**. This produced a false claim in `QA_QI_INFRASTRUCTURE_MAP.md` (V8 atom Q10).
- **Who is exposed:** any future check or audit correlating Lean names with manuscript prose.
  `prose_theorem_reference_coverage` already handles verbatim forms — **verify it unescapes**
  before assuming the trap is closed there.
- **Fix shape:** a shared unescape helper for prose-vs-Lean correlation, so each new consumer
  does not rediscover this. Needs code.

### D3. `I1`'s line-number citation for the disproved stub is off — ✅ DONE 2026-08-09

> **Reproduced exactly:** the `/- … -/` stub spans **311–325** (cited 307–321) and
> `gap_solution_monotone` runs **333–349** (cited 329–345). A uniform +4, at three sites in I1
> (`:493`, `:494`, `:512`), all corrected.
>
> ⚠️ **The entry's generalisation — "any other line-number citation into this file is likely off by
> the same amount" — was CHECKED and does not hold beyond `TetradGapEquation.lean`.** Every other
> line citation in I1 was verified against source: `Basic.lean:152` = `structure DissipativeCoeffs`
> ✓; `SKDoubling.lean` 156–168 = `structure KMSSymmetry` ✓, 367–379 = `structure FirstOrderKMS` ✓,
> 412–439 = `theorem firstOrder_uniqueness` ✓, 244–280 brackets the `firstOrderDissipativeAction`
> docstring+def ✓; `EWBaryogenesisChiralityWall.lean` 106–114 = `sphaleronSuppression_le_one` ✓.
> **The drift is local to one file, not corpus-wide.**
>
> ⚠️ **A measurement note:** the first extraction pass used one regex for "filename plus number"
> and both missed the `lines~307--321` sites (no adjacent filename) and invented a hit from a date
> (`update_counts.py:2026--6`). Enumerating by citation FORM found all nine. Fourth regex-over-
> structured-text failure this branch.
>
> The waiver coupling the entry flags (`waived:I1:gap_solution_bounded`) is untouched and still
> correct: `gap_solution_bounded` is at line 320, i.e. inside the 311–325 commented block, which is
> exactly what the waiver documents.

- **Where:** `papers/I1/paper_draft.tex:494` and `:512` — *"a commented-out stub at
  lines~307--321"*, and `:493` — the live theorem at *"lines~329--345"*.
- **Actual:** the `/- … -/` block spans **311–325**; `gap_solution_monotone` is at **333**.
- **It is a systematic 4-line offset, not a typo** — both citations are short by exactly 4, so
  the file gained four lines above that point after I1 was written. Any other line-number
  citation into this file is likely off by the same amount.
- ✅ **CONFIRMED LIVE and GENERALISED at I1's retrofit (2026-08-07).** The offset reproduces, and
  the coupling holds: I1 §10 names the `prose_theorem_reference_coverage` waiver
  (`waived:I1:gap_solution_bounded`) as *"the canonical waiver"*, so **the citation and the waiver
  must be fixed together** — half-fixing either leaves the other wrong.
- ⚠️ **The problem is not one citation.** I1 cites Lean and the registries by line number
  **pervasively**: `Basic.lean:152`, `SKDoubling.lean` 244–280 / 156–168 / 367–379 / 412–439,
  `EWBaryogenesisChiralityWall.lean:106–114`, and `constants.py` lines 2282 / 1391 / 2127 / 2329.
  This item's own note that *"any other line-number citation into this file is likely off by the
  same amount"* is now the general case, not a caveat.
- **Fix shape:** cite the block by declaration name rather than by line. A line number in prose
  is invalidated by any edit above it and nothing checks it. Paper content.

---

### D4. Ledger coverage — ✅ 100% (361/361) COVERED; ⚠️ the perishability queue is OPEN

> **Heading corrected 2026-08-09 by the closure reviewer.** The ✅ described *coverage*,
> which is genuinely 361/361, while the body carries an unexecuted queue and a three-step
> Fix shape. A reader scanning headings read this as closed. Coverage is closed;
> the queue is not, and the two are different claims.

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
- **The queue is CLOSED.** ⚠️ These two bullets described superseded state for two days,
  contradicting this entry's own corrected heading twelve lines above — the same
  correction-landed-at-one-site defect as D15 and D36. As of V9–V18 all six prose documents
  read 100% in the ledger's §Final state table: `CHECK_AUTHORING_GUIDE.md` 54/54 and
  `END_TO_END_MAP.md` 80/80 were the last two, and both are now fully enumerated.
- ⚠️ **`END_TO_END_MAP.md` was the least verified, not the cleanest** — it recorded zero
  corrections over 34 atoms, which reads as health, at 43% coverage of a document no other
  mechanism checks. It is now at 80/80, and the caveat that survives is the general one: the
  denominator counts a compound sentence once, so unit coverage overstates clause coverage.

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

### D5. The bundle readiness signal is inverted — ✅ DONE 2026-08-09 (CRITICAL)

> ⚠️ **FIVE of this entry's SIX sub-claims were already closed by ADR-011 Phase 2, and were
> re-measured rather than re-fixed.** Reproduced 2026-08-09:
>
> | sub-claim | state |
> |---|---|
> | "no code writes green to any `stage*_status`; reviewers have no write path" | **FALSE** — `record_review.py` is that writer |
> | "no enforcement point for Stage-9/10-before-13" | **FALSE** — `record_review.py` refuses it and `validate.py --check bundle_reviewer_stage_ordering` catches hand edits |
> | "`review_recorded` does not discriminate review KIND" | **FALSE** — `_KINDS_SUFFICIENT_FOR_GREEN = {"full-adversarial"}` |
> | "a bundle with no `claims_review.json` can be GREEN" | **FALSE** — Phase 2d already withholds it |
> | `_blocked_p1_gates_by_paper` returning `{}` on failure | **FALSE** — returns `None`, GREEN withheld |
> | status enum drift | **TRUE, and worse than stated** |
>
> **What was actually left, and is now fixed:**
>
> 1. **The state itself.** The withheld cases rendered **YELLOW** — "measured, has issues" — when
> the truth is "the evidence to judge does not exist". That is precisely the `CheckResult.measured`
> distinction ADR-009 gave the check layer and this entry asked for at the bundle layer. Both
> withholding paths now return **UNMEASURED**, and `datastar_bundles._VERDICT_ICON` renders it ⚪,
> distinct from 🟡. **D9 — the portfolio's only ever GREEN — now reads
> `UNMEASURED (Stage-13 evidence kind=unrecorded)`** instead of passing as merely imperfect.
>
> 2. **The enum guard, which was narrower than the entry said.** Not "3 of 5 values undeclared" but
> *the guard covered `stage13` only*: `stage9_status` and `stage10_status` had **no enum check at
> all**, and three live values (`not_started` ×2, `skeleton` ×1, `pending-redo` ×1) sat entirely
> outside any vocabulary. All three stages are now guarded against a declared `_STAGE_STATUS_ENUM`
> and undeclared values are recorded per bundle.
>
> **Not in scope and deliberately not forced:** every bundle having a Stage-10 artifact. D6 and D9
> still have none, and running Stage 10 is goal 2. UNMEASURED is the honest rendering of that until
> the reviewer stages run — which is the point of the state.

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

### D6. Corpus-wide Lean pin drift in paper drafts — ✅ DONE 2026-08-09

> **`paper_toolchain_pin_drift` now reports 0 pin-drift and 0 capability-claim sites, from 27 + 4.**
>
> **Fixed structurally, not by transcription.** Re-typing 27 live values only resets the clock; the
> v4.32.0 bump is what stranded them in the first place. `update_counts.py` now emits
> `\leantoolchain`, `\mathlibrev` and `\physlibrev` into the generated `docs/counts.tex`, read
> live from `lean-toolchain` + `lakefile.toml`, and every draft states its reproducibility
> coordinate through the macro. **A future bump cannot strand a draft, because no draft holds the
> value.** D10 additionally gained the `\input` it never had.
>
> **Two sites needed judgement rather than substitution.** The capability claims in
> `phase6AA` assert what the *pinned* Mathlib provides, and renumbering one without re-checking the
> capability is precisely the falsification the check warns about. `geometric_hahn_banach_compact_closed`
> was **verified present at the live pin** (`Analysis/Convex/Cone/Dual.lean`) before the version was
> updated, and the draft now records that re-verification.
>
> ⚠️ **Residue, stated:** `phase6AA` is Markdown and has no macro mechanism, so its pins remain
> literal and will drift again at the next bump. Every `.tex` draft is now immune; the one `.md`
> preprint is not.
>
> **Count note:** the entry says 11 bundles. Measured today it was 9 — D11 and D12 dropped out when
> TODO-D22's fix stopped reporting a CURRENT PhysLib pin as drift. Fixing the instrument shrank the
> corpus before the corpus was touched.
>
> ⚠️ **A compile failure I did NOT cause:** `paper7_chirality_formal` fails on a Unicode ι. Verified
> by restoring the HEAD version in place and recompiling — it fails identically there. Pre-existing
> legacy debt, covered by the legacy ratchet (14 legacy drafts, 0 bundles). The first check of this
> ran the HEAD copy in `/tmp` without the figures directory and produced a *different* error, which
> would have supported the wrong conclusion.

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

### D7. No mechanism assesses whether prose serves a reader — ✅ DONE 2026-08-09

> ⚠️ **All three "verified absent" claims are now FALSE, and two were closed by ADR-011 before this
> pass.** Re-measured: `bundle_reader_facing_voice` exists and is green (Phase 3, Gate 15); the
> `prose-reviewer` agent exists at `.claude/plugins/skeft-qa/agents/prose-reviewer.md` (Phase 5,
> F-04); `WAVE_EXECUTION_PIPELINE.md` mentions the mechanism three times. Em-dash density is gated
> separately by `bundle_prose_em_dash_free`, currently 0 across 21 drafts.
>
> **What was genuinely still open is the READABILITY half, and it had grown.** This entry recorded
> *"171 sentences over 60 words … 7 bundles contain a sentence over 100 words (max 179)"*. Live
> figures: **199 over 60, and 22 over 100 across 14 bundles, longest 235 words** — partly from this
> branch's own additions, which is worth saying plainly.
>
> **Built:** `bundle_sentence_length`, a down-only ratchet (`SENTENCE_OVER_100_CEILING = 22`).
> Over-100 is gated because a sentence a referee must re-read to parse is not a style preference;
> over-60 is reported as an advisory baseline and deliberately **not** gated, because 60 words is
> defensible in a methods paragraph and gating it would fire on correct work
> (VALIDATION_GATE_TOPOLOGY §3).
>
> ⚠️ **The prose was NOT rewritten to lower the number in the same change.** This entry's own
> constraint is that *"the decider must not be the generator"*, and a metric shipped together with
> the edits that satisfy it has measured nothing. The ratchet is frozen at the measured value so it
> can only shrink. A seeded test drops the ceiling to 0 and asserts the gate fails, so it is not
> inert; another asserts the ceiling equals the live count, so slack cannot hide a regression.

⚠️ Not one item but two, and they must not be conflated: the **deterministic** voice ratchet is Phase 3 (Gate 15, no new data, fires on 19 of 21 today) and the **agentic** read-through reviewer is Phase 5 (F-04). Phase 5 depends on Phase 2 — an agent whose verdict lands in a `stage*_status` field that nothing writes is a fourth instance of D5, not a fix for D7.

- **Verified absent:** zero validation checks for readability/style, zero reviewer agents briefed
  on it, zero mentions in `WAVE_EXECUTION_PIPELINE.md`.
- **Measured consequences:** 171 sentences over 60 words across 21 drafts; 7 bundles contain a
  sentence over 100 words (max **179**); em-dash density spans **11×** within the corpus
  (L1 36/1000 → D9 391/1000) and the gradient tracks bundle recency.
- **Fix shape (needs code):** a readability ratchet in the house idiom calibrated against L1/D1;
  a `prose-reviewer` agent as the fourth reviewer; a gate before Stage 13.
- ⚠️ **The decider must not be the generator.** Metrics computed independently of the rewriter,
  and human calibration on a sample.

### D8. No required-content contract for the architecture documents — ✅ DONE 2026-08-09

> **Built as Leg 4 of `architecture_inventory_fresh` (`documents_answer_their_question`).**
>
> **The contract is a declared bidirectional link compared VERBATIM, not a keyword proxy.**
> `README.md`'s ownership table assigns a question to a document; the document must carry
> `> **Answers:** <that exact question>`. A heading-keyword heuristic would pass on any document
> that merely mentions the topic, which is precisely the failure this entry describes:
> `END_TO_END_MAP.md` was assigned the promotion-path question and contained no promotion path,
> while the suite, the ledger and this very check were all green.
>
> **Measured before building: 7 of 7 owned documents had no such declaration.** All seven now do.
> `SURFACE_INVENTORY.md` is generated, so its line is **emitted by
> `architecture_inventory.py::_owned_question`**, which reads the question out of README rather than
> restating it — a second copy of the question is the drift this contract exists to prevent, and the
> generator raises rather than emitting an empty contract line.
>
> ⚠️ **Stated so a green here is not over-read: this is a completeness FLOOR, not proof of
> adequacy.** It catches an assignment that has drifted away from its answer. It cannot judge
> whether the answer is any good — that remains a reader's job.

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

### D9. The AI-disclosure template asserts unbacked numerical traceability — ✅ CLOSED 2026-08-09

> **Both halves fixed.** Kept in full below because the measurement history is the useful part.
>
> **Half 1, the clause.** The unbackable sentence is gone from `docs/DISCLOSURE_TEXT.md` (both
> variants) and from all **8** drafts that carried it (D1, D2, D3, D4, D5, D9, L2, E1). It now
> reads: *"The repository's public validation suite reports, for every draft, any numerical value
> written inline in prose rather than sourced from a generated table; that report is the authority
> on this manuscript's numerical provenance."* That is true, it is checkable, and it points at
> `numerical_literals` instead of asserting a universal over it.
>
> ⚠️ **A first replacement draft said "tables and figures are generated from the pipeline" and was
> DISCARDED before it shipped**: `bundle_tables_use_pipeline` reports D1 and E1 with hand-written
> tabulars and **zero** `\input{tables/}`. It would have replaced a false claim with a new one.
>
> ⚠️ **The population is 8, not the 4 a line-based `grep` reports.** The phrase wraps across a
> newline in four drafts. Whole-file, `re.S`.
>
> **Half 2, the root cause.** `scripts/render_bundle_counts.py` now emits
> `papers/<CODE>/bundle_counts.tex` per bundle from its **declared-apex closure**, defining
> `\bundleTheorems` / `\bundleDecls` / `\bundleModules`; `bundle_counts_fresh` gates it, and
> `render_bundle_counts.py --check` is the same derivation. **Six paper-scoped sites repointed** in
> D1, D5, E1 (two), E2 and F.
>
> **The overclaim was far worse than this item recorded.** Measured per bundle against the
> apex closure:
>
> | bundle | stated | honest | factor |
> |---|---|---|---|
> | E2 | 26 329 | **6** | **~4 400x** |
> | E1 | 26 329 | **11** | **~2 400x** |
> | D1 | 26 329 | **56** | ~470x |
> | D5 | 26 329 | **81** | ~325x |
>
> This item's "~230x" used 249 declarations as the denominator; the honest denominator for a
> *theorem-count* sentence is theorem-kind declarations, which is smaller again.
>
> ⚠️ **Four surviving `\substantivetheorems` uses are CORRECT and were deliberately left**: F's
> four project-scoped sentences (*"Project totals"*, *"The Lean backbone of the program"*, *"The
> Lean library currently ships"*, *"Total program output"*), D5's two counting-convention
> sentences, and I1's. The defect was never the macro; it was using a project figure for a
> paper-scoped claim, and the fix has to preserve the cases where the project figure is the
> right one.


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
- **Also in D1, after the D7 reassignment:** D1's measured substrate is **171** declarations, not
  the 249 first recorded. Use 171.
- **Also in D5:** its abstract states `\substantivetheorems` and `\totaltheorems` for D5's own
  content. D5's measured substrate is **216** declarations. Same project-scoped-macro defect.
- **Also in D1, same class:** the draft does not say which of the project's two counting
  conventions its `114` uses (source-level vs the `lean_deps` extraction, which additionally counts
  equation lemmas and gives 194 for the same modules). D11's draft discloses both explicitly and
  names the one it uses — borrow that sentence when fixing this item.
- **Fix shape:** template first (the traceability clause states only what is true), then per-bundle;
  and `\substantivetheorems{}` needs a per-bundle scoping — which is `SYNTHESIS.md` §6 Phase 0
  item 6, **withdrawn pending §6a approval**. Do not build it.
- Full working: `docs/audits/2026-08-01-publication-readiness/ADDENDUM-2026-08-07.md` §A5.

### D10. `_D11_MODULES` is hand-listed where the closure now derives it — ✅ DONE 2026-08-09

> **Re-verified before deleting:** D11's declared-apex closure and the 22-name literal agree with
> **zero difference in either direction**. That agreement is the moment to delete the
> hand-maintained copy, and it is now `_d11_modules_from_closure()`.
>
> `docs/counts.tex` regenerates **byte-identical**, so the derivation reproduces the literal rather
> than replacing it with something new. The **counting rule is untouched** — line-prefix, outside
> block comments, `abbrev` included — as the entry requires; only the module SET is derived.
>
> **Fails loudly on an empty closure** rather than falling back to a literal. A silent fallback is
> how a hand-maintained roster survives the mechanism meant to replace it, and that failure mode is
> asserted by test.

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

### D11. D11 §6.4 cites a conditional without its non-vacuity witness — ✅ DONE 2026-08-09

> `bernal_mexicanHat_witness` confirmed live at `GrapheneBand/BernalBilayer.lean:598`. §6.4 now
> cites it with its concrete point (γ = 1, u = 1/2, x = 3/8, E² = 1/8 < u² = 1/4), so the
> nonzero-bias conditional is evidenced as inhabited rather than left possibly vacuous — the same
> discipline §2.2 already applies with `latticeChern_Uwit` against `latticeChern_trivial`.

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


### D12. D10 §4.2–§4.3 claim a first-ever DFT formalization over uninhabited structures — ✅ DONE 2026-08-09 (CRITICAL)

> **Uninhabitedness confirmed by two instruments:** a source scan for constructions returns 0 for all
> three structures, and `lean_deps.json` shows only auto-generated projections and eliminators
> (`.E`, `.F`, `.casesOn`, `.ctorIdx`) with **no constructor application anywhere**.
>
> **Fixed in the manuscript, where the defect was.** D10 gains §4.4 *Scope of the DFT formalization*
> in the D4 §5 shape: the four theorems are faithful formal renderings of the DFT *arguments*, each
> deriving its conclusion from the Rayleigh–Ritz inequalities and non-degeneracy that the structures
> carry **as fields** — hypotheses, not conclusions. It states both consequences: no inhabitant is
> constructed, and nothing connects them to §4.1's molecular Hamiltonian. The abstract's *"first
> formalizations"* now says *"the Hohenberg–Kohn/Levy–Lieb DFT **statements**"* and points at the
> scope note.
>
> **The Lean already disclosed this and the paper did not** — `HohenbergKohnUniqueness.lean:19-21`
> and `HohenbergKohnVariational.lean:26-27`. The paper now says so too. §4.1's unconditional
> self-adjointness is explicitly contrasted as taking no analytic hypothesis of this kind.

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
- ✅ **And D5 supplies the other half — a TAXONOMY, which is the stronger instrument.** D5 §2.3
  defines three labels and applies them corpus-wide: **Derived** (*"the conclusion does not reduce
  to the statement by `rfl` or `decide` on hand-assigned constants"*), **MCC / machine-checked
  classification** (*"the proof verifies internal consistency of an author-supplied lookup table …
  does not independently re-derive the underlying physics bound"*), and **Heuristic / Empirical**.
  It applies them against itself, including in a figure caption. **D4 gives the point-of-use
  sentence; D5 gives the decision rule and the vocabulary. TODO-D12's fix wants both.**
- **Fix shape, two options, prose-only vs. real work:** (1) narrow the claim — the layer is an
  axiomatized HK/Levy–Lieb interface plus its formal consequences; or (2) construct one
  `DensityVariational`/`GroundStateData` instance from §4.1's Hamiltonian, which would make the
  present claim true. Operator's call under ADR-010 C5. **The current prose is not a third option.**
- Full working: `docs/audits/2026-08-07-d10-retrofit/FINDINGS.md` §3.

### D13. D1 §3.1 mis-describes four `decide` proofs as `native_decide` — ✅ DONE 2026-08-09

> **Verified two ways before editing:** the four counting theorems at `SecondOrderSK.lean` 260, 272,
> 285 and 937 all read `:= by decide` in source, and their `axiom_deps_project` carries no
> `._native.native_decide` marker. D1 §3.1 now says `\texttt{decide}` and states why it matters
> (kernel-checked, not compiled-evaluated), so the bundle stops understating its own purity in the
> place a referee looks.

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

### D14. D1's append log records four `Lift-section` events that inserted no content — ✅ DONE 2026-08-09

> **Measured across D1-D4: 43 `Lift-section` events, 17 of them empty.** The entry says 16; the true
> split is D1 4 ✓, D2 2 ✓, **D3 6 (not 7)**, **D4 5 (not 3)**. Wrong in both directions.
>
> **Fixed additively.** Each empty event now carries `content_inserted: false` plus a note. The
> events are real history and are NOT deleted, and **`lift_action` is deliberately unchanged** —
> `sentence_state.py` and `bundle_source_manifest.py` parse it, so rewriting the value to
> `Lift-section-empty` would have broken two consumers to fix a counting problem. An absorption
> count filters on the new field: 43 total, **26 genuine**.
>
> ⚠️ **A false zero on the first attempt.** The first measurement keyed on `action` / `event` /
> `type` and reported **0 Lift-section events in all four bundles** — the field is `lift_action`. The
> raw text contained the string 7 times in D1 alone. A narrow key produces a confident absence, which
> is the trap `reference-measurement-traps-false-absence` catalogues. Reading the schema beat guessing
> at it.
>
> **The D25 serializer paid for itself here:** annotating four D1 events produced an 8-insertion /
> 4-deletion diff instead of the ~90-line churn the pre-D25 writers would have emitted.

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
  tableau*) — **D5 adds two more**, and **I1 adds three** (Quantum Crooks no-go, APS η-invariant
  sidebar, ETH-α refutation tableau), and **I2 adds one** — so the pattern spans **seven**
  bundles. The named
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

### D15. The flagship surveys a 17-bundle program; 21 exist — ✅ DONE 2026-08-09 (CRITICAL)

> ⚠️ **REOPENED AND RE-CLOSED 2026-08-09 by the closure reviewer.** The entry below claimed
> "all six roster sites corrected". Measured again with a widened scan — roster-number words
> AND digits, across all 21 drafts, not just F — **fifteen live sites remained**: F still said
> "Sixteen sibling bundles" and carried "17-bundle" in five more places including a section
> title and a bibitem; I1 said "seventeen publication targets" in four; D3, D4 and I3 each
> carried a "14-bundle" bibitem; and I1 quoted "thirty-three registered checks" against a live
> seventy-nine.
>
> ⚠️ **AND THAT RE-CLOSURE WAS ITSELF WRONG IN TWO DIRECTIONS — corrected 2026-08-09 after a
> third pass.** It claimed "every one is now fixed by REMOVING the census figure, not by
> updating it". Measured:
>
> * **A SIXTEENTH SITE WAS STILL LIVE.** `papers/I1/paper_draft.tex:1067` read
>   "seventy-plus-source to **seventeen**-publication consolidation". The widened scan keyed on
>   the noun-phrase forms (`seventeen publication targets`) and never matched the hyphenated
>   compound-adjective form — which is *exactly* the failure the paragraph below diagnoses. The
>   entry violated its own stated lesson in the act of recording it. Now rewritten to
>   "many-source-to-few-publication", which carries the meaning and no number.
> * **F WAS FIXED BY UPDATING, NOT REMOVING.** Nine census figures remain hard-coded in
>   `papers/F/paper_draft.tex` (`:50`, `:136`, `:2230` "twenty sibling threads"; `:514`, `:2017`,
>   `:2020` "21 bundles"; `:1742` "21-bundle architecture"; `:1745`, `:2050` "20 siblings").
>   **They are being KEPT deliberately, and the entry's blanket claim was the error.** F is the
>   flagship whose subject *is* the bundle architecture: "we consolidate the twenty sibling
>   threads" is the paper's thesis sentence, not incidental bookkeeping, and removing the number
>   would remove the claim. The no-count-in-narrative rule is machine-enforced over
>   `docs/architecture/*`, not over paper prose, and F's roster figures are covered instead by
>   the Stage-10 claims review. What was wrong was asserting a remedy that had not been applied.
>
> **The instrument that let it through, twice:** the original scan keyed on the six F sites the
> entry itself enumerated; the second keyed on the noun-phrase spellings. Re-scanning the corpus
> for the *pattern* rather than the *known list* is what found the other nine — and scanning for
> the *claim* rather than the *phrasing* is what found the sixteenth. A finding's own site list
> is a claim like any other, and so is its account of what it fixed.

> **All six roster sites corrected** (abstract, §1.2, §9.4, §11.1, §11.2, §12.3): sixteen siblings →
> twenty, seventeenth bundle → twenty-first, Tier 1 `D1--D8` → `D1--D12`, and D9–D12 are now named
> in the §1.2 thread enumeration they were missing from.
>
> ⚠️ **Two occurrences of "sixteen" were deliberately NOT touched** — `:756` and `:772` are *"sixteen
> left-handed Weyl fermions per Standard-Model generation"*, a physics count that shares the word and
> nothing else. This is the shape the entry warned about: key on what the sentence claims, not on the
> token.
>
> **§11.1's compound falsehood is corrected, not softened.** It claimed the program *"has shipped 17
> bundles to reviewer-triple-closed Stage-13 GREEN status"*. Both halves were false. It now states
> that **none** has reached reviewer-triple GREEN and that the section describes the intended
> shipping architecture rather than an achieved state. §9.4 gains the same correction inline.
>
> **§7's D6 checklist was stale in the other direction** and is now evidence-backed: waves 6v.2, 6v.5
> and 6v.6 are marked shipped, each citing the declared D6 apex that witnesses it
> (`ShorTGateCount.wave_6v_2_substantive_closure`, `APMLdpcHashingBound.wave_6v_5_substantive_closure`,
> the `WStateQFT` declarations). The Stage-13 box stays unchecked and now says why.
>
> ⚠️ **I introduced a dangling `\ref` while fixing this** (`sec:phase7-closeout` did not exist) and
> caught it by checking the label set before compiling — the same defect class D17 was filed for. The
> label now exists; F compiles with zero undefined references.

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
- ⚠️ **RESTATED 2026-08-07 (E1 retrofit): the defect is SCOPE MISMATCH, not macro use.** Three
  data points now fix the shape — D1/D5 use a **project**-scoped macro for a **bundle** figure
  (wrong); L3 uses a **bundle**-scoped derived macro for a bundle figure (the template); **E1 uses
  a project-scoped macro for a genuinely project-scoped claim** (*"the Lean 4 verification of the
  underlying chain … is independent of platform parameters"*) — correct as written, and **must not
  be swept up in a fix**. Any remediation must key on what the sentence claims, not on the macro.
- ✅ **The fix template already exists, in L3 (found 2026-08-07).** `\bhThermoTotal` is derived
  per-module by `update_counts.py` (`_module_thm_count("BHThermodynamicsFourLaws.lean")`), is
  **bundle-scoped**, and is exact against the source (20 = 20). **A bundle-scoped derived macro is
  the answer to both this item and TODO-D10** — D1/D5 abuse the *project*-scoped `\totaltheorems`
  for a bundle figure; F/I1/I3 hand-type roster numbers. L3 shows the working shape.
- **FOURTH stale roster number: D6 §1.3 says *"the project's 15-bundle publication architecture"*
  (2026-08-07, D6 §D2 pass).** With F=17, I1=17, I3=14 and D6=15, **four bundles cite four different
  wrong numbers from the same strategy document.** Live roster: **21**.
- **D6 §5.4 says the network substrate is *"17 kernel-only modules"*; the `QuantumNetwork` family
  now holds 104.** True at Phase 6AA, never revised as the family grew under it. Same
  hand-maintained-count class, same fix.
- **D9's module count is off by one (2026-08-07, D9 retrofit).** The abstract and appendix say
  *"103 Lean modules"* in the `QuantumNetwork` family; measured **104**. Hand-maintained, same class
  as the roster numbers below, same fix (L3's bundle-scoped derived macro).
- **Third bundle with a stale roster number (2026-08-07, I3 retrofit).** I3's bibliography
  self-cites *"SK--EFT Hawking 14-bundle publication architecture"*; I1 §2 says 17; F says 17.
  Three different wrong numbers in three bundles, all citing the same `PAPER_STRATEGY.md`. The
  live roster is **21**. This is the shape TODO-D10 (derive, don't hand-list) exists to fix, now
  observed across bundles rather than within one.
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
- ⚠️ **SECOND BUNDLE, and it lands harder: I1** (2026-08-07). The methodology paper — the one paper
  whose subject IS the pipeline — describes it at roughly half its current size: *"thirty-three
  registered checks"* (live **66**), *"fifteen invariants"* (they run to **#17**), *"seventeen
  publication targets … D1–D8"* (live **21**, `D1`–`D12`), and the local toolchain as
  *"`v4.29.0`"* (live **`v4.32.0`**). The last is not a count but a **verification claim** —
  *"All worked-case theorems … verified to compile cleanly on the project's local 4.29.0
  toolchain"* — asserted against a configuration that no longer exists.
  ⚠️ **The irony is the finding.** I1 §2 opens by listing four failure modes the pipeline exists
  to prevent, one of which is *"a parameter whose value was inherited from a prior draft and had
  drifted."* Its own infrastructure figures are that failure mode.
- **Fix shape:** F cannot be brought current by editing counts; the roster sections need
  rewriting against the live roster, and the §9 figures need to become macros or citations. This
  is content work under ADR-010 C5, and it is the strongest argument for retrofitting the
  remaining bundles **before** F is redrafted — F's job is to describe them.
- Full working: `docs/audits/2026-08-07-f-retrofit/FINDINGS.md` §2, §3, §5.

### D16. The program's central synthesis claim has no Lean witness — ✅ DONE 2026-08-09 (CRITICAL)

> ⚠️ **The claim is not unwitnessed. As literally stated it is FALSE, and measuring it is what
> showed that.** Read directly:
> * `HeatKernelExpansion.a0_dirac (N_f : ℝ)` counts **Dirac species**, is real-valued, fiducial `15`.
> * `GenerationConstraint`'s `N_f : ℕ` counts **generations** — its own docstring says "each
>   generation contributes 16 real fermions … which reduce to `c₋ = 8` per generation" — with
>   central theorem `3 ∣ N_f`, minimal value `3`.
>
> Different types, different objects, different values. No proof of identity was ever going to
> appear, and hunting for one would have been the wrong work.
>
> **Substrate built rather than claim narrowed** (`lean/SKEFTHawking/SakharovGenerationBridge.lean`,
> 6 declarations, kernel-pure `{propext, Classical.choice, Quot.sound}`):
> * `FermionContent` — one structure carrying generations and Weyl-per-generation. **This is the
>   precise sense in which "the substrate is one object".**
> * `diracFlavourNf_eq_scaled_generationNf` — the bridge: the two counts are proportional, with the
>   per-generation Weyl count as the constant. Neither is prior; both are read off the one structure.
> * `sm_counts_differ` — at SM content the counts are `24` and `3` and are **not equal**. Numerical,
>   so it is falsifiable rather than a remark.
> * `counts_agree_iff_two_weyl_per_generation` — the exact condition under which the flagship's
>   literal claim *would* have held: two Weyl fields per generation. The SM has sixteen.
> * `generation_constraint_transfers` — **the load-bearing direction, and it survives**: the
>   modular-invariance constraint `3 ∣ generations` transfers onto the Sakharov-side species count,
>   so an anomaly condition does constrain the emergent Newton constant. With a non-vacuity witness.
>
> **F §6.1 rewritten** to claim the relation rather than the identity, citing all four theorems.
> That is a stronger claim than the original, not a weaker one: it is proved.
>
> **Developed MCP-first per the lean4 skill** — `lean_diagnostic_messages` → `lean_multi_attempt` →
> `lean_verify`, with `lake build` only as the final project gate. The goal state showed
> `field_simp` had already reduced the hypothesis to the conclusion, so the `mul_left_cancel₀`
> scaffolding I had written was the obstacle rather than the route.

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

### D17. D3's tracked-hypothesis registry contains two dangling `\ref`s — ✅ CLOSED-NOT-A-DEFECT 2026-08-09

> **Refuted by two instruments.** The strings `sec:cfl-z3-matching` and `sec:singularity-thms` appear
> **nowhere** in `papers/D3/paper_draft.tex` — not as `\label`, not as `\ref`. And a two-pass
> `pdflatex` of D3 emits **zero** `Reference ... undefined` warnings and writes the PDF. Nothing
> renders as `??`.
>
> The intended targets `sec:cfl` and `sec:penrose` both exist, so had the references been present the
> repoint would have been correct — but they are not present. Either the entry was written against a
> draft state that has since changed, or it recorded an intended edit as an observed defect. **No
> change made:** editing a reference that does not exist would have been the fix creating the defect.

- **Where:** `papers/D3/paper_draft.tex` — `sec:cfl-z3-matching` and `sec:singularity-thms` are
  referenced and never defined, so both render as `??` in the compiled PDF.
- **Why it is worth fixing despite being minor:** both live in **§28.3, the tracked-hypothesis
  registry** — the mechanism D3 offers as its accountability device, closing with *"A reader with
  auditing intent can resolve every open obligation in this list."* They are the pointers for
  `H_TopologicalOrderBeyondLG` and `IsADWPenroseApplicable`. §24.3 uses the second one again.
- **Fix shape:** repoint to `sec:cfl` and `sec:penrose`, the sections that carry the content.
  Prose-only.
- Full working: `docs/audits/2026-08-07-d3-retrofit/FINDINGS.md` §3.

### D18. `prose_theorem_reference_coverage` misses backtick-quoted theorem names — ✅ DONE 2026-08-09

> **The residue the entry said was unknown, measured:** across all drafts, Lean-ish references by
> quoting form are `\texttt{}` 2 801 · `\verb|…|` 125 · `\lean{}` 275 · `` `name' `` 1.
>
> ⚠️ **400 of those 401 non-`\texttt` references were ALREADY COVERED** — the alias fixpoint
> discovers `\lean`/`\thm`/`\mthm` structurally and `_PROSE_VERB_RE` handles `\verb`, both
> repaired in the ADR-010 pass. A naive scan says "401 invisible"; the check's actual reach says
> **one**. Reading the extractor beat counting the corpus.
>
> **That one was the whole defect:** D7 cited `` `analog\_hawking\_quantum\_advantage\_demarcation' ``,
> a theorem that does not exist. Fixed to the real biconditional
> `analog_hawking_simulable_iff_fourCycleFree_and_nonneg_and_c1_zero`, which is what the surrounding
> prose actually describes (it conjoins the structural and topological axes). D7 compiles; candidates
> 1 459 → 1 460.
>
> **Both halves of the fix shape landed** (the entry offered them as alternatives): the extractor
> gained `_PROSE_TEX_QUOTE_RE` *and* the draft was normalised to `\texttt{}`. The quote form is the
> one shape that cannot be discovered structurally — there is no macro to discover — so it needs its
> own pattern, gated on `\_` or a dot so English quotation does not flood the candidate set.

- **The defect it let through:** `papers/D7/paper_draft.tex:127` names its own headline as
  `` `analog\_hawking\_quantum\_advantage\_demarcation' `` — a theorem that **does not exist**.
  The live names are `analog_hawking_fourCycleFree_demarcation` and
  `analog_hawking_tree_simulable_demarcation`. Verified underscore-aware and **seeded** (the same
  probe returns PRESENT for the real name).
- **Existing coverage, read not assumed:** `prose_theorem_reference_coverage` runs green and
  **does not report D7 at all**. Its extractor keys on `\texttt{...}`; D7 uses backtick-apostrophe
  `` `name' `` quoting, so the reference is never seen. **The check works; its input filter is
  narrower than the drafts' quoting conventions.**
- **Residue:** unknown. Only D7's instance is confirmed. A scan of how many drafts use non-`texttt`
  quoting for theorem names has NOT been run — doing so is itself the first half of the fix.
- **Fix shape, two options:** (a) widen the extractor to accept `` `name' ``, `\verb|name|` and
  `\lean{name}` (D8 uses the last); or (b) normalise the drafts to `\texttt{}`. (a) is a check
  change and (b) is a prose change; **both need approval under §6a. Nothing built.**
- ⚠️ **This is the failure mode the goal's standing constraint targets from the other side:** the
  rule is *check whether a check already measures it*. Here one does — and the useful finding was
  that its **scope** is narrower than its name suggests. **"A check exists" and "the check covers
  this input" are different claims.**
- Full working: `docs/audits/2026-08-07-d7-retrofit/FINDINGS.md` §3.

### D19. I3 §4 names no witness or wave-closure theorem for any of its six LDP modules — ✅ DONE 2026-08-09

> **Zero of I3's 30 module theorems are now unnamed** (was 13), and zero of
> `GravitationalWaves.lean`'s 21 are unnamed by L1, D3 or F (was 10).
>
> **The entry's two counts were both wrong, in opposite directions.**
> * *I3's per-module closures:* the draft claimed **11**, this entry re-measured **10**, and the
>   true figure is **9** — four Itô (`StochasticIntegral`, `QuadraticVariation`,
>   `Semimartingale`, `ItoIsometry`) plus five LDP. `Novikov.lean` and `ItoLemma.lean` carry
>   none; `Novikov.lean` hosts the *overall* `wave_3b_ito_overall_closure`. §2.3 now says 9 + 2
>   and points at the sections where all eleven are named, so the count follows from the names.
> * *L1's unnamed theorems:* the entry said **7**; measured **11** unnamed by L1, of which
>   **10** are named by no bundle at all (D3, its deep companion, names one).
>
> **What writing §4 to §3's template exposed, and it is worth more than the prose fix.** Each LDP
> per-module "wave-closure" has the **same statement as its own witness** — e.g.
> `wave_3b_ldp_alpha_1_cramerIID_closure` and `cramerIID_subGaussian_witness` are both
> `IsCramerIIDUpperBound (fun _ => 0) (fun _ => 0)`. Two Itô closures are genuine conjunctions;
> two are not. **Padding the LDP closures into synthetic conjunctions to match was rejected** —
> that is the P2 bundle-redundancy anti-pattern the preemptive-strengthening discipline forbids.
> The prose says so instead: a module with one substrate obligation has a closure that restates
> its witness, and `Semimartingale.lean` shows what the conjunctive form looks like. A JOSS
> reader now learns which modules carry one obligation and which carry two.
>
> **`linearResponseRateFunctionCentered_zero` is NOT a dangling reference** — checked before
> "fixing" it. §2.3 cites it and it exists, in `CrooksAnalogHawking`, not in `LDP`.
>
> **L1's sharpest case, closed.** Recovery-path 3 argued in prose that
> $|\gamma| \le 10^{-30}$ does not lift the falsification while citing
> `SecondOrderSK.lean`, a module that does not carry the theorem.
> `vestigial_dispersion_below_ligo_at_inspiral_peak` proves exactly that claim and is now named,
> with `dispersion_within_ligo_iff` as the general biconditional and the four
> `H_VestigialModeIsGraviton_fails_at_*` refutations plus `ligo_satisfied_at_chi_one` and
> `c_GW_deviation_zero_iff_chi_one` naming the pointwise structure.
>
> **Not built, and the entry was right that it needs approval:** a *proved-but-unnamed*
> corpus-wide check. The three instances are closed by naming; the instrument that would prevent
> a fourth remains unbuilt and is still scoped together with TODO-D21's.

<details><summary>Original entry — kept for the record</summary>

**Found:** 2026-08-07, I3 apex retrofit (`docs/audits/2026-08-07-i3-retrofit/FINDINGS.md` §3).

**Defect.** `papers/I3/paper_draft.tex` §3 (Itô) writes every subsection to a four-part template —
*Substrate-data predicate* / *Non-vacuity witness* / *Wave-closure summary* /
*Mathlib-upstream-PR target*. §4 (LDP) writes only the first and the last for all six modules.

**Measured consequence.** 13 proved theorems in I3's own twelve modules are named nowhere in the
draft: five LDP witnesses, five LDP per-module wave-closures, and three Itô witnesses whose
subsections skip the heading. Five of the twelve modules (`CramerIID`, `Sanov`, `Contraction`,
`CramerLowerBound`, `Varadhan`) therefore appear in **no** declared closure.

**Why this is worse here than in D11 or D7.** I3 is a software paper whose deliverable *is* the
artifact. An unnamed theorem is an unfindable API — a JOSS reader wanting the Sanov witness has no
name to search for. D11's gap was prose in a results paper; D7's sections were openly unwritten.

**Same defect, second symptom.** §2.3 claims *"11 per-module wave-closure summary theorems"*;
measured **10** (probe scope: `theorem`/`lemma` declarations in the twelve module files). The 11
counts `LDPCompatibleSKEFT` as having a per-module closure, which the same paragraph gives to
`wave_3b_ldp_overall_closure`.

**Fix shape.** Extend §4's six subsections to §3's template, naming each witness and each
wave-closure; the count then follows from the names rather than from hand-maintenance. No new
Lean is required — every theorem already exists and is proved.

**Third instance — this is a portfolio-level pattern, not three bundle-level defects.**
D11 (~69 proved declarations named in no draft anywhere), I3 (13 in its own twelve modules), and
now **L1** (7 of 21 in `GravitationalWaves.lean`). L1's is the sharpest single case: five of its
seven unnamed theorems formalize the *exact* quantitative claim its §Discussion recovery-path 3
states in prose (`|γ| ≤ 10⁻³⁰` does not lift the falsification —
`vestigial_dispersion_below_ligo_at_inspiral_peak`), and the sentence cites a **different** module
(`SecondOrderSK.lean`, which does carry `GammaH` but not that theorem). The prose reads as argued
where it is in fact proved.

**Negative control — do NOT count splash/deep division as this defect (added 2026-08-07, L3).**
L3 leaves five standalone theorems unnamed, but **two of them are named by D3**, its declared deep
companion (`M_c_pos`, `four_laws_consistent_with_acoustic_regime`). A four-page Letter naming fewer
theorems than its deep companion is correct, not defective. The pattern this TODO tracks is
*proved content **no** container names*; L3's genuine residue is only the two `wave*_bridge_*`
theorems, named by neither.

**Not a check.** Per §6a nothing was built. `prose_theorem_reference_coverage` measures the reverse
direction (prose names that do not resolve); a *proved-but-unnamed* measure would be new
infrastructure and needs approval — and TODO-D14/D18 already queue related coverage questions.

</details>

### D20. E1 still carries the `c₁` description E2 retracts — ✅ DONE 2026-08-09

> Reproduced: E1 read *"the topological Chern coefficient $c_1$ of the underlying condensate"* and
> *"$c_1 = 0$ for the polariton fluid's effective Hamiltonian"*, while E2 had carried the D11
> Stage-13 correction since 2026-08-01. E2's corrected paragraph is now ported into E1, adapted to
> the polariton platform, and **carries E2's own narrowing with it** — the module *does* invoke a
> Brillouin-zone reading at `ChernBridge.lean:14`, so the scope note says the marker is not innocent
> of band language while still being a different object from a Bloch-band invariant. E1 compiles.
>
> The note records that it is ported from E2, so the two halves of a declared splash/deep pair stay
> traceably in sync rather than accidentally identical.

**Found:** 2026-08-07, E2 apex retrofit (`docs/audits/2026-08-07-e2-retrofit/FINDINGS.md` §3).

**Defect.** E1 and E2 carry the same Phase-6w demarcation paragraph. The 2026-08-01 D11 Stage-13
correction (rounds 10/12/13, finding 4.1) landed in **E2 only**.

- `papers/E2/paper_draft.tex:421–433` retracts the wording *"the topological Chern coefficient of
  the graphene moiré band-structure"*, on the grounds that `ChernBridge.lean:68` defines
  `categoricalChernExpansion c0 c1 := ⟨[c0, c1]⟩` — a two-term Chebyshev expansion — and the module
  makes no graphene or moiré claim. **Verified against the file: correct.**
- `papers/E1/paper_draft.tex:410` still reads *"AND the topological Chern coefficient `c₁` of the
  underlying condensate vanishes"*, and continues *"falls in the topologically-trivial regime
  (`c₁ = 0` for the polariton fluid's effective Hamiltonian)."*

**Fix shape.** Port E2's corrected wording into E1 — `c₁` is the **second Chebyshev expansion
coefficient of the categorical marker**, not a Bloch-band or Chern invariant. Note that E2's
correction is *itself* narrowed (the module **does** invoke a Brillouin-zone reading at
`ChernBridge.lean:14`), so port the narrowed form, not the first version.

**Existing coverage:** none — no registered check compares prose across bundles that share a lifted
paragraph. Per §6a nothing was built; the residue (a cross-bundle shared-paragraph consistency
measure) would be new infrastructure and needs approval.

### D21. D9 claims to consume I3's LDP foundations; no declaration does — ✅ DONE 2026-08-09

> **`D9 ∩ I3` went 0 → 11**, three of them in `SKEFTHawking.LDP`. The claim was made true rather
> than narrowed, which is the posture this project holds: where a gap exists, build the substrate
> or prove it cannot be built; do not reclassify.
>
> **Why building was the right call and not a stretch.** The two sides already shared their
> object. `fdt_rare_event_tail` is positivity of `linearResponseRateFunction β σ² ·`, and I3's
> LDP layer certifies `linearResponseRateFunctionCentered β σ²` — the *same function shifted by
> the constant* `I(0)` — as `LDPCompatibleSKEFT`. The consumption claim was true of the physics
> and false of the Lean.
>
> **Shipped:** `lean/SKEFTHawking/QuantumNetwork/FDTLDPBridge.lean` (new, kernel-pure, axioms
> exactly `{propext, Classical.choice, Quot.sound}`, compiled clean on the first pass).
> `fdt_rare_event_tail_is_ldp_certified` states both halves of the consumption claim for one
> object: the function is the LDP-certified one, and its centered form is bounded strictly below
> by `-β²σ²/8` away from the FDT-pinned mean. That constant is `-I(0)`, isolated as
> `linearResponseRateFunction_at_zero` so the floor is a **number** rather than "some constant"
> and a wrong centering fails it. `fdt_rare_event_tail_is_ldp_certified_witness` discharges the
> hypotheses at `β = 0, σ² = 1, W = 1`, so the bridge is not conditionally empty.
>
> **Both drafts corrected, in the same commit as the Lean.** D9 §4.2 names the theorem and states
> the eleven-declaration overlap; I3 §Cross-bridges no longer says its bridge is *"designed but
> not yet consumed at release time"* — it now says one consumer exists and D3/D5/E1 do not, which
> is what the substrate shows.
>
> **Still not built:** a check comparing a prose consumption claim against the dependency graph.
> Per §6a that is new infrastructure needing approval, and it stays scoped with TODO-D19's
> proved-but-unnamed measure.

<details><summary>Original entry — kept for the record</summary>

**Found:** 2026-08-07, D9 apex retrofit (`docs/audits/2026-08-07-d9-retrofit/FINDINGS.md` §2).

**Defect.** `papers/D9/paper_draft.tex` states twice that its rare-event tails consume the I3
bundle's large-deviation foundations (§1 companion paragraph; §4.2 *"consuming the large-deviation
foundations of the I3 bundle"*).

**Measured three ways, all negative:** `D9 ∩ I3` closure = **0**; `fdt_rare_event_tail` and
`fdt_gallavotti_cohen` (both in `QuantumNetwork.FDTNoiseFloor`) have **no** direct
`name_deps_project` entry in `SKEFTHawking.LDP.*` or `SKEFTHawking.Itô.*`. Probe seeded — the same
measurement returns 50 for `D9 ∩ D10` and 14 for `D9 ∩ D8`.

✅ **Independently corroborated by the other side's prose.** I3's own draft says its cross-bridge is
*"designed but not yet consumed at release time"*, and I3's closure intersects **nothing** in the
portfolio. The two drafts disagree and the substrate sides with I3.

**Fix shape — D9's own vocabulary supplies it.** The LDP reading of those tails is an
**identification-layer** statement, not a formula-layer dependency. D9 invented that distinction and
applies it rigorously to Caves, PLOB, DEJMPS and the readout models; it is not applied to its own
sibling-bundle claim. Restate as an identification, or build the dependency.

**Existing coverage:** none. No registered check compares a prose consumption claim against the
dependency graph. Per §6a nothing was built; the residue would be new infrastructure needing
approval — and it is close in kind to TODO-D19's proved-but-unnamed measure, so the two should be
scoped together if either is approved.

---

</details>

## ⚠️ Remediation sequencing for the prose-fix TODOs (operator ruling, 2026-08-07)

**Every TODO in the D-series that fixes paper prose — D12, D15, D17, D19, D20, D21, and the
roster/count items — is a Stage-9/10 event before it is a Stage-13 event.**

`docs/BUNDLE_LIFT_PROCEDURE.md:9` states the gate: *"Stage 13 (adversarial review) may not be
invoked until **both** Stage 9 (figure review) AND Stage 10 (claims review) are GREEN, with all
fixes from those stages applied."* Stage 10 is the **paper claims review** (`skeft-qa:claims-reviewer`,
`docs/WAVE_EXECUTION_PIPELINE.md:387` / lift procedure §9) — the sentence-level prose audit. Running
Stage 13 first is a procedure violation, not a shortcut.

**So a bundle whose prose is edited to close one of these TODOs re-enters at Stage 9/10, not at 13.**
Do not read `bundle_metadata_matches_graph`'s remedy line (*"Re-run Stage 13 for this bundle"*) as
permission to skip ahead: that check is describing what clears its own `stage13_status` field, not
the order of the gates.

⚠️ **Whether the prose-review agent the operator intends is the currently-installed
`claims-reviewer` is the operator's call, not an assumption to make here.** The plugin ships
`.claude/plugins/skeft-qa/agents/claims-reviewer.md`; the operator has flagged that the prose
reviewer under discussion may not be ready or installed. **Confirm before invoking Stage 10 on a
remediation batch.**

**The ADR-010 apex retrofit itself changed no paper prose** — only `bundle_metadata.json`
`apex_theorems` keys and `docs/audits/**` — so it invalidates no bundle's review state. That was
deliberate, and it is why the retrofit did not need to re-enter the reviewer stages at all.

### D22. `paper_toolchain_pin_drift` reports a CURRENT PhysLib pin as drift — ✅ DONE 2026-08-09

> **Reproduced first** (D11:514, D12:125 — the TODO's line numbers 546/129 had drifted with the
> drafts; the defect had not). Fixed by `_tp_live_dep_revs()`, which parses **every** `[[require]]`
> stanza's rev from `lakefile.toml` and is therefore DERIVED — a dep added later is covered without
> editing the function, rather than hand-listing PhysLib beside Mathlib. A hex is drift only if it
> prefix-matches no currently-pinned rev.
>
> **Corpus figure moves 29 → 27**, exactly the ≥2 this entry predicted. `_tp_live_pins` and
> `_tp_scan_lines` keep their declared public shapes (`other_revs` is an optional keyword), and all
> 79 pre-existing tests still pass.
>
> ⚠️ **A fixture error worth recording:** the first version of the new test asserted `live_ver =
> "v4.32.0"`. `_tp_live_pins` strips the leading `v` and returns `4.32.0`, so the test failed while
> the code was correct. Verified against the live resolver rather than assumed from the
> `lean-toolchain` file's text. The seeded control (`test_without_the_fix_the_same_line_would_flag`)
> proves the passing test is sensitive to the repair and not merely to a clean line.

**Found:** 2026-08-07, D12 §D2 pass (`docs/audits/2026-08-06-d12-retrofit/FINDINGS.md`).

**Defect.** D12 §1 states *"Lean toolchain `v4.32.0`, Mathlib revision `81a5d257` and PhysLib
revision `c4843367`"* — all three **current**. The check reports `papers/D12/paper_draft.tex:129 —
c4843367` as pin drift. `papers/D11/paper_draft.tex:546` is the same case.

**Cause, read in the code (`scripts/validation/checks/papers_prose.py`, `_tp_scan_lines`).** The
scanner collects every hex literal on a line whose *context window* matches `_TP_MATHLIB_CTX_RE`,
then tests each against the single `live_rev` returned by `_tp_live_pins()` — which reads **Mathlib's**
`rev` from `lakefile.toml` and nothing else. A sentence naming Mathlib and PhysLib together therefore
has the PhysLib hash compared against Mathlib's, and a correct pin is reported stale.

**Residue / fix shape (NOT built — §6a).** Read PhysLib's `rev` alongside Mathlib's and accept a hex
matching *either*; the lakefile already carries it under `name = "Physlib"`. Needs approval.

⚠️ **Reporting consequence, applies now:** the check's corpus figure — *"29 pin-drift sites across
65 drafts"* — contains at least these two false positives. Quote it as *"29 reported, ≥2 false
positive"* until this lands. The genuinely stale sites found in this retrofit (E1 ×3, E2 ×4, I1 ×2,
I3 ×1, L2 ×3, D9 ×1) were each confirmed against the live pin individually and are unaffected.

### D23. `bundle_metadata_matches_graph`'s description covered 3 of its 4 legs — ✅ CLOSED 2026-08-07

**Found:** 2026-08-07, operator question *"sounds like it should be green though."*

**Defect.** The check registers as *"bundle_metadata.json finding counts equal the live graph's"*.
Legs 1–3 are exactly that — field-equality on `blockers_open`, `advisories_open`, `readiness`, and
they have **never** failed. Leg 4 asserts something else: `stage13_status = 'green'` is illegal while
`live_blockers > 0`. That is a *semantic* metadata-vs-graph contradiction (metadata claims a review
verdict the graph's findings contradict), not a count equality — so a failure is uninterpretable
from the check's name.

**Cost, demonstrated twice in one session.** The retrofit's own reporting mis-described the failure
as count drift, and the operator correctly read the name as implying it should be green. Both
readings follow from the description.

**Not a bug.** The housing was deliberate and documented in-source: nothing else in the repo read
`stage13_status`, the hole had a committed mutation test (`2026-08-01-0009-internal-adversarial/
D11.md:179` — *"flip pending->green => PASS <-- missed"*), and it needed a home. The author also
recorded what NOT to assert alongside it (`stage13_redo_required`, `freshness_stale`), which is why
this entry is about the label rather than the logic.

✅ **CLOSED 2026-08-07 — operator authorized the split.** Leg 4 is now
`bundle_stage13_claim_consistent`, registered as *"No bundle claims stage13_status='green' while the
graph shows open blockers"*. The assertion is unchanged; only its label. What landed with it:

- `bundle_metadata_matches_graph` is now exactly its description — field equality on
  `blockers_open` / `advisories_open` / `readiness`, nothing else.
- The shared aggregation moved to `_readiness_aggregate()`, so **both** checks fail CLOSED on an
  import or aggregate failure rather than one inheriting the other's guard.
- **Seam guard added to both** (authoring guide §2.5): a run that inspected zero blobs returns
  `passed=False, measured=False`, not agreement. Neither had this before — an empty roster is the
  round-8 state the module header warns about.
- Position declared in `_CANONICAL_ORDER` **adjacent to its sibling**, because the two are
  cross-braced: hand-zeroing `blockers_open` to silence the Stage-13 rule trips the counts check
  instead, so both must be defeated rather than one.
- **Production-seeded (guide §2.4):** `stage13_status` flipped to `"green"` in the real
  `papers/D1/bundle_metadata.json` (37 live blockers) → `rc=1`, D1 named with the live count; the
  cross-brace seeded in production as well; restored byte-clean. Added to `PRODUCTION_SEEDED`, so
  `FIXTURE_ONLY_CEILING` stays 55 — one new check, one new production seed, net zero.
- 8 fixture legs in `TestBundleStage13ClaimConsistent`, including the two silent-on-correct-data
  cases the old housing never asserted: `pending` + blockers passes, and `green` + **zero** blockers
  passes. The rule is green-with-blockers, not green-is-forbidden.

---

### D24. The Stage-9/10-before-13 hard gate is unguarded — ✅ CLOSED 2026-08-08 as a DUPLICATE

**Superseded by [ADR-011](../../adrs/ADR-011-manuscript-quality-layer.md) Phase 2**, which ships it
with the other four sub-items of **D5**, where it already was: D5's fix shape names *"an enforcement
point for Stage-9/10-before-13"* as one of five interlocking items, and the 2026-08-01 audit had
already specified it as **Gate 16 assertion #2**.

⚠️ **Filing it separately was itself the failure `docs/architecture/README.md` rule 1 names** — a
second mechanism beside one that already existed. It was written on 2026-08-07 by an author who had
read `bundles_readiness.py` but not D5, four entries above it in this file. Shipping it alone would
have built one fifth of a mechanism and left the other four load-bearing: the ordering assertion is
free once `stage*_status` has writers, and near-useless while every green is a hand edit.

The finding below is retained verbatim as the measurement record; only its disposition changed.

### D24 (original text). The Stage-9/10-before-13 hard gate is unguarded

**Found:** 2026-08-07, while applying the operator's demotion.

**Defect.** `BUNDLE_LIFT_PROCEDURE.md:9` states: *"Stage 13 (adversarial review) may not be invoked
until **both** Stage 9 (figure review) AND Stage 10 (claims review) are GREEN, with all fixes from
those stages applied."* **No check enforces the ordering.** Verified by reading
`scripts/validation/checks/bundles_readiness.py`: it reads `stage13_status` at eight sites and
`stage9_status` / `stage10_status` at **none**.

**Measured consequence — five bundles had jumped the gate:**

| bundle | `stage13_status` | `stage9_status` | `stage10_status` |
|---|---|---|---|
| D6 | green | **`not_started`** | `skeleton` |
| D7 | green | **`not_started`** | green |
| D8 | green | `pending` | `pending` |
| D9 | green | green | `pending` |
| I3 | green | `pending` | green |

D6 is the sharpest: a Stage-13 green with figure review never started. **This is distinct from the
stale-verdict problem leg 4 catches** — those bundles' Stage-13 greens were contradicted by *later*
findings; these were invalid when written, because a prerequisite gate had not been passed.

**Now dormant, not fixed.** The operator's 2026-08-07 demotion set every reviewer-stage `green` to
`pending`, so no bundle currently violates the ordering. Nothing prevents a re-promotion from
recreating it.

**Residue (NOT built — §6a).** A check asserting `stage13_status = 'green' → stage9_status =
'green' ∧ stage10_status = 'green'`. Scope it to the ordering only; per the in-source warnings on
D23, do **not** bundle in `stage13_redo_required` or `freshness_stale`, whose meanings are owned
elsewhere. Needs approval.


### D25. Four writers of `bundle_metadata.json` disagree on `ensure_ascii` — ✅ DONE 2026-08-09

> ⚠️ **The heading under-counts its own defect, in two ways, and the measurement is the finding.**
> Not four writers but **eleven call sites across five scripts** — the entry missed
> `compile_bundle_pdf.py:364` and `record_review.py:124` (both already correct). And not one file
> type but two: measured across the corpus,
>
>     bundle_metadata.json   21 files   20 raw-unicode /  1 escaped
>     append_log.json        20 files    2 raw-unicode / 19 escaped
>
> **`append_log.json` carries the identical defect with the OPPOSITE majority.** Normalising only
> the file the entry named would have left the other free to keep oscillating.
>
> **Fixed:** `scripts/bundle_json.py` is now the single serializer (`dump_bundle_json` /
> `write_bundle_json`, `ensure_ascii=False`), and all eleven sites route through it. A
> byte-identical write is skipped so mtime does not move (the TODO-D29 discipline).
> **20 files normalised, 227 insertions / 227 deletions, and `json.loads` before vs after is equal
> for every one** — encoding-only, verified against `git show HEAD:<f>` rather than asserted.
> Second normalisation pass changes nothing.
>
> **Test:** `tests/test_bundle_json_serializer.py` — 53 cases. Each blob is a serializer fixed
> point; each writer module is checked **structurally via `ast`** (not grep) for a surviving
> `write_text(json.dumps(...))`, so a future writer that open-codes the dump fails here.
>
> ⚠️ **A self-inflicted repair worth recording:** my first insertion of the shared import used a
> regex for "the last top-level import", which matched the OPENING line of a parenthesised
> `from x import (` and split the statement in two files. A second regex attempt failed the same way
> because the line ends in `# noqa: E402`, not `(`. Resolved with `ast.parse` + `end_lineno` — the
> real parser. Third time this session that a regex over structured text produced a confident wrong
> edit.

**Found:** 2026-08-08, ADR-011 Phase 1, by causing it.

- **What:** the blobs carry `§` and `—` in their apex `claims` strings.
  `bundle_readiness.py:735` writes them with `ensure_ascii=False`; **`bundle_append.py:306/326/376/389`,
  `bundle_source_manifest.py:146/151/156` and `bundle_readiness.py:268` all use the default `True`.**
  Whichever tool touches a blob last decides its encoding, so the corpus oscillates between the two
  forms and a one-field edit can rewrite ~450 lines.
- **Measured:** seeding `length_target` through a default-`ensure_ascii` writer produced
  **98 insertions / 91 deletions on `papers/D3/bundle_metadata.json` for a 9-line change**; rewriting
  unescaped brought the same edit to 9 lines.
- **Why it is not cosmetic:** a diff that large is not reviewable, and the escaped form is what a
  reviewer would have to read the apex claims through. It also means `git diff` cannot be used to
  see what a tool actually changed — the signal the D23/D24 work depends on.
- **Fix shape (needs code, small):** one serializer for this file. `bundle_readiness.py:735` already
  has the correct form; the residue is the other seven call sites plus a test asserting a
  round-trip through each writer is byte-stable. Needs approval per §6a.
- ⚠️ **Do not "fix" by re-escaping.** The on-disk form is the readable one and is what
  `write_metadata_counts` — the most frequent writer — produces.

### D26. F-02 (a source registration must not create a section) — ✅ DONE 2026-08-09

> **Both halves shipped: the symptom in D3, and the mechanism in `bundle_append.py`.**
>
> **The stated blocker did not survive re-measurement.** The entry deferred on "a
> `CHARTER.md` that does not exist yet", blocked on ADR-010's roster decision. The roster
> decision landed (21 bundles), and all 21 bundles already carry `bundle_target`,
> `length_target` and `target_journal` — but more to the point, **the charter was the wrong
> place for the section plan.** A plan stored beside the document it describes drifts from
> it; a plan *read from* the document cannot. `--target-section` is validated against the
> draft's own top-level sections, which buys exactly what the charter was for — you may only
> append where the architecture already has a home, or say out loud that you are changing it
> — with nothing to author and nothing to keep in sync.
>
> **The mechanism, measured.** Across all 21 bundles' `append_log.json`: **74 of 74 content
> lifts created a top-level `\section`.** The `§§` subsection form the old `is_subsection`
> hint recognised was used **zero** times, because nothing ever required it. 28 of the 74
> landed in D3. A lift now takes `--target-section '<existing title>'` and lands as a
> `\subsection` inside it; `--new-section` requires `--section-rationale`, and the reason is
> written into the draft, `change_log.md` and `append_log.json`. `--initial-lift` implies the
> new-section path — a bundle with no draft has no plan to append into.
>
> ⚠️ **The entry's warning was honoured.** The skeleton insertion was NOT removed.
> `bundle_section_inserted` now carries the *resolved* anchor
> (`§ <section> / §§ <subsection>`) rather than the caller's unlocatable `--insertion-point`
> hint, which is preserved separately as `insertion_point_hint`. Measured: 127 of 129 corpus
> events are script-written and **all 127 carry an anchor**. Exactly one event corpus-wide
> has no `bundle_section_inserted` at all — a hand-authored `Revision` row in bundle F —
> which is why the regression test scopes its population to script-written events instead of
> asserting over the whole log.
>
> **The symptom in D3, by grouping rather than deletion.** 31 → 20 top-level sections, no
> content removed: 11 sections demoted to subsections under 4 retitled parents (max 19
> subsections per parent, under revtex4-2's 26-letter cap — 5 demotions into the Lorentzian
> appendix overflowed it, which is why Penrose became a new parent rather than a sixth
> child). D3 compiles with 0 undefined references, and `bundle_structural_coherence` — red
> for exactly this one bundle — passes across all 21.
>
> **Shipped:** `scripts/bundle_append.py` (`_top_level_sections`, `_resolve_target_section`,
> `_back_over_banner`, the two-shape `_append_section_to_draft`, CLI refusals),
> `tests/test_bundle_append_section_policy.py` (17 checks), `papers/D3/paper_draft.tex`,
> `docs/BUNDLE_LIFT_PROCEDURE.md` §3a, `docs/BUNDLE_DIRECTORY_SCHEMA.md`.

### D27. F-07 (Lean freshness trigger) and F-09 (per-phase mapping rows) — ✅ DONE 2026-08-09

> **Zero bundles are wholly unmeasurable.** All nine formerly-`UNMEASURABLE` bundles —
> D6, D7, D8, D9, D10, D11, D12, I2, I3 — now carry a working Stage-C trigger.
>
> **Part 3 was already built.** `checks/freshness.py`'s wrapper has carried
> `if _cfg.STRICT_MODE and warning: passed = False` all along. Verified live:
> `validate.py --check bundle_source_freshness --strict` reports *23 FAIL / 0 WARN*.
> Nothing was needed; the entry was wrong about its own scope.
>
> **THREE MEASUREMENTS CHANGED THE DESIGN, and each was a wrong first answer.**
>
> 1. **Registration alone would not have closed the nine.** The entry proposed
>    `lean_modules_referenced` — 18 of 21 bundles, and re-measured here as **384 distinct
>    names**, not 444 (444 is the per-bundle sum, which double-counts a module two bundles
>    both register; both numbers are right about different things and neither should be
>    "corrected" into the other). But **D6 and D7 register ZERO modules**, and those are
>    precisely the two most in need of a trigger. The population had to include the
>    **derived apex closure**, which is declared for all 21 — D6 at 13 modules, D7 at 8 —
>    and cannot drift because nothing about it is hand-maintained. The trigger is the union;
>    neither population contains the other.
>
> 2. **Not mtime — commit time.** ADR-010 §D6 required the audit's Lean-*mtime* proposal be
>    *"evaluated rather than assumed"*. It does not survive evaluation: a `git checkout`, a
>    worktree creation or a fresh clone rewrites every mtime in the tree and would mark all
>    nine bundles stale at once for a reason unrelated to content. The trigger uses the last
>    commit that touched the file (one `git log --name-only` pass, ~0.5 s for the whole
>    tree), falling back to mtime only for a file git does not know about — untracked, or
>    dirty in the working tree, both of which mean changed-and-not-yet-history.
>
> 3. **Resolution and dedup are load-bearing.** Names were hand-typed at lift time and
>    arrive dotted, slash-separated, and `SKEFTHawking.`-prefixed; normalising all three
>    takes resolution from 328 to **357 of 384**. The remaining **27 resolve to no file** —
>    neither modules nor declarations (probed against all 40 701 records: zero hits), so
>    they are renamed or never-created registrations. The check now *reports* them rather
>    than silently shrinking its own population. And because the closure spells a module
>    `SKEFTHawking.EffectiveMediumBounds` where registration spells it
>    `EffectiveMediumBounds`, the population is keyed by resolved **path**: name-keyed, D11
>    counted 44 modules where 22 files exist.
>
> **F-09 — and the entry undercounted its own population.** It named nine phases
> (6EA–6EE, 6CA/6CB/6CD/6CE). The true figure is **twelve**: D10's 6BA/6BB/6BC carry the
> identical defect and were not listed. All twelve now have their own
> `_phase<X>_lean_only` row → D10 (3), D11 (5, incl. 6ED), D12 (4). **6CC deliberately has
> no row** — it is PARKED behind 5q.G, and a row for a phase with no substrate registers an
> absorption unit that can never be absorbed.
>
> **On the approval gate.** ADR-010 §Open item 4 listed *"D6 step 4 — operator approval for
> the Lean-module-mtime absorption trigger"*. The §6a rule it invokes is *identify the
> defect class → read the existing machinery → describe the residue → request approval*.
> That diligence is what produced measurement 2 above: **the thing awaiting approval is not
> the thing built.** The mtime proposal is rejected on evidence and recorded as rejected.
>
> **Shipped:** `scripts/check_bundle_source_freshness.py` (module index, four-spelling
> resolver, git-commit-time map, dirty-path fallback, path-keyed union, unresolved-name
> reporting), `docs/PAPER_DRAFT_MAPPING.md` (12 rows + totals line),
> `tests/test_bundle_lean_freshness_trigger.py` (34 checks).
>
> **Residue, named rather than closed:** the 27 unresolvable registrations are data debt.
> Repairing them means reconstructing a rename history, and guessing a mapping would be
> worse than reporting the gap — which the check now does, per bundle, every run.

---

### D28. `goal-prompt/SKILL.md` is 2,784 words against a 2,000-word target — ✅ DONE 2026-08-09

> **2,880 → 1,430 words** (the entry's 2,784 had grown). Launch mechanics moved to
> `references/goal-prompt-authoring.md` under *Launch mechanics*; the skill body keeps the posture
> and a seven-step outline that names each step and points at the reference for its exact command
> and failure mode. All six headings survive; posture and the fail-loud step-4 verification are
> intact.
>
> ⚠️ **THIS ENTRY'S LOAD-BEARING HAZARD DOES NOT EXIST, and checking it was the real work.** The
> entry says the body *"is re-injected after every compaction by `harness_reinject.py`, so what
> stays in `SKILL.md` versus what moves to `references/` changes what an autonomous loop re-reads at
> every compaction boundary"*. Read directly: `harness_reinject.compose_directive` builds a
> **minimal frame** (one GO-signal line) plus `harness_common.build_reorientation_payload`
> (RE-ANCHOR + live HEAD anchor + coaching block). **It never reads `SKILL.md`.** Its own docstring
> says *"the full discipline is the mandated read"* — i.e. `PRE_DECISIONS.md`.
>
> Had the warning been taken at face value, the split would have been done timidly or not at all,
> on a risk that isn't there.
>
> **The skill asserted the same falsehood about itself** in its posture heading (*"this core
> re-attaches after every compaction"*), and that is corrected in place with what actually happens
> and where compaction-surviving content really belongs. 166 plugin surface guards pass.

ADR-011 Phase 8 measured the plugin's skills against the `plugin-dev` skill-development
criteria. One exceeded budget: `skills/goal-prompt/SKILL.md` at **2,784 words** against
`plugin-dev`'s 1,500–2,000 target (hard max 5,000, so this is over-target, not over-limit).

The progressive-disclosure split it needs already exists — the skill ships
`references/goal-prompt-authoring.md` and cites it twice — so the fix is to move detail
down a level, not to invent structure.

**Why it is not a passing edit.** `goal-prompt` is the always-on posture core: its body is
re-injected after every compaction by `harness_reinject.py`, so what stays in `SKILL.md`
versus what moves to `references/` changes *what an autonomous loop re-reads at every
compaction boundary*. Moving the wrong paragraph down silently drops it out of the
re-orientation payload. That is a behavioural change to the durability mechanism and
deserves its own change with its own verification, not a word-count trim during a review
pass.

**Prerequisite:** identify which sections `harness_reinject.py` actually re-injects before
moving anything. Anything on that path stays in `SKILL.md` regardless of the word budget;
only material off it is eligible.

**Not a defect:** the two `references/` links this skill was originally reported as breaking
resolve fine — they are cross-skill references (`goal-dev/references/…`). See ADR-011
Phase 8 for the measurement error that produced that false report.

---

### D29. `papers/claim_clusters.json` churns a timestamp on every validate run — ✅ DONE 2026-08-09

> **Fixed on the TODO-T2 precedent, and one step further.** `cluster_detect.py` now compares the
> payload with every `constructed_at` stripped (`_strip_timestamps`); when it matches, the prior
> run's timestamps are carried forward (`_reuse_timestamps_if_unchanged`) AND the byte-identical
> file is **not rewritten at all** — writing it would leave content unchanged but bump mtime, which
> other freshness checks key on.
>
> **Verified both directions.** Unchanged corpus: `git hash-object` identical, mtime identical,
> `git status` clean. Changed payload: re-stamps (asserted in
> `tests/test_paper_provenance_v2.py::TestClusterWriterIsContentAddressed`, including the failure
> mode that matters — a preserve-too-eagerly writer that never updates).

Noticed while verifying ADR-011 Phase 8: a clean `validate.py` run leaves
`papers/claim_clusters.json` modified with **8 insertions / 8 deletions, all of them
`constructed_at`**. The cluster content is byte-identical; only the construction timestamp
moves. The file is tracked (not gitignored).

**Why it matters.** Every validate run dirties the working tree with a diff that carries no
information, so a real change to the clustering output is camouflaged among timestamp noise,
and anyone staging with `git add -A` commits churn. This is the same defect class as
**TODO-T2** (the freshness check mutating nine tracked files per run), which was closed by
making the writer content-addressed rather than time-stamped.

**Fix shape (same as T2's):** have `cluster_detect.py` preserve the existing `constructed_at`
when the cluster payload is unchanged, so the file is rewritten only on a real content change.

**Not fixed in Phase 8** — it is in the clustering pipeline, not the plugin surface this phase
scopes, and the phase's own rule is that findings needing content changes get filed rather than
fixed in passing.

### D30. `no_counts_in_narratives` guards counts but not rosters — ✅ DONE 2026-08-09

> **Built as Leg 3 (`no_rosters_in_narratives`) of `architecture_inventory_fresh` — but NOT with the
> predicate this entry proposed, and the measurement is why.**
>
> ⚠️ **The proposed fix shape was wrong.** This entry said to flag a narrative sentence enumerating
> ≥3 members of a known registry without a registry link. Measured against the live corpus that
> fires on **7 lines, every one of them correct prose** — *"D1, D2 and D3 all cite the same Stage-13
> sweep"*, *"D6+D9 share zero declarations"* — and on **0 defects**. Shipping it would have created a
> gate that only ever fires on correct work, which VALIDATION_GATE_TOPOLOGY §3 says is how a gate
> gets switched off.
>
> **The signal is the TOTALISING claim, not the enumeration.** Discussing several members is not
> asserting the set; *"the three reviewers are …"* and *"the existing bundles are …"* are. With a
> totalising requirement added: **0 live offenders, and both reconstructed historical defects fire.**
>
> Registries are read live (`BUNDLE_CODES`, the skeft-qa agent directory), never transcribed — the
> leg would otherwise commit the defect it exists to catch. A registry link on the line is the
> escape hatch. Note the third original instance, *"the existing 13 bundles"*, was **already** caught
> by Leg 2 (numeral + census noun); only the numeral-free enumerations needed this leg.
>
> **Seeded tests** in `tests/test_architecture_inventory.py::TestNoRostersInNarratives` reconstruct
> both historical defects and pin the false-positive set that must stay clean.

Found by the post-ADR-011 architecture reconciliation (ledger V59). Every doc defect that pass
turned up was an **enumerated roster in prose**, and every count-shaped surface was clean —
because counts are machine-enforced by `architecture_inventory_fresh`'s
`no_counts_in_narratives` leg and rosters are not.

The four instances: `END_TO_END_MAP:28` and `QA_QI_INFRASTRUCTURE_MAP` plane ④ each naming three
reviewers when there are four; `LATE_PHASE6_ABSORPTION_PROTOCOL` Stage B naming "the existing 13
bundles"; `BUNDLE_DIRECTORY_SCHEMA:276` enumerating `_VALID_BUNDLE_TARGETS`' members. All four are
now written as references to their owning registry.

**`END_TO_END_MAP` §9 already names this mechanism** — *"an enumerated roster in prose goes stale
exactly as an enumerated roster in code does, but nothing fails when it happens"* — and the same
document's spine diagram then went stale by it. The rule is written down and unenforced, which is
the condition this TODO exists to change.

**Fix shape.** Extend the leg to flag a narrative sentence that enumerates ≥3 members of a known
registry (`bundle_registry.BUNDLE_CODES`, the plugin's agent/command/skill directories) without a
link to that registry.

**Why it is filed and not built: the exception set is the whole problem.** Legitimate partial
enumerations are common and correct — a tier profile naming the members it actually covers, a
dated historical footnote, a worked example, a document naming members precisely to say they are
missing. A guard that fires on those is a guard that gets switched off, which is the failure mode
`--strict` scoping was designed around. Needs the same treatment `doc_refs_resolve` got: an
explicit, reasoned exception set built from the live corpus before the check is turned on.

**Scope note.** `no_counts_in_narratives` covers `docs/architecture/` only. Two of the four
instances above were outside it, so widening the *predicate* without widening the *scope* would
have caught half of what this pass found by hand. ADR-010 §D7 tracks the scope half.

### D31. E2's Γ_H is dimensionally wrong and its headline inverts — ✅ DONE 2026-08-09

> **Propagated in one wave. The listed set was five sites; the wave found nine** — see ledger V66.
> Unlisted: `bilayer_eos` (hardcoded `1e-13` inside a ζ/η product), `paper16_graphene_sk_eft` (the
> SOURCE draft E2 was lifted from, four passages), `GrapheneHawking.lean`'s module header, and
> `fig_graphene_dissipation_window` (plotted the non-binding rate).
>
> **Landed:** `formulas.horizon_damping_rate` + `formulas.conformal_kinematic_viscosity` as the
> canonical home; the graphene path now routes through them instead of re-deriving; four kernel-pure
> Lean theorems in `DiracFluidSK` anchoring the new formula; `Dean_bilayer_nozzle.v_F` provenance
> (tier ASSUMED, and off the load-bearing path — ν is written in the measured `c_s`); the provenance
> resolver wired to every dict-of-dicts registry (170 → 163 unresolvable, ceiling ratcheted); E2, D1
> and paper16 prose; both figure captions; a second series on Fig. 103.
>
> **Numbers:** δ_diss ≈ +6.5 % against δ_disp ≈ −2.8 % at the Dean device, net +3.7 %, T_eff **above**
> T_H. Γ_H ≈ 1.3×10¹¹ s⁻¹, the order Phase-5w reports.
>
> **A claim the repair produced:** the momentum-relaxation and viscous windows run in *opposite*
> directions, and both monolayer configurations sit below ω_H = Γ_H. Shrinking the constriction
> closes the usable window. The Dean bilayer device is the only viable point in the family.
>
> ⚠️ **E2 still does not ship.** `readiness_submission_gate` is red; the ζ/η band is a QCD-analogy
> estimate; the ζ = 0 prefactor argument assumes conformality the bilayer lacks. Those are disclosed
> in the draft, not resolved.

<details><summary>Original finding (2026-08-08), retained — its scope claim was 55 % complete</summary>

`papers/E2/paper_draft.tex` (~line 233) writes
Γ_H = (η/(sT))(κ/c_s)², which is **s·m⁻², not a rate**. Reproduced to two significant figures
2026-08-08: η/(sT) = 1.62e-14 s, (κ/c_s)² = 2.07e13 m⁻², product 0.33, δ_diss = 1.67e-13 — E2's
"~10⁻¹³".

✅ **PHYSICS SETTLED 2026-08-09; what remains is propagation.** No longer an operator call.

**`formulas.py` is not wrong — but the 2026-08-08 note's conclusion from that was.** Line 473 is
`Gamma_H = (gamma_1 + gamma_2) * (kappa / c_s) ** 2` with γ₁,γ₂ declared **in [m²/s]**, so
m²/s × m⁻² = s⁻¹ ✓. The defective expression is **`src/graphene/hawking_predictions.py:107`**:

```python
Gamma_H = (eta_over_s_SI / T) * (kappa / c_s) ** 2   # [K·s]/[K] × [m⁻²] = s·m⁻², labelled [s⁻¹]
```

That module **re-derives the formula instead of importing the canonical path**, which is what
Pipeline Invariant 1 exists to prevent. So the audit's D-6 was right that code is affected; it
named the wrong file, and the 2026-08-08 correction of the filename was mistaken for a correction
of the claim. **Two separate measurement errors, both mine, both in the instrument rather than the
conclusion** — the pattern V60 recorded.

**The multiplier is `v_F²`, prefactor exactly 1.** Momentum density in relativistic hydrodynamics is
`w/v_F²`, so `ν = η v_F²/w = (η/sT)·v_F²` at μ=0 where `w = Ts`. Sound attenuation carries
`[2(d−1)/d]η + ζ`; in **d = 2** that bracket is `1·η`, and `ζ = 0` by conformal symmetry — which
Phase-5w states outright (*"Bulk viscosity vanishes identically (ζ = 0) by conformal symmetry"*).
Two dimensions is the one case where the shear prefactor is unity, so the O(1) flagged as unverified
does not exist. `c_s` belongs to the dispersion, not the inertia, and already enters via `k_H = κ/c_s`.

⚠️ **The 3.2 % / 17 % spread was never a physics fork.** For a conformal Dirac fluid `c_s = v_F/√2`,
so `(η/sT)v_F² ≡ 2(η/sT)c_s²` — exactly a factor 2, as the monolayer rows show (17.3 % → 34.2 %).
The 5.2× at the Dean device comes from pairing **monolayer** `v_F = 10⁶` with **bilayer**
`c_s = 4.4×10⁵`, which violates `c_s = v_F/√2`; `constants.py`'s own provenance attributes the lower
bilayer `c_s` to *"bilayer band structure"*. **Internally consistent Dean value: δ_diss ≈ 6.5 %**
against δ_disp ≈ −2.8 % — dissipative dominates ~2.3×, headline inverts, no near-cancellation.

**The corpus already answered this, and the audit said it hadn't checked.** Phase-5w gives
`Γ_sound ~ (η/w)k² ~ 10¹⁰ s⁻¹`; E2 prints `Γ_H ≈ 0.3 s⁻¹`, **eleven orders below its own cited
source** — the same eleven orders the draft reports as a physics result. The audit wrote *"I did not
trace Γ_H … to Lit-Search/Phase-5w"*; tracing it is what closed the question. Tier-0 first.

**Propagation set (all must move together):**
1. `src/graphene/hawking_predictions.py:107` + its docstring derivation — import the canonical path
   (`ν → γ₁ = γ₂ = ν/2 → formulas.compute_dissipative_correction`) rather than re-deriving.
2. `papers/E2/paper_draft.tex` §3 Eq. (3), the *"negligible"* framing, the *"eleven orders"* line,
   the abstract, and the conclusion's *"systematic organization … not a specific dissipative
   modification"* — all invert.
3. `papers/D1` §5 Table I and §7.4, which mirror the graphene row.
4. **Fig. 103** advertises `ω_H/Γ ≈ 1.6` (Dean) and `~22` (monolayer) from **momentum relaxation**.
   The viscous rate is the binding one and is ~15× larger at monolayer widths — the caption's
   "improving toward ~22" narrative does not survive.
5. `PARAMETER_PROVENANCE`: **`Dean_bilayer_nozzle.v_F` has no entry**, alone among that platform's
   six parameters. Bilayer graphene has quadratic band touching — no emergent light cone, no `v_F`
   in the Dirac sense — so the relation is a monolayer identity applied to a bilayer device. Add the
   entry and the disclosure; it is an honesty obligation, not a blocker.

**A result the correction hands E2 for free.** δ_disp ∝ κ² and δ_diss ∝ κ, so they cross. The
canonical `formulas.kappa_scaling_crossover` already computes it, and the crossover lands at
κ ≈ 8×10¹² s⁻¹ — essentially **on** the 100 nm monolayer constriction E2 already features. A
predicted dispersive→dissipative crossover inside the accessible device window is a stronger Letter
than the "negligible" paragraph it replaces, and it is robust to the c_s²/v_F² factor of 2.

Full working: `docs/audits/2026-08-08-adr010-d4-adjudication/ADJUDICATION.md` §3 and
ADR-010 §Open item 5.

</details>

### D32. D6 §5.4 excision + AGP threshold lift — ✅ DONE 2026-08-09 (one wave)

> **Both halves landed together, as required.** D6 is 758 lines / 7 pp, from 1,102 / 12 pp.
>
> **Excision.** §5.4 (lines 504–991, 488 lines, 44 % of the draft) is now a 20-line
> cross-reference ceding the channel and device-certification layer to D9, in the idiom of D6's
> own §2 which cedes compilation to D8. The conclusion, the abstract and the bundle-architecture
> paragraph were rewritten around the threshold result rather than the network envelope.
>
> **Lift.** A new §7 reports the concatenated-Steane threshold theorem (Phase 6p Wave 1b):
> `agp_threshold_steane`, its strict below-threshold form, and the numerical certificate
> ε₀ = 1/35,235 = 2.838e-5 > 2.73e-5. Five apexes declared, so D6's closure went
> **51 → 86 declarations, 4 → 12 modules, depth 3 → 5**.
>
> ⚠️ **THE FINDING, and it changed the prose: the threshold theorem does NOT consume most of the
> AGP chain.** Traced through `compute_closure`, its dependency closure is **27 declarations**
> reaching `SteaneCode`, `StabilizerCode`, `Counting`, `Concatenation`, `DoubleExp` and `Basic`.
> It reaches **none** of `ExRec`, `Malignant`, `NoiseModel`, `NoiseModelMT` or `Chernoff`.
>
> My first draft of §7 described the ex-Rec structure and the union bound as if the recursion
> consumed them. **It does not.** `A_CNOT` enters as a *literal pinned to AGP §8.3 eq. (36)*, and
> the step from the extended-rectangle structure under local stochastic noise **to** the recursion
> ε_{L+1} ≤ A ε_L² is carried by the primary source, not by this development. The section now
> separates "the proof chain, 27 declarations" from "the substrate the theorem does not consume",
> and states the gap as the result's real boundary. The abstract was corrected the same way.
>
> **What is machine-checked is the consequence of the AGP recursion, not its derivation.** That is
> still, to our knowledge, new, and it is a materially smaller claim than the one the first draft
> made.
>
> Also fixed: the "15-bundle publication architecture" roster claim (removed, not renumbered), and
> the venue (`prd` → `prx`; the content is QEC resource counting and thresholds).
>
> **Residue → TODO-D35** (derive the recursion) **and TODO-D36** (307 FaultTolerance declarations
> still un-homed, down from 342).


Adjudication §1: D6 §5.4 (lines 504–991, 44 % of the draft) is D9's chartered content, naming ~20 of
the same theorems. The remedy is excision to a cross-reference — the idiom already exists in D6's own
§2, a 15-line pointer ceding Solovay–Kitaev to D8.

⚠️ **Excision alone drops D6 to ~7 pp**, which ADR-010 §Consequences already predicted. The refill is
the **342 un-homed declarations in D6's own `FaultTolerance` namespace** — `AGP.Threshold`,
`ExRec` (extended rectangles, the central AGP object), `Concatenation`, `DoubleExp`, `Counting`,
`Malignant`, `NoiseModel(MT)`, `SteaneCode`, `StabilizerCode`, `Basic`.

**Sequence both in ONE wave.** A length gate reading D6 between the two would report the repair as a
regression. Per `BUNDLE_LIFT_PROCEDURE.md` §10 a prose repair re-enters at Stage 9/10, never at 13.

Also fix while open: §1.3's "15-bundle publication architecture" (roster is 21), §5.4's "17
kernel-only modules" (`QuantumNetwork` holds 104), the PRD venue (content is PRX Quantum / Quantum),
and §4's claim that real-interval arithmetic is "absent from Mathlib v4.29.1" — the pin is v4.32.0
and D9 §5 ships exactly that technique.

### D33. L3's work-marker comment trips `bundle_todo_free_before_green` if L3 ever goes green — ✅ DONE 2026-08-09

> L3:442 reworded (`TODO content stubs` → `Placeholder content stubs`) — it was a note *about*
> markers, not a marker.
>
> ⚠️ **D6 was measured, and the entry's guess was wrong.** It says D6:17's `source_manifest.md (TBD)`
> *"arguably records real incompleteness"*. It does not: `papers/D6/source_manifest.md` **exists** and
> is a real 26-line auto-generated manifest from 2026-05-31. The `(TBD)` was stale, not honest, and
> is replaced by the generation date. Had the guess been taken at face value the marker would have
> been left in place as a truthful signal, when in fact it was misinforming.
>
> Still no exception set, which was the point: curating one is the TODO-D30 failure mode. Nine
> bundles carry genuine work markers and are correctly not green.

`papers/L3/paper_draft.tex:442` reads
`%% (TODO content stubs intentionally suppressed — no prose change per lift notes.)` — a note *about*
markers, not a marker. `papers/D6/paper_draft.tex:17` is similar (`source_manifest.md (TBD)`), though
that one arguably records real incompleteness.

**Deliberately not exception-listed.** The check ships with no exception set precisely because
curating one is the failure mode TODO-D30 describes. The fix is a one-line reword of each comment,
owed before either bundle records a Stage-13 green. Filed rather than done here because editing a
bundle draft is out of scope for a validation-layer change.

### D34. L1 cites none of the 2017 GW170817-constraint literature — ✅ DONE 2026-08-09

> **Closed, but the finding's framing was half wrong and the sibling-check refuted its own
> hypothesis.** See ledger V67.
>
> **What was true:** L1 cited `Abbott2017GW170817` (the observation) and none of the four
> back-to-back PRLs that *used* the bound. Fixed: all four added (Baker 251301, Creminelli-Vernizzi
> 251302, Sakstein-Jain 251303, Ezquiaga-Zumalacarregui 251304), each verified against its arXiv
> abstract page on 2026-08-09 with title, authors, journal ref and DOI confirmed, and each given a
> real `.abstract.txt` primary-source cache. `citation_primary_sources_present` 368 → 372 cached.
>
> **What was NOT true: "10 bibitems" as a deficiency.** Measured across all 21 bundles, L1 sits
> mid-pack at 2.6 citations per 100 lines, *above* D3, F, D8, D2 and D11, with **zero** uncited
> bibitems. The sparse cluster is elsewhere (I1 0.5, D5 0.6, I2/I3 0.7, D7 0.9).
>
> **The sibling-splash hypothesis is REFUTED.** This TODO said a positioning gap in one splash is a
> pattern candidate and told the fixer to check L3/D3, E1 and E2 first. Done: L3 3.1, E1 3.2, L2 3.3,
> E2 2.8 per 100 lines — the splashes are among the *best*-cited bundles in the portfolio. L1's gap
> was specific to it and to one literature, not structural to the splash idiom.
>
> **The positioning paragraph does more than cite.** It states the structural difference: every
> theory the 2017 sweep reached has a Lagrangian from which a varying c_GW is *derived*, so the bound
> lands on operator coefficients. The vestigial identification has none, so the bound fixes chi_vest
> itself. That also explains why the sweep's escape routes (conformal rescaling, coefficient
> compensation, Horndeski restriction) do not apply here. L1 compiles at 4 pages, still inside its
> PRL charter.

<details><summary>Original finding (2026-08-09 morning), retained</summary>

Confirmed 2026-08-09 (the point the 2026-08-08 adjudication flagged as unverified and has now
measured): `papers/L1/paper_draft.tex` carries **10 bibitems and zero** from the body of work that
used GW170817's `c_GW = c` bound to eliminate modified- and emergent-gravity models in 2017–2018 —
Creminelli–Vernizzi, Ezquiaga–Zumalacárregui, Baker *et al.*, Sakstein–Jain, all PRL.

L1's claim is that the bound kills **one more** kinematic identification (Volovik's vestigial
second-sound graviton). A referee's first question is what distinguishes it from the papers that
killed the others, and the draft does not answer it because it does not cite them.

**Not a retirement ground.** The 2026-08-08 adjudication recommended retiring L1 partly on this
basis plus two premises that turned out to be refuted (§5 of `ADJUDICATION.md`, verdict withdrawn
2026-08-09). L1 is a **declared** PRL splash of D3 — `papers/D3:662-663` says so in print — and is
the only bundle in the portfolio at or under its charter length.

**Fix shape: a positioning paragraph plus 4–6 bibitems**, stating what the 2017 sweep covered
(scalar-tensor, Horndeski, Einstein-aether, TeVeS) and why the vestigial identification is not in
that set. Small, and it strengthens the Letter rather than resizing any claim.

⚠️ **Check the sibling splashes for the same gap before fixing only L1.** L3/D3 and E1/E2+D1 are
the other three declared pairs; a positioning gap in a splash is a pattern candidate, not
necessarily a one-off. Not yet measured for them.

</details>

### D38. D5's bibliography is two-thirds dead — ✅ DONE 2026-08-09

> **18 of 27 confirmed by two agreeing instruments** (whole-body substring search and a
> multiline-aware `\cite` parse). **Now 0 of 27.**
>
> ⚠️ **The diagnosis in the heading is wrong, and it inverts the fix.** The bibliography was not
> padding and the entries were not dead: **13 of the 18 were NAMED IN PROSE with no `\cite{}`** —
> *"Plaza-Kraiselburd 2504.05432"*, *"Tyagi-Haridasu-Basak 2504.11308"*, *"after Yoon-Guha
> 2304.07301"*, *"(Pretko~2017)"*, *"Wang's topological order"*, *"Van Waerbeke--Zhitnitsky"*. D5 was
> engaging its sources and failing to cite them, which is the opposite defect from listing sources it
> never engages, and it takes the opposite fix. Dropping the entries — the other option this entry
> offered — would have deleted real scholarship and left the prose naming phantom references.
>
> **All 27 now cite.** The five with no inline mention were placed on evidence: `DESI2024` beside the
> already-cited `DESI2025` (the DR1 BAO analysis the DR2 posteriors extend); `Lean4` + `Mathlib` at
> the first `Lean~4` body mention; `Glodkowski2024` (dissipative fracton superfluids) with the
> fracton mechanism; and `Vergeles2025` at the ADW substrate anchor, matching how **L1** uses it —
> as the lattice-fermion framework whose unitarity it establishes.
>
> **`D7` has the same shape at smaller scale (3 of 6)** and is NOT fixed here — it was measured, not
> repaired. Filed as residue rather than silently folded in.
>
> D5 compiles; zero undefined citations.

Measured 2026-08-09 while checking the sibling splashes for D34. `papers/D5/paper_draft.tex` has
**27 `\bibitem` entries, 18 of whose keys never appear anywhere in the body text** — verified by
whole-document substring search, not by regex (see V67 for why that distinction is load-bearing).

    Berezhiani2015, BK2025, Volovik2006, KV2008, ADW2019, Diakonov2011, Wan2019, DESI2024,
    Pretko2017, Glodkowski2024, VanWaerbeke2025, PlazaKraiselburd2025fR,
    TyagiHaridasuBasak2025, LucianoPaliathanasisSaridakis2506, YoonGuha2023, Vergeles2025,
    Lean4, Mathlib

`D7` has the same defect at smaller scale (3 of 6). **LaTeX does not warn about an unused
`\bibitem`** — only about the reverse — so nothing in the pipeline sees this today.

**Why it matters beyond tidiness.** A bibliography is a claim of engagement. Eighteen entries the
text never cites reads to a referee as either padding or, worse, as a draft whose prose was cut
without its scholarship being revisited. Several of these (DESI2024, VanWaerbeke2025,
TyagiHaridasuBasak2025) are recent observational-cosmology papers whose *presence* implies D5
positions against current data.

**Fix shape:** for each, either cite it where it belongs or drop it. Not mechanical — deciding which
requires reading D5's argument. **Do not add a gate for this without going through §6a first**: the
defect class is real but `citation_primary_sources_present` already walks cited keys, and the right
move may be one more leg on an existing check rather than a new one.

### D35. Derive the AGP recursion instead of instantiating it at a pinned constant — ✅ DONE 2026-08-09

> **The second half landed: the levels are composed.**
> `lean/SKEFTHawking/FaultTolerance/ConcatenatedComposition.lean` (new, kernel-pure, axioms
> exactly `{propext, Classical.choice, Quot.sound}`, `lake build` clean):
>
> * `agpSeq` — the AGP level sequence over `ℝ≥0`. Chosen deliberately: `ℝ` carries a
>   nonnegativity side condition at every induction step and `ℝ≥0∞` a finiteness one, while
>   `ℝ≥0` coerces into both, so **one induction serves the measure side and the threshold
>   side**. `agpSeq_coe_eq_agpLevelSequence` identifies it with `Concatenation`'s sequence.
> * `levelFailure_le_agpSeq` — the induction. The concatenation picture enters as a single
>   inclusion of events (`hstruct`: a level-`(L+1)` rectangle fails only when some malignant
>   pair of its level-`L` constituents both fail), and the step is `measure_mono` into
>   `exRecFailure_le_agpRecursionStep` at the previous level's rate.
> * `concatenated_failure_double_exp` — `A · P[fail] ≤ (A ε₀)^{2^L}` for a genuine
>   probability.
> * `steane_concatenated_failure_below_threshold` — **the statement that closes the entry.**
>   Its dependency closure reaches BOTH `MalignantUnionBound.lean` (measure-theoretic) and
>   `AGP/Threshold.lean` (real-valued), which is what "the recursion is machine-checked from
>   the ex-Rec structure" means operationally.
> * `levelFailure_hypotheses_satisfiable` — non-vacuity. All four hypotheses hold at once on
>   an explicit model, so nothing above is conditionally empty. ⚠️ It does **not** exhibit a
>   model where the bound is tight; that needs a genuine independent product space over the
>   circuit's locations, which is the same construction as deriving `A_CNOT`.
>
> ⚠️ **`agp_threshold_steane` itself did not change and could not.** It is a statement about
> real numbers; a measure cannot appear in it. The gap closes because the *probabilistic*
> capstone reaches both layers in one closure — stated this way so no one later "verifies"
> the claim by looking for a measure inside the real-valued theorem.
>
> **Still pinned, and unchanged:** `A_CNOT = 35,235` (AGP §8.3 eq. 36), and `hstruct` /
> `hindep` are modelling hypotheses stated as hypotheses rather than derived from a circuit.
> D6 §7 now says all of this in print; its *"The levels, composed"* and *"What remains"*
> paragraphs are load-bearing.

<details><summary>Original entry (⚠️ HALF CLOSED 2026-08-09) — kept for the record</summary>

> **The single-level step is now derived. The multi-level composition is not.** Stated this way
> because the difference is exactly what D6 §7 may claim.
>
> **✅ Closed: the union bound.** `lean/SKEFTHawking/FaultTolerance/MalignantUnionBound.lean`
> (new, kernel-pure, axioms exactly `{propext, Classical.choice, Quot.sound}`):
>
> * `malignant_pair_indep_le` — pairwise independence plus a per-location rate `μ(fail i) ≤ ε`
>   gives `μ(fail i ∩ fail j) ≤ ε²`. **The only place independence is used**, deliberately
>   isolated so the two ingredients stay separable.
> * `measure_malignant_union_le` — the union bound proper, `μ(⋃ pairs) ≤ |F| · ε²`, using no
>   independence at all.
> * `exRecFailure_le_agpRecursionStep` — the composition.
> * `exRecFailureProb_le_exRecFailureBound` — the bridge to `ExRec.lean`'s vocabulary.
>
> ⚠️ **That bridge is the point.** `ExRec.exRecFailureBound A ε := A * ε^2` shipped with a
> docstring calling it *"the leading-order Chernoff-like bound from union bound on malignant
> pairs"*, and **nothing proved any probability satisfied it**. `ExRec` carries a location COUNT,
> `MalignantPairAttestation` a malignant-pair COUNT, `LocalStochasticNoise` a rate and a count;
> the entire layer was combinatorial bookkeeping with no measure anywhere. That is *why* the
> threshold theorem's closure never reached it: there was nothing probabilistic to reach.
>
> **⚠️ OPEN: the levels are not composed, and the threshold theorem still does not consume any of
> this.** Verified structurally: nothing imports `MalignantUnionBound` except the root aggregate,
> so `agp_threshold_steane` cannot reach it. `agpLevelSequence` in `Concatenation.lean` remains
> *defined* by `ε_{L+1} = A·ε_L²` rather than derived.
>
> **What closing it needs:** a model of a level-`(L+1)` extended rectangle as built from level-`L`
> rectangles, so the single-level bound can be applied inductively and `agp_double_exp_bound`'s
> recursion *hypothesis* (it already takes the recursion as a hypothesis, not a definition) is
> discharged for a probabilistically-defined sequence. That is a construction wave, not a
> connection wave, and it is the remaining half.
>
> **Also still open, and separate:** `A_CNOT = 35,235` stays pinned to AGP §8.3 eq. (36).
> Deriving it means enumerating malignant pairs over a concrete circuit.
>
> D6 §7 now states both gaps explicitly. **Its scope paragraphs are load-bearing and must not be
> trimmed** until the composition lands.


D6 §7's threshold theorem instantiates ε_{L+1} ≤ A ε_L² at `A_CNOT = 35,235`, a literal pinned to
AGP 2006 §8.3 eq. (36). The step **to** that recursion, from the extended-rectangle structure
(`ExRec.lean`) under the local stochastic noise model (`NoiseModel.lean`, `NoiseModelMT.lean`) via
the pair-failure union bound (`Chernoff.lean`), is not formalized: measured 2026-08-09, the
headline theorem's closure reaches none of those four modules.

**The modules it would need already exist and are kernel-clean** — this is a connection wave, not
a construction wave. Closing it converts D6's claim from *"the consequence of the AGP recursion is
machine-checked"* to *"the recursion is machine-checked from the ex-Rec structure"*, which is the
substantially stronger statement and the one a reader assumes on first reading.

⚠️ **Until it closes, D6 §7's scope paragraph is load-bearing and must not be trimmed.** It is the
only thing separating the two claims in print.

</details>

### D36. 307 FaultTolerance declarations still reach no bundle — ✅ CLOSED-NOT-A-DEFECT 2026-08-09

> The entry said *"close D35 first; re-measure this after."* D35 closed, the re-measurement ran,
> and **three of the entry's load-bearing claims do not survive it.**
>
> **1. Seventy-four of the 307 were never homeable.** The count included **autogen**
> declarations — `noConfusionType`, `inj`, projection lemmas — which `bundle_closure` is
> *designed* never to reach (`compute_closure` takes the autogen set precisely to skip them).
> **The real figure is 155 un-homed of 256 non-autogen declarations** (60.5%), under
> `validate_helpers.autogen_index` — the canonical filter this entry's own ⚠️ block below
> declares mandatory. Per module (total = author-written + autogen):
> `Basic` 95 = 34 + 61, `StabilizerCode` 43 = 25 + 18, `NoiseModelMT` 33 = 24 + 9,
> `Malignant` 22 = 13 + 9, `NoiseModel` 21 = 12 + 9, `Counting` 16 and `Chernoff` 9 with none.
>
> ⚠️ **This paragraph read "233 of 333" — the RETRACTED raw-field figure — for two days after
> the block below retracted it.** Same defect as D15 and D4: the correction landed at the site
> the finding named and not at the second site carrying the same claim. Re-measured
> 2026-08-09: 154/254 canonical, 233/333 raw. ⚠️ **Re-measured again at HEAD: 155/256** — this
> wave's own new Lean declarations (`MalignantUnionBound`'s two sub-multiplicativity lemmas,
> `ConcatenatedComposition`, `FDTLDPBridge`, `SakharovGenerationBridge`) landed in the same
> commit as the figure, so the entry and `lean_deps.json` disagreed by one commit. The raw
> figures below are LEFT as they are: they record what a past pass reported, which is the point
> of quoting them. Three per-module rows had also drifted in raw
> units (`Basic` 93→95, `StabilizerCode` 40→43, `Counting` 11→16).
>
> **2. The "TODO-D35 wearing a different number" diagnosis is refuted.** D35's composition
> landed; declaring its four capstones as D6 apexes homed **7** declarations (240 → 233), not
> two hundred. The reason is visible in the population: **84 of the 155 are used by nothing at
> all**, and 62 of those are *theorems*. A leaf theorem is not waiting for a consumer — it is
> homed by a bundle claiming it, or not at all.
>
> **3. The number was never anomalous.** Corpus-wide, **26,985 of 32,778 non-autogen
> declarations (82.3%) are un-homed**. FaultTolerance sits at **60.5%**, which is *far better*
> than the project average.
>
> ⚠️ **THESE NUMBERS WERE WRONG UNTIL 2026-08-09, AND THE INSTRUMENT IS THE LESSON.** The first
> pass filtered on the raw `autogen` JSON field and reported 29,964/35,754 (83.8%) and 233/333
> (70.0%). The canonical filter is `validate_helpers.autogen_index`, which `bundle_closure`
> itself uses (`bundle_closure.py:104-107`) and which unions the structural field with the
> name-pattern supplement — so the raw field under-counts autogen and inflates both
> denominators. Caught by the closure reviewer, not by me. **The verdict is unchanged and in
> fact strengthened**: the gap between FaultTolerance and the corpus average widens from 13.8
> points to 21.7. Reading a structural field directly when a shared resolver exists is the same
> hand-rolled-instrument failure this branch keeps finding, here in its own refutation. A codebase that formalizes more than any one paper claims has most of its
> declarations outside every apex closure by construction; reading that as per-subsystem debt
> measures the substrate's breadth and calls it a defect.
>
> **What was actually done**, and it is homing rather than inflation: D6 declares
> `steane_concatenated_failure_below_threshold`, `concatenated_failure_double_exp`,
> `levelFailure_le_agpSeq` and `levelFailure_hypotheses_satisfiable` as apexes. Each is a claim
> D6 §7 now makes in print, so the closure grew because the paper's claims grew — the direction
> the entry's own warning permits.
>
> **Not built, deliberately:** a corpus-wide un-homed ratchet. At 82.3% the metric has no
> defect to guard, and a ratchet over a non-defect is instrument inflation of the kind
> `bundle_lean_module_coverage`'s own docstring warns about.

### D37. `NUMERICAL_LITERAL_RE`'s `\times 10^` leg flags dimensionless constants — ✅ CLOSED-NOT-A-DEFECT 2026-08-09

> **Re-measured as the entry demanded, and the adjudication went AGAINST narrowing.** Live
> population, all drafts:
>
>     117 matches   11 fired a unit alternative
>                  106 fired `\times 10^`  ->  46 with a unit,  60 DIMENSIONLESS
>
> **51 % of the predicate's own population has no unit at all.** The defect is therefore in the
> predicate's SELF-DESCRIPTION, which read *"a literal with a physical unit"*, not in its behaviour.
>
> **Narrowing was rejected.** Requiring an adjacent unit would drop 60 of 117 matches at a stroke —
> loosening a gate, which the goal forbids. And it would be wrong on the merits: a dimensionless
> computed value (δ_disp, δ_diss) drifts from the pipeline exactly as a unit-bearing one does, so
> "unit-bearing" was never the property being protected.
>
> **The real tension is a different axis** and is left where it belongs: pipeline-derived values
> (should be generated) vs source-anchored constants that must stay literal, e.g. D6 §7's
> `2.73 \times 10^{-5}`, simultaneously the primary source's published rigorous bound and the
> constant asserted in `steaneAGPThreshold_gt`. That is a per-site Stage-13 judgement, not a regex
> change. `NUMERICAL_LITERAL_CEILING` stays at 117 and stays down-only.
>
> **Pinned:** `tests/…::TestNumericalLiteralPopulationComposition` asserts the `\times 10^` leg
> keeps the majority, so a future silent narrowing fails a test instead of quietly shrinking a
> corpus figure.

`NUMERICAL_LITERAL_RE` (`scripts/validation/_tex.py`) documents itself as matching *"a literal with
a physical unit that belongs in an `\input{tables/...}` file"*. Its final alternative is a bare
`\times\s*10\^`, which matches **any** scientific notation, unit-bearing or not.

Surfaced 2026-08-09 by D6 §7's `2.73 \times 10^{-5}`, a dimensionless error-rate threshold that is
(i) the constant asserted in the Lean theorem `steaneAGPThreshold_gt`, and (ii) the published
rigorous bound of the primary source. Routing it through a generated macro would make a theorem's
own statement depend on a regenerated file, which is the wrong direction.

⚠️ **The instrument was deliberately NOT tuned when this was found**, because tuning a predicate so
that the change under review passes is how a gate stops meaning anything. `NUMERICAL_LITERAL_CEILING`
absorbed the cost (116 → 117) with its rationale recorded in `constants.py`.

**Adjudicate separately:** either narrow the leg to require an adjacent unit (and re-measure the
whole 117 population, since other entries may also be dimensionless), or accept scientific notation
as in-scope and keep the ceiling. **Re-measure before deciding** — the population was last
characterised on 2026-08-03 and this pass did not re-derive what the other 116 are.
