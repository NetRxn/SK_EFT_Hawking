# Accuracy verification ledger

**Purpose.** Track assertion-granularity verification of every architecture document, so
scope cannot be silently dropped and "complete" is earned rather than asserted.

**Why this exists.** Two prior passes reported completion and were wrong. The first checked
~20% of the surface and called it 100%. The second checked at **bullet** granularity — for a
compound claim it verified the measurable clause and let the rest ride, then reported the
bullet verified. Three errors survived into documents declared correct:

| escaped claim | how it hid |
|---|---|
| `"Invariant #16 cites the doc under a wrong filename"` | 3 assertions in one sentence; the *adjacent* bullet half (two files absent) was true and checked |
| `"--strict is scoped to submission by Invariant #12"` | `--strict`'s BEHAVIOUR was verified; that the invariant SAYS so was not |
| `"the four hazards … These are ADR-009 D3"` | each named test was verified to exist; the **completeness of the set** was never checked (D3 declares five) |

**The rule this ledger enforces:** an entry is `VERIFIED` only when **every atom** of it has
its own recorded check. A compound sentence is not one entry — it is one entry per assertion.

**Status key:** `TODO` · `IN-PROGRESS` · `VERIFIED` (every atom checked, method recorded) ·
`CORRECTED` (was wrong, fixed, atoms re-checked).

---

## Final state

**All seven VERIFIED at assertion granularity**, across two passes: V1–V7 over the documents
as they stood at `eb11fe97`, and **V8** over the prose the A1/A2/B2–B6 remediation added
afterwards. A sentence written after a verification pass is unverified by definition, so the
second pass is not optional bookkeeping.

| | |
|---|---|
| atoms verified | **222** individual rows (187 in V1–V7, 35 in V8) |
| claims found false and replaced | **18** (13 in V1–V7, 5 in V8) |
| error-priming blocks removed | **10** |
| incident citations reframed | **4** |
| documents unchanged by V1–V7 | **1** (`END_TO_END_MAP.md`) |

⚠️ **The second pass found 5 false claims, and the remediation pass wrote 4 of them** —
one inside a paragraph that was itself correcting an earlier error, and one *while correcting
that*. Writing a correction is exactly as error-prone as writing the original, and a single
failure mode — **a search scoped narrower than the sentence** — produced every one:

| the search | what it missed |
|---|---|
| raw identifier in `.tex` | drafts write `gapped\_interface\_axiom`; 14 files, 25 hits |
| sentence split on `.` | truncates at a dotted module filename, before the qualifier that follows |
| one record inspected | a set claim needs the whole population |

**The lesson is not "check twice."** Each of these was a proxy standing in for a decider, and
the decider existed in every case — the escaped-form scan, the check that already scans all 64
drafts, the full population. Reach for it first.

✅ **`SURFACE_INVENTORY.md`'s header now states how its tables actually derive (B7 closed).**
Values and membership are read from the owning artifact, **with one exception the header names**:
the registries table lists a curated set declared in the generator, because "is this collection
a registry?" is an editorial call, not a mechanical property — `constants.py` holds 67
module-level uppercase collections and 60 are physics data. The sentence is emitted by
`architecture_inventory.py:289` rather than stored in the tracked file, so the correction was a
generator edit (made under explicit authorisation, outside the no-code constraint).

**What the corrections had in common.** Of the 13, **four were inherited claims that were
already false when they were written into these files**, and none of the four would have been
caught by checking the numbers they cited — each required running the tool, reading its CLI, or
resolving a cited invariant number to its actual subject.

**Three distinct failure modes produced them:**

| mode | example |
|---|---|
| **proxy accepted as decider** | `grep -c "@register_check" validate.py` returns 5 (all comments); the AST returns none |
| **set verified by named members** | "the four hazards … These are ADR-009 D3" — D3 declares five; H2 was live and enforced |
| **search scoped narrower than the sentence** | "`stage9_status` is read by nothing" — true of `validation/checks/`, false of the repo |
| **the same mode, in a correction** (V8) | "neither name appears in any `.tex`" — true of the RAW identifier, false of the LaTeX-escaped `gapped\_interface\_axiom` that drafts actually write. 14 drafts, 25 hits |
| **the same mode, correcting THAT** (V8) | "two drafts assert a live axiom" — a sentence split on `.` truncated at `SPTClassification.lean`, before the *"since retired"* that followed. `axiom_count_prose_consistency` had the right answer all along |

---

## Per-document progress

| document | sections | V1–V7 | V8 (prose added 2026-08-07) | status |
|---|---|---|---|---|
| `README.md` | index · two rules · scope boundary | 8 atoms | 5 atoms, 0 corrected | ✅ **VERIFIED** |
| `SURFACE_INVENTORY.md` | header prose · derivation sources | 6 atoms, 1 corrected (B7) | regenerated, derived | ✅ **VERIFIED** |
| `VALIDATION_ARCHITECTURE.md` | §1–§6 | 22 atoms, 1 corrected | unchanged | ✅ **VERIFIED** |
| `CHECK_AUTHORING_GUIDE.md` | thesis · §1–§6 | 24 atoms, 1 corrected, 4 reframed | 4 atoms, 0 corrected | ✅ **VERIFIED** |
| `VALIDATION_GATE_TOPOLOGY.md` | §1–§7 | 27 atoms, 1 corrected | 5 atoms, 0 corrected | ✅ **VERIFIED** |
| `QA_QI_INFRASTRUCTURE_MAP.md` | §1–§6 | 31 atoms, 2 corrected | **18 atoms, 3 corrected** | ✅ **VERIFIED** |
| `END_TO_END_MAP.md` | §1–§9 | 34 atoms, 0 corrected | unchanged | ✅ **VERIFIED** |

`SURFACE_INVENTORY.md` is wholly generated, so V8 re-ran the generator and diffed rather than
re-reading prose; its only hand-authored sentence is the header, verified in V1–V7.

## Method, per atom

1. Restate the atom as a single falsifiable proposition.
2. Name the artifact that decides it (file + symbol, or a command).
3. Run the check; record the result verbatim.
4. If the atom is about a **set** (all/every/only/none), verify the set's **completeness**,
   not just that named members exist — that is how the D3 five-vs-four error survived.
5. If the atom cites an invariant/ADR/doc **by number or section**, verify the number resolves
   to that subject — not merely that the cited behaviour is real. That is how the #12 and #16
   errors survived.

---

## Corrections found by this pass

(Appended as found; each carries the atom that failed and the evidence.)


---

## V1 — `README.md` — VERIFIED (8 atoms)

| # | atom (single falsifiable proposition) | decided by | result |
|---:|---|---|---|
| 1a | No document here carries an as-of date stamp | grep for `(Written\|Status\|Date\|as of\|Measured\|re-based) YYYY-MM` across the directory | **0 hits** ✓ |
| 1b | No narrative here states a census count | `validate.py --check architecture_inventory_fresh` leg 2 | 6 narratives, 0 counts ✓ |
| 2 | `SURFACE_INVENTORY.md` is generated by `scripts/architecture_inventory.py` | its own header line 3 | states exactly that ✓ |
| 3 | It is gated by `validate.py --check architecture_inventory_fresh` | check registered in `validate._CHECKS` | `True` ✓ |
| 4 | **That check enforces exactly THREE things** — a SET claim | count the legs the check actually emits | **3** emitted: `inventory_fresh`, `no_counts_in_narratives`, `doc_refs_resolve` ✓ |
| 5a | `../adrs/` holds decision records | directory listing | 10 ADR files ✓ |
| 5b | `../KNOWLEDGE_GRAPH.md` holds the graph schema | count `### Node Types` / `### Edge Types` headings | 2 ✓ |
| 5c | `../WAVE_EXECUTION_PIPELINE.md` is the process law | count `## Stage N` headings | 14 ✓ |
| 6 | Each ownership-table row names a document that actually owns that question | per-row grep for the owning section | census 8 sections; gate semantics 1; QA_QI's four subsystems 1 each ✓ |
| 8 | `END_TO_END_MAP` and `QA_QI` do not restate each other's tables | count markdown table rows in each | `END_TO_END_MAP` has **zero** tables; `QA_QI` has two ✓ |

Atom 7 ("if a sentence would need editing because a number changed…") is a rule of thumb,
not a falsifiable proposition — recorded as **not an assertion**, deliberately, rather than
silently skipped.

⚠️ **Atom 4 is the one that matters methodologically.** It is a SET claim, and the previous
pass's failure mode was verifying named members without verifying completeness. Checked by
counting emitted legs, not by confirming three named legs exist.


---

## Corrections applied to the seven documents

The seven production documents state current fact only. Everything below was found false or
error-priming and **removed from them**; this table is the sole record.

### Round 1 — false claims replaced by the correct statement

| document | claim removed | what is true | evidence |
|---|---|---|---|
| `END_TO_END_MAP` §7, `QA_QI` §3 | bundle-level Stage-13 reports "reach no gate"; the publication-target review path "produces nothing the gates can see" | bundle-era reviews are the **largest** source of `ReviewFinding` nodes | `review_docs_mint_findings` passes over 135 docs, 0 mint zero; D12 203, D11 124, I2 69, I1 63, D2 61, D1 58, D4 54, L2 41 |
| `VALIDATION_GATE_TOPOLOGY` §5, `CHECK_AUTHORING_GUIDE` §5 | "Pipeline Invariant #16 cites the AI-Defense doc as canonical, under a filename that is also wrong" | Invariant #16 is the tracked-hypothesis registry; the pipeline law never cites that doc; the filename is correct. The real defect is that the doc declares its **own** `## Pipeline Invariant #16` at `:162` | `WAVE_EXECUTION_PIPELINE.md:695`; repo-wide grep for the doc's name |
| `VALIDATION_GATE_TOPOLOGY` §3 | "`--strict` is scoped to submission by Pipeline Invariant #12" | scoping is a property of `gate_precheck.py`; #12 mandates `--strict` for `provenance_doi_in_registry` only | `WAVE_EXECUTION_PIPELINE.md:685`; `gate_precheck.py` STAGES |
| `VALIDATION_ARCHITECTURE` §3 | "the four hazards … These are ADR-009 D3" | D3 declares **five**; H2 is live | `ADR-009:235`; `_ROSTER_CONSUMERS` at `bundles_readiness.py:815`; `EXPECTED_DYNAMIC` in `test_validate_public_surface.py` |
| `VALIDATION_ARCHITECTURE` §6 | the suite "does not recompute paper-quoted numbers" / "verify citation content" | both are done, per-artifact and partial | `check_paper_table_consistency`; `check_bibitem_title_primary_source` |
| `END_TO_END_MAP` §4 | `lean_zero_sorry` "hard-fails always" | no `--strict` leg, so the verdict is never softened; two cannot-measure branches return `passed=True, measured=False` | `lean_substrate.py` `check_lean_zero_sorry` |

### Round 2 — error-priming narrative removed (goal criterion 7)

Statements that were *true* but reproduced a false claim in order to negate it. A reader can
absorb the vivid claim and miss the correction, so the production documents no longer carry
any of it.

| document | removed |
|---|---|
| `END_TO_END_MAP` §7 | "An earlier revision of this map said bundle-level Stage-13 reports 'reach no gate' … That is false." |
| `QA_QI` §3 | "Do not repeat the claim that bundle-level Stage-13 reports reach no gate." |
| `QA_QI` header | "This file used to restate all three, and its copies went stale while reading as authoritative." |
| `QA_QI` §2 | "An earlier repair had widened the walk from `glob` to `rglob` — it went deeper and never went up." |
| `QA_QI` §3 | heading "narrow, but no longer single" → "narrow, and the live risk is a NEW form" |
| `CHECK_AUTHORING_GUIDE` §2.4 | "the sentence that used to sit here quoted the numbers … and then went stale" |
| `VALIDATION_GATE_TOPOLOGY` §3 | "An earlier revision of this section said …That is an overread" |
| `VALIDATION_GATE_TOPOLOGY` §4 | "a crashed gate **used to be** indistinguishable" → present-tense statement of why `blocked` is used |
| `VALIDATION_ARCHITECTURE` §3 | "An earlier revision was titled 'the four hazards' and silently omitted H2" |
| `VALIDATION_ARCHITECTURE` §6 | "An earlier revision of this section flatly said … Both were wrong" |

**Kept deliberately:** facts about the *system's* past that are load-bearing for reading its
present state — e.g. `gapped_interface_axiom` **was retired**, which is why citing it is a
defect. Those are not doc-history and do not prime a false belief about current behaviour.


---

## V2 — `SURFACE_INVENTORY.md` — BLOCKED on one atom

| # | atom | decided by | result |
|---:|---|---|---|
| 1 | Generated by `scripts/architecture_inventory.py` | `--write` entry point at `:410`, header emitted at `:289` | ✓ |
| 2 | **SET:** "Every table below is read from the artifact that owns the population" | AST walk of all seven derivation functions | ❌ **FALSE** — `registries()` iterates a hand-written `probes` list; and the four named sources are six in fact. Filed as **B7**; fix requires a generator edit, which this goal forbids |
| 3 | "Do not edit this file: run … `--write`" — the file is regenerable | ran `--write`, diffed | byte-identical, **idempotent** ✓ |
| 4 | **SET:** the eight `##` sections are each produced by a derivation function | 8 sections ↔ 7 functions (`agents_and_commands` yields two) | complete ✓ |
| 5 | "No timestamp is recorded here on purpose" | grep for `YYYY-MM-DD` in the file | 0 hits ✓ |
| 6 | The narrative companion is `END_TO_END_MAP.md` | link resolves; that file is the narrative | ✓ |

**Atom 2 — CORRECTED (B7).** The header conflated two different properties. It now reads:

> *"Each table's VALUES are read from the artifact that owns them … Their MEMBERSHIP is derived
> the same way, with one exception: the registries table lists a curated set named in the
> generator, because which collections count as tracked registries is an editorial call, not a
> mechanical property."*

Re-verified by AST over all seven derivation functions: **values** target the owning artifact
in all seven; **membership** is derived in six and curated in one (`registries()`'s `probes`
list). "One exception" is a counted claim.

The curation is correct and was deliberately NOT mechanised: `constants.py` holds 67
module-level uppercase collections and 60 are physics data (`A1_EXT_DIMENSIONS`,
`ADW_2D_MODEL`, lattice scans). Which collections count as tracked registries is editorial.
**The defect was the sentence, not the design.**

The fix is a one-string change to `scripts/architecture_inventory.py`, since the text is
emitted rather than stored — applied under explicit operator authorisation to correct code
that generates false statements.

---

## V3 — `VALIDATION_ARCHITECTURE.md` — VERIFIED (22 atoms, 1 correction)

| # | atom | decided by | result |
|---:|---|---|---|
| 1 | **SET:** `validate.py` registers ZERO checks | AST walk for `@register_check`-decorated `FunctionDef` | **none** ✓ (grep shows 5 hits — all comments; the AST is the decider) |
| 2 | Checks live in domain modules under `scripts/validation/checks/` | directory listing | 12 modules ✓ |
| 3 | **SET:** framework modules are `_registry`, `_config`, `_memo` | listing of `scripts/validation/_*.py` | those three + `_tex` + `__init__.py` (19 lines, **0 definitions** — a package marker) ✓ |
| 4 | `_tex` is the shared helper | same listing | ✓ |
| 5 | **SET:** `validate_helpers.py` is THE single path anchor | count anchors there; count check modules deriving their own root | 8 anchors; **0** modules derive their own ✓ |
| 6 | **SET:** the 12 modules named in the tree block == the 12 on disk | `diff` of extracted names vs `ls` | **sets identical** ✓ |
| 7 | ADR-009 D1 set the criterion "every module readable in one pass" | `ADR-009:150,165` | states exactly that ✓ |
| 8 | The modules deliberately share no line threshold | `wc -l` across the 12 | 404–1140, no threshold ✓ |
| 9 | **SET:** `CheckResult` fields are exactly `passed`,`details`,`error`,`measured` | `dataclasses.fields` | exact ✓ |
| 10 | `passed` is D2 contract item 5 | `ADR-009:622` | states it ✓ |
| 11 | **SET:** `passed` is read by the `--json` payload, `gate_precheck.py`, `pre-commit-sync.sh` | grep each consumer; read `run_check()`; read `main()`'s return | ❌ **CORRECTED** — `gate_precheck.py`'s only `passed` is in a **comment** (`:33`); it consumes `returncode` (`:87`). `pre-commit-sync.sh` consumes `rc`. Both are **exit-code** consumers; `validate.py:846` derives the code as `0 if all_passed else 1`. Only the `--json` payload reads the field |
| 12 | §Deferred item 4 declined `UNEVALUATED` | `ADR-009:956` | states it ✓ |
| 13 | **SET:** two consumers depend on `measured` | `validate.py:801-803` (`--ci` floor); `_memo.py:342` | exactly those two ✓ |
| 14 | `@register_check` appends to `_registry._CHECKS` | `_registry.py:123` | `_CHECKS.append(CheckSpec(...))` ✓ |
| 15 | `validate` re-exports the SAME list object | `validate._CHECKS is _registry._CHECKS` | `True` ✓ |
| 16 | `test_validate_public_surface.py` asserts that identity | `:167` | asserts it ✓ |
| 17 | `_CANONICAL_ORDER` declares order; `_apply_canonical_order()` sorts in place | `validate.py:168,205-216` | `_CHECKS.sort(key=…)` ✓ |
| 18 | **SET:** the regenerators live in `freshness.py` | AST: registered checks in that module containing `subprocess.run` | exactly `counts_fresh`, `tables_fresh`, `claim_clusters_fresh` ✓ |
| 19 | **SET:** ADR-009 D3 identifies five hazards, H1–H5 | `ADR-009:235` heading + the five `**HN —**` blocks | five ✓ (H2 restored to the table this pass) |
| 20 | Each hazard's named enforcing test exists and enforces it | read each test body | all five ✓ |
| 21 | **SET:** the memo is applied to exactly two checks | `_memo.unwrap(spec.func) is not spec.func` over the registry | `axiom_closure_allowlist`, `lean_docstring_refs_resolve` ✓ |
| 22 | §6's four coverage-gap statements | read each named check | ✓ (corrected in an earlier round; re-checked here) |

**NOT-AN-ASSERTION:** §5's *"Measure rather than quote"* and §3's *"They are not style rules"* —
guidance, no truth value.


---

## V4 — `CHECK_AUTHORING_GUIDE.md` — VERIFIED (24 atoms)

| # | atom | decided by | result |
|---:|---|---|---|
| 1 | **SET:** §2 contains exactly seven obligations | count `### 2.N` headings | **7** ✓ |
| 2 | **SET:** §3 routes every check module | names in the guide `comm`'d against `ls checks/` | every module routed ✓ |
| 3 | `test_cannot_measure_baseline.py` fails in BOTH directions | read its test names | `test_no_new_silent_pass` + `test_baseline_has_no_stale_entries` ✓ |
| 4 | `--ci` floor counts measurements; `_memo` refuses a non-measurement | `validate.py:801-803`; `_memo.py:342` | ✓ |
| 5 | §2.7's backlog is ratcheted at its live floor | read `test_d5_mutation_obligation.py` | `MUTATION_VERIFIED` 65 = every registered check; `AWAITING` 0; `AWAITING_CEILING` 0 ✓ |
| 6 | §4's commands are valid invocations | read them against the CLI | ✓ |
| 7 | `readiness_submission_gate` is fixed | `bundles_readiness.py` — returns `passed=False` on a blocked gate | ✓ |
| 8 | `paper_latex_compiles`' slow gate is deleted | AST read of the function body, docstring stripped | `SKIPPED (slow)` appears **only** in the docstring ✓ |
| 9 | The `--ci` floor counts `measured` | `validate.py:801-803` | ✓ |
| 10 | `_memo` refuses to cache a non-measurement | `_memo.py:342` `if not result.measured` | ✓ |
| 11 | `TestCheckKeysSpanTheirInputs` seeds through the real key | `tests/test_validation_memo.py:435` | seeds `__memo_key_fn__` ✓ |
| 12 | `test_ci_mode.py` no longer asserts the floor's own definition | grep for `CI_MIN_CHECKS_RUN == len(_CHECKS)` | **absent** ✓ |
| 13 | `check_bundle_source_freshness` reports UNMEASURABLE on an absent dir | `:169-170` | ✓ |
| 14 | `evaluate_all_gates` records `state='blocked'` on an exception | `readiness_gates.py:854` | ✓ |
| 15 | `_blocked_p1_gates_by_paper` returns `None`, not `{}` | AST: its return statements are `out` and `None` | ✓ |
| 16 | The dead-edge guard is scoped structurally | `graph_atlas.py:603` `{"source","target"} <= keys` | ✓ |
| 17 | `harness_lock` on contention is still OPEN | `harness_lock.py:103` `yield acquired` | ✓ |
| 18 | AI-Defense Tier 1 is still OPEN | `os.path.exists` on both named scripts | both absent ✓ |
| 19 | **SET:** exactly two rows are OPEN | count `🔴 **OPEN**` | **2** ✓ |
| 20 | `harness_lock`'s open row: callers treat a skip as a completed regen | `harness_lock.py:103` `yield acquired` + caller behaviour | ✓ |
| 21 | AI-Defense Tier 1's open row: neither named script exists | `os.path.exists` on both | both absent ✓ |
| 22 | **CORRECTED:** `passed` "read by the `--json` payload, `gate_precheck.py` and `pre-commit-sync.sh`" | grep each consumer; read `run_check()`; read `main()` | ❌ same error as `VALIDATION_ARCHITECTURE` atom 11, **propagated**. One direct reader; two exit-code consumers |
| 23 | ADR-009 §Deferred item 4 declined `UNEVALUATED` | `ADR-009:956` | ✓ |
| 24 | §6's checklist | 9 items | **NOT-AN-ASSERTION** — a checklist, no truth value |

### Reframed for criterion 7 — incidents that accused a currently-correct file

Four citations named a live artifact as *having* a defect it no longer has. Each now states the
**anti-pattern** without asserting the current state of a named file. The pedagogy the document
declares in its header ("the citation after each is the incident") is preserved; the
superseded accusation is not.

| § | named artifact | was asserted | now |
|---|---|---|---|
| 2.1 | `_memo` | "cached a `SKIPPED — lake not found` PASS and replayed it" | states the shape: a fail-open SKIP is a PASS |
| 2.3 | `test_ci_mode.py` | "asserted `CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)`" | states the self-sealing form, unattributed |
| 2.4 | "the memo's key tests" | "seeded the fingerprint helpers … returned `24 passed`" | states the failure mode of such a test |
| 2.5 | a guard | "found its name **in a comment** and passed" | states it in the present, as a property of substring scans |

⚠️ **Row 2 of the ledger table is a worked example of criterion 3.** A substring search for
`SKIPPED (slow)` in `papers_prose.py` returns a hit, which reads as "the slow gate is still
there". An AST read of the function shows the hit is inside the **docstring**; the executable
body carries no skip gate. The claim is `fixed`, and the substring would have said otherwise.


---

## V5 — `VALIDATION_GATE_TOPOLOGY.md` — VERIFIED (27 atoms, 1 correction)

| # | atom | decided by | result |
|---:|---|---|---|
| 1 | Tier 0 runs a leak/IP guard on the staged diff | `.git/hooks/pre-commit` | contains `IP guard` / `LEAK` ✓ |
| 2 | `pre-commit-notebooks.sh` fires only on staged `.ipynb` | its `STAGED_NBS` guard | ✓ |
| 3 | Tier 0 exits 0 in a worktree | `pre-commit-sync.sh:17-24` | worktree-detect → skip ✓ |
| 4 | Tier 0 tolerates missing `uv` | `:35` `command -v uv \|\| …` | ✓ |
| 5 | Tier 0 never blocks on a check crash | `run_check()` maps non-0/1 → `SKIP` | ✓ |
| 6 | Tier 0 hard-blocks on `main` only | 3 `[ "$BRANCH" = "main" ]` guards | ✓ |
| 7 | Tier 1 = `gate_precheck.py s9` · `s10` | `STAGES` dict `:44-46` | ✓ |
| 8 | Tier 2 `s13` = full suite **+ `--force-latex`** | `STAGES:47` + `:115` | passes `--force-latex` ✓ |
| 9 | Tier 2 `s13-lean` = same suite, exit scoped | `STAGES:64` `__substrate__` + `:117` `--scope substrate` | ✓ |
| 10 | Tier 3 `submission` passes `--strict` | `:120` | ✓ |
| 11 | No scheduled CI runner | no `.github/workflows/` | ✓ |
| 12 | `TestScopeSubstrate` asserts a substrate failure still blocks AND non-blocking failures are still reported | its two test names | both present ✓ |
| 13 | **SET:** `--ci` skips the mtime regenerators + `notebook_exec` | `_config.CI_SKIP` | exactly `counts_fresh`, `tables_fresh`, `claim_clusters_fresh`, `notebook_exec` ✓ |
| 14 | `--ci` enforces a coverage floor | `CI_MIN_CHECKS_RUN` present | ✓ |
| 15 | `--ci` never archives | `validate.py:790` `… and not args.ci` | ✓ |
| 16 | `--strict` implies `--no-memo` | `_memo.py:293` `bypass = (_cfg.NO_MEMO or _cfg.STRICT_MODE` | ✓ |
| 17 | `--strict` is passed only by the submission gate | grep `gate_precheck.py` | one call site ✓ |
| 18 | Invariant #12 governs `provenance_doi_in_registry`, not `--strict` globally | `WAVE_EXECUTION_PIPELINE.md:685` | ✓ |
| 19 | `CitationIntegrity` = registry coverage only | `_eval_citation_integrity` + its docstring | *"DOI fetch-and-verify is deferred to Stage 13"* ✓ |
| 20 | `CrossPaperConsistency` = `CONTRADICTS` + cross-paper `REPORTS` disagreement | `_eval_cross_paper_consistency` | both legs present ✓ |
| 21 | `ParameterProvenance` = every `DEPENDS_ON → param:*` has `human_verified_date` | its docstring + body | ✓ |
| 22 | `ComputationCorrectness` requires a non-`{bounds,unknown}` VERIFIES edge | AST: the exact literals in the body | `bounds`, `unknown` — exactly the two ✓ |
| 23 | `LeanProofSubstance` = cited theorems ∌ `PlaceholderMarker` | its body; two citation sources | ✓ |
| 24 | `AssumptionDisclosure` matches a **lowercased** substring of the tex | `'lower()' in source` | `True` ✓ |
| 25 | `NarrativeGrounding` = every `interesting` ProseClaim has ≥1 `SUPPORTS` | its body | ✓ |
| 26 | `ProductionRunHealth` = PRODUCES-linked runs + an MC prose regex | its body | both legs ✓ |
| 27 | `NumericalFreshness` can only ever emit `needs-recheck`/`passed` | regex over its assigned states | exactly those two ✓ |
| 28 | `FirstClaimVerification` likewise, and its ledger node type does not exist | assigned states; node-type set | ✓ |
| 29 | `FixPropagation` self-promotes to P1 when blocking | its severity branch | ✓ |
| 30 | **SET:** exactly the three named edge types have no emitter | `gate_edge_types_are_emitted` | `CONTRADICTS`, `PRODUCES`, `SUPPORTS` ✓ |
| 31 | `READINESS_GATES.md` documents the P2 gates as blocking; they cannot | its `**Blocks on any:**` sections vs the evaluators' assigned states | doc has the section; evaluators emit only `needs-recheck`/`passed` ✓ |
| 32 | An evaluator that raises records `state='blocked'` | `readiness_gates.py:854` | ✓ |
| 33 | **SET:** the web-egress guard is the ONE fail-closed hook | inspect every hook's command in `hooks.json` | 1 of 5 is fail-closed ✓ |
| 34 | AI-Defense Tier-1's two named scripts are absent | `os.path.exists` | both absent ✓ |
| 35 | **CORRECTED:** "`stage9_status` / `stage10_status` are read by nothing" | grep across `scripts/ src/ tests/` | ❌ **FALSE** — `bundle_append.py:322-325` reads both and demotes a `green` to `pending`. What is true: **no gate or check** reads them (0 files under `validation/checks/`, `readiness_gates.py`, `gate_precheck.py`) |
| 36 | Nothing writes a `stage*_status` to `green` | grep every assignment | 4 writes, all `"pending"` ✓ |
| 37 | **SET:** §6's six field-ownership rows | `write_metadata_counts` body; `check_bundle_source_freshness`; `apex_theorems` writers | all six ✓ (`apex_theorems`: no script writes it) |
| 38 | §7's two expensive checks are the memoized/cached pair | `_memo.unwrap` over the registry | ✓ |

**NOT-AN-ASSERTION:** §2's framing question, and §7's *"Measure rather than quote"* — guidance.

⚠️ **Atom 35 is a scope-of-search failure, not a reading failure.** An earlier check searched
only `validation/checks/` and `gate_precheck.py`, found nothing, and the claim was written as
"read by nothing". Widening to `scripts/ src/ tests/` found the real reader immediately. The
narrow search was *true* about its own scope and false as stated.


---

## V6 — `QA_QI_INFRASTRUCTURE_MAP.md` — VERIFIED (31 atoms, 2 corrections)

| # | atom | decided by | result |
|---:|---|---|---|
| 1–7 | §1's mermaid names real artifacts | `find` each | all 7 resolve ✓ |
| 8 | The three reviewer agents exist | plugin `agents/` | all 3 ✓ |
| 9 | `lean_deps.json` — writer `extract_lean_deps.py`, key = content hash incl. the root aggregate | `compute_lean_hash` body | hashes the subtree **and** `lean/SKEFTHawking.lean` ✓ |
| 10 | `counts.json`/`.tex` — writer `update_counts.py`, key = **mtime** | `_counts_is_stale` | compares `st_mtime` against sources ✓ |
| 11 | `papers/*/tables/*.tex` — writer `render_paper_tables.py`, key = **mtime** | `_tables_is_stale` | `st_mtime` comparison ✓ |
| 12 | Inventory-Index blocks — writer `update_inventory_index.py`, key = **content compare** | `compute_stale` | `existing_inner != inner` ✓ |
| 13 | `atlas_view.json` — key = content compare | `_atlas_view_stale` | rebuilds and compares ✓ |
| 14 | `ATLAS_HEATMAP.md` — key = content compare | `_atlas_heatmap_stale` | `fresh != p.read_text()` ✓ |
| 15 | `KernelNoGos.lean` — key = content compare | `_kernel_nogos_module_stale` | ✓ |
| 16 | `SURFACE_INVENTORY.md` — content compare, gated, **not** auto-written | `architecture_inventory_fresh` | deliberately non-regenerating ✓ |
| 17 | `claim_clusters.json` — writer `cluster_detect.py`, via check only | the check | ✓ |
| 18 | `PERMANENT_TRACKED_HYPOTHESES.md` — content compare, hard-fail, never auto-written | `render_tracked_hypotheses.py` | ✓ |
| 19 | `cluster_bundle_index.json` — **no** staleness key | `bundle_clusters.py`; absent from `sync_manifest.EDGES` | ✓ |
| 20 | `BUNDLE_READINESS_HEATMAP.md` — **no** key | `bundle_readiness.py`; absent from EDGES | ✓ |
| 21 | `QI_REGISTER.md` — **no** key; re-parses its own Closed Items | `qi_register.py` | ✓ |
| 22 | PG+AGE `sk_eft` — **no** key, full delete + rewrite, opt-in | `write_graph_to_pg`; `sync_pg=False` default | ✓ |
| 23 | `figures/provenance_graph.json` — **no** key | `build_graph --out` | ✓ |
| 24 | `harness_lock.regen_lock` is skip-and-use-cache, bounded poll, fail-open | `harness_lock.py:103-126` | ✓ |
| 25 | **CORRECTED:** the build cost claim | 8 call sites; `extract_readiness_gate_nodes` body; cache decorators | the pre-gate view re-runs the node extractors **except its own** (recursion break), and `build_graph_json` is uncached — but two internal indices ARE `lru_cache`d and the dashboard holds its own cache. Original wording implied nothing anywhere is cached |
| 26 | `ReviewFinding.status` is `'open'` at birth, unconditionally | `build_graph.py:1867` | `status = 'open'` ✓ |
| 27 | The supersession ledger overrides that status | `:1918` | override validated against `_KNOWN_STATUSES`, else `'open'` ✓ |
| 28 | Drop 1 — a finding with neither `inferred_paper` nor `inferred_bundle` | `bundle_readiness.py:129` `m.get("inferred_paper") or m.get("inferred_bundle")` | ✓ |
| 29 | Drop 2 — `_emit` is a silent no-op on an absent FLAGS target | `build_graph.py:3711` `if target_id not in node_ids: return` | no log ✓ |
| 30 | Drop 3 — ambiguous paper-key prefix, info-level log, edges skipped | `:3742` `logger.info(...)` then `paper_id = None` | ✓ |
| 31 | Drop 4 — `AutomatedReviews/*/*.md` is a one-level glob | `:1746` `reviews_dir.glob("*/*.md")` | ✓ |
| 32 | Drop 5 — a heading outside `_REVIEW_SECTION_RE` mints nothing | the regex; `review_docs_mint_findings` as the post-hoc guard | ✓ |
| 33 | **SET:** `FixPropagation` is the only evaluator reading FLAGS | scan every evaluator's source | exactly one ✓ |
| 34 | `_REVIEW_SECTION_RE` accepts the listed heading forms | `build_graph.py:1574-1580` | ✓ |
| 35 | Bundle-level Stage-13 reports reach the gates | `review_docs_mint_findings`; per-bundle `ReviewFinding` attribution | passes over 135 docs; bundle-era reviews are the largest source ✓ |
| 36 | The VERIFIES resolver's two gating rules | `build_graph.py:3882` | "resolve only as a full Lean name, never by its tail" ✓ |
| 37 | The gate named as the victim reads `formula:` targets only | `inspect.getsource(_eval_computation_correctness)` | mentions `formula:`, never `lean:` ✓ |
| 38 | The real consumer was `last_modified.py`'s VERIFIES propagation | `last_modified.py:55` | `'VERIFIES'` in its edge set ✓ |
| 39 | Arm a `/goal` loop — structural | `disable-model-invocation` in `skills/goal-prompt/SKILL.md` | ✓ |
| 40 | Promote System-2 → `human-reviewed` — structural via `_clamp_tier` | `system2_register.py:55,229,279` | caps every other writer ✓ |
| 41 | Close/misfile a System-2 finding — `## Misfiled` reachable only from `/debrief` | `system2_register.py` + `skills/debrief/SKILL.md` | ✓ |
| 42 | Integrate a process win — per-win sign-off | `skills/debrief/SKILL.md` | ✓ |
| 43 | Graduate a finding → pre-decision — structural | `/debrief` → `PRE_DECISIONS.md` | ✓ |
| 44 | Sign off a structural-prevention proposal — never auto-applied | `skills/debrief/SKILL.md` | ✓ |
| 45 | Close a QI item — Invariant **#13** preserves Closed Items | `WAVE_EXECUTION_PIPELINE.md:687` | subject matches ✓ |
| 46 | Approve a new axiom — Invariant **#15** + `AXIOM_METADATA` | `:691` | subject matches ✓ |
| 47 | Toggle the AskUserQuestion guard — structural | `commands/goal-guard.md` | `disable-model-invocation` ✓ |
| 48 | Verify a parameter — Invariant **#8** | `:671` | subject is parameter provenance ✓ |
| 49 | Declare apex theorems — ADR-010 **§D5a**, per-bundle review | `ADR-010:394`; no script writes `apex_theorems` | ✓ |
| 50 | `chain_canonicalize.py --report` exists and is read-only | its CLI | ✓ |
| 51 | **CORRECTED:** "the instrument ranks per-bundle severity and surfaces bundles with no chain-of-backing" | ran `--report`; read the full CLI | ❌ **FALSE** — it emits a breakdown by **resolution class** only. The single other flag is `--paper <dir>`, which *limits* a run. No per-bundle ranking exists |
| 52 | A discharged axiom is still cited | `gapped_interface_axiom` in `claims_review.json`; `counts.json` axioms | cited; axiom count **0** ✓ |
| 53 | A FALSE theorem is still cited, with an I1 waiver | `TetradGapEquation.lean:314` note; `papers/I1/claims_review.json` | note present; I1's record documents it as history ✓ |
| 54 | **SET:** nothing gates on the chain instrument | grep `validation/checks/`, `readiness_gates.py`, `gate_precheck.py` | **0** references ✓ |
| 55 | **SET:** the Codex control plane has zero references to the five named modules | grep `scripts/lean_slots/`, `.codex/` | 0 for all five ✓ |

**NOT-AN-ASSERTION:** §1's *"well-designed in its architecture and substantially broken in its
wiring"*, and §6's *"re-measure the scope before fixing"* — thesis and guidance.

⚠️ **Atom 51 is the third inherited claim to fail in this pass.** It came from a 2026-08-03
hand measurement that reported per-bundle numbers, and was rewritten as a capability of the
instrument. The instrument never had it. Verifying the *numbers* would not have caught this —
only running the tool and reading its CLI did.


---

## V7 — `END_TO_END_MAP.md` — VERIFIED (34 atoms, 0 corrections)

Graph claims re-derived against a **fresh** `build_graph_json()`, not the cached JSON from
earlier in the session.

| # | atom | decided by | result |
|---:|---|---|---|
| 1 | **SET:** no check module references `docs/roadmaps/` | grep `validation/checks/` | **0** ✓ |
| 2 | **SET:** no `*_close.md` exists under `docs/roadmaps/` | glob | **0** ✓ |
| 3 | `notebook_lib.py` wraps the roadmap read in `except Exception: return None` | `:201-205` | ✓ |
| 4 | The graph schema lives in `KNOWLEDGE_GRAPH.md`, with a delta and a roadmap table outside `docs/architecture/` | all three paths | ✓ |
| 5 | **SET:** every hook fails open except the egress guard | every hook command in `hooks.json` | 1 of 5 fail-closed ✓ |
| 6 | The cached plugin builds differ from the repo copy; no drift detector | `diff` all three caches; grep for a detector | 79-line diffs; none contains `_PATH_WHITELIST` ✓ |
| 7 | **SET:** `_read_active_issues` has zero callers | grep repo-wide | all hits are the same `def` across worktree copies ✓ |
| 8 | `PRE_DECISIONS.md` names `/skeft-qa:trace`, which does not exist | the doc; `commands/` listing | named; 6 commands, `trace` absent ✓ |
| 9 | `lean_zero_sorry` never softens the verdict | its source — no `_cfg.STRICT` reference | ✓ |
| 10 | It reads `docs/counts.json`, returning `measured=False` when absent/unparseable | two early-return branches | ✓ |
| 11 | Tier 0 catches `sorry` independently, via a quote-agnostic regex | `pre-commit-sync.sh:72` `declaration uses .?sorry.?` | ✓ |
| 12 | ADR-006 states the gauntlet is the safety mechanism for the toolchain divergence | `ADR-006:85` verbatim | ✓ |
| 13 | `zero_sorry` is inert — fixed-string quote style the toolchain does not emit | `aristotle_submit.py`; measured Lean output | ✓ |
| 14 | `kernel_pure` is computed over target decls only | `aristotle_submit.py:719-721` | ✓ |
| 15 | The gauntlet regenerates `lean_deps.json` before judging | its step 2 | calls `load_lean_deps()` ✓ |
| 16 | **SET:** nothing compares `PLACEHOLDER_TOTAL_COUNT` to `counts.json` | grep every consumer | none compares ✓ |
| 17 | **SET:** `last_modified` is one value across the whole graph | fresh build | **1** distinct: the epoch ✓ |
| 18 | `docs/verification_log.jsonl` does not exist | filesystem | absent ✓ |
| 19 | `Phase5v_Roadmap.md` calls the freshness layer "the highest-value capability" | `:823` verbatim | ✓ |
| 20 | **SET:** `PRODUCES`/`SUPPORTS`/`CONTRADICTS` are emitted nowhere | fresh build's edge-type set | none present ✓ |
| 21 | `PRODUCES` was deferred to Wave 4 | `Phase5v_Roadmap.md:220` | *"PRODUCES edges deferred to Wave 4 where run-to-claim mapping is curated"* ✓ |
| 22 | **SET:** the string appears nowhere from the Wave-4 close onward | close heading located at `:363`; all `PRODUCES` at 94/220/311 | all **before** the close ✓ |
| 23 | The PG mirror is schema-complete and data-empty | live AGE query | **48** labels, **1** vertex ✓ |
| 24 | `provenance_dashboard.py` honours `SK_EFT_GRAPH_SOURCE=pg` | `:152` | ✓ |
| 25 | **SET:** `BACKED_BY.link_state` produces two of five declared states | fresh build | `resolved`, `missing_target` only ✓ |
| 26 | **SET:** `Sentence.verification` is never derived | fresh build | every value `None` ✓ |
| 27 | `sentence_state.py` is the declared sole writer of AuditEvent records | `KNOWLEDGE_GRAPH.md:197`; the script's own header | *"written EXCLUSIVELY via"* ✓ |
| 28 | The skipped records carry neither `target_id` nor `actor` | scan all `audit_log.jsonl` | 1 of 239 has the writer's shape ✓ |
| 29 | **SET:** nothing validates either genre | grep `validation/checks/` for `audit_log` | **0** ✓ |
| 30 | `ProductionRun` nodes have no outgoing edges | fresh build | **0 of 18** ✓ |
| 31 | Stage 14 derives zero QI items | `qi_register.py --stats` | `findings_total` 1561, `qi_items_detected` **0** ✓ |
| 32 | The dashboard prints the working route for Invariant #8 | `provenance_dashboard.py:5488` | names `wave2_flip_provenance.py` ✓ |
| 33 | **SET:** §9's five process-law drift items | one measurement each | *12 stages* vs **14** headings · *Checks (16 total)* · *18 targets* enum vs **21** live incl. D10–D12 · *we run 4.29.1* vs **v4.32.0** · *no per-repo CLAUDE.md* vs one that **exists** — all five ✓ |
| 34 | `bundle_registry_consistency` Leg C forbids re-hardcoded rosters | the check's Leg C | ✓ |

**NOT-AN-ASSERTION:** §1's *"the two ends are the weak ones"* and the §6 lesson *"a gate that
fires is not a gate that measures what it claims to"* — thesis and lesson.

**Zero corrections.** This is the only document of the seven to survive assertion-granularity
verification unchanged — because it was rewritten from measurement after the earlier passes,
and every claim it inherited had already been re-derived or removed.

---

## V8 — assertions added 2026-08-07 (post-V1–V7) — VERIFIED (34 atoms, 3 corrected)

**Why a second pass exists.** V1–V7 verified the documents as they stood at commit
`eb11fe97`. The A1/A2/B2–B6 remediation then wrote **new prose** into four of them, and a
sentence written after a verification pass is unverified by definition. These are those
sentences, at the same granularity.

⚠️ **Three of the atoms below were FALSE, and all three were written by the remediation pass
itself — one of them inside a paragraph correcting an earlier error.** The failure mode was
the one V1–V7 catalogued: *a search scoped narrower than the sentence*. Recording it here
rather than treating the second pass as more trustworthy than the first.

### `QA_QI_INFRASTRUCTURE_MAP.md` §2 — concurrency

| # | atom | decided by | result |
|---|---|---|---|
| Q1 | `regen_lock` is a bounded poll, then skip — never block-and-wait | `harness_lock.py` `WAIT_SECONDS=5.0`, `POLL_SECONDS=0.25`, yields `False` on timeout | ✓ |
| Q2a | `load_lean_deps()`'s skip path logs at **WARNING**, not INFO | `extract_lean_deps._run_extraction`, read directly | `logger.warning(...)` ✓ |
| Q2b | **SET:** the named blast radius (counts, atlas, graph, axiom closure) are all real consumers of `lean_deps.json` | each traced to a reader | `update_counts.py`, `atlas_view.json` builder, `build_graph.py`, `axiom_closure_allowlist` ✓ |
| Q3 | `sync.py` records skipped artifacts and prints `sync INCOMPLETE` naming them | `sync.py` `skipped` list + summary branch | ✓ |
| Q4 | Its exit code stays **0** on skip | same branch: `return 0` | ✓ |
| Q5 | On internal error the lock fails **open**, yielding `True` | `harness_lock` module docstring **and** the `except` path | both agree ✓ |
| Q6 | **SET:** the auto-regenerating freshness checks shell out with **no lock at all** | `freshness.py` regenerator sites vs `regen_lock` call sites | 0 of the shell-outs take the lock ✓ |

### `QA_QI_INFRASTRUCTURE_MAP.md` §5 — chain of backing

| # | atom | decided by | result |
|---|---|---|---|
| Q7 | `gap_solution_bounded` is inside a `/- … -/` comment, not a declaration | `TetradGapEquation.lean` 311–325; absent from `lean_deps.json` | ✓ both |
| Q8 | It carries the note *"This theorem is FALSE as originally stated"* | line 314, verbatim | ✓ |
| Q9 | ~~I1's citation is a **documented waiver**~~ | I1 `claims_review.json`: waiver field? `link_state`? | ❌ **FALSE** — no waiver field, no `link_state`, no waiver record anywhere. I1's two mentions are narrative history. **Inherited claim, never derived.** Statement replaced |
| Q10 | ~~Neither name appears in any `.tex` under `papers/`~~ | raw-identifier scan → **escaped**-form scan | ❌ **FALSE** — the raw scan was a PROXY. LaTeX escapes to `gapped\_interface\_axiom`: **14 drafts / 25 hits**; `gap\_solution\_bounded`: I1 / 3 hits. Statement replaced |
| Q11 | ~~Every prose mention reports it as disproved~~ | all 4 prose mentions read | ❌ **FALSE as a set claim** — 3 of 4 carry a negative marker; I1's first is narrative setup. Statement replaced |
| Q12 | Most manuscript mentions state the conversion accurately | the 25 sentences, read | D2/D4/D5/F/L2/paper8/paper21 all say *"formerly … converted to a tracked `Prop` on 2026-05-19"* ✓ |
| Q13 | ~~`paper18` and `paper20` assert a **live** axiom count of 1~~ | first: a regex sentence-split; then: `validate.py --check axiom_count_prose_consistency` | ❌ **FALSE** — both carry *"since retired into the tracked Prop `TPFConjecture`"*. The split broke on the `.` in `SPTClassification.lean` and truncated before the qualifier. The check scans all 64 drafts and reports **0 stale claims**. Statement replaced |
| Q19 | **SET:** all 25 manuscript mentions carry a historical qualifier | `axiom_count_prose_consistency` over 64 drafts | 0 stale, 0 advisory ✓ |
| Q20 | I1's line citations for `TetradGapEquation.lean` are accurate | block bounds computed from the file | ❌ **FALSE** — I1 cites 307–321 for the stub (actual **311–325**) and 329–345 for the live theorem (`gap_solution_monotone` at **333**). A consistent **4-line** offset: the file grew above that point. Filed as **D3** |
| Q14 | `chain_backing_targets_resolve` fails on a link resolving against no population | the check, run | 156 / ceiling 156 → PASS; +1 seeded → FAIL ✓ |
| Q15 | It is a ratchet reported by paper each run and can only shrink | check body + its zero-headroom test | ✓ |
| Q16 | A declaration-names-only resolver reports **more than 3×** the true figure | both resolvers run over the same corpus | 515 vs 156 = **3.30×** ✓ |
| Q17 | **SET:** the difference is modules, short names, core axioms, notation variants | categorised counts | module 247 + short 785 + core + variants 89; residue 156 ✓ |
| Q18 | The rest of `--report`'s output gates on nothing | `chain_canonicalize.py` has no `@register_check`; no check imports it | ✓ |

### `CHECK_AUTHORING_GUIDE.md` — ledger rows

| # | atom | decided by | result |
|---|---|---|---|
| C1 | `harness_lock` row's "fixed" claim | same evidence as Q3/Q2a | ✓ |
| C2 | AI-Defense row: neither named script was written | `ls scripts/pre_commit_hook.sh scripts/install_pre_commit.sh` | both ABSENT ✓ |
| C3 | `@[csimp]` is the one uncovered soundness item | `csimp` across `scripts/` + `tests/` | **0 occurrences** ✓ |
| C4 | The lock "was always correct" — the defect was in its callers | lock yields the right signal; callers discarded it | ✓ |

### `VALIDATION_GATE_TOPOLOGY.md`

| # | atom | decided by | result |
|---|---|---|---|
| G1 | `NumericalFreshness`/`FirstClaimVerification` reach only `passed`/`needs-recheck` | AST of both evaluators' `r.state` assignments | `blocked` absent from both ✓ |
| G2 | `readiness_submission_gate` counts only P1-not-passed and P2-`blocked` | its body: `blockers = s['p1_blocked'] + s['p2_blocked']` | ✓ |
| G3 | The `READINESS_GATES` policy is stricter than the mechanism | GREEN requires all-passed; the check tolerates P2 advisories | ✓ |
| G4 | AI-Defense's substance shipped under other names | each mapped to a live check | `axiom_closure_allowlist` verbatim; `prose_theorem_reference_coverage`; `paper_latex_compiles` ✓ |
| G5 | Invariant numbers #15/#16/#17 are axiom sign-off / tracked-hypothesis / kernel no-go | `WAVE_EXECUTION_PIPELINE.md`, each number read | ✓ — cited **by number**, per method rule 5 |

### `README.md`

| # | atom | decided by | result |
|---|---|---|---|
| R1 | `tests/test_architecture_claims.py` exists and pins load-bearing claims | file present; 10 tests collected | ✓ |
| R2 | Each assertion binds sentence **and** code fact | every test calls `_claim(...)` plus a code assertion | 10 of 10 ✓ |
| R3 | Rewording a claim fails its test | seeded `five`→`four` in `VALIDATION_ARCHITECTURE.md` | FAILED as intended, reverted ✓ |
| R4 | Changing the code fails its test | seeded `.measured`→`.passed` in `_memo.py` | FAILED as intended, reverted ✓ |
| R5 | Coverage there is partial, by design | 10 assertions vs the documents' full assertion count | partial — stated as such ✓ |

### NOT-AN-ASSERTION (recorded, not skipped)

| statement | why it has no truth value |
|---|---|
| *"If any part of this document is built, build this"* (QA_QI, on `@[csimp]`) | a recommendation |
| *"Resolve against every population a target may name, and normalize first"* | an instruction to a future author |
| *"choosing which is the work"* (README, on claim coverage) | editorial judgement |
| *"A specification and a description are not interchangeable"* | a general principle, not a claim about this repo |
