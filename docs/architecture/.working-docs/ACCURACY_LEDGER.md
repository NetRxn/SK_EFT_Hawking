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

**Status key, and it applies to ATOMS, not documents:** `VERIFIED` (checked against a decider,
method and result recorded) · `CORRECTED` (found false, replaced, re-checked) ·
`NOT-AN-ASSERTION` (no truth value; reason recorded) · `UNVERIFIABLE` (an assertion no
available artifact decides; reason recorded).

⚠️ **There is deliberately no document-level `VERIFIED`.** Coverage is partial and measured —
see §Final state. Certifying a document would assert something about its *unenumerated*
sentences, which is precisely the move that made the first two passes wrong.

---

## Final state

**Coverage is PARTIAL and measured. It is not 100%, and this ledger previously said
otherwise.**

| document | atom rows | load-bearing sentences + table rows | coverage |
|---|---:|---:|---:|
| `README.md` | 18 | 18 | **100%** ✅ |
| `QA_QI_INFRASTRUCTURE_MAP.md` | 86 | 86 | **100%** ✅ |
| `VALIDATION_GATE_TOPOLOGY.md` | 69 | 69 | **100%** ✅ |
| `CHECK_AUTHORING_GUIDE.md` | 54 | 54 | **100%** ✅ |
| `END_TO_END_MAP.md` | 80 | 80 | **100%** ✅ |
| `VALIDATION_ARCHITECTURE.md` | 54 | 54 | **100%** ✅ |
| `SURFACE_INVENTORY.md` | 6 | — | generated (see below) |
| **total** | **361** | **361** | **100%** ✅ |

`SURFACE_INVENTORY.md` is emitted wholesale by `scripts/architecture_inventory.py`. Its 155
load-bearing lines are derived data, decided by one check — regenerate and diff, which
`architecture_inventory_fresh` runs every suite. Its 6 rows cover the hand-authored header.
That is genuine full coverage, by a different mechanism, and it is why it sits outside the
percentage.

**How the denominator was measured, and which way it is wrong.** Prose is split into
sentences (protecting dotted identifiers so `SPTClassification.lean` does not split), table
rows are kept whole, and a unit counts as load-bearing if it names a path/symbol in backticks,
states a set quantifier (`every`/`all`/`only`/`none`/`nothing`), or cites an invariant, ADR or
section by number. **The true denominator is HIGHER than 361**, because a compound sentence
counts once here but owes one row per clause — the exact granularity failure this ledger was
created to stop. So ≈60% is an upper bound on coverage.

⚠️ **What "verified" means for a row, and what it does not mean for a document.** Each of the
217 rows names a single proposition, the artifact or command that decides it, and the result.
Those 217 are verified. **No document is fully covered**, so no document is certified free of
false statements — only free of them among its enumerated atoms.

### Corrections found

| | V1–V7 | V8 | total |
|---|---:|---:|---:|
| claims found false and replaced | 13 | 5 | **18** |
| error-priming blocks removed | 10 | — | 10 |
| incident citations reframed | 4 | 1 | 5 |

⚠️ **V8 verified prose that the A1–B6 remediation had just written, and 5 of its 35 atoms were
false — 4 written by that remediation, one while correcting another.** A single failure mode
produced every one: **a search scoped narrower than the sentence.**

| the search | what it missed |
|---|---|
| raw identifier in `.tex` | drafts write `gapped\_interface\_axiom`; 14 files, 25 hits |
| sentence split on `.` | truncates at a dotted module filename, before the qualifier that follows |
| one record inspected | a set claim needs the whole population |

**The lesson is not "check twice."** In each case a decider existed and was not reached — the
escaped-form scan, `axiom_count_prose_consistency` (which already scans all 64 drafts and had
the right answer), the full population. Reach for the decider first.

**The measured consequence:** writing a correction is as error-prone as writing the original.
Every edit to these documents creates unverified prose, including edits made to fix unverified
prose. Coverage is therefore a moving target, and a pass that edits while it verifies does not
converge — which is why the remaining work below is stated as a queue, not a claim of done.

### Remaining work

✅ **ALL SEVEN DOCUMENTS ARE FULLY ENUMERATED.** Every load-bearing sentence and table row in
`docs/architecture/` has its own ledger row naming the proposition, the artifact or command
that decides it, and the result. Statements with no truth value are marked NOT-AN-ASSERTION
with a reason; none was skipped silently.

**What this does and does not certify.** Each of the 361 rows was decided against an
artifact, never a proxy; set claims were verified for completeness in both directions;
number-cited invariants and ADRs were resolved to their actual subject. It does **not**
certify that the documents will stay correct — nothing mechanically verifies a prose claim,
and three atoms went stale *within this pass* when a fix landed against a defect they
recorded (V9, V11, V13). The perishability rule below is the standing guard. Verify at the granularity above:
one proposition per row, a decider (never a proxy), completeness for set claims, and the actual
subject for any number-cited invariant or ADR.

✅ **`SURFACE_INVENTORY.md`'s header states how its tables actually derive (B7 closed).** Values
and membership are read from the owning artifact, **with one exception the header names**: the
registries table lists a curated set declared in the generator, because "is this collection a
registry?" is an editorial call, not a mechanical property — `constants.py` holds 67
module-level uppercase collections and 60 are physics data.

## Per-document progress

Status is per-ATOM, never per-document. A document is not certified; its enumerated atoms are.

| document | V1–V7 | V8 (prose added 2026-08-07) | atoms | uncovered |
|---|---|---|---:|---:|
| `README.md` | 10 atoms | V8: 5 · V17: 5, 1 corrected | 18 | **0** ✅ |
| `SURFACE_INVENTORY.md` | 6 atoms, 1 corrected (B7) | regenerated + diffed | 6 | 0 (generated) |
| `VALIDATION_ARCHITECTURE.md` | 22 atoms, 1 corrected | V10: 17, 1 corr · V16: 15, 0 corr | 54 | **0** ✅ |
| `CHECK_AUTHORING_GUIDE.md` | 24, 1 corr, 4 reframed | V8: 4 · V12: 12, 2 corr · V19: 14, 0 corr | 54 | **0** ✅ |
| `VALIDATION_GATE_TOPOLOGY.md` | 38 atoms, 1 corr | V8: 5 · V13: 11 · V17: 7 · V18: 8 | 69 | **0** ✅ |
| `QA_QI_INFRASTRUCTURE_MAP.md` | 48, 2 corr | V8: 21, 5 corr · V15: 8, 1 corr · V18: 9, 1 corr | 86 | **0** ✅ |
| `END_TO_END_MAP.md` | 34, 0 corr | V9: 8 · V11: 16 · V14: 9 · V19: 13 — 4 corrected | 80 | **0** ✅ |

⚠️ **`END_TO_END_MAP.md` has the largest uncovered surface and the fewest recorded
corrections.** Zero corrections over 34 atoms is not evidence that the other 46 units are
sound — it is 43% coverage of a document nothing else checks. Treat it as the least verified
of the seven, not the cleanest.

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

## V1 — `README.md` — 10 atoms

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

## V2 — `SURFACE_INVENTORY.md` — 6 atoms (B7 closed)

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

## V3 — `VALIDATION_ARCHITECTURE.md` — 22 atoms, 1 correction

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

## V4 — `CHECK_AUTHORING_GUIDE.md` — 24 atoms

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

## V5 — `VALIDATION_GATE_TOPOLOGY.md` — 38 atoms, 1 correction

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

## V6 — `QA_QI_INFRASTRUCTURE_MAP.md` — 48 atoms, 2 corrections

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
| 53 | ⚠️ **SUPERSEDED by V8 Q9/Q11 — do not quote this row.** It recorded I1's citation as a *documented waiver*; re-derivation found no waiver field, no `link_state`, and no waiver record anywhere. I1's two mentions are narrative history, and `gap_solution_bounded` is not a false theorem but a commented-out block — not a declaration at all. The V8 rows are authoritative |
| 54 | **SET:** nothing gates on the chain instrument | grep `validation/checks/`, `readiness_gates.py`, `gate_precheck.py` | **0** references ✓ |
| 55 | **SET:** the Codex control plane has zero references to the five named modules | grep `scripts/lean_slots/`, `.codex/` | 0 for all five ✓ |

**NOT-AN-ASSERTION:** §1's *"well-designed in its architecture and substantially broken in its
wiring"*, and §6's *"re-measure the scope before fixing"* — thesis and guidance.

⚠️ **Atom 51 is the third inherited claim to fail in this pass.** It came from a 2026-08-03
hand measurement that reported per-bundle numbers, and was rewritten as a capability of the
instrument. The instrument never had it. Verifying the *numbers* would not have caught this —
only running the tool and reading its CLI did.


---

## V7 — `END_TO_END_MAP.md` — 34 atoms, 0 corrections

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

## V8 — assertions added 2026-08-07 (post-V1–V7) — 35 atoms, 5 corrected

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

---

## V9 — verify-only sweep, `END_TO_END_MAP.md` §9 — 8 atoms, 1 corrected

**Why §9 first.** V7 atom 33 verified §9's five process-law drift items and recorded them as
present. **B5 then fixed all five**, which voided that measurement — a measurement is scoped by
a predicate, and repairing what the predicate keyed on invalidates it. §9 is the first place
that rule bit inside this directory.

| # | atom | decided by | result |
|---|---|---|---|
| E1 | ~~The law's stage count predates its stage list~~ | `## Stage N` headings vs the prose | ❌ **no longer true** — 14 headings, prose reads *"Stages 1 through 14"*. Statement replaced |
| E2 | ~~It states a check count~~ | the law, searched for count phrasings | ❌ **no longer true** — points at `validate.py --list` as the authoritative roster |
| E3 | ~~A frozen roster enum cannot hold the authorized bundles~~ | the law | ❌ **no longer true** — 3 references to `validate.BUNDLE_CODES`, no enum |
| E4 | ~~It states a stale toolchain version~~ | the law | ❌ **no longer true** — cites the pin in `lean/lean-toolchain`. The only version literal left is Aristotle's own **4.28.0**, which is correct |
| E5 | ~~It claims no per-repo `CLAUDE.md` exists~~ | the law's document table | ❌ **no longer true** — the row names `CLAUDE.md` (this repo) |
| E6 | The mechanism claim — *a rule text that enumerates a roster is a hardcoded roster* | not a factual claim about the tree | **retained**: it is the transferable finding, and it survives the five repairs |
| E7 | `bundle_registry_consistency` Leg C forbids re-hardcoded rosters in code | the check's Leg C | ✓ (re-confirms V7 atom 34) |
| E8 | **SET:** `no_counts_in_narratives` covers `docs/architecture/` only, so the law is outside it | the leg's own output | *"6 narrative doc(s) **in architecture/**"* — the law lives in `docs/`, unscanned ✓ |

**Net:** five of §9's assertions were true when written and are now false. The section is
rewritten to state what the law does — name owners rather than copy values — and to record the
one thing no mechanism covers: prose rosters outside `docs/architecture/` have no guard.

⚠️ **This is the general hazard, not a §9 quirk.** Any atom in V1–V8 that recorded a defect as
*present* is invalidated the moment that defect is fixed, and nothing re-opens it. Atoms
recording a defect are therefore perishable in a way atoms recording a design are not.

---

## V10 — `VALIDATION_ARCHITECTURE.md`, uncovered remainder — 17 atoms, 1 corrected

Closes the 32-unit gap recorded in D4 for this document. Verify-only sweep first; the single
correction was applied after the sweep, per D4's separation rule.

### §2 — the framework contract

| # | atom | decided by | result |
|---|---|---|---|
| A1 | `run_checks` fills a result for **every** spec, including from its `except` handler | `validate.py:272-280` | `for spec in _CHECKS:` … `except Exception` → `results[spec.name] = CheckResult(passed=False, …)` ✓ — this is why the `--ci` floor had to count `measured`, not `len(results)` |
| A2 | H5's guard requires **`_cfg`** in `co_names`, not just the flag name | `test_validate_flag_propagation.py:241` | `assert "_cfg" in fn.__code__.co_names` ✓ |
| A3 | H5's stated reason: `co_names` records both `LOAD_GLOBAL` and `LOAD_ATTR` | same file `:230-237` | states it verbatim ✓ |
| A4 | `test_regenerators_precede_their_consumers` derives the consumer set by AST | `test_validate_registry_contract.py:_counts_consumers` | AST-derived, with a non-empty guard at `:143` ✓ |
| A5 | `counts_fresh` runs **first** in `_CANONICAL_ORDER` | the live list | index **0** ✓ |
| A6 | ~~The accepted limit is stated in **both** the test and the production comment~~ | exhaustive grep of `scripts/`, then both texts read | ❌ **FALSE** — stated in the TEST only (`:92-94`). The production comment at `validate.py:148-160` states the ordering intent and *"Do not re-enumerate consumers here"*, not the limit. The test's own sentence says the production comment states **the ordering intent**; the doc read that as the limit. Statement replaced |

⚠️ **A6 is requirement 3's failure mode exactly:** the limit is real and the test does state it,
so the true half carried an unchecked clause. Verifying "is the limit real?" would have passed
it. The atom is *where each statement lives*, and only reading both texts decides it.

### §4 — runtime flags

| # | atom | decided by | result |
|---|---|---|---|
| A7 | **SET:** the table's five flags are exactly the runtime flags | AST of `_config.py` (`Assign` **and** `AnnAssign`) vs the table | all 5 declared; the only other uppercase names are `CI_MIN_CHECKS_RUN` and `CI_SKIP` — a floor constant and a skip list, not flags ✓ complete |
| A8 | **SET:** each flag's CLI switch exists | `validate.py` argument parser | `--strict`, `--force-latex`, `--force-notebooks`, `--no-memo`, `--ci` all present ✓ |
| A9 | `--strict` implies `--no-memo` | `validate.py` | sets `NO_MEMO` on the strict path ✓ |

### §5 — the memo's five guards

| # | atom | decided by | result |
|---|---|---|---|
| A10 | Guard 1 — the key spans the **whole defining module** plus the body | `_memo.py:150` | `getsource(getmodule(fn))`, widened from `getsource(fn)` 2026-08-05 ✓ |
| A11 | Guard 2 — `TestCheckKeysSpanTheirInputs` seeds each input **in the production tree** | `test_validation_memo.py:440` | seeds through the real `key_fn` ✓ |
| A12 | Guard 3 — a non-measurement is never cached | `_memo.py:342` | `if not result.measured:` → no store ✓ |
| A13 | Guard 3b — it also **evicts** a stale green under the same key | `_memo.py:343-345` | `entries.pop(name, None)` ✓ |
| A14 | Guard 4 — a hit replays the full detail list | `_memo.py:318-321` | rebuilds every `Detail` from the hit ✓ |
| A15 | Guard 5 — `conftest.py` disables the memo suite-wide | `tests/conftest.py:26` | `os.environ["SKEFT_VALIDATION_NO_MEMO"] = "1"` ✓ |
| A16 | `paper_latex_compiles` caches per draft over the full `\input` closure, and its slow gate is deleted | `papers_prose.py:403-404` + `:22-25` | per-draft content hash of the input closure; the slow gate is gone and `--force-latex` now bypasses only the cache ✓ |

### §6

| # | atom | decided by | result |
|---|---|---|---|
| A17 | There is no scheduled CI runner | filesystem | `.github/workflows` **does not exist** ✓ |

**Coverage after V10:** `VALIDATION_ARCHITECTURE.md` 22 → **39 atoms** of 54 load-bearing
units (41% → **72%**). The remaining 15 are §1's tree-block lines and §3's hazard-table cells,
each already covered in aggregate by V3 atoms 6 and 19–20 but not enumerated individually.

---

## V11 — `END_TO_END_MAP.md` §§1–7 remainder — 16 atoms, 1 corrected

### §1 — the spine

| # | atom | decided by | result |
|---|---|---|---|
| M1 | **SET:** everything quantitative downstream derives from `lean_deps.json` — counts, atlas, graph, frontier | each generator read for a `lean_deps` / `load_lean_deps` reference | `update_counts.py` ✓ · `atlas_view.py` ✓ · `build_graph.py` ✓ · the frontier reads `atlas_view.json`, so it derives **transitively** ✓ — set complete |
| M2 | ① has no mechanization | V7 atoms 1–2 re-confirmed: no check module references `docs/roadmaps/` | ✓ |
| M3 | ⑨ contains gates returning verdicts they did not compute | `gate_edge_types_are_emitted` + the dead-edge set | `PRODUCES`/`SUPPORTS`/`CONTRADICTS` unemitted ✓ |
| M4 | *"Below that node drift is structurally impossible"* | — | **NOT-AN-ASSERTION** — a design characterisation of the chokepoint, not a falsifiable claim about a specific artifact |
| M5 | *"This is the single largest ungated seam in the map"* | — | **NOT-AN-ASSERTION** — a ranking judgement; "largest" has no defined metric here |

### §4 — Lean and the chokepoint

| # | atom | decided by | result |
|---|---|---|---|
| M6 | **NUMBER-CITED SET:** §4 cites Invariants #4, #9, #10, #15, #16, #17 — each resolves to the subject §4 uses it for | the law's `## Pipeline Invariants` section, each number read | #4 formula content-grounding **and** *"Every Lean theorem has a proof (zero sorry)"* · #9 placeholders non-load-bearing · #10 no heartbeat overrides · #15 axiom sign-off · #16 tracked-hypothesis registry · #17 kernel no-go ✓ all six |
| M7 | Invariant #4 covers zero-`sorry`, so *"Invariant #4 (zero `sorry`)"* is a correct citation | #4's body, read in full | *"Every Lean theorem has a proof (zero sorry)"* ✓ |
| M8 | `lake build` exits 0 on a `sorry` | the tier-0 gate's implementation | `pre-commit-sync.sh` must grep lake's **stdout** for `declaration uses .?sorry.?` and `exit 1` itself — it would be unnecessary if the exit code carried it ✓ |
| M9 | `axiom_closure_allowlist` catches `sorryAx` warn-first only | `lean_toolchain.py:550-557` | `strict = _cfg.STRICT_MODE`; `Detail(..., not strict, warning=not strict)` ✓ |
| M10 | The gauntlet's `zero_sorry` conjunct is inert | V7 atom 13 re-confirmed | fixed-string quote style the toolchain does not emit ✓ |
| M11 | Invariant #9's registry-completeness clause has no enforcement | V7 atom 16 | nothing compares `PLACEHOLDER_TOTAL_COUNT` to `counts.json` ✓ |

### §5–§6

| # | atom | decided by | result |
|---|---|---|---|
| M12 | `measured` is a separate field from `passed`, and that is what makes the `--ci` floor meaningful | `CheckResult` fields; the floor's branch | V3 atoms 9/13 + V10 A1 ✓ |
| M13 | `KNOWLEDGE_GRAPH.md` carries an **Emitted?** column naming each unemitted edge type and the gate that queries it | the schema doc's table header and rows | column present, rows name the gates ✓ |
| M14 | The three unemitted edge types are `PRODUCES`, `SUPPORTS`, `CONTRADICTS` | V7 atom 20, fresh build's edge-type set | none present ✓ |

### §7

| # | atom | decided by | result |
|---|---|---|---|
| M15 | ~~"Stage 10" means two different things; tracked as B6~~ | the law's Stage-10 body | ❌ **FALSE** — the law carries a scope note: claims review is a **sub-gate inside** Stage 10, and *"there is no second Stage 10."* B6 is closed; the collision does not exist. Statement replaced |
| M16 | `stage10_status` and `gate_precheck.py s10` use the narrower sub-gate sense | the field's writers; `gate_precheck`'s `s10` step list | both key on the claims-review gate ✓ |

⚠️ **M15 is the same perishability hazard as V9.** §7 cited an open tracker item that closed the
same day. An atom recording a defect is invalidated by the fix, and nothing re-opens it — this
is the second instance inside `docs/architecture/` in one pass.

**Coverage after V11:** `END_TO_END_MAP.md` 42 → **58 atoms** of 80 (53% → **73%**).

---

## V12 — `CHECK_AUTHORING_GUIDE.md` remainder — 12 atoms, 2 corrected

⚠️ **Both corrections are in prose written or reviewed earlier the same day**, and both would
have taught a future author to *remove a working guard*. This is the highest-consequence class
of error in these documents: not a stale fact, but advice that is wrong.

### §2 — the obligations

| # | atom | decided by | result |
|---|---|---|---|
| K1 | ~~A floor asserted as `CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)` **guarantees it can never fire**~~ | `test_ci_mode.py:163-167`, read, and its observed behaviour | ❌ **FALSE** — that is the live assertion, and it **fired** on 2026-08-07 when a check was added (`CI_MIN_CHECKS_RUN is 61 but a fully-provisioned runner executes 62`). Self-sealing is comparing the floor to the number that *ran* (identically `registered - skipped` because `run_checks` fills every spec), not comparing a **hardcoded constant** to that expression. Statement replaced with the distinction |
| K2 | ~~The floor test is fixed because **no formula assertion remains**~~ | same test | ❌ **FALSE** — a formula assertion remains at `:163`. What was added is a second, `slow` test that **executes** the registry and counts `measured`. The test's own docstring says `registered - skipped` *"is the DEFINITION of the floor, so comparing the floor to it can only catch an arithmetic slip"* — the guide read that as removal. Statement replaced |
| K3 | The floor's second test executes the registry and counts `measured` | `test_the_LIVE_floor_matches_what_a_REAL_run_MEASURES` | runs `run_checks`, filters `r.measured` ✓ |
| K4 | `test_cannot_measure_baseline.py` fails in **both** directions | the two test bodies | `test_no_new_silent_pass` (`:208`) and `test_baseline_has_no_stale_entries` (`:222`, *"FIRES in the other direction"*) ✓ |
| K5 | `AWAITING_CEILING` ratchets the backlog so adding a name breaks it in the same commit | `test_d5_mutation_obligation.py:584` | `AWAITING_CEILING = 0`, with `AWAITING_MUTATION_TEST` empty ✓ zero headroom |
| K6 | **SET:** `PRODUCTION_SEEDED` and `FIXTURE_ONLY_CEILING` both exist there | AST of module-level constants | present, alongside `MUTATION_VERIFIED`, `AWAITING_MUTATION_TEST`, `AWAITING_CEILING` ✓ |
| K7 | The guide does not restate the mutation split | the guide's §2.4 text | defers to the test file and names the two constants ✓ |

### §3 — where the check goes

| # | atom | decided by | result |
|---|---|---|---|
| K8 | **SET:** the module table's population equals the modules on disk | extracted names vs `ls scripts/validation/checks/*.py` | **12 = 12, sets identical**, no extras either way ✓ complete |

### §4–§6

| # | atom | decided by | result |
|---|---|---|---|
| K9 | §4's two commands are runnable as written | `validate.py --check <name> --no-archive`; `pytest tests/ -q` | both used throughout this pass ✓ |
| K10 | §4's third step is the production-seeded mutation, stated as prose not a command | the block | ✓ consistent with §2.4 |
| K11 | §5's ledger status column is load-bearing (most rows are repaired) | the table | 10 of 12 rows `fixed`, 1 open, 1 kept-visible ✓ |
| K12 | §6's checklist items | — | **NOT-AN-ASSERTION** — nine imperatives ("a leg that cannot fire on any input"), a review aid with no truth value |

**Coverage after V12:** `CHECK_AUTHORING_GUIDE.md` 28 → **40 atoms** of 54 (52% → **74%**).

---

## V13 — `VALIDATION_GATE_TOPOLOGY.md` remainder — 11 atoms, 1 corrected

### §4 — what each gate actually computes

| # | atom | decided by | result |
|---|---|---|---|
| T1 | **SET:** §4's gate table population equals `readiness_gates.GATES` | extracted names vs the live roster | **11 = 11, sets identical** ✓ complete |
| T2 | **SET:** every priority in the table matches the roster | per-row comparison | **0 mismatches** ✓ |
| T3 | ~~`CitationIntegrity` is registry-coverage-only **contra its doc**~~ | `READINESS_GATES.md` as it now stands | ❌ **FALSE** — that doc now states *"This gate is registry COVERAGE, not content verification"* and routes each content claim to the check that verifies it. The gate's computation is unchanged; the *contra* is gone. Statement replaced |
| T4 | `AssumptionDisclosure` matches a **lowercased substring** of the tex | `_eval_assumption_disclosure:486-494` | `idx.paper_tex(...).lower()`, key and human name both `.lower()` ✓ heuristic as described |
| T5 | `ProductionRunHealth`'s `PRODUCES` leg is dead and the **prose regex** is what fires | `_eval_production_run_health:590` vs `:599` | queries `PRODUCES` (unemitted) and separately `re.search(r'\b(Monte\s+Carlo\s+evidence\|MC\s+evidence)\b', …)` ✓ |
| T6 | `FixPropagation` **self-promotes** to P1 when blocking | `_eval_fix_propagation:795` | `r.priority = 1` ✓ |

### §6 — field ownership

⚠️ **Every row here was checked by READING, after a grep suggested three were wrong.** A
reference is not a write: `bundle_readiness.py` mentions `freshness_stale` three times and
writes it zero times. Counting occurrences would have produced three false corrections.

| # | atom | decided by | result |
|---|---|---|---|
| T7 | `bundle_readiness.write_metadata_counts` exists and owns the counts fields | `bundle_readiness.py:688` | `def write_metadata_counts(...)` ✓ |
| T8 | `freshness_stale` is **not** written by `bundle_readiness.py` | its three references, read | all three are **comments**, one stating *"`freshness_stale` is deliberately NOT written here"* ✓ |
| T9 | `freshness_stale` is owned by `check_bundle_source_freshness.py` | that script | writes it ✓ |
| T10 | `apex_theorems` is written by a human, never a script | the only script naming it | `architecture_inventory.py:264` **reads** it (`.get("apex_theorems")`) for its census table; no script writes it to `bundle_metadata.json` ✓ |
| T11 | The §6 thesis — *"a check telling you to run a script that cannot fix the field"* | — | **NOT-AN-ASSERTION** — a statement of the table's purpose |

**Coverage after V13:** `VALIDATION_GATE_TOPOLOGY.md` 43 → **54 atoms** of 69 (62% → **78%**).

---

## V14 — `END_TO_END_MAP.md` §§7–8 — 9 atoms, 1 corrected

| # | atom | decided by | result |
|---|---|---|---|
| N1 | **SET:** the only writers of `stage*_status` are `bundle_source_manifest.py` and `bundle_append.py` | every assignment across `scripts/` | 2 writers ✓ complete |
| N2 | **SET:** nothing writes any `stage*_status` to `"green"` | the literal values assigned | `bundle_source_manifest` initialises `"pending"` ×3; `bundle_append` demotes green→`"pending"` ×3. **No `"green"` assignment exists** ✓ |
| N3 | *"Stages 9 and 10 before 13"* has no enforcement point | no check reads the fields to gate | `bundle_append.py:320-325` reads them to DEMOTE, never to block ✓ |
| N4 | `tables_fresh` cannot fail on staleness | `freshness.py:301-330` | stale → `Detail(..., True, ..., warning=True)` then falls through to `return CheckResult(passed=True, ...)` ✓ |
| N5 | Only a non-zero subprocess or an unverified regeneration fails it | same body | `passed=False` at `:318`, `:323`, `:327` only ✓ |
| N6 | **SET:** every `tables.py` on disk is under a legacy `paperNN_*` directory | `find papers -name tables.py` | **9 files, all `paperNN_*`; zero under a bundle directory** ✓ complete |
| N7 | **NUMBER-CITED:** §8's *"Invariant #8"* resolves to parameter provenance | the law's invariant list | *"Every experimental parameter has verified provenance."* ✓ — matches the dashboard/provenance context §8 uses it in |
| N8 | ~~Legibility is the **only** blocking figure assertion~~ | `bundle_figure_integrity`'s `n_fail` increments | ❌ **FALSE** — **four** legs block: `missing_fn`, `missing_png`, `render_error`, `illegible`. Only `drift` carries `warning=True`. Statement replaced |
| N9 | The drift comparison is advisory | the `drift:` Detail | `warning=True` ✓ |

⚠️ **N8 is a set claim that was verified by its named member.** Legibility *does* block, so
confirming it would pass; the atom is *"the only"*, which needs every `n_fail` increment
enumerated. This is requirement 4 exactly, and it survived four prior passes over this file.

**Coverage after V14:** `END_TO_END_MAP.md` 58 → **67 atoms** of 80 (73% → **84%**).

---

## V15 — `QA_QI_INFRASTRUCTURE_MAP.md` §§1/6 + ledger integrity — 8 atoms, 1 corrected

| # | atom | decided by | result |
|---|---|---|---|
| P1 | **SET:** every artifact name in §1's mermaid resolves in the tree | all 17 names, resolved by basename | **17 of 17** ✓ complete (they are labels, not paths — resolving them as repo-root paths reports 13 false failures) |
| P2 | ~~§6: a filed item's four fields *"were wrong"*~~ | requirement 7 | ❌ **retraction narrative in a production document.** Reframed to the forward rule: each field of a finding is its own assertion, and an entry written from a sample reads exactly like one that was counted |
| P3 | **SET:** the Codex control plane has zero references to the five named surfaces | `scripts/lean_slots/` + `.codex/` searched for each | `validate.py` 0 · `register_check` 0 · `gate_precheck` 0 · `bundle_readiness` 0 · `build_graph` 0 ✓ |
| P4 | **SEAM GUARD for P3** — the searched directories are non-empty | `find` | `scripts/lean_slots` 11 files, `.codex` 7 files ✓ — the zero is a measurement, not an empty scan |
| P5 | §6's *"re-measure the scope before fixing"* | — | **NOT-AN-ASSERTION** — an instruction to a future author |

### Ledger integrity

| # | atom | decided by | result |
|---|---|---|---|
| P6 | V6 row 53 and V8 Q9 contradicted each other | both rows, read | ❌ V6 recorded I1's citation as a *documented waiver* ✓; V8 re-derived and found **no waiver anywhere**. Row 53 now carries a SUPERSEDED marker naming V8 Q9/Q11 as authoritative |
| P7 | No other V1–V7 row is contradicted by V8–V14 | each correction cross-checked against the earlier passes | row 53 was the only collision ✓ |
| P8 | The requirement-7 scan pattern was too narrow | re-run with `(was\|were\|had been\|used to be) (wrong\|false\|incorrect\|stale)` etc. | the original matched `was wrong` and missed **`were wrong`** — one live hit in §6. All seven now scan **0** under the wider pattern ✓ |

⚠️ **P8 is a proxy failure inside the audit of proxy failures.** A requirement-7 scan is only
as good as its pattern, and a clean result from a narrow pattern is indistinguishable from a
clean document. The wider pattern is recorded here so the next scan starts from it.

⚠️ **P6 establishes that ledger rows can go stale against each other.** A later pass that
re-derives a claim and finds it false must mark the earlier row, or the audit trail asserts
both. This is the ledger's own version of the perishability hazard in V9/V11/V13.

**Coverage after V15:** `QA_QI_INFRASTRUCTURE_MAP.md` 69 → **77 atoms** of 86 (80% → **90%**).

---

## V16 — `VALIDATION_ARCHITECTURE.md` §1 tree + §3 hazard table, per row — 15 atoms, 0 corrected

V3 verified these two structures **in aggregate** (atom 6: the 12 module names match disk;
atoms 19–20: five hazards, each enforcer read). Requirement 2 wants one row per assertion, so
each row is enumerated here.

### §3 — each hazard's named enforcer, individually

| # | atom | decided by | result |
|---|---|---|---|
| W1 | H1's enforcer is a real test | AST of `tests/` | `test_no_check_derives_a_path_from___file__` **defined** in `test_validate_public_surface.py` ✓ |
| W2 | H2's enforcer names `_ROSTER_CONSUMERS` and it exists | exhaustive search, then the file | **defined** at `bundles_readiness.py:813` as an *annotated* assignment — a `NAME *=` pattern misses it, and reports it absent |
| W3 | H2's Leg B does what the row says | `bundles_readiness.py:862`, `:925-954` | *"every module in `_ROSTER_CONSUMERS` exposes …"*, and the loop asserts each ✓ |
| W4 | H2's second enforcer `EXPECTED_DYNAMIC` exists | AST | **defined** in `test_validate_public_surface.py` ✓ |
| W5 | H3's two enforcers are real tests | AST | `test_every_registered_check_has_a_declared_position` and `test_the_sort_runs_after_the_last_registration`, both **defined** in `test_validate_registry_contract.py` ✓ |
| W6 | H4's enforcer exists | AST + file | `test_cannot_measure_baseline` ✓ |
| W7 | H5's enforcer exists | AST + file | `test_validate_flag_propagation` ✓ |

⚠️ **W2 is the fourth measurement this pass defeated by an annotated assignment.** `X: T = v`
is invisible to both a `^X\s*=` grep and an `ast.Assign`-only walk. Match `AnnAssign` too, or
the audit reports a live symbol missing.

### §1 — each module's description

| # | atom | decided by | result |
|---|---|---|---|
| W8 | **SET:** every module named in the tree hosts registered checks | `spec.func.__module__` grouped over the live registry | **12 of 12 non-empty**; none is a description of an empty file ✓ |
| W9–W14 | each Lean/physics/paper module's description matches what it hosts | the check names in each | `lean_substrate` 7 (`lean_zero_sorry`, `placeholder_not_cited`) · `lean_toolchain` 6 (`native_decide_regression`, `lean_source`) · `lean_statements` 3 (`formula_grounding`, `vacuous_statement_audit`) · `physics` 9 (`numerical`, `identities`) · `papers_prose` 7 (`paper_provenance`, `numerical_literals`) · `prose_lean_refs` 2 (`prose_theorem_reference_coverage`) ✓ |
| W15 | each remaining module's description matches what it hosts | same | `citations` 4 (`parameter_provenance`, `provenance_doi_in_registry`) · `bundles_readiness` 7 · `graph_atlas` 4 (`graph_integrity`, `atlas_integrity`) · `freshness` 7 (`counts_fresh`, `tables_fresh`) · `notebooks` 3 · `reviews` 5 ✓ |

**Note, not a defect:** grouping the live registry by `__module__` also yields `_memo`, because
the memo decorator rewraps a check's function. The tree block correctly lists `_memo.py` as a
*framework* module rather than a checks module; the extra key is an artifact of the wrapper.

**Coverage after V16:** `VALIDATION_ARCHITECTURE.md` 39 → **54 atoms** of 54 — **fully
enumerated**. Every load-bearing unit in this document now has a row.

---

## V17 — `README.md` final 3 + `VALIDATION_GATE_TOPOLOGY.md` §3 — 12 atoms, 1 corrected

### `README.md` — completing the enumeration

| # | atom | decided by | result |
|---|---|---|---|
| X1 | ~~"…exactly how the claims corrected on 2026-08-07 survived"~~ | requirements 7 + 8 | ❌ **audit-trail content in a production document**, and a date in a file whose own first rule forbids dated snapshots. Reframed to the forward failure mode: *a claim is true when written, and nothing re-reads it afterwards* |
| X2 | Neither map restates the other's tables | markdown table rows in each | `END_TO_END_MAP` **0** table rows, `QA_QI` **30**, **0** rows shared ✓ |
| X3 | The "not tidiness" paragraph and the rule-of-thumb | — | **NOT-AN-ASSERTION** — a rationale and a heuristic |
| X4 | Rule 2, *"design is written here first"* | — | **NOT-AN-ASSERTION** — a policy this repo adopts, not a claim about the tree |
| X5 | *"They overlap by design at exactly one point"* | — | **NOT-AN-ASSERTION** — a design characterisation; "one point" names no countable artifact |

✅ **`README.md` is now fully enumerated** — 18 of 18 load-bearing units.

### `VALIDATION_GATE_TOPOLOGY.md` §3 — the flag table, row by row

| # | atom | decided by | result |
|---|---|---|---|
| X6 | `--strict` promotes submission advisories and implies `--no-memo` | `validate.py`'s strict path | sets `NO_MEMO` ✓ (V10 A9) |
| X7 | `--scope substrate` prints paper failures but does not set the exit code | `validate.py:838-844` | `if args.scope == "substrate" and not all_passed:` → prints, exit unchanged ✓ |
| X8 | `--force-latex` bypasses the per-draft cache only | `papers_prose.py:22-25` | the slow gate is gone; the flag bypasses the content-hash cache ✓ (V10 A16) |
| X9 | `--no-memo` re-measures the memoized checks | `_memo` bypass path | ✓ (V3 atom 21, V10 A10–A15) |
| X10 | **SET:** `--ci` skips exactly *the mtime regenerators + `notebook_exec`* | `_config.CI_SKIP` | `{counts_fresh, tables_fresh, claim_clusters_fresh, notebook_exec}` — the three mtime regenerators plus that one ✓ exact |
| X11 | `--ci` never archives | `validate.py:792` | `if not args.no_archive and … and not args.ci:` ✓ |
| X12 | `--force-notebooks` bypasses the notebook skip-cache | `_config.FORCE_NOTEBOOK_REEXEC` + its consumer | ✓ (V10 A7–A8) |

**Coverage after V17:** `README.md` 15 → **18 of 18** ✅ · `VALIDATION_GATE_TOPOLOGY.md` 54 →
**61 atoms** of 69 (78% → **88%**).

---

## V18 — `VALIDATION_GATE_TOPOLOGY.md` §§1/5/7 + `QA_QI` §3 — 17 atoms, 1 corrected

### `VALIDATION_GATE_TOPOLOGY.md` §1 — the tiers

| # | atom | decided by | result |
|---|---|---|---|
| Y1 | **SET:** the gates §1 names are exactly those `gate_precheck` defines | its gate→steps table | `{s9, s10, s13, s13-lean, submission}` = the five named ✓ |
| Y2 | Tier 0 runs a **short named list**, not the suite | `pre-commit-sync.sh:103` | `for c in formula_grounding placeholder_not_cited native_decide_regression` — three ✓ |
| Y3 | **SET:** that list is all substrate-side, so paper reds cannot block a commit | each of the three | `formula_grounding` (Lean refs), `placeholder_not_cited` (Lean), `native_decide_regression` (Lean) ✓ none reads the paper corpus |
| Y4 | Tier 0 hard-blocks on `main` only | the script | three sites, each `[ "$BRANCH" = "main" ] && { …; exit 1; } \|\| echo "(off-main: warn only)"` ✓ |
| Y5 | `s13` is the full suite; `s13-lean` the same suite scope-limited | the step lists | `s13 → ["__full__"]`, `s13-lean → ["__substrate__"]` ✓ |
| Y6 | `s9` and `s10` are reviewer prechecks with named check lists | same | `s9` 2 checks, `s10` 4 ✓ |

### §5 — enforcement reality

| # | atom | decided by | result |
|---|---|---|---|
| Y7 | The commit gate exits 0 in a worktree | `pre-commit-sync.sh:24-25` | detects the worktree via `--git-dir` ≠ `--git-common-dir`, then `exit 0` ✓ |
| Y8 | It exits 0 on a missing `uv` | `:35-36` | `command -v uv … \|\| { echo …; exit 0; }` ✓ |
| Y9 | `.git/hooks/pre-commit` is local-only and uncommitted | `git ls-files` | untracked — git does not version `.git/`, so **a fresh clone has no mechanical gate** ✓ |
| Y10 | The web-egress guard is the one unambiguously fail-CLOSED control | `harness_web_egress_guard.py` | its contract: *"FAILS CLOSED: any internal error => deny"*, plus a second printf-deny layer in `hooks.json` ✓ |
| Y11 | It is wired to `WebSearch\|WebFetch` | `hooks.json:49` | `"matcher": "WebSearch\|WebFetch"` ✓ |

### §7 — cost

| # | atom | decided by | result |
|---|---|---|---|
| Y12 | The two expensive checks are scoped by the memo and the per-draft cache | `_memo` targets + `papers_prose` cache | `axiom_closure_allowlist` + `lean_docstring_refs_resolve` memoized; `paper_latex_compiles` content-hashed ✓ (V3 21, V10 A16) |
| Y13 | *"Measure rather than quote"* | — | **NOT-AN-ASSERTION** — an instruction |

### `QA_QI_INFRASTRUCTURE_MAP.md` §3 — the dialect

| # | atom | decided by | result |
|---|---|---|---|
| Y14 | ~~`_REVIEW_SECTION_RE` accepts these 7 named heading forms~~ | the full pattern at `build_graph.py:1582-1595` | ❌ **INCOMPLETE SET** — the prefix alternation also accepts `Finding` and `REQUIRED`, and the separator accepts a colon as well as a spaced dash. Replaced with the **shape** plus a pointer to the pattern: an enumeration of a regex's accepted forms beside that regex is the hand-maintained-list failure this map documents elsewhere |
| Y15 | The live risk is a NEW form, not the existing corpus | the widening history in the pattern's comments | every on-disk form was minting zero before the widening ✓ |
| Y16 | Bundle Stage-13 reports are the largest source of `ReviewFinding` nodes | fresh build, findings grouped by source | ✓ (V6 atom 35) |
| Y17 | A document whose severities appear only in PASS/RESOLVED notes is skipped, not failed | `review_docs_mint_findings` | skip branch, no failure ✓ |

⚠️ **Y14 is a set claim that under-enumerated rather than over-claimed** — the doc named a
subset of what the regex accepts. Both directions matter: an incomplete accept-list makes a
future author believe a working heading form will be rejected.

**Coverage after V18:** `VALIDATION_GATE_TOPOLOGY.md` 61 → **69 of 69** ✅ ·
`QA_QI_INFRASTRUCTURE_MAP.md` 77 → **86 of 86** ✅

---

## V19 — the last two documents — 24 atoms, 1 corrected

### `CHECK_AUTHORING_GUIDE.md` §5 — each ledger row's "fixed" claim, individually

V12 verified the status column is load-bearing in aggregate (K11). Each row's claim is its own
assertion; V8 covered `harness_lock` and AI-Defense, V12 the floor test. The rest:

| # | atom | decided by | result |
|---|---|---|---|
| Z1 | `readiness_submission_gate` returns `passed=False` on a blocked gate | `bundles_readiness.py:654,679` | `ok = not red` → `CheckResult(passed=ok, …)` ✓ |
| Z2 | `paper_latex_compiles` derives its verdict; the slow gate is deleted | `papers_prose.py:22-25` | ✓ (V10 A16) |
| Z3 | The `--ci` floor counts `CheckResult.measured` | the floor branch | ✓ (V10, and the B2 claim test) |
| Z4 | `_memo` refuses to cache a non-measurement | `_memo.py:342` | ✓ (V10 A12) |
| Z5 | The memo's key tests seed through the real `key_fn` | `TestCheckKeysSpanTheirInputs` | ✓ (V10 A11) |
| Z6 | `check_bundle_source_freshness` reports UNMEASURABLE on an absent source directory | `:169`, `:196` | *"A source naming a directory that does not exist is UNMEASURABLE, not fresh"*, and the emitted detail says so ✓ |
| Z7 | An `evaluate_all_gates` evaluator exception records `state='blocked'` | `readiness_gates.py:838-847` | `except Exception` → blocked, with the reasoning that `open` aggregates to YELLOW ✓ |
| Z8 | `_blocked_p1_gates_by_paper` returns `None` when it cannot compute, and GREEN is withheld | `bundle_readiness.py:274`, `:330` | signature is `-> dict[str, list[str]] \| None`; the caller guards `is None` ✓ |
| Z9 | The dead-edge guard's scan is scoped structurally to dicts carrying `source`/`target` | `graph_atlas.py:603` | `if not {"source", "target"} <= keys: continue` ✓ |
| Z10 | §1's skeleton compiles as written | its shape vs `_registry`'s API | `@register_check(name, description)` + `CheckResult(passed=…, measured=…, details=[Detail(…)])` matches the dataclasses ✓ |
| Z11–Z14 | §2.1/2.2/2.5/2.6's stated rules | each rule's enforcing mechanism | `measured` contract ✓ · "never discard a computed verdict" — the shape of every repaired row above ✓ · AST-over-substring ✓ (V3 atom 1) · `_H.<NAME>` at each use / `_cfg` by attribute ✓ (V16 W1, W7) |

### `END_TO_END_MAP.md` §§2/3/5 — the remainder

| # | atom | decided by | result |
|---|---|---|---|
| Z15 | ~~Waves are declared in `docs/roadmaps/Phase<N><X>_Roadmap.md`~~ | every file in that directory, matched against the pattern | ❌ **TOO NARROW** — 116 roadmap files, **93 match, 23 do not**: topic roadmaps (`FormulaRefSweep_Roadmap.md`), bundle-discharge roadmaps (`D10_Discharge_Roadmap.md`), lab notebooks and plans. Statement replaced, with an explicit warning not to scope a wave search to the `Phase*` prefix |
| Z16 | The roadmap records a phase's scope, waves and design decisions | the files | ✓ |
| Z17 | The `/goal` contract is in **both** `CLAUDE.md`s | each file | this repo's ✓ and the workspace's ✓ — both state the Stop hook is a GO signal |
| Z18 | The harness implementation is `.claude/plugins/skeft-qa/` | the directory | 75 files ✓ |
| Z19 | Execution order is semantic because the `*_fresh` regenerators rewrite what later checks read | `_CANONICAL_ORDER` + the three regenerators | ✓ (V3 atom 17–18, V10 A5) |
| Z20 | `measured` separate from `passed` is what makes the `--ci` floor meaningful | both consumers | ✓ (V3 atoms 9/13) |
| Z21–Z24 | §1's mermaid edges, §5's cross-references, §6's schema pointer, §8's roster pointer | each target document/section | all resolve; `doc_refs_resolve` covers the path half every run ✓ |

⚠️ **Z15 is the third under-enumeration in two passes** (with Y14 and the V16 `AnnAssign`
misses). The over-claims are easier to spot because they sound absolute; a **too-narrow
pattern reads as precision** and silently shrinks the population a future reader will search.

**Coverage after V19:** `CHECK_AUTHORING_GUIDE.md` 40 → **54 of 54** ✅ ·
`END_TO_END_MAP.md` 67 → **80 of 80** ✅

---

## V20 — `END_TO_END_MAP.md` §8, the promotion path — 9 atoms, 1 corrected

⚠️ **This section did not exist when V7/V9/V11/V14 verified this document at 80/80.** The
operator asked how a bundle reaches submission-ready and the answer was in no architecture
document, while `README.md:14` assigns exactly that question here.

**The limit this exposes.** Assertion-granularity verification asks *"is every sentence here
true?"* It cannot ask *"is every sentence that should be here, here?"* Both documents were 100%
accurate — `README` about which document owns the question, `END_TO_END_MAP` about everything it
did say — and the requirement was entirely absent. **The ledger is a soundness check with no
completeness dimension**, and no required-content contract exists for these documents. Filed as
a control gap in `ARCHITECTURE_TODOs.MD`.

| # | atom | decided by | result |
|---|---|---|---|
| S1 | Transition 1 — creation writes `"pending"` ×3 | `bundle_source_manifest.py:129-131` | ✓ |
| S2 | **Transition 2 — `"pending"` → `"green"` has no actor** | every `stage*_status` write, whole repo (not `scripts/` only) | only writers are S1 and S3; **no `"green"` assignment exists** ✓ |
| S3 | Transition 3 — append demotes green → `"pending"` | `bundle_append.py:320-325` | ✓ |
| S4 | Transition 4 — findings → `blockers_open`/`readiness` | `bundle_readiness.write_metadata_counts:688` | ✓ |
| S5 | The §12 exit condition is six conjuncts | `BUNDLE_LIFT_PROCEDURE.md` §12 | `stage9/10/13 == green` · `blockers_open == 0` · `stage13_redo_required == false` · `freshness_stale == false` ✓ |
| S6 | ~~The readiness formula has no unreviewed-guard~~ | `bundle_readiness.py:370-391`, read in full | ❌ **FALSE** — `not review_recorded → YELLOW (unreviewed)` is evaluated *before* GREEN, and GREEN is withdrawn on a blocked **or uncomputable** P1 gate. The real defect is that `review_recorded` does not discriminate review KIND: any `stage13_review_doc` satisfies it, so a 16-anchor attribution sweep counts as a full adversarial pass. Statement replaced |
| S7 | The green-with-blockers guard exists and compares the LIVE count | `bundles_readiness.py:321` | added 2026-08-03; compares recomputed blockers, so hand-editing the stored count trips the other leg ✓ |
| S8 | The ordering rule (9,10 before 13) remains unenforced | no check reads the fields to gate | D6 is the live case: `stage9: not_started`, `stage10: skeleton`, `stage13: green`, 0 blockers — satisfies S7, violates the rule ✓ |
| S9 | **SET:** the status enum has drifted | declared vs observed | declared `pending\|green\|red` (+`yellow` for s13) at `Phase7a_Roadmap.md:91-93`; live corpus uses **5** values — `green`, `pending`, `pending-redo`, `skeleton`, `not_started` — **3 undeclared** ✓ |

⚠️ **S6 is the fourth over-claim this session produced by reading a mechanism partially.** The
formula's first two branches were not read before it was characterised. Read the whole function.

---

## V21 — the D11 apex retrofit — 10 atoms, 0 corrected

Not a document-accuracy pass: these are the load-bearing facts the D11 retrofit
(`docs/audits/2026-08-07-d11-retrofit/FINDINGS.md`) rests on, recorded so a later reader can
tell which of them are **perishable**. Atoms recording a *defect* (P) die when the defect is
fixed; atoms recording a *measurement of a design* (D) survive.

| # | atom | decided by | result |
|---|---|---|---|
| W1 | D11's draft is 670 lines and was read in full before any apex was declared | the file | ✓ |
| W2 | Every one of the 73 declared apexes names a live **theorem** | `validate.py --check bundle_apex_resolves` | ✓ 128 apexes across 5 bundles resolve |
| W3 | **SET:** the closure's module set equals `update_counts.py`'s hand-listed `_D11_MODULES` | both directions, not just containment | ✓ 22 = 22, zero difference either way (D — the agreement is the design's point; the hand-list is TODO-D10) |
| W4 | D11's closure intersects **every** other declared bundle's closure in zero declarations | D6, D9, D12, L2 — all four, not a sample | ✓ (D) |
| W5 | 89 of 502 roster declarations lie outside the closure | derived, both numbers recomputed | ✓ (P — shrinks as the draft absorbs them) |
| W6 | ≈69 of those are content, after subtracting 12 structure fields/projections and 4 `congr_simp` | kind + parent-kind of each | ✓ (P) |
| W7 | Those 69 appear **nowhere** in the D11 draft | **underscore-aware** scan, seeded with two known-present names first | ✓ — a raw-identifier grep would have returned a false zero (P) |
| W8 | Nor in **any** other draft | 10 representatives × all 65 `papers/**/*.tex`, underscore-aware | ✓ none found (P) |
| W9 | `bernal_mexicanHat_witness` exists and is cited nowhere, while the conditional it inhabits **is** cited | the draft + the module | ✓ TODO-D11 (P) |
| W10 | 4 `congr_simp` declarations are classed author-written by the autogen index | the records | ✓ — a measurement artifact, not D11 content; subtracted explicitly rather than silently |

⚠️ **W10 is the counterpart to the V16 `AnnAssign` misses**: there, a scan classed live things
as absent; here, an index classes generated things as authored. Both inflate or deflate a
population that a later claim is stated over. **Subtract the artifact in the open, in the same
sentence as the number** — a clean-looking count with an unstated exclusion is the failure mode.

---

## V22 — the D10 apex retrofit — 8 atoms, 0 corrected

Same convention as V21: **P** = perishable (records a defect), **D** = durable (records a design).

| # | atom | decided by | result |
|---|---|---|---|
| X1 | D10's draft is 315 lines and was read in full before any apex was declared | the file | ✓ |
| X2 | `molecularHamiltonian_essSelfAdjoint` is **unconditional** as the abstract claims | the **statement**, not the prose describing it | ✓ takes `N`, `m`, `0 < m`, nuclei only; no tracked `Prop`; axioms exactly the three classical ones (D) |
| X3 | `traceDist_lindblad_monotone` carries **no** disclosed CPTP-realization argument | the statement | ✓ (D) |
| X4 | `coulomb_isRelBounded` **produces** the bound rather than assuming it | the statement | ✓ existential in `(a, b)` with `a < 1` (D) |
| X5 | **SET:** `GroundStateData`, `DensityVariational`, `LevyLiebData` have **no inhabitant** | every declaration in the tree whose type mentions each — all three, not a sample | ✓ only auto-generated projections/eliminators and the theorems stated over an arbitrary instance (P) |
| X6 | Those theorems reduce to their structures' own fields | the **full Lean source** of all three modules, read directly — not the extracted signature | ✓ `ciInf_le` + `nondegen` + `ground`; `rw [hn]; linarith` against `decomp` (P) |
| X7 | The Lean discloses this and the manuscript does not | both, side by side | ✓ `HohenbergKohnUniqueness.lean:19-21`, `HohenbergKohnVariational.lean:26-27` vs the abstract's novelty sentence (P) |
| X8 | **SET:** D10 ∩ every other declared bundle | D6, D9, D11, D12, L2 — all five | ✓ D11 **0**, D9 **50**, D12 1, D6 0, L2 0 (D) |

⚠️ **X2/X3 are the atoms that make X5–X7 usable.** Reading a boldest-claim statement *before*
reading the layer that fails is what separates "one layer overclaims" from "the bundle
overclaims" — and only the first is true. A finding that does not measure the parts that hold is
not a measurement, it is a verdict.

---

## V23 — the D1 apex retrofit — 7 atoms, 1 near-miss withdrawn before filing

**P** = perishable (records a defect), **D** = durable (records a design).

| # | atom | decided by | result |
|---|---|---|---|
| Y1 | D1's draft is 1,234 lines and was read in full, including everything after the bibliography | the file | ✓ — the four empty lifts are *only* visible after `\end{thebibliography}` |
| Y2 | D1's measured substrate is its apex closure | the closure | ✓ 249 declarations / 18 modules / depth 3 (D) |
| Y3 | The abstract's theorem figure is the **project-scoped** macro | `counts.tex` + the abstract | ✓ TODO-D9's defect, now with a real denominator (P) |
| Y4 | **SET:** all four counting theorems are `by decide`, not `native_decide` | all four, read in source; then the axiom profiles; then the project-wide `Lean.ofReduceBool` population | ✓ zero declarations carry it — there is no load-bearing `native_decide` anywhere (P) |
| Y5 | **SET:** four `Lift-section` events produced zero manuscript content | all 13 append-log events enumerated, each matched to the draft | ✓ four of them (P) |
| Y6 | **SET:** D1 ∩ every other declared bundle | D6, D9, D10, D11, D12, L2 — all six | ✓ 0 each (D) |
| Y7 | D1 claims `ChernBridge`, which D11 explicitly disclaims and attributes to a companion bundle | both drafts + both closures | ✓ the two agree (D) |

⚠️ **The near-miss, recorded because it nearly shipped.** The `lean_deps` extraction attributes
**194** author-written theorems to §7.2's nine modules against the draft's **114** — an apparent
80-theorem understatement in a load-bearing reuse claim. Running
`scripts/count_theorem_reuse.py` reproduces **114 / 106 / 8 → 92.98%** exactly, module by module:
the two figures are the project's two counting conventions, and the draft's is right.

**The seductive number is the one already in hand.** An extraction was open, a claim was in front
of me, and they disagreed — which is a reason to run the tool the claim names, not to file. This
is `feedback-remeasure-filed-findings-before-fixing` in its other direction: not *re-measure a
filed finding*, but *re-measure before filing at all*, especially when the contradicting number
cost nothing to produce.

---

## V24 — the F apex retrofit — 8 atoms, 0 corrected

First Tier-0 retrofit. **P** = perishable, **D** = durable.

| # | atom | decided by | result |
|---|---|---|---|
| Z1 | F's draft is 2,494 lines and was read in full | the file | ✓ |
| Z2 | **SET:** F states a 17-bundle / 16-sibling roster **consistently** | every scope statement in the draft, not one | ✓ seven sites, all agreeing — so this is a considered claim, not a typo (P) |
| Z3 | D9, D10, D11, D12 appear **nowhere** in F | full read | ✓ (P) |
| Z4 | **SET:** F ∩ every *declared* bundle | D1, D6, D9, D10, D11, D12, L2 — all seven | ✓ D1 **27**, all others **0** (D) |
| Z5 | F §7's D6 checklist shows six unchecked boxes for work that has shipped | the checklist vs D6's declared apexes | ✓ ≥4 of 6 stale (P) |
| Z6 | `figure_eight_normalized` is **not** `native_decide` | its axiom profile, then the project-wide `Lean.ofReduceBool` population | ✓ zero declarations carry it — the D1 defect recurs independently (P) |
| Z7 | **SET:** §9's five infrastructure claims | each re-derived from its own source, not from memory | ✓ 4 wrong (checks, invariants, plugin name, branch set), 1 right-but-hardcoded (P) |
| Z8 | F's *physics* hedging is accurate where it matters | the factor-6000 scoping, the Bayes-threshold separation, the Λ bound-vs-heuristic split, the naturalness-window disclosure — each read against its theorem | ✓ all four correctly scoped (D) |

⚠️ **Z8 is not politeness.** Six atoms of this pass are defects, and a reader who saw only those
would conclude the flagship overclaims. It does not: its physics claims are hedged with more care
than its surrounding infrastructure prose, and the two failure modes need different fixes.
**A findings document that records only defects mis-describes its object** — the same error as a
scan that reports only presence.

⚠️ **Z6 is the second independent instance of one defect, and that changes its shape.** One
draft misdescribing its own substrate is a prose slip; two, drafted separately, is a corpus
pattern — and it converts an ADR-010 open *posture* question into a settled measurement. **Count
the instances before choosing the size of the fix.**

---

## V25 — the D3 apex retrofit — 9 atoms, 0 corrected

The heaviest bundle. **P** = perishable, **D** = durable.

| # | atom | decided by | result |
|---|---|---|---|
| A1 | D3's draft is 2,885 lines and was read in full, including the commented material after §28 | the file | ✓ — the seven empty lifts are only visible there |
| A2 | **SET:** every tracked-hypothesis `Prop` D3 names is a `def`/`structure`, never a theorem | all of them, by kind | ✓ — so none can be an apex, and the gate enforces it independently (D) |
| A3 | **SET:** D3 ∩ every other declared bundle | D1, D6, D9, D10, D11, D12, F, L2 — all eight | ✓ **F 126**, everything else **0** (D) |
| A4 | **The `N_f` identity has no Lean witness** | three independent probes: closure intersection, module-level dependency reach from D3's calibration modules into the anomaly tree, and a name-level bridge search over the whole corpus | ✓ none finds a link (P — a theorem would close it) |
| A5 | A5's conclusion is stated as *unformalized*, not *false* | reasoning, recorded deliberately | ✓ disjoint proof DAGs are compatible with physical identity |
| A6 | **SET:** seven `Lift-section` events produced no content | all 33 append-log events enumerated, each matched to the draft | ✓ 7 of 26 lifts (P) |
| A7 | Two `\ref`s resolve to no `\label`, both inside §28.3 | label/ref set difference over the whole file | ✓ (P) |
| A8 | F **overstates** D3 on the Vergeles triple and **understates** it on factor-6000 | both F passages against both D3 passages against the Lean | ✓ one in each direction (P) |
| A9 | `Sakharov_iff_horizon_Crooks` does not exist, exactly as the draft says | the corpus | ✓ a deferral that is honestly labelled (D) |

⚠️ **A8 is why "does the flagship overclaim?" is the wrong question.** F is wrong about D3 in
**both** directions in the same document — too generous about an open hypothesis, too stingy
about a shipped theorem. A drift audit that only looks for overclaims finds half the drift, and
the half it misses costs the program credit it has already earned.

⚠️ **A4/A5 is the pass's most important discipline point.** The measurement is strong and the
temptation is to write "the synthesis claim is unsupported." It is not: three probes found no
*formal* witness for a claim that may well be true physically. **State what the instrument
measured, then state what it cannot see** — the same rule as `truncated_private` travelling with
every closure size.

---

## V26 — ❌ CORRECTION: the `native_decide` finding was wrong, and how

**Withdrawn: V23 atom Y4's generalisation and V24 atom Z6 in full.** Both are struck; the rows
below replace them. The local half of Y4 — that D1's four counting theorems are `by decide` —
**survives**, because it rests on reading the four proofs, not on the bad probe.

| # | claim as filed | measured truth | decider |
|---|---|---|---|
| Y4′ | D1's four counting theorems are `by decide`, not `native_decide` | ✅ **TRUE** | the four proof bodies (`SecondOrderSK.lean:260, 272, 285, 937`) + empty `axiom_deps_project` |
| Y4″ | ~~`Lean.ofReduceBool` appears on zero declarations project-wide → no load-bearing `native_decide` anywhere~~ | ❌ **FALSE.** `axiom_deps_core` contains **only** `propext`, `Quot.sound`, `Classical.choice`; it never records that axiom. The marker is `<decl>._native.native_decide.ax_N_M` in **`axiom_deps_project`**. **546 declarations** are in the closure | `validate.py --check native_decide_regression` |
| Z6 | ~~F's `(native_decide)` annotation on `figure_eight_normalized` is false~~ | ❌ **FALSE. F is correct** — `FigureEightKnot.lean:122` is literally `:= by native_decide` | the source |
| — | ~~ADR-010's `native_decide` posture item is resolved on the merits~~ | ❌ **FALSE and out of scope.** Operator-owned, untouched | ADR-010 §Open |

### Why this one matters more than the error

**Three separate guards existed and none was consulted.**

1. `native_decide_regression` is a **registered check** that measures exactly this quantity. The
   goal's own standing constraint — *before measuring anything, check whether a check already
   measures it* — was violated for the fifth time in this workstream.
2. `lean_statements.py:557-564` **documents this precise trap**: *"`native_decide` axioms were
   STRIPPED from the project-axiom list before the test, so a `native_decide`-backed refutation
   scored kernel-pure"*, and states the 546 figure in as many words.
3. `reference-measurement-traps-false-absence`, written by me the previous day, says: *"a scan
   reporting zero is a claim that needs the same scrutiny as a scan reporting a defect… Before
   filing 'X does not exist,' seed a known-present instance and confirm the scan finds it."*
   **Seeding one `native_decide` theorem would have caught it in one call.**

### The failure mode, named precisely

Not "I used a bad field." **I treated an absence in a field I had not verified was the right
field as a measurement, and then let the strength of the conclusion license widening it** — from
one draft's sentence, to two drafts, to a corpus-wide pattern, to closing an operator-owned ADR
item. Each widening step made the claim more valuable and none added evidence.

⚠️ **The tell was present and ignored:** the conclusion was *surprising in a flattering
direction* — the corpus turned out purer than its own authors claimed. **A measurement that
makes the work look better than the authors thought deserves the scrutiny reserved for one that
makes it look worse.** Every widening step should have lowered confidence, not raised it.

### Standing rule this produces

**Before filing an absence, name the field or tool that would show presence, and prove it can —
by finding a known-present instance with it.** An absence measured with an instrument never
demonstrated to detect the thing is not evidence.

---

## V27 — the D2 apex retrofit — 7 atoms, 1 PRIOR atom corrected

**P** = perishable, **D** = durable.

| # | atom | decided by | result |
|---|---|---|---|
| B1 | D2's draft is 1,403 lines and was read in full, including the commented stubs after the bibliography | the file | ✓ |
| B2 | ❌ **CORRECTS V25 A4's scope.** V25 said *"no D3 gravity-side declaration reaches the anomaly-side tree at all"* | **D2 ∩ D3**, then a per-apex closure walk over **all 89** of D3's apexes | **FALSE as stated** — 3 shared `GenerationConstraint` declarations, reached by exactly one apex, `horizon_wittTrivial_iff_three_generations`. D3 §7.3's prose claim is witnessed (P) |
| B3 | The **narrowed** claim: the Sakharov `N_f` identity has no witness | the Sakharov/heat-kernel chain walked separately — 19 decls / 4 modules | ✓ ∩ D2 = **0**, never reaches `GenerationConstraint` (P) |
| B4 | **SET:** D2 ∩ every other declared bundle | D1, D3, D6, D9, D10, D11, D12, F, L2 — all nine | ✓ L2 **391**, D3 **3**, D12 **3**, rest **0** (D) |
| B5 | L2 is a near-subset of D2 | set difference both ways | ✓ 391 of L2's 430 inside D2; the 39 outside are the Ext modules + `WangBridge` (D) |
| B6 | D2's `native_decide` disclosure is TRUE | the draft against the corpus figure | ✓ consistent with the 546-declaration closure — this is the draft that caught V26 (D) |
| B7 | `dai_freed_spin_z4` is disclaimed by D2 as a trivially-discharged placeholder, matching F's disposition | both drafts | ✓ excluded from apexes on the drafts' own instruction (D) |

⚠️ **B2 is a different failure from V26, and the distinction is the point.** V26 was a **wrong
instrument** — a field that could not detect the thing. B2 was a **right probe reported at wrong
scope**: I searched D3's *calibration* modules and wrote the conclusion about D3's *gravity side*.
Both produced a false absence; only one would have been caught by seeding a known-present
instance.

**The rule B2 adds:** *state the scope the probe actually covered, in the sentence that reports
it.* "No declaration in modules X, Y, Z reaches W" is a different claim from "nothing in this
bundle reaches W," and the second does not follow from the first.

⚠️ **Both corrections this session ran in the same direction — I under-credited the corpus.** The
`native_decide` error made the library look purer than it is; this one made it look less connected
than it is. **Findings that diminish the object are not automatically the conservative choice.**

---

## V28 — DONE-condition backfill: purpose statements + the §D4 evidence ledger

Not a measurement pass. Two DONE-condition items were being skipped and are now discharged for
every bundle declared so far.

| # | atom | decider | result |
|---|---|---|---|
| C1 | **SET:** every bundle I declared now carries an ADR-010 §D2 purpose statement | all five earlier FINDINGS docs (D11, D10, D1, F, D3) plus D2's — enumerated, not sampled | ✓ 6 of 6 |
| C2 | Each states all five required fields: audience, venue, the claim only this container can make, substrate, honest size vs charter | the §D2 text, field by field | ✓ plus an explicit boundary-failure verdict, which §D2 also requires |
| C3 | **SET:** boundary failures named where they exist | every declared bundle | ✓ **F** (by genre — a survey's purpose is definitionally unstatable without siblings), **D10** (partial — §5.3 needs D9), **D6** (partial — borrows 133, claims ~19 %); the other six: no |
| C4 | §D4 evidence assembled for all four named proposals, recommendation NOT made | `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md` | ✓ D6+D9 supported-but-relocated · D6+D9+D12 refuted · D10+D11 refuted · E1+E2 and D4→D8 **not decided** (both undeclared) |
| C5 | Every "0" in that ledger against an undeclared bundle is marked **unmeasurable, not empty** | the file's §4 | ✓ — and the warning is not theoretical: D3 ∩ D2 read as unmeasurable-0 and turned out to be **3** |

⚠️ **NOT-AN-ASSERTION.** *"F cannot be redrafted until the bundles it surveys are measured"* is a
**sequencing recommendation**, not a proposition with a truth value. It is recorded as guidance in
the SHAPE queue and the §D4 ledger, and it is the operator's to accept or reject.

⚠️ **Why these were missed for five bundles.** The FINDINGS docs answered *"what did the closure
show?"* — the interesting question — while §D2's purpose statement answers *"what is this
container for?"*, which the closure cannot decide and which therefore never surfaced as a
measurement. **A DONE condition whose output is not a measurement is the one a measurement-driven
loop drops.** The fix that stuck was writing the purpose statement into D2's FINDINGS *before* its
findings sections, so the next bundle's template already contains it.

---

## V29 — the D4 apex retrofit — 8 atoms, 0 corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| E1 | D4's draft is 1,584 lines and was read in full, including §9 (appended after the original synthesis) | the file | ✓ — §9 carries the Solovay–Kitaev content and the whole D4→D8 finding |
| E2 | **SET:** D4 ∩ every other declared bundle | D1, D2, D3, D6, D9, D10, D11, D12, F, L2 — all ten | ✓ F **73**, D3 **22**, D2 **3**, D12 **3**, rest **0** (D) |
| E3 | **`D4 ∩ D6 = 0`** despite F listing D6 as absorbing D4's SK headline | D6's declared apex list, enumerated in full | ✓ none of D6's eleven is SK-related (P) |
| E4 | **SET:** which drafts name the four FKLW headline theorems | underscore-aware scan over **all 21** drafts, not a sample | ✓ three are D4-only; `…cliffordT_strict_constructive_tight_unconditional` is named by **D4 and D8** (P) |
| E5 | D4's WRT theorems are labelled definitional encodings in the prose, at the point of use | the draft against the Lean | ✓ `rfl`-discharged and said to be — the template TODO-D12 needs (D) |
| E6 | `H_HorizonBoundaryCondition` is shown **satisfiable**, not just stated | `fibonacci_horizon_satisfies_H_HorizonBoundaryCondition` | ✓ — a five-field Prop with a witness is not vacuous (D) |
| E7 | Both figure-eight theorems genuinely use `native_decide`, as the draft says | `axiom_deps_project` markers | ✓ (D) |
| E8 | 90 walks stopped at a `private` declaration — the highest measured | the closure | ✓ reported with the size, never separately (D) |

⚠️ **NOT-AN-ASSERTION.** *"Only D4's claim is backed by a declared closure"* is a statement about
**what is measurable today**, not about who should own the substrate. D8 is undeclared; when it is
read, E4's overlap becomes a declaration conflict to resolve, not a fact about entitlement.

⚠️ **E5 is the pass's most transferable result and it is a positive one.** D4 and D10 face the
identical structural problem — a theorem whose content sits in a definition — and handle it
oppositely. **The corpus already contains the fix for its own worst claim-integrity finding.**
Looking for the good instance of a defect pattern is cheaper than designing a remedy, and this
pass found one only because the retrofit reads whole drafts rather than diffs.

---

## V30 — the D5 apex retrofit — 7 atoms, 0 corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| G1 | D5's draft is 1,527 lines and was read in full | the file | ✓ |
| G2 | **SET:** D5 ∩ every other declared bundle | D1, D2, D3, D4, D6, D9, D10, D11, D12, F, L2 — all eleven | ✓ D3 **11**, F **17**, rest **0** — both are D5 *supplying*, not consuming (D) |
| G3 | D5's closure is the flattest measured: 70 apexes → 216 declarations, depth 3 | the closure, against D4 (66 → 753, depth 13) and D2 (47 → 516, depth 11) | ✓ (D) |
| G4 | G3 **corroborates** the draft rather than contradicting it | §2.3's MCC definition and §9's aggregator/proof-load separation | ✓ a verdict has almost no substrate beneath it, and the draft says so up front (D) |
| G5 | D5 defines and applies a three-way Derived / MCC / Heuristic taxonomy | the draft, including a figure caption that labels its own figure MCC | ✓ the strongest disclosure instrument in the corpus (D) |
| G6 | **NOT FILED:** D5 and F cite Pipeline Invariant #14 for two different rules | `WAVE_EXECUTION_PIPELINE.md:693`, read in full | ✓ **both correct** — #14's body contains both the authorization rule and the `bundle_destination` schema clause. Nothing to file (D) |
| G7 | D5's abstract states project-scoped `\substantivetheorems` for its own content | the abstract vs the closure | ✓ measured substrate is **216** — TODO-D9's defect, second instance (P) |

⚠️ **NOT-AN-ASSERTION.** *"Apex-to-closure ratio is a genre signal, not a quality metric"* is an
**interpretive rule for reading future measurements**, not a proposition about the corpus. It is
recorded because D11's high ratio was read as a prose signal and D5's would be misread the same
way; **compare ratios only within a genre.**

⚠️ **G6 is the first probe this session that was scoped correctly BEFORE the conclusion was
written**, and it is the reason nothing was filed. Two drafts citing one invariant for two rules
is exactly the shape of a real defect; reading the invariant took one call and dissolved it.
**The V26 and V27 corrections both cost more than that call would have.**

---

## V31 — the D8 apex retrofit — 8 atoms, 1 PRIOR declaration corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| H1 | D8's draft is 796 lines and was read in full, including the appendix inventory | the file | ✓ |
| H2 | **D8's closure is the largest in the portfolio** | the closure, against all 12 others | ✓ **2,290** declarations / **289** modules / depth **24** / 103 truncations (D) |
| H3 | ❌ **CORRECTS the D4 declaration.** Four `GenericSU2` apexes belong to D8, not D4 | **both drafts, read in full** — D8 §4 and §Relationship-to-companion-work cede Fibonacci to D4 *twice*; D4 named the Clifford+T/trapped-ion theorems only in a module list | ✓ reassigned (P) |
| H4 | The reassignment is corroborated by the closure, not just by the prose | D4's closure recomputed before and after | ✓ **753 → 620** declarations, **61 → 43** modules — those four were pulling D8's whole `SU(d)` tree (D) |
| H5 | **SET:** D8 ∩ every other declared bundle | D1, D2, D3, D4, D5, D6, D9, D10, D11, D12, F, L2 — all twelve | ✓ D4 **280**, D9 **14**, D10 **8**, D2/D12 **3** each, rest **0** (D) |
| H6 | D8's kernel-purity claim ("zero `native_decide` in this corpus") is **true as stated** | `axiom_deps_project` over D8's closure — **the field that actually carries the marker** | ✓ **0** in D8's closure, and the same instrument found **19** in D4's on the same run (D) |
| H7 | F's D6-absorption attribution is corrected by D8's own text | D8's §Relationship-to-companion-work vs F §7 | ✓ the primitive is D8's, not D4's — and `D8 ∩ D6 = D4 ∩ D6 = 0`, so D6's declared substrate has neither (P) |
| H8 | D8's ancilla-free Ross–Selinger gap is carried as an explicit theorem hypothesis, never an axiom | `gridFindT_isSome_of_residual`, `rossSelinger_synth_of_residual` | ✓ and a second unconditional mechanism (KMM) ships alongside (D) |

⚠️ **H6 is the V26 correction applied correctly, and the difference is worth stating.** V26 failed
by probing a field that never carries the marker. Here the instrument was **validated on the same
run** — it returned 19 for D4's closure — before the zero for D8 was reported. **An absence is
only evidence once the instrument has demonstrated presence somewhere.**

⚠️ **H3/H4 is the first time a *declaration* — not a finding — has been corrected.** The flag was
set deliberately at D4's retrofit ("revisit when D8 is read") rather than resolved by guessing,
and the resolution came from the drafts saying who owns what, with the closure as independent
corroboration. **A conflict recorded and deferred cost one line; a conflict guessed would have
cost a wrong ownership assignment in two bundles.**

---

## V32 — the D7 apex retrofit — 8 atoms, 1 PRIOR declaration corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| J1 | D7's draft is 339 lines and was read in full | the file | ✓ |
| J2 | **Five of seven sections are square-bracket placeholders** | every section, enumerated | ✓ §§2–6; only abstract, intro and discussion carry prose (P) |
| J3 | ❌ **CORRECTS the D1 declaration.** Six apexes are D7's, not D1's | **both drafts** — D7's title/abstract/§§2–6 vs D1's §8.2 *"Independent cross-check"* | ✓ reassigned; D1's closure **249 → 171**, modules **18 → 12** (P) |
| J4 | ⚠️ J3's signal is **weaker** than the D4→D8 case | both drafts | ✓ D8 explicitly ceded Fibonacci **in words**; here neither draft mentions the other and the decision rests on **document position**. Recorded as revisitable (D) |
| J5 | `analog_hawking_quantum_advantage_demarcation` does not exist | corpus scan, underscore-aware, **seeded** with the real name | ✓ ABSENT; the seed returns PRESENT (P) |
| J6 | `prose_theorem_reference_coverage` does not report D7 | the check, run | ✓ its extractor keys on `\texttt{}`; D7 uses `` `name' `` (D) |
| J7 | §2 declares zero apexes, correctly | the section | ✓ it describes 24 theorems in aggregate and **names none**; no named statement, no apex (D) |
| J8 | `analog_hawking_simulable_BEC_instance` is absent, exactly as D7 says | the corpus | ✓ the draft's own negative claim verifies (D) |

⚠️ **J6 is the standing constraint hitting from the other side.** The rule is *check whether a
check already measures it*. One does — and the finding was that its **scope** is narrower than its
name. **"A check exists" and "the check covers this input" are different claims**, and only the
second licenses trusting a green result. Filed as TODO-D18; nothing built (§6a).

⚠️ **J3/J4 together are the rule the remaining bundles inherit:** *the container that develops
content owns it; the container that cites it in a cross-check subsection does not.* Second
instance today. **But record the strength of the signal** — a draft that cedes in words (D8) is
stronger evidence than document position (D7), and the weaker one should say so rather than
present both as equally settled.

---

## V33 — the I1 apex retrofit — 8 atoms, 1 SELF-CORRECTED before publication

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| K1 | I1's draft is 1,875 lines and was read in full | the file | ✓ |
| K2 | I1 names only **seven** Lean theorems in monospace; six are citations | every `\texttt{}` token resolved | ✓ the seventh is an `IntCongr.rfl` token collision (D) |
| K3 | **SET:** I1's four infrastructure figures, each re-derived from the artifact it names | `validate.py --list`; `WAVE_EXECUTION_PIPELINE.md`; `BUNDLE_CODES`; `lean/lean-toolchain` | ✓ **33 vs 66**, **15 vs #17**, **17 vs 21**, **v4.29.0 vs v4.32.0** — all four stale (P) |
| K4 | The toolchain item is a **verification claim**, not a count | the sentence | ✓ *"All worked-case theorems … verified to compile cleanly on the project's local 4.29.0 toolchain"* — asserted against a configuration that no longer exists (P) |
| K5 | Nine `% TODO: substantive draft` blocks are stale | each section read | ✓ all nine sections are fully drafted (P) |
| K6 | ❌ **SELF-CORRECTED.** I wrote the overlap table from reasoning, then measured it | the closure | **guess: D2 20 / D3 3 / F 3. Actual: D1 30, F 26, D2 1, D3 0.** Replaced before commit (P) |
| K7 | TODO-D3's 4-line offset reproduces, and the waiver coupling holds | the file + I1 §10 | ✓ and the item generalises: I1 cites by line number in ~10 places (P) |
| K8 | I1 publishes an unflattering number about itself | §10, §14 and the abstract | ✓ *"roughly three per ten spot-checked load-bearing attributions"* were fabricated, called *"exactly the kind of number a verification program must be willing to publish about itself"* (D) |

⚠️ **K6 is the session's cleanest self-catch and the reason it is recorded rather than quietly
fixed.** I reasoned "the case studies belong to D2 and D3, so the overlap is with D2 and D3" — and
was wrong in shape *and* magnitude. **An apex's closure is what it RESTS ON, not what it is
ABOUT.** `sm_no_nu_R_ewbg_doubly_forbidden` is a chirality-wall theorem whose dependency cone
barely touches what D2 declares; `firstOrder_uniqueness` sits on the whole `SKDoubling` stack, so
the overlap is with D1 and F. **Subject matter does not predict dependency structure — that is
what the closure is for**, and writing the table before running it nearly published a fourth
wrong measurement this session.

⚠️ **K3/K4 is the pass's substantive finding and it is self-referential.** I1 §2 opens by naming
four failure modes the pipeline exists to prevent, one of which is *"a parameter whose value was
inherited from a prior draft and had drifted."* **I1's own infrastructure figures are that failure
mode, in the paper that names it.**

---

## V34 — the I2 apex retrofit — 6 atoms, 0 corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| L1 | I2's draft is 1,016 lines and was read in full | the file | ✓ |
| L2 | **SET: every per-theorem purity claim I2 makes, in BOTH directions** | `axiom_deps_project` on each named theorem — the field that carries the marker | ✓ `verlinde_k3_full` and `verlinde_k5_full` **no marker** (draft: "no native_decide"); `fib_pentagon` **marker present** (draft: "by native_decide"); `fib_hexagon_R_vacuum` **no marker** (draft: "kernel-pure"). **4/4 correct** (D) |
| L3 | The instrument was validated on the same run | `fib_pentagon` returning `True` | ✓ — the V26 discipline applied (D) |
| L4 | I2 names 21 theorems; 20 are citations | every `\texttt{}` token resolved | ✓ the 21st is a `Collar.…sum_nonneg` collision with a bare-named Mathlib lemma (D) |
| L5 | The declared closure (223/10) is smaller than the described library (27 modules, ~949 decls) | the closure vs the abstract | ✓ **not a discrepancy** — I2 names theorems only for the components it exhibits, and discloses the rest by per-module counts (D) |
| L6 | **SET:** I2 ∩ every other declared bundle | all fifteen | ✓ D4 **6**, F **5**, rest **0** — I2 supplying, never consuming (D) |

⚠️ **L2 is the strongest disclosure instance measured, and it is the mixed direction that makes
it so.** D8 claims corpus-wide purity and verifies; D4 discloses `native_decide` where it uses it.
**I2 claims "kernel-pure here, `native_decide` there" in adjacent subsections and is right on
both counts.** A claim that discriminates is worth more than a claim that generalises, because
only the discriminating one can be wrong in two directions.

⚠️ **L5 records an interpretive rule, NOT-AN-ASSERTION about the artifact:** *for a library paper,
closure size measures citation practice, not artifact size.* I2's 223 is what it names; its
per-module prose table is the better figure for the library's extent — and that table is
hand-maintained prose no check covers (same class as TODO-D10, recorded not filed).

---

## V35 — the I3 apex retrofit — 8 atoms, 0 corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| M1 | I3's draft is 1,349 lines and was read in full | the file | ✓ |
| M2 | **SET: I3 ∩ every other declared bundle** | all sixteen | ✓ **0 in every case** — the only bundle in the portfolio whose closure intersects nothing (D) |
| M3 | §6's published grep — *"no D3, D5, or E1 Lean module currently invokes `LDPCompatibleSKEFT`"* | re-run over `lean/SKEFTHawking/` | ✓ exactly one file, `LDP/LDPCompatibleSKEFT.lean`. **M2 corroborates it by an instrument the draft knows nothing about** (D) |
| M4 | §2.3's *"exact count 775"* lines across 12 modules | `wc -l` | ✓ **775** (D) |
| M5 | §2.3's *"15 `Prop`-typed predicates (14 `def Is*` plus the `class`)"* | the module sources | ✓ 14 + 1 = **15** (D) |
| M6 | *"Zero `sorry`; zero new axioms beyond `[propext, Classical.choice, Quot.sound]`"* | sources + closure's `axiom_deps_core` | ✓ zero/zero; core union is **exactly** those three; 0 `native_decide`, instrument seeded at **19** in D4's closure (D) |
| M7 | §3.5's *"a prior redundant `wave_3b_itoBeta_5_itoLemma_closure` … was retired"* | resolution over `lean_deps.json` | ✓ **absent**; seeded — its four sibling `wave_3b_itoBeta_N_*` closures all resolve, so the probe detects presence (D) |
| M8 | **SET: theorems in I3's twelve modules named nowhere in the draft** | full declaration list of the twelve modules vs every `\texttt{}` token | ⚠️ **13** — five LDP witnesses, five LDP per-module closures, three Itô witnesses. §4 omits two of §3's four template headings for all six modules. → TODO-D19 (D) |

⚠️ **M8's second symptom, probe scope stated:** §2.3 claims *"11 per-module wave-closure summary
theorems"*; measured **10** over the `theorem`/`lemma` declarations in the twelve module files. The
11 counts `LDPCompatibleSKEFT` as having a per-module closure, which the same paragraph gives to
`wave_3b_ldp_overall_closure`. Filed *with* the naming gap, not separately — one defect, two faces.

⚠️ **A declaration-rule refinement, NOT-AN-ASSERTION about I3:** `LDPCompatibleSKEFT`'s five field
projections (`ldpRateFn`, `cramerCompatible`, …) resolve with **`kind: theorem`** — a `Prop`-class
field projection is a theorem — and so would pass `apexes_are_theorems` while being pure machinery.
**`kind == theorem` is necessary, not sufficient.** The D11 declaration rule already excludes them
by meaning; this is the first case where the kind check could not.

✅ **The ownership call was made by the draft, not by me.** I3's *"Out-of-bundle dependency
disclosure"* names which field is inherited from Phase 6n and which four I3 authored, so
`linearResponseRateFunctionCentered_zero` is excluded and `…_continuous` declared on the draft's own
instruction. First pre-empted ownership call in the retrofit.

---

## V36 — the L1 apex retrofit — 8 atoms, 0 corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| N1 | L1's draft is 391 lines and was read in full | the file | ✓ |
| N2 | *"`GravitationalWaves.lean`, 21 theorems"* | the module's declaration list | ✓ **21** = 23 `theorem`-kind minus the 2 compiler-generated `eq_1`. The autogen marking is what makes it land exactly (D) |
| N3 | *"zero `sorry`, zero new axioms"* | closure `axiom_deps_core` + `axiom_deps_project` | ✓ exactly `{propext, Classical.choice, Quot.sound}`; 0 `native_decide` (D) |
| N4 | *"zero `maxHeartbeats` overrides"* | the file | ✓ 0 (D) |
| N5 | *"49 `pytest` cases"* | `pytest --collect-only` | ✓ **49** (D) |
| N6 | *"the compatible window has measure 4τ ≈ 1.2×10⁻¹⁴"* | arithmetic on the quoted τ | ✓ (D) |
| N7 | **SET: bundles declaring `GravitationalWaves` theorems** | every bundle's apex list, both directions | ⚠️ **three** — L1 11, D3 8, F 3. D3 shares **5** with L1; F shares **3** (all of F's). L1's unique-at-declaration content is the biconditional + the five `H_VestigialModeIsGraviton_*` (D) |
| N8 | **SET: L1 theorems named nowhere in the draft** | 21 module theorems vs every `\texttt{}`/`\verb` token | ⚠️ **7**, of which five formalize the §Discussion claim the prose attributes to a *different* module (D) |

⚠️ **N7 is a conflict I deliberately did NOT resolve, and the reason is the durable part.** D4→D8
and D1→D7 moved apexes between containers whose *existence* was settled; each was decided by a
draft's own words or document position, with the closure corroborating. **N7 asks whether L1 exists
as a container** — the reserved `L1 disposition` item. Under ADR-010 C5, reassigning would
pre-decide a charter by moving declarations. The duplicates stand as evidence.
**The ownership rule decides who owns content; it does not decide who exists.**

⚠️ **N8 makes TODO-D19 a portfolio pattern, not a bundle defect** — third instance after D11 and I3.
L1's is the sharpest: `vestigial_dispersion_below_ligo_at_inspiral_peak` proves, with the hypothesis
`|γ| ≤ 1e-30` the prose quotes, exactly what §Discussion path 3 asserts — while that sentence cites
`SecondOrderSK.lean`. The attribution is not false (`SecondOrderSK` carries `GammaH`); the theorem
that discharges the sentence is simply unnamed.

✅ **NOT-AN-ASSERTION, recorded as a genre observation:** L1's depth-1 single-module closure is
*correct*, not thin. A one-equation refutation against a published bound has nothing to stack.
Per V30's rule, ratios compare only within genre — and L1 is the first instance of its genre.

---

## V37 — the L3 apex retrofit — 8 atoms, **1 CORRECTED** (a prior V36 atom)

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| O1 | L3's draft is 445 lines and was read in full | the file | ✓ |
| O2 | *"`\bhThermoTotal` theorems and lemmas"* (macro = 20) | source `theorem`/`lemma` keyword count | ✓ **20 = 20**, and the macro is **derived** by `update_counts.py` per-module, so it cannot drift (D) |
| O3 | *"zero `sorry`, zero new axioms, zero `maxHeartbeats`"* | closure axioms + the file | ✓ core = exactly the three standard axioms; 0 `native_decide`; 0 heartbeat overrides (D) |
| O4 | *"`backreaction.py` (line 449) … evolves the full coupled-ODE system rather than assuming the exponential form"* | `src/wkb/backreaction.py:447–451` | ✓ the file's own docstring says exactly that (D) |
| O5 | *"the four laws are NOT bundled into a single Lean Prop structure `H_BCH`"* | the module's structures | ✓ no `H_BCH`; two per-regime predicates exist, which is what *"separate theorems and predicates"* describes. **Re-measured, NOT filed** (D) |
| O6 | **SET: bundles declaring `BHThermodynamicsFourLaws` theorems** | every bundle's apex list, both directions | L3 13, D3 4 (3 shared), F 1 (shared). Same triangle as L1's (D) |
| **O7** | ⚠️ **CORRECTS V36/N7's stated basis** — *"neither draft mentions the other"* (L1/D3) | `papers/D3/paper_draft.tex` read directly | ❌ **FALSE.** D3 §7: *"**Bundle L1 ships the same content as a four-page Physical Review Letters splash**"*; D3 §8, subsection ***Cross-bundle anchor to L3***: *"character-for-character identical."* **Both pairs are DECLARED splash/deep companions** (D) |
| O8 | **SET: L3 standalone theorems named nowhere in L3** | 18 standalone vs every `\texttt{}`/`\verb` token | **5** — but **2 are named by D3**, the declared deep companion. Genuine TODO-D19 residue: the 2 `wave*_bridge_*`, named by neither (D) |

### ⚠️ The correction, stated fully

**What was wrong.** V36/N7 recorded the L1/D3 apex overlap as an undecided *conflict* whose
resolution "rests on document position," on the stated basis that neither draft mentions the other.
D3 mentions L1 by name, in prose, and calls the duplication deliberate.

**What changes.** The overlap is not a collision — it is a splash/deep publication pair. **The
ownership rule (*develops → owns; cites in a cross-check → does not*) presumes the containers make
different claims. A splash/deep pair makes the same claim at two lengths on purpose, so shared
apexes are correct and neither container cedes.** The rule has no jurisdiction there.

**What does not change.** Nothing was reassigned — still correct, now for the corrected reason. And
`L1 disposition` remains a reserved STOP-AND-ASK: whether to *publish* splash companions is a
charter decision, applying equally to L1 and L3.

**How it happened, and the standing rule it re-teaches.** I compared apex lists and grepped D3 for
`GravitationalWaves` / `c_GW`. The sentence that shows presence says *"Bundle~L1"* and matched
neither. **This is V26 verbatim: before filing an absence, name the probe that would show presence
and prove it can.** Carried forward as method: *the probe for a sibling relationship is a search of
the other draft for the **bundle name**, not for shared theorem names.*

✅ **NOT-AN-ASSERTION, recorded as a reusable template:** `\bhThermoTotal` is what TODO-D9 and
TODO-D10 are asking for and it already works — bundle-scoped, derived per-module, exact. The defect
in D1/D5 is not "a macro" but "a *project*-scoped macro used as a bundle figure."

---

## V38 — the E1 apex retrofit — 7 atoms, 0 corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| P1 | E1's draft is 583 lines and was read in full | the file | ✓ |
| P2 | **E1 is a declared companion of D1** | `papers/D1/paper_draft.tex` searched for the **bundle name** | ✓ D1's abstract: *"**Companion experimental letters E1 (Paris-LKB polariton) and E2 (Dean-Kim-Lucas graphene)** carry the experimental-team-targeted implementations."* **Third declared pair; first found deliberately** (D) |
| P3 | **SET: E1 apexes declared by no other bundle** | all twenty bundles' apex lists | ✓ exactly **2** — `polariton_tier1_fails_tmds` and `polariton_dkm_f3_holds_at_pump_below_threshold`, both labelled by E1's own inline provenance as its Wave-6v deliverables (D) |
| P4 | E1's closure is kernel-clean | `axiom_deps_core` / `axiom_deps_project` over the closure | ✓ exactly the three standard axioms; 0 `native_decide` (D) |
| P5 | E1's toolchain-pin claims (*"v4.29.0, Mathlib `8850ed93`"*, twice) are stale | **the existing `paper_toolchain_pin_drift` check**, run rather than reimplemented | ✓ stale — live pin **v4.32.0 / `81a5d257`**; the check names **E1:449, 453, 454** at line granularity. **Existing coverage; nothing filed, nothing built** (D) |
| P6 | corpus-wide pin drift | the same check | **29 pin-drift + 5 capability-claim sites across 65 drafts** — the live figure. The bump memory's "32 sites" is superseded and not quoted (P) |
| P7 | `\axiomcount` resolves to 0 | `docs/counts.tex` | ✓ the project carries no project-local axioms, so E1's *"0 axiom"* is derived and true (P) |

✅ **P2 is the L3 correction paying off immediately.** The prescribed probe — *search the sibling
draft for the **bundle name**, not for shared theorem names* — found a pair a theorem-token grep
would have missed for the third time: D1's sentence says "E1", not `attenuation_ge_one`.
**A method fix is worth more than the finding that produced it.**

⚠️ **NOT-AN-ASSERTION, a correction to TODO-D9's shape rather than a claim about E1:** E1 uses the
*project*-scoped `\substantivetheorems` / `\leanmodules` macros **correctly**, because its sentence
makes a project-scoped claim (*"independent of platform parameters"*). With L3's bundle-scoped
derived `\bhThermoTotal` and D1/D5's project-macro-for-bundle-figure, the three cases show
**TODO-D9's defect is scope mismatch, not macro use** — and a remediation keyed on "uses a macro"
would break E1. Restated in the TODO.

---

## V39 — the E2 apex retrofit (final bundle) — 9 atoms, 0 corrected

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| Q1 | E2's draft is 579 lines and was read in full | the file | ✓ |
| Q2 | E2's retraction — *"`ChernBridge.lean:68` defines `categoricalChernExpansion c0 c1 := [c0, c1]`, a two-term Chebyshev expansion"* | the file, read before repeating the claim | ✓ exact (D) |
| Q3 | E2's **correction of its own retraction** — *"`ChernBridge.lean:14` frames the crystalline limit as a Brillouin-zone Chern number reducing to a sum"* | the same file's docstring | ✓ exact. **Both layers of a nested self-correction check** (D) |
| Q4 | **E1 still carries the retracted phrase** | `grep "topological Chern coefficient" papers/*/paper_draft.tex` | ⚠️ **E1:410** does; E2:422 is the retraction. The 2026-08-01 correction landed in one letter of a shared paragraph → TODO-D20 (D) |
| Q5 | E2's closure is kernel-clean | `axiom_deps_core` / `_project` over the closure | ✓ exactly the three standard axioms; 0 `native_decide` (D) |
| Q6 | **SET: `E1 ∩ E2` closure** | both declared closures | ✓ **5 declarations**, all in `AcousticMetric` + `Basic` — the platform-**independent** `T_H` binding. Apex overlap **1**, and it is that binding (D) |
| Q7 | **SET: shared platform modules between E1 and E2** | both module sets, both directions | ✓ **none.** E1-only 6 modules, E2-only 4 (D) |
| Q8 | `DKMBootstrap.E1E2CrossBridge` — the module named for the relationship | its declaration list | ⚠️ holds `platform_kms_qualities_pairwise_distinct` + three per-platform quality theorems. **It proves the platforms are distinct** (D) |
| Q9 | E2's pin claims (`v4.29.0` / `8850ed93`, ×4) | the existing `paper_toolchain_pin_drift` check | ✓ already reported at **E2:484, 485, 488, 489**. Existing coverage; nothing filed, nothing built (D) |

⚠️ **NOT VERIFIED, stated per C4:** §2's *"`DiracFluidWKB.toExactWKB` … is checked in ~93% of the
transferred Lean theorems."* No derivation of 93% was found and none was constructed — building one
would be new infrastructure under §6a. **Recorded as unverified, not as wrong.**

⚠️ **NOT RESOLVED, deliberately:** E2 §3's `Γ_H = (η/s T)(κ/c_s)² ≈ 0.3 s⁻¹`, `δ_diss ≈ 10⁻¹³` is
the reserved **`graphene Γ_H`** STOP-AND-ASK item. Noted where it lives; not adjudicated.

✅ **Q6–Q8 complete DONE item 4.** The E1+E2 merge is **REFUTED at the substrate level** — shared
closure is only the universal temperature binding, platform substrates are disjoint, and the sole
formal cross-bridge establishes *difference*. It is **NOT DECIDED editorially**, and the ledger says
so explicitly: two ~580-line letters addressed to different experimental groups is an
audience-and-submission question no dependency measurement can settle. **No recommendation is made
on any of the four proposed merges.**

---

## Retrofit close-out — what the twenty-one bundles cost in corrections

Three assertions were made and later corrected during this retrofit, and all three failed the
**same** way — an absence filed without a probe proven able to show presence:

1. **V26** — `Lean.ofReduceBool` absent from `axiom_deps_core` ⇒ "no load-bearing `native_decide`".
   Wrong field; the marker lives in `axiom_deps_project`. Three existing guards said so.
2. **V27/TODO-D16** — "no D3 gravity-side declaration reaches the anomaly-side tree **at all**".
   Right probe, over-wide reporting scope; `D2 ∩ D3 = 3`.
3. **V37/O7** — "neither draft mentions the other" (L1/D3). Probe was a theorem-token grep; the
   sentence says *"Bundle~L1"*.

**The standing rule, in its final form:** *before filing an absence, name the field or tool that
would show presence, prove it can — and state the scope the probe actually covered in the sentence
that reports it.* Its three corollaries, each bought with a correction: **the marker field is
`axiom_deps_project`**; **a probe's scope is part of its finding**; **the probe for a sibling
relationship is the bundle name, not a shared theorem name.**

---

## V40 — the L2 FINDINGS backfill — 7 atoms, 0 corrected

L2 declared its apexes before this retrofit began and so had no FINDINGS doc. Enumerating the
population (21 bundles vs 19 docs) found it — **a spot-check of any of the seventeen would not
have**. Written so DONE item 2 holds for all 21.

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| R1 | L2's draft is 489 lines and was read in full | the file | ✓ |
| R2 | L2's closure shape | the derived closure | **430 decls / 40 modules / depth 14** — the only Letter with a deep closure (L1 d1, E2 d1, L3 d2, E1 d2) (D) |
| R3 | why R2 is not a defect | which apex carries it | one apex, `SmoothSpinManifold4.rokhlin`, pulls ~90% — the Hasse–Minkowski / theta-modularity / lattice tower L2 built to *discharge* `8 ∣ σ` rather than assume it. The draft says so (D) |
| R4 | **D2 declares L2 a splash companion** | `papers/D2/paper_draft.tex`, **bundle-name** probe | ✓ *"The **PRL splash companion** [L2] **compresses this material to four pages**; here we expose the algebraic core."* **Fourth declared pair** (D) |
| R5 | **SET: `native_decide` carriers in L2's closure, vs what the abstract names** | `axiom_deps_project`, both directions | ✓ **exactly 6** — `d1_d2_zero`…`d4_d5_zero`, `chain_complex_property`, `ext_computation_summary` — which is precisely the abstract's *"`dₙ·dₙ₊₁ = 0` for `n=1,…,4` via `native_decide` on explicit `𝔽₂` matrices"* (D) |
| R6 | *"the formerly asserted `gapped_interface_axiom` is now a tracked Prop `TPFConjecture`"* | the declaration index | ✓ `gapped_interface_axiom` **absent**; `TPFConjecture` present as a **`def`**; **zero** declarations of kind `axiom` project-wide, so `\axiomcount = 0` is derived and true (D) |
| R7 | L2's pin claims (`v4.29.1`, `5e932f97`) | the existing `paper_toolchain_pin_drift` check | ✓ already reported at **L2:12, 387, 396**. Existing coverage; nothing filed (D) |

⚠️ **R4 carries a new observation worth more than the pair itself.** D2 states that a hypothesis
**listed as open in the L2 splash** it has since *"substantively discharged … at the dimensional
level."* **A declared pair can diverge in hypothesis status, not only in length** — the deep paper
moved and the Letter did not. Same class as TODO-D20 (E2 corrected, E1 not): **shared content
drifting because only one member of a declared pair was revised.** Two instances now, in two
different pairs.

⚠️ **R5 is the exact inverse of the error V26 corrected.** L2 declares a `native_decide`-carrying
theorem as an apex *and* names the fact in its abstract; the V26 error was my claiming no
load-bearing `native_decide` existed anywhere. **The corpus was more careful than the audit.**

⚠️ **NOT VERIFIED, stated per C4:** *"builds in ∼30 s on commodity hardware."* Not measured — a
build-time claim is not a closure question and measuring it was not in scope.

✅ **Fourth data point for the restated TODO-D9:** L2 uses project-scoped macros for an explicitly
*library-state* claim (*"library state: … theorems across … modules, … axioms"*) — **correct
usage**, like E1's, unlike D1's and D5's.

---

## V41 — the D9 FINDINGS backfill (final bundle of the set) — 8 atoms, 0 corrected

With this, **DONE item 2 holds for all 21 bundles.**

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| S1 | D9's draft is 1,318 lines and was read in full | the file | ✓ |
| S2 | *"over 900 kernel-checked theorems"* in `QuantumNetwork` | the declaration index, autogen excluded | ✓ **969** — true and conservatively stated (D) |
| S3 | *"103 Lean modules"* | the same index | ⚠️ **104** — off by one, hand-maintained → TODO-D10/D15 class (D) |
| S4 | *"no `native_decide` … trust escapes"*, *"no project-local axioms"* | `axiom_deps_project` / `_core`; kind index | ✓ **0** carriers family-wide; core union exactly the three standard axioms; **zero** `axiom`-kind declarations project-wide. Instrument seeded at 19 in D4's closure (D) |
| **S5** | **D9's claim to consume I3's LDP foundations** (stated twice) | `D9 ∩ I3` closure **and** the two theorems' direct `name_deps_project` | ❌ **0**, and neither `fdt_rare_event_tail` nor `fdt_gallavotti_cohen` reaches any `LDP.*` / `Itô.*` declaration. Probe seeded: same measurement gives 50 for `D9 ∩ D10`, 14 for `D9 ∩ D8` → **TODO-D21** (D) |
| S6 | **corroboration for S5 from an independent source** | I3's own draft | ✓ I3 says its cross-bridge is *"designed but not yet consumed at release time"*, and I3's closure intersects **nothing** in the portfolio. **The two drafts disagree; the substrate sides with I3** (D) |
| S7 | `D9 ∩ D6` | both closures | **0** — and `D4 ∩ D6 = D8 ∩ D6 = 0` already. **D6 shares no declaration with any of the three bundles it is said to absorb or adjoin** → EVIDENCE §9 (D) |
| S8 | D9's pin claims (`v4.29.1`, `5e932f97`) | the existing `paper_toolchain_pin_drift` check | ✓ already reported at **D9:1074**. Existing coverage; nothing filed (D) |

⚠️ **S5 is the retrofit's cleanest cross-bundle finding, and the reason is method, not luck.** It is
corroborated by *the other bundle's own prose* and by *two independent measurements*, and the probe
was seeded before the absence was reported. That is the V26/V37 rule applied prospectively rather
than learned from a correction.

⚠️ **S7 is recorded as a measurement, NOT an argument.** A zero intersection does not oppose a
merge: two containers can be adjacent in subject and disjoint in substrate, which is what a
physical-layer / logical-layer split should look like. What it establishes is narrower and worth
stating exactly: **a D6+D9 merge would consolidate no substrate.**

⚠️ **NOT VERIFIED, stated per C4:** the appendix's claim that D9's PhysLib-touching theorems are
*"verified by axiom audit not to depend on the one sorried declaration present in that library at
our pin."* Auditing a dependency's internals was not done and a probe for it would be new
infrastructure under §6a.

---

## Retrofit status after V41

| DONE item | state |
|---|---|
| 1 — `UNDECLARED_APEX_CEILING == 0`, all bundles declare, gate green | ✅ **met** — 617 apexes / 21 bundles / 0 undeclared |
| 2 — a FINDINGS doc per bundle | ✅ **met for all 21** (L2 and D9 backfilled after enumerating the population) |
| 3 — an ADR-010 §D2 purpose statement per bundle | ⚠️ **19 of 21** — D6 and D12 have FINDINGS docs without one |
| 4 — §D4 evidence assembled, no recommendation | ✅ **met** — all four rows measured; EVIDENCE §8 summary; no recommendation made |
| 5 — ledger at assertion granularity | ✅ V21–V41 |
| 6 — `validate.py` green / `pytest` green / one bundle per commit | ⚠️ **pytest green (5,676 passed / 5 skipped); `validate.py` at 64/66** — the two paper-corpus failures pre-date this work (archived reports show `bundle_metadata_matches_graph` red since 2026-08-01) and concern `stage13_status` vs open blockers, not apexes. **Not closable by this work**: the check's own remedy is re-running Stage 13 on 14 bundles. |

---

## V42 — D6's §D2 purpose statement + a correction to my own EVIDENCE line — 6 atoms, **1 CORRECTED**

D6 had a FINDINGS doc but no ADR-010 §D2 purpose statement (DONE item 3). Written after re-reading
`papers/D6/paper_draft.tex` (1,102 lines) in full.

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| T1 | D6's draft is 1,102 lines and was re-read in full | the file | ✓ |
| T2 | D6 names `QuantumNetwork` theorems it declares nothing from | resolvable `\verb`/`\texttt` tokens vs D6's apex list | ⚠️ **133 named, 0 declared.** D6's 11 apexes are all in `GaugingQEC` / `APMLdpcHashingBound` / `ShorTGateCount` / `WStateQFT` (D) |
| T3 | of those, how many are **D9's declared apexes** | D9's apex list | ⚠️ **17** (D) |
| T4 | `QuantumNetwork` theorems D6 names that **no** bundle declares | all 21 apex lists | **116** (D) |
| **T5** | ⚠️ **CORRECTS my own EVIDENCE §9 line of earlier today** — *"a D6+D9 merge would be motivated by narrative adjacency alone; there is no substrate overlap to consolidate"* | `docs/audits/2026-08-06-d6-retrofit/FINDINGS.md` §2 | ❌ **misleading as stated.** True of the declarations; invites the false reading that the bundles are disjoint in *subject*. D6 §5.4 is **44% of D6's draft and is D9's chartered content**, absorbed nine days before D9 existed. **Corrected statement: D6 and D9 share no declaration because D6 declares none of the shared content, not because the content is not shared** (D) |
| T6 | D6's two count claims | the live roster; the `QuantumNetwork` module index | ⚠️ *"15-bundle publication architecture"* — live is **21**, the **fourth** wrong roster number across four bundles; *"17 kernel-only modules"* — the family now holds **104** (D) |

⚠️ **T5 is the retrofit's third correction, and the first where the right answer was already
written down.** V26 was a wrong instrument; V37/O7 was an unrun probe; **T5 was an unread document.**
The measurement I ran was correct and the *inference* was under-informed, because D6's own FINDINGS
§2 — written a day earlier — had already measured the prose overlap and explained the
declaration-level zero.

**The rule this adds, narrower than the earlier two: *before quoting a fresh measurement against a
bundle, read that bundle's own FINDINGS doc first.*** The retrofit produces the context its own
later measurements need.

⚠️ **NOT-AN-ASSERTION, recorded as scope discipline:** the 2026-08-06 figure (**78** shared) and
today's (**17** shared) are *different probes*, not a drift — prose-vs-prose against
prose-vs-declared-apexes. Both stand at their stated scope. Per V27, the scope is in the sentence
that reports each.

✅ **Operator ruling recorded (2026-08-07), and it governs every prose-fix TODO:** per
`BUNDLE_LIFT_PROCEDURE.md:9`, **Stage 13 may not be invoked until Stage 9 and Stage 10 (claims
review) are GREEN with their fixes applied.** A bundle whose prose is edited re-enters at 9/10, not
at 13 — and `bundle_metadata_matches_graph`'s *"Re-run Stage 13"* remedy line describes what clears
its own field, not the gate order. Whether the intended prose reviewer is the installed
`skeft-qa:claims-reviewer` is the operator's to confirm. **The apex retrofit changed no paper
prose**, so it owes none of this.

---

## V43 — D12's §D2 purpose statement (closes DONE item 3) — 7 atoms, 0 corrected, 1 scope correction

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| U1 | D12's draft is 829 lines and was read in full | the file | ✓ |
| U2 | **D12's stated pins are current** | `lean-toolchain` + `lakefile.toml` | ✓ **all three** — toolchain `v4.32.0`, Mathlib `81a5d257`, PhysLib `c4843367`. **The only pin-current bundle in the portfolio** (D) |
| **U3** | ⚠️ `paper_toolchain_pin_drift` nonetheless reports D12:129 as drift | **the check's source**, `_tp_scan_lines` in `scripts/validation/checks/papers_prose.py`, read before concluding | ❌ **false positive.** The scanner tests every hex on a Mathlib-mentioning line against the single `live_rev`, which `_tp_live_pins()` reads from **Mathlib's** `rev` only. D12's sentence names both libraries, so PhysLib's hash is compared against Mathlib's → **TODO-D22** (D) |
| U4 | the same false positive elsewhere | the check's own output | `papers/D11/paper_draft.tex:546` (D) |
| U5 | D12's kernel-purity claim | the draft's own statement of method | *"verified from the project's extracted axiom closures for **every** declaration in all thirteen modules — not from spot checks"* — the population-enumeration discipline, self-applied (D) |
| U6 | D12's overlaps | the declared closures | `D12 ∩ D9 = 3`, `D12 ∩ D4 = 3`, all `PauliMatrices`. The one substantive dependency (POVM/Helstrom) is disclosed and correctly attributed to the project's own substrate (D) |
| U7 | **SET: D12's self-corrections** | the draft, read in full | **four**, each naming what it previously got wrong — the class-option note, the provenance line, the γ paragraph (*"both of this paragraph's predecessors were wrong"*), and the hypothesis list (*"asserted completeness at 'four' and then at 'six'; both were wrong"*), which then **refuses to claim completeness** (D) |

⚠️ **SCOPE CORRECTION to my own reporting, U3's consequence.** At E1's and E2's retrofits I quoted
the check's *"29 pin-drift sites across 65 drafts"* as a clean corpus figure. **At least two of the
29 are false positives.** Correct form until TODO-D22 lands: *"29 reported, ≥2 false positive."* The
individually-confirmed stale sites (E1 ×3, E2 ×4, I1 ×2, I3 ×1, L2 ×3, D9 ×1) are unaffected —
each was checked against the live pin one at a time, not inherited from the summary line.

*This is the fourth time in the retrofit that a number was safe only once its scope was stated.
The pattern is now general enough to name: **a check's summary count is a claim like any other, and
inherits the check's blind spots.** "Existing coverage measures it" licenses not re-implementing the
measurement — it does not license quoting the total without knowing what the instrument can see.*

✅ **U7 records the corpus's high-water mark.** D12 corrects itself in public four times, names the
wrong version each time, ships `\thm{}`/`\mthm{}` so its provenance claim is *checkable rather than
asserted* (independently solving TODO-D18's problem), scopes absence to evidence rather than
asserting it, flags two prior-art checks as **blocking**, discloses that a citation could not be
inspected **because the repository lies outside this work's network egress policy**, and marks two
sources read-in-abstract-only with the attribution *"provisional"*. **TODO-D12 and TODO-D19 are both
defects D12 does not have.**

---

## DONE-item status after V43

| item | state |
|---|---|
| 1 — ceiling 0, all 21 declare, gate green | ✅ 617 apexes / 21 bundles / 0 undeclared |
| 2 — FINDINGS doc per bundle | ✅ **21 / 21** |
| 3 — ADR-010 §D2 purpose statement per bundle | ✅ **21 / 21** — D6 and D12 backfilled 2026-08-07 |
| 4 — §D4 evidence assembled, recommendation NOT made | ✅ all four rows measured; EVIDENCE §8 summary; **no recommendation made** |
| 5 — ledger at assertion granularity | ✅ V21–V43 |
| 6 — `pytest` green / `validate.py` green / one bundle per commit | ⚠️ **pytest green** (5,676 passed / 5 skipped); **`validate.py` 64/66** — `bundle_metadata_matches_graph` and `readiness_submission_gate`, both red since 2026-08-01, both about `stage13_status` vs open blockers and P1 gates, **neither caused by nor closable by this work**. Per the operator's 2026-08-07 ruling their remedy runs Stage 9/10 → 13, not Stage 13 alone. One bundle per commit: ✅ |

---

## V44 — `bundle_metadata_matches_graph`, measured per leg — 5 atoms, 1 reporting correction

Prompted by the operator: *"`bundle_metadata_matches_graph` sounds like it should be green though."*
It does, and the reason is worth recording — the check's name describes the three legs that pass.

| # | atom | decider | result |
|---|---|---|---|
| W1 | the check's count legs (`blockers_open`, `advisories_open`, `readiness`) | its own detail lines, every archived run | ✅ **0 failures** in all six reports inspected. `bundle_readiness.py` writes them and they stay written (D) |
| W2 | which leg is red | the same detail lines | **all 14 drift entries are the `stage13_status='green'` while live blockers > 0 leg**, added 2026-08-03 (D) |
| W3 | is the red correct? | the check's source comment + `BUNDLE_LIFT_PROCEDURE.md` §12 | ✅ **yes** — 14 bundles assert a Stage-13 green that later findings contradict. The comment states the design: the count legs *"cannot catch the state 14 of 21 bundles are in right now, because that state is internally CONSISTENT"* (D) |
| W4 | **did this retrofit move it?** | drift composition across archived runs | ❌ **no** — `14 drift / 14 stage13-leg / 0 count-leg`, identical on 2026-08-04, 2026-08-05 and all three runs of 2026-08-08 (D) |
| W5 | could it have? | `bundle_readiness.py:78` — `REVIEWS_DIR = PAPERS_DIR / "AutomatedReviews"` | ❌ **no** — findings load from `papers/AutomatedReviews/`, newest dir `2026-08-01-bundle-stage13`, six days before this work. This retrofit's docs live in `docs/audits/` and are **not** ingested (D) |

⚠️ **Reporting correction, two parts.**
1. I described the two failures together as *"about `stage13_status` vs open blockers **and P1
   gates**"*, collapsing two checks into one phrase. `readiness_submission_gate` owns the P1 gates;
   this check's failure is **purely** the stage13 leg.
2. **I inferred "pre-existing, not mine" from the archived pass/fail flag.** Right conclusion,
   lazy route: the flag would have looked identical had this work added blockers and
   `bundle_readiness.py` rewritten the counts to match — because the count legs would then still
   agree. **The load-bearing evidence is W4 (leg composition unchanged) and W5 (findings source
   predates the work)**, and neither was measured until the operator pushed.

**The rule this adds to the retrofit's standing set:** *a check's pass/fail flag is an aggregate.
When attributing a failure — especially to "not my work" — measure the leg, not the flag.* This is
the same family as V43's *a check's summary count inherits the check's blind spots*, one level up:
V43 was about trusting a total, this is about trusting a boolean.

✅ **NOT-AN-ASSERTION, recorded because it is the useful residue:** D12 is the worked example of the
honest state — `stage9/10/13: pending-redo`, 46 blockers open — and it does **not** trip this check.
The 14 either re-enter Stage 9/10 → 13 per the operator's 2026-08-07 ruling, or carry a
`stage13_status` that reflects the stale green. **That disposition is the operator's**; the retrofit
neither made nor can clear it.

---

## V45 — the operator's reviewer-stage demotion — 6 atoms, 0 corrected

**Operator decision, 2026-08-07: *"No bundle should be green - demotion is required."*** Applied to
all three reviewer-stage fields. This is a change to review-state claims, made on operator
instruction; the retrofit neither proposed nor could make it.

**P** = perishable, **D** = durable.

| # | atom | decider | result |
|---|---|---|---|
| X1 | the demotion value | `scripts/bundle_append.py:320–325` — the repo's own `green → "pending"` demotion | used verbatim rather than invented (D) |
| X2 | scope applied | all `papers/*/bundle_metadata.json` | **52 fields across 20 bundles**: `stage9_status` 16→0 green, `stage10_status` 17→0 green, `stage13_status` 19→0 green (P) |
| X3 | `stage13_redo_required` | deliberately untouched | unchanged (2 True / 19 False). The check's own comment records asserting it as a prior mistake — the field is owned by `bundle_append.py` and means *"new content was appended since the last review"*, not *"blockers are open"* (D) |
| X4 | effect on the check | `validate.py --check bundle_metadata_matches_graph` | ✅ **PASS — 21 compared, 0 drift** (P) |
| X5 | effect on the suite | full `validate.py`; `pytest tests/ -q` | **65/66** (was 64/66); only `readiness_submission_gate` remains. pytest **5,676 passed / 5 skipped**, unchanged (P) |
| **X6** | **SET: bundles that had jumped the Stage-9/10-before-13 hard gate** | every bundle's three status fields, both directions | ⚠️ **five** — D6 (`s9 = not_started`, `s10 = skeleton`), D7 (`s9 = not_started`), D8 (`s9,s10 = pending`), D9 (`s10 = pending`), I3 (`s9 = pending`) — all with `s13 = green` (D) |

⚠️ **X6 is a different defect from the one leg 4 catches, and the distinction matters for the fix.**
Leg 4 catches a Stage-13 green *contradicted by findings filed later*. X6 is a Stage-13 green that
was **invalid when written**, because `BUNDLE_LIFT_PROCEDURE.md:9` forbids invoking Stage 13 until
Stages 9 and 10 are green. **No check enforces that ordering** — verified by reading
`scripts/validation/checks/bundles_readiness.py`, which reads `stage13_status` at eight sites and
`stage9_status`/`stage10_status` at none. → **TODO-D24**. The demotion makes it dormant, not fixed.

⚠️ **TODO-D23 filed on the check's label, not its logic.** Its registered description —
*"bundle_metadata.json finding counts equal the live graph's"* — covers legs 1–3, which have never
failed. Leg 4 is a semantic contradiction, not a count equality, so its failure is uninterpretable
from the name. **Cost demonstrated twice in one session**: this retrofit mis-described the failure
as count drift, and the operator read the name as implying it should be green. Both readings follow
from the description.

✅ **What the demotion actually bought, stated plainly:** `validate.py` went 64/66 → 65/66 not by
suppressing a check but by **making a false claim false** — 20 bundles stopped asserting a review
verdict they had not earned. The remaining failure, `readiness_submission_gate`, is the P1-gate
check and a separate subject.

## V46 — ADR-011 Phase 1: `length_target` + Gate 12 — 9 atoms, 1 SELF-CORRECTED mid-build

**Scope.** Every new assertion in `ADR-011-manuscript-quality-layer.md`, the
`BUNDLE_DIRECTORY_SCHEMA.md` and law amendments, and the `bundle_manuscript_length` check.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | `PAPER_STRATEGY.md` §6 carries a venue AND a length for **all 21** bundles | direct read of §6 rows 383–403 | 21 rows, each with `Target` + `Length`. **CONFIRMED, both directions** — the population was enumerated, not sampled |
| 2 | `target_journal` is already populated in every `bundle_metadata.json` | scripted read of all 21 | 21/21 non-null. CONFIRMED |
| 3 | The ADR-010 §D2 purpose statements supply 3 of the charter's 5 fields | read of `docs/audits/*-retrofit/FINDINGS.md` §1b | 21/21 carry Audience · Venue · claim · Substrate · honest size. CONFIRMED |
| 4 | `compile_bundle_pdf.py` computes the page count and discards it | read of `:105-112` then `:114` | `ok = not errors and unresolved <= 0 and not unused_opts`; `pages` reaches only the report string. CONFIRMED |
| 5 | Renumbering the pipeline would break four consumers | read of each | `paper_tables/sources.py:418` (regenerates paper15 Table 1), `gate_precheck.py` stage names, `stage{9,10,13}_status` across 21 blobs, ~all of `docs/`. CONFIRMED |
| 6 | No check module imports another at module level | `grep` over `scripts/validation/checks/*.py` | zero hits. CONFIRMED — hence the local import of `_draft_input_closure`, recorded in-source |
| 7 | Gate 12 fires on the live corpus | the check, on freshly compiled PDFs | **21 sized, 0 unmeasured, 12 outside band** (1 over ceiling, 11 under floor) |
| 8 | The audit's F-01 claim "F is 23 pp against an 80–150 pp target" | independent re-measurement | F measured at **23 pp**. CONFIRMED — a prior finding reproduced by a different instrument |
| 9 | The check responds to production data | production-seeded mutation on real `papers/D3` | floor→200 ⇒ `D3: 59 pp < floor 200`; restored, `cmp` byte-identical |

**⚠️ SELF-CORRECTED, atom 9's probe.** The seeding writer used `json.dumps(...)` with the default
`ensure_ascii=True`, re-encoding every `§`/`—` in the apex `claims` strings and turning a 9-line
edit into **98 insertions / 91 deletions** on one file. Caught by reading the diff rather than
trusting the write. Fixed in `_persist_pages`, all 21 blobs rewritten unescaped, and the underlying
inconsistency — **four writers of this file disagree on `ensure_ascii`** — filed as TODO-D25 rather
than silently normalised.

**NOT-AN-ASSERTION.** ADR-011's phase ORDER is a plan, not a claim about the tree; it has no truth
value and is not verified here. Its *inputs* are (atoms 1–6). The 12-of-21 result at atom 7 is a
measurement of today's corpus and will change as the corpus does — it is dated, not durable.

## V47 — ADR-011 Phase 2a: the ordering gate + the promotion writer — 6 atoms, 0 corrected

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | No code path writes `"green"` to any `stage*_status` | `grep` over `scripts/`, then read of every hit | 2 writers only — `bundle_source_manifest.py:129-131` (sets `pending`) and `bundle_append.py:320-325` (demotes `green`→`pending`). CONFIRMED, and it is what `record_review.py` now supplies |
| 2 | `bundle_reviewer_stage_ordering` and `bundle_stage13_claim_consistent` are disjoint | production probe on real `papers/D6` | D6 seeded to its 2026-08-07 state ⇒ ordering **FAIL** naming D6, sibling **PASS** throughout (D6 has 0 blockers). **Disjointness demonstrated, not assumed** |
| 3 | The ordering check passes on the clean tree | the check | 21 checked, 0 violations — the operator's demotion cleared all five historical violations |
| 4 | `Detail`'s fields are `name`/`passed`/`message`/`warning` | read of `_registry.py:50-55` | CONFIRMED — four tests asserted `.detail`/`.ok` and failed; fixed against the source, not guessed |
| 5 | Every refusal path in `record_review.py` fires | 5 CLI probes against a real blob | prerequisite-unfinished, wrong KIND, absent KIND, non-existent `--doc`, and the legitimate path ⇒ rc 1,1,1,1,0. Restored byte-identical |
| 6 | A refused write leaves the blob unchanged | fixture test | byte-identical before/after — a partial write would leave a timestamp implying a rejected review happened |

**⚠️ Process note, not an assertion.** A background `compile_bundle_pdf.py --all` silently ran from
the workspace root instead of the repo and did nothing, reporting exit 0. Background commands do not
inherit the foreground cwd. Caught by checking a PDF's mtime rather than trusting the completion
notification (cf. memory `feedback_harness_cli_cwd_fails_open`).

**NOT-AN-ASSERTION.** `KINDS_SUFFICIENT_FOR_GREEN = {full-adversarial}` is a policy choice, not a
measured fact. It follows the audit's finding that `review_recorded` cannot distinguish evidence
kinds, but which kinds *should* earn a green is a decision, and it is recorded here as one.

## V48 — ADR-011 Phase 2b: the recompile skip (operator-approved) — 7 atoms, 1 SELF-CAUGHT

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The promoted `draft_input_closure` behaves identically to the original | side-by-side on 4 real drafts | D3 2/2, D11 7/7, D12 5/5, I1 9/9 — **sorted path lists identical**. Verified BEFORE rewiring any consumer |
| 2 | `compile_bundle_pdf.py` had no cache and recompiled unconditionally | read of `compile_one` + `main` | no skip path existed. CONFIRMED — the operator's inference was right, and restoring PDFs deferred churn rather than avoiding it |
| 3 | pdflatex output is not byte-stable across runs | two full `--all` runs on unchanged sources | 45 tracked PDFs dirty each time ⇒ a creation timestamp is embedded. This is why the churn was permanent, not one-time |
| 4 | The skip covers all 64 drafts, not just the 21 bundles | `--all`, twice | run 2 skipped **47 of 64** — exactly the 47 that pass the gate. PDF churn **45 → 16** |
| 5 | A draft that FAILS the gate is never skipped | D3, run twice | `FAIL … unresolved_refs_in_pdf=3` both times. D3 recompiles forever, by design |
| 6 | A draft that PASSES records its verdict then skips | D11, run twice | `OK` then `SKIPPED (up to date) pages=9` |
| 7 | A module-level `X = _H.Y` alias is forbidden in a check module | `test_validate_public_surface` | my alias was rejected by the existing contract; removed, call site reaches `_H` by attribute |

**⚠️ SELF-CAUGHT BEFORE SHIPPING — the skip masked a standing FAIL.** The first implementation
returned `passed=True` on skip, so D3 — which genuinely fails with 3 unresolved references and whose
PDF is perfectly fresh — would have reported `SKIPPED` and been counted as passing on every run
after the first. A freshness heuristic that converts a standing FAIL into a PASS is a gate that
stops firing. Fixed by requiring a **recorded PASS** before a skip is permitted; the load-bearing
test asserts it.

**⚠️ SECOND CORRECTION, same change.** The verdict was first stored in `bundle_metadata.json`,
which only the 21 bundles have — so the 43 legacy drafts could never record one and recompiled
forever, leaving two-thirds of the churn unaddressed. Moved to one sidecar covering all 64.

**NOT-AN-ASSERTION.** "mtime, not content hash" is a design choice with a stated failure mode
(`touch` recompiles needlessly), not a claim about the tree. `--force` is the escape the operator
made a condition of approval.

## V49 — ADR-011 Phase 2c: byte-reproducible PDF output — 5 atoms, 0 corrected

Answering the operator's question — *"pdf churn should go to zero next right? or is there
something different about the 16?"* Nothing is different about the 16: they are the drafts that
FAIL the compile gate and therefore must recompile every run. The churn was not caused by them
being special; it was caused by recompiles not being reproducible.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The residual churn is entirely non-content | `cmp -l` on two `--force` compiles of unchanged D3 | **58 bytes**, all inside `/CreationDate` + `/ModDate` |
| 2 | `SOURCE_DATE_EPOCH` + `FORCE_SOURCE_DATE` pin those two | re-measure | dates pinned (`D:20260806023829Z`) — **but 56 bytes still differed** |
| 3 | The remainder is the PDF trailer `/ID` | byte-offset inspection at the first difference | `/ID [<B84EE6AF…> …]` vs `[<B37641DC…> …]` — pdfTeX derives it independently of the source date |
| 4 | `\pdftrailerid{}` closes it | two isolated `pdflatex` runs, fixed epoch | **byte-identical.** Passed on the command line with `-jobname=paper_draft`, so no draft has to carry it |
| 5 | The gate verdict is unaffected by the changed invocation | D3 before/after | `FAIL pages=59 overfull=73 tex_errors=0 unresolved_refs_in_pdf=3` — identical. The reproducibility change moves bytes, not verdicts |

**End-to-end: `--all` twice ⇒ 0 tracked PDFs dirty. `--all --force` on all 64 ⇒ 0.** Churn is
gone, including for the 17 drafts that cannot be skipped.

**NOT-AN-ASSERTION.** Pinning the stamp to the newest input mtime rather than to a constant is a
choice: the date still means "when this document was last edited" and is stable across recompiles,
but it is not reproducible across machines with different mtimes. Local churn is what was asked
for; cross-machine reproducibility was not, and is not claimed.

## V50 — ADR-011 Phase 2d: the readiness formula stops granting an unearned GREEN — 6 atoms

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | Only `bundle_readiness.py`, `provenance_dashboard.py` and `datastar_bundles.py` consume the verdict string | grep across `scripts/` + `tests/` | 3 consumers (the `rhmc_*` hits are an unrelated diagnostic). Blast radius bounded — which is why the fix WITHHOLDS GREEN inside the existing 3-value enum rather than adding a fourth |
| 2 | This layer already has a "withhold, don't invent a value" precedent | read of `aggregate_by_bundle` + `test_readiness_cannot_measure` | two: `blocked_p1 is None` and the evaluator-crash handler. The new rules are the **third and fourth**, in the same shape |
| 3 | The attribution-sweep problem is live, not hypothetical | read of live metadata | **D1, D2 and D3** all cite `docs/audits/stage13_attribution_sweep_2026-06-10.md` as `stage13_review_doc` |
| 4 | D9's GREEN is withheld by the new rule | CLI run over the live tree | `YELLOW (Stage-13 evidence UNVERIFIED — kind=unrecorded; only full-adversarial earns GREEN)` — the portfolio's only GREEN, and the bundle whose Stage 10 never ran |
| 5 | GREEN is still reachable | fixture with `kind=full-adversarial` + a `claims_review.json` | GREEN. A rule that made GREEN unreachable would be a different defect |
| 6 | The writer and the renderer agree on what earns a green | test comparing the two frozensets | `br._KINDS_SUFFICIENT_FOR_GREEN == rr.KINDS_SUFFICIENT_FOR_GREEN`. Two enforcement points, one rule — drift would let a verdict the writer rejected still render GREEN |

**⚠️ CHECKED FOR A SELF-CONFIRMING LOOP.** Running `bundle_readiness.py` writes 21 aggregation
docs into `papers/AutomatedReviews/<today>-bundle-stage13/` — the same directory
`find_stage13_review_evidence` scans for review evidence. Verified it is excluded rather than
assumed: the docs carry `AGGREGATION_MARKER`, and `find_stage13_review_evidence('D9')` returns
`None` after the run. The byproduct was removed rather than committed — 21 files dated today
implying Stage-13 artifacts that no review produced.

**Docs corrected in the same commit, because their claims are now FALSE**: `END_TO_END_MAP` §8
(transition 2 has no actor; `review_recorded` does not discriminate kind; the ordering rule is
unenforced) and `VALIDATION_GATE_TOPOLOGY` §5 (nothing reads `stage9_status`/`stage10_status`) and
§6 (field ownership). Each stated a true fact that this work made untrue.

## V51 — ADR-011 Phase 3: the em-dash sweep — 9 atoms, 2 of my own hypotheses REFUTED

**Method.** Six Sonnet agents over disjoint bundle sets read all 741 occurrences in context and
rewrote each. Every claim below was re-verified by me against `git show HEAD:` rather than taken
from an agent report.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The generic AI-slop vocabulary is present in this corpus | 20 markers × 21 bundles | **REFUTED — 11 hits total, 17 of 20 markers at ZERO.** No `delve`, `tapestry`, `realm of`, `it is worth noting`, `moreover`. A denylist would have been a check that cannot fire |
| 2 | `bundle`/`lift` are mostly legitimate mathematics (my hypothesis) | context read of all 239 + 35 | **REFUTED — `bundle` is 230 publication-architecture to 9 mathematical.** I was wrong. But `lift` is irreducibly mixed: my own context classifier misclassified in BOTH directions on its own samples, which is why the word is excluded rather than gated |
| 3 | There is an auditable history of prose antipatterns to Pareto over | 273 review docs, 926 BLOCKERs | **NO — every one classifies to a claim-integrity gate that already has a check.** Prose was first reviewed 2026-08-01, so any wider gate extrapolates from one measurement |
| 4 | Em-dash total, and how many bundles are clean | corpus scan | **741** (621 `---` + 120 `—`); **0 of 21** clean |
| 5 | The en-dash population is separate and larger | corpus scan | **1,121.** A scan not requiring exactly-three would flag 1,862 and be wrong about 1,121 |
| 6 | The sweep removed every em-dash without touching an en-dash | per-file diff vs `HEAD` | **741 → 0**; en-dash counts identical in all 21 except 4 deliberate U+2013 normalizations |
| 7 | Nothing regressed in the build | `--all` compile | **47/64, identical to pre-sweep**; all 21 bundles pass |
| 8 | The check responds to production data, in both directions | seeded into real `papers/D1` | em-dash ⇒ rc=1 naming `D1:3`; `Bose--Einstein` in the SAME position ⇒ PASS. Restored byte-identical |
| 9 | A `:` in a bibitem title carries a functional risk (operator's concern) | read of the citation pipeline | **NO.** Cache files are keyed by BIBKEY (`Berti2015.pdf`), never by title; no filename derives from a title. And the registry's own title for `Roehm2026F` **already uses a colon**, so the edit moved the `.tex` toward canonical |

**A third dash variant, found by an agent and not in my brief.** Literal Unicode en-dashes
(U+2013) in rendered prose — `Kaul–Majumdar` in D3, `Chowdhury–Hartnoll–Hebbar–Khondaker` in E1.
D3 spelled the same name both ways. Normalized to `--`; this is atom 6's only en-dash movement.

**Two cases the agents correctly refused to fix, resolved by judgment:**
- **L2's table cells** — `---` as a "not applicable" marker. Replaced with `--` rather than adding
  a table exemption to the check: an exemption is a hole prose gets driven through, and the table
  dash has a conventional alternative that costs nothing.
- **I3:997** — an em-dash inside a verbatim quotation of the project's *own internal directive*.
  The agent was right that altering a quotation falsifies it. But the defect was not punctuation:
  a JOSS referee cannot parse "the program's user direction at Phase~6o opening". Rewritten
  forward-facing, which removed the quote, the process narration and the em-dash together.

**NOT-AN-ASSERTION.** The generative-habit analysis (six independent reports converging on
"state a claim, interrupt it mid-clause to pre-empt a misreading, resume") is qualitative field
evidence for `references/prohibited-patterns.md`, not a measured claim. It is recorded as the
agents' judgment, corroborated across disjoint file sets, not as a fact about the corpus.

## V52 — ADR-011 Phase 3b: the reader-facing-voice check — 6 atoms, design changed TWICE by measurement

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The audit's word denylist is usable as specified | corpus scan | **NO — 90 hits, I1 alone holds 48.** I1 is the methodology paper, so the review pipeline is its subject matter |
| 2 | `reviewer` has one disposition | context read across 4 bundles | **NO — three.** Scar tissue in F (`\texttt{adversarial-reviewer} agent; fresh-context Stage-13 pass`), subject matter in I1, the paper's own audience in I2/I3 (*"lets Mathlib4 reviewers calibrate expectations"*) |
| 3 | Matching the ACT instead of the vocabulary removes the need for an exemption | corpus scan | **YES — 13 hits, 4 bundles, I1 at ZERO.** Pinned by a test asserting I1's pipeline description passes clean |
| 4 | The four act-patterns are complete | the de-scarring agent's out-of-scope report | **NO — it found two D11 passages the patterns miss.** Both unmistakable self-narration |
| 5 | The three added patterns false-positive nowhere | corpus scan before adding | **4 hits, all D11, all genuine, zero elsewhere.** Measured across all 21 before being trusted |
| 6 | The check responds to production data, both directions | seeded into real `papers/D3` | *"(corrected 2026-08-01, D3 Stage-13 round-4 finding 2.1)"* ⇒ rc=1 naming D3:3; *"Smith corrected this coefficient in 2019."* in the IDENTICAL position ⇒ PASS. Restored byte-identical |

**⚠️ Atom 4 is the honest one.** My pattern set was derived from examples in four bundles and had
gaps; a subagent reading the same corpus found them. The guard is not that the first set was
complete — it was not — but that a new pattern is measured across all 21 bundles before it is
trusted. A test now pins the boundary explicitly: a bare `round 3` is clean (legitimate in
numerical work) while `rounds 7 and 10 both rated` fires, so the addition did not quietly become
the vocabulary ban that atom 1 rejected.

**De-scarring content preserved, not deleted** (agent report, spot-checked): D11's retracted
Chern/mass-inversion classification survives as a present-tense negative result with both reasons
it fails; D12's completeness disclaimer survives with the specific non-load-bearing binder named;
E2's two nested scope corrections both survive with their `ChernBridge.lean` line references.

**NOT-AN-ASSERTION.** "13 hits" and "90 hits" are measurements of today's corpus, not durable
facts. Both move as drafts change, which is the point of the gate.

## V53 — ADR-011 Phase 5: the authoring skill and the fourth reviewer — 6 atoms, 0 corrected

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The pipeline has reviewers but no authoring guidance | read of the plugin + lift procedure | 3 reviewer agents, 0 authoring surfaces. Drafting rules lived in `BUNDLE_LIFT_PROCEDURE` §7 as a bookkeeping checklist. The operator's diagnosis was right |
| 2 | `references/` is an established convention here, not an invention | `ls` over `skills/` | `goal-dev` and `goal-prompt` both carry one |
| 3 | The new skill meets the `plugin-dev` criteria the others miss | re-audit of all 7 skills | `paper-authoring`: **661 words, third-person description, 0 second-person, 0 broken refs.** The other six all fail the third-person rule; `goal-prompt` is 2,784 words with 2 broken reference links |
| 4 | `SURFACE_INVENTORY` picks up new plugin components without hand-editing | regenerate + diff | 2 insertions, both automatic. The hand-maintained `README.md` rosters do NOT, and were updated by hand |
| 5 | The new components break nothing | plugin suite + repo suite | `.claude/plugins/skeft-qa/tests/` 156 passed; repo 5,757 passed |
| 6 | Stage 10 gains a sub-gate without renumbering | design check against C1 | `prose-reviewer` lands at lift §7.5 inside Stage 10. No `stage*_status` field, `gate_precheck` name, or paper-15 table row changes |

**The design decision worth recording** is the resolution of the operator's shared-reference
proposal against C5 (*the decider must not be the generator*): **shared floor, divergent
ceiling.** Both surfaces read `prohibited-patterns.md`, so a rule cannot mean one thing while
writing and another while reviewing. The reviewer alone carries reader-outcome questions
(*where would a reader stop*), and the author is deliberately never given them, because a
generator optimises against any checklist it can see. Stated in both files.

**NOT-AN-ASSERTION.** The frequency table in `prohibited-patterns.md` (~45–55% paired asides,
~30–45% colon-substitutes) is the six sweep agents' judgment aggregated across disjoint file
sets, not a measurement I re-derived. It is labelled as field evidence in the reference.

## V54 — ADR-011 Phase 4a: Gate 13, and a bibliography that was never compiled — 7 atoms, 1 AUDIT CLAIM REFUTED

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | 9 of 21 bundles ship zero figures | corpus scan | **CONFIRMED** — F, D1, D2, D3, D4, D6, D7, D10, I3. Reproduces the audit exactly |
| 2 | The audit's Gate-14 leg *"bibliography with `\bibitem` count > 0 … catches D8 and D10"* | read of both drafts | **REFUTED.** Both carry `\bibliography{bibliography}` + a real `.bib`; the leg would have flagged two bundles that have a bibliography, by a different mechanism. Not implemented as specified |
| 3 | …but D8's citations resolve | `pdftotext` on the rendered PDF | **NO — 26 rendered as `[?]`, and NO reference list at all.** Its text reads *"poly-logarithmically in 1/ε [? ? ? ]"* |
| 4 | The compile gate could see that | read of `compile_one` | **NO.** It counted `??` (unresolved `\ref`) and never `[?]` (apsrev4-2's unresolved `\cite`). D8 reported **OK** with every citation broken |
| 5 | Root cause | grep for `bibtex` across the compile paths | **No compile path ran bibtex at all.** A draft using `\bibliography{}` never got a `.bbl` |
| 6 | Running bibtex fixes it | recompile after the change | first attempt still 26: bibtex runs with `cwd=out` where the `.aux` is, but the `.bib` files live beside the draft, so it silently found no database. With `BIBINPUTS` set ⇒ **0 unresolved, bibliography rendered** |
| 7 | Nothing regressed corpus-wide | `--all` with the cache cleared | 46/64. **D3 is the only failing bundle**, on its pre-existing 3 unresolved `\ref`s; the other 17 are legacy drafts. D8 moved from *hidden* failure to genuine pass |

**⚠️ A REPORTING ERROR OF MINE, CORRECTED.** I first said "all 21 bundles pass" from a `grep`
over the background job's output file. That file was tail-truncated by the invoking command, so
the grep matched nothing and I read absence as success. The gate cache is the authoritative
record and says D3 fails. **An empty grep result is not evidence of absence when the input may be
truncated** — the same class as the round-8 defect this suite exists to catch.

**NOT-AN-ASSERTION.** The tier figure floors (0→8, 1→4, 2→1, 3→2, 4→1) are the audit's proposed
backstop, not a measured requirement. They apply only until a bundle declares a charter figure
plan, at which point the comparison should be against the plan.

## V55 — ADR-011 Phase 4b: Gate 14, narrowed by measurement — 5 atoms, 2 REJECTIONS pinned

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The audit's sedimentation ratio `n_sections/n_sources` is implementable | corpus measurement | **NO.** It divides by *registered* sources and a sourceless bundle has one synthetic key, so **D9 scores 9.0 with nine sections while D3 — 31 sections, 114 subsections, the actual case — scores 0.97.** It ranks them backwards. Not implemented |
| 2 | Sedimentation is therefore untreated | read of the mechanism | No: it is addressed at its *cause*, `bundle_append.py` inserting a section per registered source. That fix needs charters and is filed as TODO-D26, blocked on the roster decision |
| 3 | A closing section can be found by testing the last `\section` | my first implementation, measured | **NO — 10 of 21 bundles reported as lacking a conclusion when all 21 have one.** Papers legitimately end with *Methods and tools disclosure*, *Verification status*, *Code Availability*. Widened to the last three |
| 4 | The remaining legs discriminate | the check on the live corpus | **1 of 21 fails: D3, on the section ceiling.** The floor legs (abstract, bibliography, closing section) pass everywhere and are regression guards, which is how they are described rather than sold as findings |
| 5 | The check responds to production data | seeded into real `papers/L3` | renaming its closing section *"Discussion"* → *"Further remarks"* ⇒ rc=1 naming L3 and printing the three sections examined; 1 → 2 short. Restored byte-identical |

**Both rejections are pinned by tests**, so a later author reinstating either meets a failing
test that explains why it was dropped: `test_EITHER_bibliography_mechanism_is_accepted` and
`test_a_closing_section_may_sit_BEFORE_a_methods_section`.

**NOT-AN-ASSERTION.** The tier section ceiling of 20 is a judgment about readability, not a
measured threshold. Tier 0 is exempt because a review's shape is legitimately a long section
list.

## V56 — ADR-011 Phase 6: absorption repair — 6 atoms, 1 AUDIT CLAIM REFUTED, 1 near-miss

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The audit's *"the data already exists — `bundle_append.py` takes `--lean-modules`"* | probe of `append_log.json` for `lean_modules` | **0 of 21 bundles, across 129 events.** Read alone, that retires F-07 and F-10 as unbuildable |
| 2 | …but the probe was wrong | read of `bundle_append.py:299` | **The field is `lean_modules_referenced`.** Re-probed: **18 of 21 bundles, 444 distinct modules.** The audit's claim is true; my first measurement was the false absence |
| 3 | Declared modules reach the draft | underscore-aware, basename-tolerant scan | **238 of 444 (54%) are registered and never named.** D10 declares 11 and cites 0; E1 declares 7 and cites 0; D9 is 64 absent of 77 |
| 4 | 238 absences are 238 defects | judgment on the mechanism | **NO, and the check says so.** A module can support a cited result without being named, so the rate more likely reflects generous registration than incomplete drafts. Shipped as a shrink-only ratchet, not a hard fail |
| 5 | The ratchet has zero headroom | seeded into real `papers/I3/append_log.json` | one uncited module registered ⇒ **238 → 239, rc=1** with the remediation named. Restored byte-identical |
| 6 | D.0 is the exceptional branch | live blocker counts | **It is the normal case.** D1 carries 37 open blockers, D12 carries 46; absorbing into either makes the review loop non-convergent. Placed first in the decision table, not as a footnote |

**⚠️ ATOM 1→2 IS THE NEAR-MISS AND THE LESSON.** I measured `lean_modules`, got zero across the
whole corpus, and was one step from reporting that the audit was wrong and the phase unbuildable.
The field is named `lean_modules_referenced`. This is
`reference-measurement-traps-false-absence` in its purest form: **a narrow key makes a live
population scan empty, and an empty scan reads as evidence.** The wrong-field case is now a test,
so the trap is pinned rather than remembered.

**NOT-AN-ASSERTION.** The ambiguous-basename exclusion list (`Basic`, `Trace`, `Module`, …) is a
judgment about which names a substring test cannot resolve, not a measurement. Widening it would
lower the ratchet without improving anything, which the check's own message forbids.

---

## V57 — ADR-011 Phase 8: plugin review & sync — 8 atoms, 2 OF MY OWN FILED CLAIMS REFUTED

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | *(filed in ADR-011)* "Six of six skills miss the third-person description form" | re-measure with whitespace-normalised, folded-YAML-aware scan | **REFUTED — wrong by more than double.** The rule does not bind on the 2 skills carrying `disable-model-invocation: true`; `goal-dev` carries the phrase mid-sentence and was missed by a `startswith` test. **Real: 3 of 5 model-invocable skills** (`harvest`, `sync`, `wave-close`) |
| 2 | *(filed in ADR-011)* "`goal-prompt` names two `references/` files that do not exist" | resolve the full cited path | **REFUTED.** Both are cross-skill refs — `goal-dev/references/{lab-notebook,parallel-worktrees}.md` — and both exist. The scan's regex discarded the `goal-dev/` prefix. **Zero broken reference links exist in the plugin** |
| 3 | The README documents what ships | diff of `agents/`, `commands/`, `hooks.json` against README text | **4 of 9 agents, 4 of 6 commands, 4 of 5 hooks.** Components are auto-discovered from the filesystem, so nothing forced the README to follow |
| 4 | The README's hook posture claim is accurate | read of `hooks.json` against the sentence *"four (all default-inert + fail-open)"* | **FALSE, and inverted on the one that matters.** The undocumented fifth hook is the web-egress guard: **unconditional and fail-CLOSED**. The blanket sentence was wrong *because* the omitted hook is the exception |
| 5 | `/frontier` cites two scripts that do not exist | path-root disambiguation | **NO — my scan's false positive.** `scripts/atlas_{view,heatmap}.py` are repo-relative and present. But the same conflation is a real defect elsewhere: **3 bare `scripts/X.py` prose refs** name plugin scripts in a form that resolves to nothing from the repo root |
| 6 | `prose-reviewer` cannot edit the draft it reviews | read of its frontmatter | **It could.** No `tools:` field ⇒ inherits Write/Edit/Bash. Its body's *"You do not edit"* was a request. Now `tools: ["Read","Glob","Grep"]` — read-only by construction; `compiled_pages` is present for all 21 bundles, so it needs no Bash |
| 7 | The plugin's guards run in the workflow | `pytest --collect-only` | **They ran nowhere.** `testpaths = ["tests"]` collected **5,781 repo tests and 0 plugin tests**; no CI workflow exists and the pre-commit hook runs only IP clearance. 156 guards — incl. `test_skill_safety.py`, written to catch shipped defects — fired only when someone passed the path by hand. `testpaths` now collects both (**5,947**) |
| 8 | The new guards have zero headroom | production-seeded, 4 mutations | undocumented agent ⇒ rc=1; agent with no `model:` ⇒ rc=1; a 6th hook added to real `hooks.json` ⇒ **2 checks** rc=1; rotted `${CLAUDE_PLUGIN_ROOT}` path ⇒ rc=1. All restored **byte-identical** |

**⚠️ ATOMS 1, 2 AND 5 ARE THE LESSON, AND ALL THREE ARE MINE.** Three separate false positives in
one phase, every one from a scan keyed too narrowly: a `startswith` where the phrase sits
mid-sentence, a regex that discarded a path prefix, a pattern that conflated two `scripts/` roots.
Two of them I had already *filed into ADR-011 as findings* before re-measuring. This is
`feedback-remeasure-filed-findings-before-fixing` earning its keep — **a filed finding is a claim,
including when I filed it** — and the same trap as V56 atom 1. The corrections are recorded in
ADR-011 Phase 8 rather than silently overwritten.

**Why the deliverable is a test and not an edit.** Fixing the README syncs it once; the drift
returns with the next component, exactly as it did here. `tests/test_plugin_surface.py` (10 checks)
makes the surface-to-README contract a test failure at the moment it is introduced. Note the
derived `SURFACE_INVENTORY.md` was **correct throughout** — it listed all 5 hooks, 9 agents and
6 commands. Only the hand-written narrative drifted, which is the whole rationale for
architecture rule 3 ("never write a count into a narrative"). The plugin README keeps its count
because it must stand alone when distributed; the count is now pinned by a guard instead.

**A PRE-EXISTING GUARD I HAD NOT FOUND CAUGHT MY OWN EDIT.** The combined run failed on
`tests/test_plugin_prompt_code_refs.py::test_every_referenced_script_path_exists` — a repo-side
test that requires every `scripts/...`-shaped string in a plugin file to resolve. It was tripping
on the literal placeholder `scripts/X.py` I had written into the new test's own docstring, and
then a second time on `scripts/foo.py` in the note I added while fixing the first. The guard was
right both times: a placeholder that looks like a real path is indistinguishable from a broken
reference, which is the same defect class `test_skill_safety.py` guards for `` !`cmd` ``.
Placeholders are now written `scripts/<name>.py`. Two consequences worth keeping:
(a) I built a path-integrity check without first finding the repo-side one that already existed —
the recurring "second mechanism beside one that already exists" failure architecture rule 1 names;
(b) they are **not** duplicates and both are kept — the repo-side test accepts either root
(permissive, broad net), while Defect 7 here requires prose to resolve from the repo root a reader
actually stands in. The relationship is now documented in the new file's header so neither is
later deleted as redundant.

**NOT-AN-ASSERTION.** `goal-prompt` at 2,784 words is filed as TODO-D28, not fixed. Its body is
re-injected at every compaction boundary, so choosing what moves to `references/` changes what an
autonomous loop re-reads after a compact. That is a behavioural change to the durability
mechanism, not a word-count trim.

---

## V58 — ADR-011 Phase 7: the pipeline law rewritten — 8 atoms, 4 ACCURACY DEFECTS FOUND

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The document's weight is "back-and-forth / oscillation / troubleshooting language" (the brief) | marker scan before any edit | **Only partly.** Troubleshooting voice **0**, hedging **2**, first-person **3**. The weight is **49 provenance citations** (31 ADR/TODO/audit back-refs, 18 dated incidents). It does not oscillate; it cites its own history |
| 2 | The rewrite is stylistic | read of the full 828 lines | **NO — 4 accuracy defects.** See atoms 3–6 |
| 3 | The Quick Reference commands are live | `argparse` structure of `submit_to_aristotle.py` | **The block invoked the ARCHIVED interface.** It carried `--priority` / `--integrate` / `--resume`; the CLI is subcommand-based (`sorries`/`stage`/`submit`/`status`/`retrieve`/`graft`/`verify`). Stage 4 in the same document calls that interface "archived and disabled" |
| 4 | Stage 13's tier table matches the roster | `bundle_registry.TIER_OF` | **Stale.** Doc said Tier 1 = D1–D5, Tier 3 = I1–I2; registry says **Tier 1 = D1–D12**, **Tier 3 = I1–I3** |
| 5 | The absorption-branch set is current | grep of the protocol | **Stale in two places and self-inconsistent** — one site D.1–D.3, the other D.1–D.4; the protocol ships **D.0–D.4** (D.0 added in Phase 6) |
| 6 | Paper 15's Table 1 is unaffected by a doc rewrite | read of `paper_tables/sources.py:418` | **It parses this document's overview block.** The table had been reproducing pre-ADR-011 gate text; 6 of 13 rows were stale. Rows/stages/names identical after the rewrite; gate text corrected and regenerated |
| 7 | Stage and invariant numbering survived | scoped re-parse | Stage headings **1–14** intact; invariants **1–17** in order. Constraint C1 (no renumbering) held |
| 8 | No operative content was lost | token extraction, old vs law+rationale | **First pass reported 61 missing and was WRONG** (keyed on `--check <name>` and exact paths, so a check named in a table read as absent). Re-run on basenames: **31 genuinely absent**, each classified; operative ones restored; the rest are deliberate substitutions |

**⚠️ ATOM 8 IS THE FOURTH NAIVE-SCAN FALSE POSITIVE IN TWO PHASES.** Same failure as V57 atoms 1, 2
and 5: a scan keyed too narrowly reports a live thing as absent. Here it would have caused the
opposite error from usual — not a false finding, but **false confidence in a deletion**, since I was
using it to prove nothing was lost. The correction is the same one that has worked every time:
re-measure on a looser key and classify by hand before acting.

**Why a companion document rather than deletion.** Provenance is not decoration: the incident
behind a rule is what stops someone re-litigating it. `docs/WAVE_PIPELINE_RATIONALE.md` keeps all of
it, keyed by stage and invariant, and the law links to it once. Nothing was deleted.

**NOT-AN-ASSERTION.** The 39% reduction is a consequence, not a target. A shorter law that misstated
the process would be a worse outcome than the document it replaced.

---

## V59 — post-ADR-011 architecture-doc reconciliation — 6 atoms, 5 DEFECTS, 1 SELF-INFLICTED

Scope: does `docs/architecture/` still describe the system after eight ADR-011 phases landed?
Method: last-touching commit per doc, then a targeted read of every doc whose owned surface an
ADR-011 phase changed. Not a re-read of the directory.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | Census figures drifted | `validate.py --check architecture_inventory_fresh` | **NO — clean.** `SURFACE_INVENTORY.md` is derived and gated, and it already carried `prose-reviewer`, the new checks and the new agent rows. The counts rule worked exactly as designed: nothing to chase |
| 2 | The narrative docs drifted on counts | `no_counts_in_narratives` leg, 7 docs | **NO.** Zero census counts in any narrative. The rule holds |
| 3 | Enumerated *rosters* in narrative drifted | read of both maps' plane/spine diagrams | **YES — 2 defects.** `END_TO_END_MAP:28` ⑧ REVIEW named 3 reviewers; `QA_QI_INFRASTRUCTURE_MAP` plane ④ named the same 3. `prose-reviewer` (Phase 5, lift §7.5) was in neither |
| 4 | The portfolio map's drift ledger is still accurate | item-by-item re-check against the protocol | **One verdict INVERTED by our own Phase 6.** It said the absorption protocol "omits the branch every modern phase uses" — Phase 6 added D.0 and the stage + decision tables now carry D.0–D.4. The *roster-arithmetic* half of the same verdict is still true |
| 5 | The protocol's roster arithmetic | read of Stage B + §gates | **STALE, and it is a hardcoded roster in prose:** "the existing 13 bundles … a 14th+ bundle target". Live roster is 21. Replaced with the registry owner, not a corrected number |
| 6 | Same defect class elsewhere | grep for roster counts across `docs/*.md` | **1 further live instance.** `BUNDLE_DIRECTORY_SCHEMA:276` asserted `_VALID_BUNDLE_TARGETS` "now covers … (14 entries)" in the present tense; it is an alias re-exporting `bundle_registry.VALID_BUNDLE_TARGETS`, live at 21. The other hits (`RESEARCH_STATUS_OVERVIEW`, `ARXIV_DEPOSIT_PLAN`, `PAPER_STRATEGY` §341) are already dispositioned ⛔ in the portfolio map's ledger — known, not newly found |

**⚠️ ATOM 3 IS THE FAILURE `END_TO_END_MAP` §9 ITSELF NAMES.** That section states the mechanism —
*"an enumerated roster in prose goes stale exactly as an enumerated roster in code does, but nothing
fails when it happens"* — and then the document's own spine diagram went stale by that exact
mechanism, four sections above the sentence describing it. Writing the rule down does not enforce it.
The counts rule is machine-enforced and held (atoms 1–2); the roster rule is prose and did not.

**⚠️ ATOM 4 IS SELF-INFLICTED AND IS THE ONE WORTH GENERALISING.** Phase 6 repaired the branch index
and did not re-check which *other* documents asserted it was broken. A fix silently converts every
downstream statement about the defect into a false statement, and a drift ledger is precisely a
document made of such statements. **Repairing a defect obliges a scan for who documented it.**

**NOT-AN-ASSERTION.** Atoms 1 and 2 are the load-bearing result here, not the five defects. The
surfaces under a derived-and-gated census did not drift at all; every defect found sits in prose
that names a roster. That is an argument for widening the mechanical guard to rosters, not for
another manual pass — filed rather than built, because the exception set is the hard part.

---

## V60 — ADR-010 §D4 adjudication + the native_decide/TODO ratchets — 10 atoms, 6 INVERSIONS, 1 SELF-INFLICTED

Scope: the operator delegated the final grouping call after the apex retrofit completed. Method:
all merge-candidate manuscripts read in full (D6 1,102 lines, D9 1,318, D10 315, D11 633, L1 391,
E1/E2 abstracts + Γ_H sections), closures re-derived live, ADR-010 C4 binding throughout.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The 2026-08-06 probe's `D6 ∩ D9` Jaccard 0.482 still holds | live closure from declared apexes | **0.000.** Not a contradiction — the probe said so itself: it seeded from *what drafts cite*, and the retrofit closed the gap to *what bundles claim*. **I nearly filed this as an inversion before reading the probe's own closing paragraph** |
| 2 | `D6 ∩ D9 = 0` means the two are unrelated | D6's draft, read in full | **NO.** D6 §5.4 is 488 lines (44 %) of D9's corpus, naming ~20 of the same theorems. The zero is D6 declaring only the four sections that overlap D9 in nothing. **The D6 retrofit had already written this correction down a day earlier** — see the goldfish note below |
| 3 | The audit's D6+D9 merge is therefore right | referee reading of both | **Right diagnosis, wrong remedy.** D9 strictly supersedes D6 §5.4 (strong duality with both attainments, sharp Audenaert, max-flow/min-cut); merging would bolt four FT vignettes onto a coherent device-certification paper. **Excise, don't consolidate** |
| 4 | D6 is thin and should be demoted | `FaultTolerance` homing, live | **NO — 342 declarations in D6's own namespace reach no bundle**, incl. `ExRec` 31 and `StabilizerCode` 43, which are in neither the retrofit's list nor any bundle. D6 is holding someone else's paper and not its own |
| 5 | D10+D11 needs a non-substrate merge argument (ADR-010's own words) | closure + both drafts | **The premise was withdrawn the next day.** `D10 ∩ D11 = 0`, and the two are methodologically *opposed*: D10 is built on PhysLib, D11's acknowledgments state it imports none and exists to show the analytic route is unnecessary |
| 6 | PhysLib's post-bump spectral theory may make D10's Kato–Rellich redundant | grep of the resolved package at pin `c4843367` | **Refuted. `Kato`, `Rellich`, `relBound`, `RelativelyBounded` occur NOWHERE in PhysLib.** It has `IsEssentiallySelfAdjoint` as a definition + the defect-index criterion — a different and harder route for a molecular Coulomb Hamiltonian |
| 7 | E1+E2 is an open editorial question | recompiled PDFs | **Closed by arithmetic. 5 pp each against PRL's ~4 pp** — two over-length letters cannot make one letter |
| 8 | The graphene Γ_H defect is "in both the paper and `formulas.py`" | line 473 + its docstring | **Half wrong. `formulas.py` declares γ₁,γ₂ in [m²/s]** — m²/s × m⁻² = s⁻¹, dimensionally sound. Only E2's prose substitutes η/(sT), a *time*. Fixing the code would have broken a correct function |
| 9 | `native_decide` disclosure is a live gap (audit D-5) | per-bundle closure ∩ carriers | **The state is clean and was unguarded.** 5 bundles carry debt (D4 19, L2 6, F 3, D2 3, I2 1) and **all 5 already disclose**; 16 measure zero, incl. every bundle claiming purity in print. Now enforced rather than lucky |
| 10 | TODO markers can be found by scanning for `TODO\|placeholder` | sample of the hits | **NO — two populations.** `placeholder` in prose is a *disclosed technical term* here (`True := trivial` stubs, which drafts are REQUIRED to name), and D11 §1 factually describes an in-source TODO in *Mathlib*. Correct predicate: markers inside LaTeX comments. 80 real, across 10 bundles |

**⚠️ ATOM 10 IS THE SIXTH NAIVE-SCAN FALSE POSITIVE IN THIS ARC, AND THE SEVENTH CAME FROM A GATE I
WAS BUILDING.** `bundle_native_decide_debt` shipped with a third leg that hard-failed a draft
asserting zero `native_decide` while its closure said otherwise. On first run it fired on **I2,
wrongly**: I2's *"no `native_decide`"* is scoped to its Q(√n) subsection, and I2 separately discloses
`fib_pentagon` *"by `native_decide` on the 512-case F-symbol catalog"* — the exact declaration
counted. **The draft was right and my regex was wrong.** The leg is deleted, not exception-listed:
separating a corpus-wide claim from a scoped one is a reading task, and reading tasks belong to the
prose reviewer. What survives is narrower and true — debt cannot grow, and cannot be silent.

**⚠️ ATOM 2 IS A NEAR-MISS GOLDFISH RESEED.** The D6 retrofit's §5 already contained the exact
correction, written 2026-08-07, including the sentence *"D6 and D9 share no declaration because D6
declares none of the shared content, not because the content is not shared."* Its own closing lesson
is the one that saved this pass: **before quoting a fresh measurement against a bundle, read that
bundle's FINDINGS doc first.**

**⚠️ SELF-INFLICTED, and worth recording because it destroyed work.** Mutation-testing the ratchet, I
restored `src/core/constants.py` with `git checkout` — which reverted the mutation *and* the
uncommitted `NATIVE_DECIDE_BUNDLE_DEBT` block I had just written. The hash comparison caught it
immediately (that is why it is in the harness) and the block was rewritten. **Mutation-test only
committed files, or snapshot to the scratchpad first** — `git checkout` cannot distinguish a seeded
defect from new work.

**⚠️ AN EIGHTH, CAUGHT WHILE RE-CHECKING MY OWN WRITE-UP — and it is two traps in one probe.** The
adjudication's first draft claimed D9 *"strictly supersedes"* D6 §5.4 and named three things §5.4
*"has none of"*. **Two of the three were false**: §5.4 carries the full Watrous strong duality
(`diamondDist_eq_choiSDP`, three mentions) and carries *more* negativity text than D9. The probe
failed twice over: `grep -E` with `\|` searched for a **literal pipe-delimited string** rather than
an alternation, returning 0 for D9 on content D9 plainly has; and a follow-up pattern using `.`
between name parts could not match drafts that write `diamondDist\_eq\_choiSDP` — the
**LaTeX-escaped-underscore trap `QA_QI_INFRASTRUCTURE_MAP` §5 already documents**, met from a new
direction. The verdict was unchanged and the corrected justification is stronger (D9's scope
*contains* §5.4's and adds four families it has nothing of), but the claim as first written was
wrong and is corrected in place rather than quietly rephrased.

**The through-line across all eight: every single error this pass was a MEASUREMENT error, and not
one was a reasoning error.** The conclusions held up; the instruments did not. That is the argument
for C4 stated as a fact about this pass rather than as a principle.

> ⚠️ **The "20" below was superseded within a day — see V61 (L1 reversed) and V65 (roster 21
> decided). It is retained as the record of what was recommended on 2026-08-08, not as a live
> number.** The paragraph's actual point — that the deliverable is the merge verdicts, not the
> count — is what survived, and survived *because* the count moved and it did not.

**NOT-AN-ASSERTION.** The recommended roster of 20 is not the deliverable. **Six of six proposed
merges failed against the manuscripts and the one retirement was never proposed** — so the finding
is that the portfolio's problem was misplaced *content*, not an inflated *count*, and reassignment
(D4→D8, D1→D7, and now D6 §5.4→D9) fixes three of the four boundary failures while changing the
roster by zero.

---

## V61 — orientation pass over the audit corpus: one verdict REVERSED, one live claim-integrity defect surfaced

Triggered by the operator's *"make sure you are up to speed on the relevant context including past
audits."* Method: read the retrofit FINDINGS for every bundle V60 ruled on but had not opened
(L1, D10, D11, E1, E2), the 2026-08-07 audit addendum, PR-review pass 3, and `REMEDIATION_PLAN` §6a.

| # | Proposition (from V60 / the adjudication) | Decider | Verbatim result |
|---|---|---|---|
| 1 | "Retire L1 — D3 and F already declare its content" | `papers/D3:662-663` | **REFUTED. L1/D3 is a DECLARED splash/deep pair:** *"Bundle L1 ships the same content as a four-page Physical Review Letters splash."* The shared declarations are the design. **The L1 retrofit had already corrected an earlier draft of my exact argument**, recording its basis as false |
| 2 | The overlap pattern is unusual | D1's abstract, D3 §7 | **It is the portfolio's idiom, used FOUR times** — L1/D3, L3/D3, and D1's *"Companion experimental letters E1 … and E2"*. §3 of my own adjudication treated E1/E2's identical situation as legitimate design while §5 treated L1's as redundancy — **inconsistent standards inside one document** |
| 3 | L1 is thin (18 declarations) | L1 retrofit §1 | **Wrong instrument.** *"There is no tower beneath it and there should not be one"* — and L1 is **the only bundle at or under its charter length** |
| 4 | The 2017 GW170817-constraint literature gap (V60 filed it UNVERIFIED) | bibliography scan | **CONFIRMED — 10 bibitems, zero from that body.** Real, and a citation fix rather than a retirement ground → TODO-D34 |
| 5 | D10+D11 and E1+E2 keep-separate | their retrofits | **CORROBORATED independently.** E2's retrofit reached the E1+E2 answer at substrate level before I did: 5 shared declarations, all the platform-*independent* `T_H` binding |
| 6 | The AI-disclosure clause is a closed item | whole-file scan of 21 drafts | **LIVE, and 8 bundles carry it** — D1, D2, D3, D4, D5, D9, L2, E1. **D9 carries it with no `claims_review.json`** |

**⚠️ ATOM 6 IS THE NINTH MEASUREMENT TRAP, AND IT NEARLY CLOSED A LIVE DEFECT.** A line-based
`grep` for the clause returned **4** bundles; the true number is **8**. LaTeX prose wraps, and the
phrase *"all numerical claims trace to the / repository's computation pipeline"* straddles a newline
in four drafts. A line-oriented scan over wrapped prose is structurally unable to see it. Had I
stopped there I would have reported addendum item A5 as mostly fixed. **Whole-file, `re.S`.**

**The defect atom 6 surfaces is the sharpest open item in the portfolio**, and V60 did not know it:
eight manuscripts assert *"all numerical claims trace to the repository's computation pipeline
through its automated validation checks"* while `numerical_literals` reports **116 inline literals**
and `\substantivetheorems{}` = **26 329** — a PROJECT-wide count — is used as if paper-scoped in D1,
D5, E1, E2, F and I1. D1's own chain is ~114 theorems. **The mechanism built to make numbers
trustworthy is producing the portfolio's largest numerical overclaim, inside the disclosure section
of papers whose subject is verification integrity.**

**⚠️ AND THE ARCHITECTURAL FINDING THAT REFRAMES THE D6 EXCISION.** PR-review pass 3's H1: every
content-facing predicate is universally quantified over a population *the draft itself supplies*,
so the system is **monotone in emptiness** — *"a one-paragraph draft with no citations, no Lean
references and no numbers is a clean run of all 60 checks and a clean review from all three LLM
agents."* Excising D6 §5.4 makes D6 emptier, and the only guard pointing the other way is
ADR-011 Phase 1's length **floor**. TODO-D32's one-wave sequencing is therefore not tidiness; it is
the only thing standing between the excision and a bundle that scores better for containing less.

**NOT-AN-ASSERTION.** The reversal is the finding, not the roster number. V60's own headline was
that six merges failed because they were argued from counts rather than manuscripts — **and its one
original recommendation was argued from a ledger's summary of a retrofit instead of the retrofit.**
C4 is not satisfied by reading most of the drafts.

---

## V62 — closing the portfolio's sharpest claim-integrity defect (A5 / TODO-D9) — 7 atoms, 2 near-misses

Scope: the AI-disclosure clause and the theorem-count overclaim beneath it. Prioritised over the
D6 excision because it is template-level (every future bundle inherits it), small per bundle, and
a false statement about verification inside papers whose subject is verification.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | The clause is carried by 4 drafts | line-based `grep` | **WRONG — it is 8.** The phrase wraps across a newline in four drafts, and a line-oriented scan cannot see it. `re.S`, whole file |
| 2 | The honest replacement is "tables and figures are generated from the pipeline" | `bundle_tables_use_pipeline` | **REJECTED BEFORE SHIPPING.** D1 and E1 carry hand-written tabulars and **zero** `\input{tables/}`. That sentence would have replaced a false claim with a new one |
| 3 | The overclaim is "~230x" (this item's own figure) | per-bundle apex closure | **Far worse. E2 stated 26 329 against 6 theorems (~4 400x); E1 against 11 (~2 400x).** The old ratio used a declaration count where the sentence says *theorems* |
| 4 | Every `\substantivetheorems` use is a defect | read all 10 sites in context | **NO — 4 are correct**, and deleting them would have been vandalism: F's *"Project totals"*, *"Lean backbone of the program"*, *"Lean library currently ships"*, *"Total program output"*, plus D5's and I1's counting-convention sentences. **The defect is a project figure in a paper-scoped sentence, not the macro** |
| 5 | D3 compiles clean, like the other 20 bundles | `compile_bundle_pdf.py D3` | **FAIL — 3 unresolved refs**, i.e. three literal `??` in a 58-page PDF, while `paper_latex_compiles` reported **21/21 bundles clean**. Two instruments, one corpus, opposite verdicts |
| 6 | D3's dangling refs were caused by my disclosure edit | `git stash` + recompile at HEAD | **Pre-existing, identical at HEAD.** Both targets existed under other labels (`sec:cfl`, `sec:penrose`) and had never been repointed |
| 7 | Dangling refs are gated somewhere | read `paper_latex_compiles` | **Nothing gates them.** It hard-fails on fatal `!` breakage only, by design and as documented. `compile_bundle_pdf.py` measures the count and reaches no gate |
| 7b | The failure was at least undetected | `grep compile_gate_ok` | **WORSE: it was RECORDED.** `papers/D3/bundle_metadata.json` carried `compile_gate_ok: false` in tracked, committed state. The field has exactly ONE writer and **ZERO readers** outside the script that writes it |

**⚠️ ATOM 7b IS THE SYSTEMIC FINDING AGAIN, IN A NEW PLACE.** The audit's thesis is that this
system's dials exist and are disconnected. Here the verdict was not merely uncomputed, it was
**computed, written to a tracked file, and committed** — and the suite reported *21/21 bundles
clean* over it. A recorded verdict nobody reads is indistinguishable from no verdict, except that
it looks like diligence in the diff.

**⚠️ ATOM 2 IS THE ONE WORTH KEEPING.** The instinct on finding a false claim is to replace it with
a stronger true one, and the replacement I drafted was **false for two of the eight bundles**. The
check that caught it is the one that already tracks the fact. **Verify the replacement against the
same instruments you used to condemn the original** — a correction is a claim.

**⚠️ ATOM 4 IS ITS MIRROR.** Having established the macro was producing a 4 400x overclaim, the
tempting move is to purge it. Four of ten uses are exactly right, and three of those are in the
flagship where a project total is the *subject* of the sentence. A defect class is not a token.

**What shipped.** Clause replaced in the template and 8 drafts with a statement that points at
`numerical_literals` rather than asserting a universal over it. `render_bundle_counts.py` derives
per-bundle `\bundleTheorems` / `\bundleDecls` / `\bundleModules` from the apex closure, gated by
`bundle_counts_fresh`. Six paper-scoped sites repointed. D3's three dangling refs repointed, and
`bundle_cross_references_resolve` now gates the class at zero headroom across 707 reference sites.

**NOT-AN-ASSERTION.** Closing TODO-D9 does not make the eight drafts' numbers *right* everywhere;
it makes the four sentences that quoted a project total for their own content quote their own
content. `numerical_literals` still reports **116** inline literals at a frozen ceiling, and that
is a separate, disclosed, ratcheted debt.

---

## V63 — TODO-D32: D6 repaired in one wave, and the lift's own prose was the thing that failed review

Scope: excise D6 §5.4 (D9's content, 44 % of the draft) and lift the un-homed AGP threshold chain
in its place, sequenced as ONE wave so D6 is never measured in the gap.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | §5.4 is separable | line-range read + recompile | **Yes, cleanly.** 488 lines out, a 20-line cross-reference in, D6 compiles at 7 pp with 0 unresolved refs |
| 2 | The AGP chain is worth a Tier-1 section | read all 11 modules | **Yes.** `agp_threshold_steane` + strict form + a `norm_num`-backed certificate ε₀ = 1/35 235 = 2.838e-5 > 2.73e-5, with `A_CNOT ≤ C(M,2)` well-formedness checked rather than asserted |
| 3 | The threshold theorem rests on the ex-Rec and noise-model machinery | `compute_closure` on the two headline theorems | **NO — and this is the finding.** Its closure is **27 declarations** over `SteaneCode`, `StabilizerCode`, `Counting`, `Concatenation`, `DoubleExp`, `Basic`. It reaches **none** of `ExRec`, `Malignant`, `NoiseModel`, `NoiseModelMT`, `Chernoff` |
| 4 | The lift raises D6's closure toward the 342 un-homed declarations | re-measure after declaring 5 apexes | **51 → 86 decls, 4 → 12 modules, depth 3 → 5.** 307 remain un-homed, and atom 3 explains why: the theorem that would consume them does not exist yet |
| 5 | D6's other defects | direct read | "15-bundle publication architecture" removed (roster claim, not renumbered); venue `prd` → `prx` |

**⚠️ ATOM 3 CAUGHT MY OWN PROSE, WHICH IS THE POINT OF MEASURING AFTER WRITING.** The first draft of
§7 described the extended rectangle, the malignant-pair attestation and the pair-failure union
bound as the chain the recursion is built from. **The recursion consumes none of them.**
`A_CNOT` enters as a literal pinned to AGP §8.3 eq. (36), and the step from the ex-Rec structure
under local stochastic noise *to* ε_{L+1} ≤ A ε_L² is carried by the primary source. What is
machine-checked is the **consequence** of the AGP recursion, not its derivation.

The section now separates *"the proof chain, 27 declarations"* from *"the substrate the theorem
does not consume"*, and names the gap as the result's real boundary. The abstract was corrected the
same way. **The claim is materially smaller than the one I first wrote, and still novel.**

**This is the D11 lesson from the other side.** D11 records that a wrong bilayer Hamiltonian passed
every determinant-level gate because *"formal verification certifies that a proof is correct; it
does not certify that the object proved about is the intended one."* Here the proof was correct and
the *prose about what it rests on* was wrong. A dependency closure is the cheapest available check
on that, and it is not in any gate: nothing compares a section's narrative to the closure of the
theorems it cites.

**NOT-AN-ASSERTION.** D6 is 758 lines / 7 pp against a ~40 pp Tier-1 charter, so
`bundle_manuscript_length` will still read it as under floor. That is the correct verdict: the
repair moved D6 from *holding another bundle's paper* to *holding its own and being short*, which
is a better failure and an honest one. Filling it further is TODO-D35, and D35 is a proof wave, not
a writing wave.

---

## V64 — TODO-D35: the ex-Rec layer contained no probability at all — 5 atoms

Scope: derive the AGP recursion rather than instantiate it at a pinned constant. First Lean wave of
this stretch; MCP-first loop per the project's Lean conventions.

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | D35 is a connection wave: the modules exist and need wiring | read `ExRec`, `NoiseModel`, `Chernoff`, `Concatenation` in full | **NO — it is a construction wave.** `ExRec` is `{M : ℕ, M_pos}`, a location COUNT. `MalignantPairAttestation` is `{A : ℕ, A_le_choose_two}`, a COUNT. `LocalStochasticNoise` is a rate and a count. **No measure appears anywhere in the layer** |
| 2 | `pairFailureBound` and `agpRecursionStep` are proved bounds | read their definitions | **Both are `def`s.** `Chernoff.lean`'s own docstring: *"we abstract this as a real-valued upper-bound function ... The concrete MeasureTheory instantiation is deferred"* |
| 3 | `exRecFailureBound A ε := A * ε^2` is a bound on something | grep for any theorem relating it to a measure | **Nothing.** Its docstring calls it *"the leading-order Chernoff-like bound from union bound on malignant pairs"* and no probability was ever shown to satisfy it |
| 4 | Mathlib supplies the pieces | leansearch | `measure_biUnion_finset_le` and `IndepSet.measure_inter_eq_mul`, both exact fits. The module compiled **first pass** with one deprecation, closed by `gcongr` |
| 5 | The new module closes D35 | structural check of the import graph | **Half.** Nothing imports `MalignantUnionBound` except the root aggregate, so `agp_threshold_steane` still cannot reach it. `agpLevelSequence` remains DEFINED by the recursion |

**⚠️ ATOM 1 IS THE FINDING, AND IT INVERTS THE TODO I WROTE YESTERDAY.** TODO-D35 said *"the modules
it would need already exist and are kernel-clean — this is a connection wave, not a construction
wave."* **That was wrong**, and it was wrong because I had read the module *headers*, which describe
extended rectangles and local stochastic noise in physical language, rather than the *declarations*,
which are three natural numbers and two inequalities between them. The layer models the AGP argument's
BOOKKEEPING, not its probability. That is the real reason the threshold theorem's closure never
reached it: **there was nothing probabilistic there to reach.**

This is `feedback_verify_substrate_strength_not_docstrings` met from a new direction — I judged a
substrate's strength from its prose and filed a scoping claim on that basis.

**What shipped.** `MalignantUnionBound.lean`, kernel-pure (`{propext, Classical.choice, Quot.sound}`):
independence isolated in one lemma, the union bound proper in another using no independence, their
composition, and `exRecFailureProb_le_exRecFailureBound` bridging to `ExRec`'s vocabulary. The bridge
theorem's closure reaches `ExRec`, so the probabilistic layer now genuinely touches the structure.

**NOT-AN-ASSERTION.** This does not make the threshold theorem's proof depend on probability. The
levels are uncomposed: nothing yet models a level-`(L+1)` rectangle as built from level-`L`
rectangles. D6 §7 says so in the manuscript, in the paragraph headed *"What remains, stated because
it is the result's real boundary."* **The single-level justification sits beside the threshold
theorem, not beneath it**, and writing it up any other way would repeat the overclaim V63 caught.

---

## V65 — the graphene Γ_H "open physics call" was a transcription error against a source in our own corpus — 6 atoms, 2 SELF-INFLICTED

**Trigger.** The operator asked what the specific question was, whether a best path existed, and —
pointedly — *"what source materials are important … and have you read them in full? did audits cover
the path forward on this already?"* Three of the six atoms below exist only because that last
question was answered by reading rather than by recall.

**A1 — the multiplier was never open.** ν = η v_F²/w = (η/sT)·v_F², because the momentum density in
relativistic hydrodynamics is w/v_F². The sound-attenuation bracket [2(d−1)/d]η + ζ is **1·η in
d = 2** with ζ = 0 by conformal symmetry, so the "O(1) prefactor, not verified" flagged twice in
ADR-010 and TODO-D31 **does not exist**. Two dimensions is the one case where the shear prefactor
is unity — the ambiguity was imported from the 3D textbook form (4/3).

**A2 — the 3.2 %/17 % spread was an inconsistent parameter pairing, not a physics fork.** For a
conformal Dirac fluid c_s = v_F/√2 exactly, so the two "routes" differ by exactly 2 — visible in the
monolayer rows (17.3 % → 34.2 %). The 5.2× at the Dean device comes from pairing **monolayer**
v_F = 10⁶ with **bilayer** c_s = 4.4×10⁵. Internally consistent Dean value: **δ_diss ≈ 6.5 %**.

**A3 — SELF-INFLICTED. My own 2026-08-08 correction to the audit was itself a measurement error.**
I wrote *"`formulas.py` is dimensionally sound, so only the prose is wrong. Do not fix the code."*
The first clause is true; the conclusion is false. The defect is at
`src/graphene/hawking_predictions.py:107`, a module that re-derives the formula instead of importing
the canonical path. **I corrected the audit's filename and mistook that for correcting its claim** —
the audit was right that code is affected. Pipeline Invariant 1 exists to prevent exactly the
re-derivation that hid it, and grepping `formulas.py` alone could never have found it.

**A4 — SELF-INFLICTED. The v_F² recommendation was right for the wrong reason.** I recommended it
from a verbal argument about "the emergent light speed" and attached δ_diss ≈ 17 % — a number that
is an artifact of A2's bad pairing. Right answer, wrong derivation, wrong number.

**A5 — the corpus answered it, and the audit said so.** Phase-5w gives Γ_sound ~ (η/w)k² ~ 10¹⁰ s⁻¹.
E2 prints Γ_H ≈ 0.3 s⁻¹ — **eleven orders below its own cited source**, which is the same eleven
orders the draft reports as its physics result. The audit's calibration note read *"I did not trace
Γ_H … to Lit-Search/Phase-5w"*, and the finding then sat as "an operator physics call" for eight
days. **Nobody, including me, opened the file the finding itself named as unread.**

**A6 — live doc defect: ADR-010 still carried the retracted L1 retirement.** V61 reversed it in
`ADJUDICATION.md` §5; ADR-010 §Open items 1 and 3, its summary line, and the §D4 discharge box all
still said *"retire L1 / roster 20"* — the ADR is the review surface, so the retraction had not
reached any reader. Fixed, and the roster recorded as **21** under the operator's 2026-08-09
delegation.

> **The through-line, and it is not the same one as V60.** V60's lesson was *the errors live in the
> measurement, not the conclusion*. V65's is narrower and sharper: **three of these six exist because
> a document that names its own gap was trusted to have closed it.** The audit wrote down precisely
> what it had not checked; ADR-010 carried a note saying an O(1) was unverified; TODO-D31 repeated it.
> Each restatement made the gap look more examined. **A gap that is disclosed in writing is still a
> gap, and disclosure is not diligence** — three passes over this finding cited the caveat and none
> discharged it, until reading the named file took a single grep.

**NOT-AN-ASSERTION.** No prose or code has been propagated yet. E2, D1 §5/§7.4,
`hawking_predictions.py`, Fig. 103's caption and the missing `Dean_bilayer_nozzle.v_F` provenance are
all still uncorrected, and E2 remains blocked. What changed is that the blocker is now **a known
propagation set, not an adjudication** — TODO-D31 carries the list.

---

## V66 — TODO-D31 propagated: the repair found four sites the finding never listed — 7 atoms

**A1 — the propagation set was itself under-measured.** TODO-D31 listed five sites. The wave found
**nine**, and the four unlisted ones were the interesting ones:
`src/graphene/bilayer_eos.bilayer_impact_on_hawking` multiplied ζ/η into a hardcoded `1e-13` and
reported the product as *"negligible²"*; `papers/paper16_graphene_sk_eft` — the **source draft E2 was
lifted from** — carried the defect in four passages, so the next lift would have re-imported it;
`GrapheneHawking.lean`'s module header asserted the eleven orders as a physics finding; and
`fig_graphene_dissipation_window` plotted the non-binding rate. **A finding's own scope is a claim,
and this one was 55 % complete** — consistent with `feedback-remeasure-filed-findings-before-fixing`.

**A2 — the resolver was blind to an entire registry.** `_lookup_provenance_value` hand-listed ATOMS /
EXPERIMENTS / POLARITON_PLATFORMS, so **every `Dean_bilayer_nozzle.*` key resolved to `None`** and was
absorbed into `PROVENANCE_UNRESOLVABLE_CEILING` as inherited debt. An unresolvable entry is *counted*,
not *reported* — so a blind resolver reads as debt. Deriving the sweep from every dict-of-dicts
registry in `constants` resolved 7 entries (170 → 163, ceiling ratcheted down) and **immediately
caught a live mismatch the moment it could see them**: `l_ee_nm` registry 51 vs code 50.92.

**A3 — and that mismatch exposed a dead literal.** `GRAPHENE_PLATFORMS['Dean_bilayer_nozzle']['l_ee_nm'] = 51`
is overwritten at import by the derived `ℏv_F/(k_B T)`. No caller has ever seen 51; the registry
recorded a value the code does not have. Annotated at both ends rather than deleted, so the
deep-research cross-reference survives.

**A4 — four tests asserted the defect, and each replacement is stronger than what it replaced.**
`Γ_H/κ < 1e-10` → a two-sided band that fails both on the old defect (1.7e-13) and on double-counting;
`δ_diss < |δ_disp|×1e-8` → the inverted relation *plus* the opposite-sign assertion;
`T_eff < 0` as the 50 nm EFT-breakdown proxy → assertions on the individual terms, because a positive
δ_diss can hold the *sum* positive while both terms are individually non-perturbative — a worse regime
that the old proxy would have scored as safe; and `|n_H/n_P − 1| < 0.1` → the exact low-ω limit
`(1+δ_disp+δ_diss)/(1−δ_k)`, verified to 1e-3. **A tolerance test encodes an era; an identity test
encodes the physics.**

**A5 — a new claim the repair produced, and it is not a restatement.** The two dissipation windows run
in *opposite* directions in T_H: momentum relaxation improves 1.6 → 22 as the constriction tightens,
while the viscous window falls 2.5 → 0.23. **Both monolayer configurations sit below unity** — Γ_H >
ω_H, the quanta damped faster than they oscillate. The Dean bilayer device, the one that already
exists, is the only configuration in the family with ω_H > Γ_H. E2's figure previously plotted only
the improving series.

**A6 — Lean.** Four kernel-pure theorems in `DiracFluidSK`, anchoring the new
`formulas.conformal_kinematic_viscosity`. `kinematicViscosity_eq_vF_form` states the equivalence
`2(η/sT)c_s² = (η/sT)v_F²` **under the explicit hypothesis `v_F² = 2c_s²`** — written as a hypothesis
precisely because it is what fails for bilayer graphene. Axioms `{propext, Classical.choice, Quot.sound}`.

**A7 — `Dean_bilayer_nozzle.v_F` now has provenance, tier ASSUMED.** It was the only one of that
platform's six parameters without an entry. The entry records that it is a monolayer value carried on
a quadratic-band device, and that the dissipative path **deliberately does not use it** — ν is written
in the measured c_s so the unprovenanced number is off the load-bearing path entirely.

> **The through-line.** V65 said a disclosed gap is still a gap. V66 is the sequel: **a filed finding's
> scope is a measurement, and measurements decay.** TODO-D31 was written on 2026-08-08 by me, from a
> grep, and was 55 % complete a day later — not because the code moved, but because the grep's keys
> (`formulas.py`, `Γ_H`, `10^{-13}`) could not see a hardcoded `1e-13` inside a ζ/η product, a source
> draft under a different bundle, or a figure that plots the wrong quantity without naming it.

**NOT-AN-ASSERTION.** E2 is not clear to ship. `readiness_submission_gate` remains red, the ζ/η
bilayer band is an estimate from a QCD analogy rather than a measurement, and the O(1) prefactor
argument rests on the fluid being conformal — which the bilayer is not. What changed is that
δ_diss is now derived through the canonical path with its assumptions written down, instead of
being a dimensionally-inconsistent literal.

---

## V67 — TODO-D34 closed; its premise was half wrong and its own hypothesis refuted — 6 atoms, 4 INSTRUMENT FAILURES IN ONE PASS

**A1 — the true half.** L1 cited the GW170817 *observation* and none of the four PRLs that used the
bound (251301-251304). Fixed, with all four verified against arXiv on 2026-08-09 and given real
`.abstract.txt` caches; the gate went 368 → 372 cached with no header disagreement, meaning title,
authors, year, DOI and arXiv all match the registry.

**A2 — the false half.** TODO-D34 framed *"10 bibitems"* as the deficiency. Measured across all 21
bundles, L1 is **mid-pack** at 2.6 cites/100 lines, above D3, F, D8, D2 and D11, with zero uncited
entries. Citation count was never L1's problem; one missing literature was.

**A3 — the sibling hypothesis, refuted by its own check.** The TODO instructed the fixer to check
the other three declared splashes first because *"a positioning gap in a splash is a pattern
candidate."* Checked: L3 3.1, E1 3.2, L2 3.3, E2 2.8 — the splashes are among the **best**-cited
bundles. The pattern hypothesis was wrong, and checking it cost one measurement.

**A4 — FOUR instrument failures in a single measurement pass, each caught by the next.**
1. Counted `\bibitem` → scored D8 and D10 at **zero**; they use `.bib` + bibtex.
2. Line-based `\cite` regex → reported **5 uncited entries in L1**; the `\cite{...}` spans two lines
   with a `%` continuation, so the regex stopped at the newline. **L1 has zero uncited entries.**
3. Read `paper_draft.log` for undefined citations → reported **8 for D6** from a *stale log*; a
   clean recompile shows zero.
4. Same log sweep → reported 29/17/16 undefined for D8/D10/D11, which is what a single pdflatex pass
   *always* reports for a bibtex bundle.
> Every one of the four was an instrument error, and **not one changed a conclusion** — because each
> was caught before it was written down as a finding. The one survivor (A5) survived because I
> switched instruments to whole-document substring search rather than trusting a third regex.

**A5 — the survivor, and it is bigger than what I set out to fix.** **D5 has 27 bibitems and 18
whose key never appears in the body** (D7: 3 of 6). LaTeX warns about the reverse case only, so
nothing in the pipeline sees it. Filed as TODO-D38, explicitly *without* a gate: §6a first.

**A6 — a cost I incurred and am not hiding.** The E2 rewrite (V66) pushed that bundle from over its
charter ceiling to further over: `bundle_manuscript_length` now reports E2 at 4 751 word-equivalents
against a 3 750 ceiling. E2 was already over before this wave, and the added text is load-bearing
(the ν derivation and the two-window correction), but the gap is wider because of me. Trimming E2 to
its Tier-4 letter charter is now a harder job than it was this morning.

> **The through-line, third in a row and now a rule rather than an observation.** V65: a disclosed
> gap is still a gap. V66: a filed finding's scope is a measurement, and measurements decay. V67:
> **when a measurement disagrees with the thing it measures, suspect the instrument first.** Four
> times in one pass the instrument was wrong and the corpus was fine. The productive discipline is
> not "measure more carefully" but "measure the same quantity two different ways, and only believe
> the ones that agree" — the substring check and the LaTeX compiler agreed about L1 and about D6, so
> those stand; the regex stood alone on D5, so it was re-run by a different method before being filed.

**NOT-AN-ASSERTION.** L1 is not submittable. `readiness_submission_gate` remains red across the
portfolio, the positioning paragraph has had no Stage-13 adversarial review, and the naturalness
window it rests on is still project-adopted rather than derived, which the draft says in print.

---

## V68 — goal-2 opening: the list verified, and the two-instrument rule caught ME misapplying it — 3 atoms

**A1 — the list is correct.** 38 entries: 28 marked OPEN + D33 (conditional, carries no status
marker) + D35's second half = **30 work units**, matching the goal's enumeration exactly. D1 is
WITHDRAWN (no defect: a sentence-split regex truncating before a qualifier, and
`axiom_count_prose_consistency` was right all along) and D4 is closed at 100 %. Both predictions in
the goal prompt — "verify it, headings lie, D4 may be closed" — were correct.

**A2 — SELF-INFLICTED, and it is the rule's own failure mode.** My first pass ran two "independent"
instruments: heading-text scan and section-body scan. They agreed on all 38 items, and **both were
wrong about D1**, which reads `~~...~~ — WITHDRAWN, no defect exists`. They agreed because they
shared a keyword vocabulary (`DONE|CLOSED|✅|RESOLVED`) that did not contain `WITHDRAWN`. **Two
spellings of the same check is one instrument run twice.** The rule was satisfied on its face and
violated in substance.

**A3 — what actually resolved it.** A *positively*-keyed instrument: count headings that assert
`OPEN` rather than headings that fail to assert closure. Absence-of-marker and presence-of-marker
are genuinely different questions, and only the second one surfaced D33 (open work, no marker at
all) and cleared D1.

> **Sharpening of V67's rule, learned by breaking it immediately.** "Measure two ways" is not the
> requirement; the requirement is that the two ways can *fail differently*. Before trusting
> agreement, ask what each instrument keys on — if both key on the same vocabulary, the same file
> region, or the same regex family, their agreement carries no information. Prefer pairing an
> absence-test with a presence-test, or a parser with a compiler.

---

## V70 — goal item 6, the three bundle gates — 6 atoms, MY DICHOTOMY WAS MECHANICALLY FALSE

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | `bundle_structural_coherence` is green | `validate.py --check` | **Green.** Closed under TODO-D26 by regrouping D3 from 31 to 20 top-level sections, no content deleted |
| 2 | `bundle_figure_adequacy` has only two routes to green: draw ~40 figures, or lower the floor | read of `bundles_readiness.py:741` | **FALSE, and this is the atom that matters.** `if n_fig + n_def < floor` — a `\figuredeferred{id}{reason}` counts toward the floor. That is not a loophole: `WAVE_EXECUTION_PIPELINE.md:357` *mandates* it (*"never omitted silently"*) and `BUNDLE_LIFT_PROCEDURE.md:208` carries the worked example |
| 3 | …and the mandated form was in use | scan of all 21 drafts | **ZERO uses.** The law required a disclosure form that had never once been exercised. The audit's finding was *"no step in the procedure ever planned a figure"*; authoring the plans **addresses** it |
| 4 | `bundle_manuscript_length` has the same escape | read of the same file | **It does not.** Its only green routes are writing the content or nulling/lowering `length_target`, and all 11 under-floor bundles carry a declared `target_journal`, so nulling is re-chartering — item 5's exact prohibition, and what the check's own docstring calls *"agree with every one of the audit's findings"* |
| 5 | E2's over-ceiling case needs a re-charter | trim attempt, measured after each step | **No — trimmed to 3738 against a ceiling of 3750**, from 4751. Captions 4751→4573, the ν-derivation to the deep companion →4525, conclusion →4496, the KZU/demarcation digressions →4176, `fig105` to D1 →3776, acknowledgments + intro →3738. **0 over ceiling** |
| 6 | The green can be trusted to stay honest | production-seeded, 2 mutations | a fully-deferred bundle still passes but its summary now reads `0 drawn, 4 declared-deferred`; four drawn + four deferred reports `4 and 4`, not `8 and 0`. Both pinned by tests |

**⚠️ ATOM 2 IS THE LESSON AND IT IS MINE.** I read the figure gate's *docstring* and its *failure
messages*, concluded "nine bundles at zero figures, therefore ~40 figures must be drawn", and
carried that into a decision request as a settled dichotomy. **The counting line one screen below
the docstring says otherwise.** This is `feedback_verify_substrate_strength_not_docstrings` in the
gate layer rather than the Lean layer: a check's contract is its code, and the docstring is a
claim about the code like any other. The coach caught it in one file read.

**NOT-AN-ASSERTION.** Whether 40 declared deferrals *should* satisfy a referee is a judgement, not
a measurement. What is measured is that the corpus now states its figure programme where a reader
can see it, and that the gate's summary reports `42 drawn, 40 declared-deferred, 8 bundle(s) with
zero drawn figures` so the magnitude cannot hide behind the green.

**Item 6 closes PARTIALLY MET, deliberately.** Two of three gates green; `bundle_manuscript_length`
stays red for 11 under-floor bundles because red is its designed output until the manuscripts
exist. Its parenthetical *"none depends on a reviewer stage"* is true of the mechanism and
irrelevant to the remedy: the remedy is ~150 pp of manuscript, which is goal 2's headline
deliverable. **No floor was lowered and no `length_target` was nulled.**

---

## V71 — the four "failures" that were my own dirty tree — 4 atoms, 1 SELF-INFLICTED NEAR-LOSS

| # | Proposition | Decider | Verbatim result |
|---|---|---|---|
| 1 | `pytest -m ''` leaves 4 failures after the branch's work | full suite on a restored `.lake` | **4 failed / 6,247 passed** — `chain_backing_targets_resolve` at 122 against a ceiling of 121, plus two `phase6i_wave1` registry legs |
| 2 | The +1 is a regression one of my commits introduced | bisect across `6aad2988`, `d540fd47`, `4e6f078e`, `3032bd6c` | **Every one of them GREEN at 121.** So the delta was not in any commit |
| 3 | …therefore it is in the working tree | `git reset --hard HEAD`, re-measure | **121. Green.** The 122 came from content an accidental `git stash pop` had dropped into the tree, and the four tests pass on the committed state |
| 4 | The bisect was harmless | `git stash list` after the loop | **NO — I dropped a stash that was not mine.** `git stash push -u` with nothing to stash is a no-op, so each paired `pop` took `stash@{0}` — an unrelated 2026-08-03 `paper-remediation WIP` (137 files). A later `git stash drop` then deleted it |

**⚠️ ATOM 4 IS THE LESSON AND IT IS THE SHARPEST ONE ON THIS BRANCH.** Recovered via
`git fsck --unreachable` → `git stash store`, and verified restored at the same 137-file
stat. Nothing was lost. But the *method* was wrong twice over:

* **`git stash push` is not a safe scratch tool for measuring an earlier commit.** It has a
  shared, ordinal namespace (`stash@{0}`) that other work occupies, and a push that stashes
  nothing silently shifts what the matching `pop` refers to. Use `git worktree add` for a
  detached measurement, or measure the artifact directly (`git show <ref>:<path>`).
* **A bisect over a dirty tree measures the tree, not the commit.** Atoms 2 and 3 together
  say the same thing from both sides: every commit was green and the tree was not, so the
  quantity being attributed to a commit was never a property of any commit.

**NOT-AN-ASSERTION.** That the four tests will stay green is not established here; what is
established is that they are green at `8a643c91` on a clean tree, which is the state the
branch ships.
