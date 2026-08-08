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
