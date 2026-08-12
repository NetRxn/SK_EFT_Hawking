# The remediation loop — design

**Date:** 2026-08-12 (rewritten same day, scope expanded on operator ruling)
**Status:** spec, pending implementation plan
**Implements:** ADR-012 in full — D1 through D22
**Reconciled with:** ADR-002 (ratchet shape) · ADR-004 (single-writer posture) · ADR-005/007 (the
atlas the `lean` lane points into) · ADR-006 (the Aristotle gauntlet) · ADR-008 (worktree slots) ·
ADR-009 (the check contract §4 obeys) · ADR-010 (§D5a apex model; §6a's build-approval constraint,
which §4 satisfies rather than waives) · ADR-011 (`prose` gates; `record_review.py`, the model for
the writer). Per-ADR detail lives in ADR-012 §Overlap reconciliation and is **not** restated here.
**Supersedes:** this file's own first version, which covered only the ledger's write side. That
scope was a strict subset and survives intact as **§4 (Closure)**.

---

## Why this exists

A review produces findings. Findings become graph nodes. **Below BLOCKER severity, a node blocks
nothing and routes nowhere** — which is how an I1 review closed with seventeen REQUIRED and seven
RECOMMENDED items that were recorded and not tracked. Above BLOCKER, a finding can only be retired
through `docs/review_finding_supersessions.json`, which had **no writer**: all 870 records were
hand-typed, and 66 of the `review:`-scheme ones name no node at all, so the findings they meant to
close still read `open`.

Between those two facts sits the whole problem. The system knows what is wrong and knows nothing
about who repairs it, in what order, with which gates, or when a human is genuinely needed.

This spec designs the loop end to end: **emit → type → route → schedule → execute → verify → close
→ observe.**

### The correction history, because it is load-bearing

Three instruments have corrected this design, and each found a class the previous one could not:

1. **The 117-finding triage pilot** shrank it — two of four proposed fields already existed in the
   reviewer template and were merely discarded at extraction.
2. **An adversarial review of the ADR, spec and plan** found that the first spec proposed to build
   a check that already exists, that one proposed guard could never fire, and that the plan omitted
   every registration obligation a new check carries.
3. **An intent-drift assessment** found the first spec had solved the closure half and dropped the
   routing half, including the originating problem.

The generalisable lesson, and the reason ADR-012 D18 codifies the process: **a specification that
nobody adversarially reviews produces a first draft like the one this replaces.**

---

## Measurements

Re-measured at HEAD, 2026-08-12. Re-derive before acting on any of them.

| quantity | value |
|---|---|
| `ReviewFinding` nodes | 1,631 — open 1,028 · fixed 481 · accepted 122 |
| severity | advisory 462 · major 430 · minor 426 · critical 313 |
| open critical / open major | 152 / 219 |
| ledger records | 870 |
| orphans — `review:` scheme / legacy schemes | **66** / 190 |
| `ReadinessGate` nodes | 704 — passed 483 · blocked 113 · open 69 · needs-recheck 39 |
| gates whose `blockers` payload is prose, not a reference | 145 |
| `FLAGS` edges | 4,879 |
| `qi_register.py --stats` | **1,631 findings in → 0 QI items out** |
| non-blocking closures that would flip on unscoping the bar | **0** (all 231 already meet it) |

Two of these decide design choices rather than merely describing state. **66 is exactly the frozen
baseline of the guard that already exists** (§4). **0 is the blast radius of unscoping the closure
bar**, which is what makes that change cheap.

---

## Architecture

Six participants. Three are new.

| participant | role | change |
|---|---|---|
| the three markdown reviewers | emit findings | template gains four lines (D1) |
| `build_graph.extract_review_finding_nodes` | mints ids, parses fields, reads the ledger, applies the closure bar | parse six fields; emit `BLOCKED_BY`; unscope the bar |
| `docs/review_finding_supersessions.json` | the closure ledger | schema amended |
| **`scripts/close_finding.py`** | the only supported writer | **new** |
| **the bundle-green gate** | REQUIRED enforcement, ratcheted | **new leg on an existing check** |
| **the dashboard** | the operator's control surface | **five surfaces, two repairs** |

### Two load-bearing constraints

**The id minter is shared, never copied.** `close_finding.py` imports `mint_finding_id` from
`build_graph`. A second implementation reproduces the orphan class by construction. Precedent:
`_recurrence_norm` was moved to module scope for exactly this reason, after a period in which the
production matcher could have been deleted or inverted with its test still green.

**No new mechanism lands beside a working one.** This is `CLAUDE.md` rule 1, and this spec's own
first version violated it — see §4.

---

## 1. Emission and extraction (ADR-012 D1, D2, D10, D17)

### The finding record

Six fields beyond `severity` and `status`. Two are already written by reviewers and thrown away;
four are new lines in the template.

| field | source | corpus | absent means |
|---|---|---|---|
| `blocks` | existing `- **Gate:**` line | whole corpus, immediately | `none` — advisory |
| `target` | existing `- **Location:**` line | whole corpus, immediately | `unknown` — not dispatchable |
| `lane` | new template line | forward-only | `unclassified` |
| `verify` | new template line | forward-only | no `verified_by` requirement at closure |
| `blocked_by` | new template line, optional | forward-only | dispatchable now |
| `needs_operator` | new template line, optional — `now` \| `queue` | forward-only | no operator gate |

Measured coverage of the two parsed fields: **93% carry `Gate:`, 92% carry `Location:`**. The
retrofit the first draft called unaffordable is a parser change.

**Binds three emitters, not five** (ADR-012 C3): `adversarial-reviewer`, `claims-reviewer` in bundle
mode, `figure-reviewer` in bundle mode. `claims_review.json` is per-sentence verdicts under
`sentence_state.py`, not work items. `prose-reviewer` emits a restructuring instruction and no
findings by design.

### Enforcement

`review_severity_declared` is **extended**, not paired with a sibling. It already validates a
declared token against a map (`build_graph._SEVERITY_DECL_MAP`), which is the same shape as
validating a lane. Its population is findings emitted from the contract date forward; historical
findings read `unclassified` without failing.

### `lane` is not `needs_operator`

`lane` says who does the work. `needs_operator` says who decides. They are orthogonal: a `lean`
finding can need a physics call, a `substrate` finding can need a scope decision. Folding the second
into a seventh lane — the first draft's shape — hides operator-owned Lean and substrate findings
inside `infra`.

### `BLOCKED_BY` — the edge that makes it a DAG

`blocked_by` emits a `ReviewFinding → ReviewFinding` edge. A finding with an unclosed `blocked_by` is
not dispatchable; closing a finding re-evaluates everything that named it. That re-evaluation is the
cascade the operator's step 4 asked for.

⚠️ **Two obligations, both from failures already shipped here.** `KNOWLEDGE_GRAPH.md` carries three
edge types that gates query and nothing emits, and `PRODUCES` sat expired for a whole wave because a
prose-regex fallback fired and masked it. So `BLOCKED_BY` ships with a consumer and a seeded-defect
test proving the consumer sees it. And a `blocked_by` naming an id that mints no node **fails
loudly** — silently dropping it is the 29% orphan class one layer up.

⚠️ **This field also carries §5.1's external release-condition tokens, so discrimination is
explicit.** A prefix matching a **declared** scheme (`run:` · `phase:` · `pub:` · `research:`) is a release condition and never resolves to a node. Everything else must resolve to a
minted id or fail — **including an unrecognised scheme**, so `runs:42` fails rather than becoming a
blocker nothing can satisfy. The scheme list is declared once and validated against, on the shape of
`_SEVERITY_DECL_MAP`.

### Orientation is generated (D17)

`scripts/review_runner.py --prep-brief` already generates a review-prep brief. The same generator
gains a **per-finding** mode keyed on `target`: source files, the Lean declarations in its closure,
the formulas and constants it touches, the authorizing roadmap, and the relevant git history.

The finding carries its pointers; the worker does not go looking. This is also what makes the
decision package (§3) affordable — four of its five elements are generated rather than researched.

---

## 2. Gating (ADR-012 D9)

⚠️ **CORRECTED 2026-08-12.** This section previously said REQUIRED blocks nothing until D9 lands.
**False, and never traced to code before being written.** `readiness_gates.py:856` sets
`BLOCKING_SEVERITIES = {'critical','blocker','major'}`, `bundle_readiness.py:391` counts `major` into
`n_blockers`, and `bundle_stage13_claim_consistent` compares a green claim against that count.
REQUIRED already blocks the gate, the readiness verdict and the green claim.

**What is missing is a population guard.** Every existing mechanism asserts *consistency*; none
asserts the open-REQUIRED population **cannot grow** — and `bundle_stage13_claim_consistent` fires on
zero rows today, since no bundle claims `stage13_status: green`. A bundle can accumulate REQUIRED
findings indefinitely without tripping anything.

**So D9 is a down-only ratchet on the open-REQUIRED population**, per bundle, as a new leg on
`bundle_stage13_claim_consistent` — not a new severity tier, which already exists.

**It extends `bundle_stage13_claim_consistent`**, which already forbids a `green` Stage-13 while the
live graph carries open blockers, by adding a severity tier to the same assertion. A sibling check
would be §4's own failure repeated.

⚠️ **Measured coverage: 167 of 219.** 52 open majors (23%) and 19 open criticals carry no
`inferred_bundle` — silent-drop point 1 — so they attach to no bundle ceiling. Left there, the gate
also creates a perverse incentive: a finding that *loses* attribution silently leaves the ratchet. So
**two ratchets ship, not one** — the per-bundle ceiling, and a corpus-wide down-only count of
unattributed open blocking findings frozen at 52/19. Both may only shrink.

**Ratcheted per bundle, down-only, frozen at the live count**, on the same shape as
`NATIVE_DECIDE_BUNDLE_DEBT` and `UNDECLARED_APEX_CEILING`. 219 open majors across the roster would
otherwise take every bundle non-green on the first run, and **a gate that fires on the existing
corpus gets switched off** — a lesson this project has recorded twice (`bundle_source_freshness`
under `--strict`; the pre-ADR-011 figure-prefix literal). Zero headroom per bundle. Lower in the
commit that lowers the population; never raise.

The ceiling is the on-ramp and the distance marker, not the destination. Zero open majors is the
target state.

---

## 3. The operator path (ADR-012 D11, D12)

### The decision package

A finding carrying `needs_operator` is **not routed until it carries all five**:

1. **Orientation, generated** — §1's per-finding brief.
2. **Ground truth vs. best case** — what is true now, what correct looks like, the distance.
3. **Substrate delta** — has anything moved that should change the target? An explicit answer,
   including "no".
4. **Research done or dispatched** — the three-tier ladder run to the tier the question needs, with
   the cited report vetted by the lead. A `research` finding that has not run the ladder is not
   ready for the operator.
5. **Two or more options with tradeoffs, a recommendation, and what changes if the answer goes the
   other way.**

**A finding surfaced without a package is deferred, not routed.** Defining it that way is the point:
the failure mode is an agent escalating early with a question it could have answered itself.

### The `infra` lane's three dispositions

1. **Fix now** — mechanically obvious, defined so it is not a judgment call: no physics judgment,
   no public API change, and a test can be written that fails before the fix and passes after. All
   three, or it is not obvious.
2. **Ask now, non-blocking** (`needs_operator: now`) — surfaces immediately; the loop keeps working
   everything else meanwhile.
3. **Queue** (`needs_operator: queue`) — enters the operator queue with its package, and the
   operator is told it is there. This is the "suggestion box", and where `/skeft-qa:harvest`'s
   System-2 register splices in.

---

## 4. Closure (ADR-012 D6, D13, D14)

### `scripts/close_finding.py` — the writer the ledger never had

```
--doc PATH            review document containing the finding
--section N.N [N.N …] one or more section numbers
--status              fixed | accepted | reopened
--evidence TEXT       what was done, where, when
--commit SHA          }  at least one anchor required
--date ISO            }
--verify CMD          optional; run before writing, must exit 0
--superseded-by ID    optional; the re-review that confirmed it
--dry-run
```

Modelled on `scripts/record_review.py`, which closed this exact class of gap for bundle status and
whose docstring calls itself *"the writer transition 2 never had"*.

⚠️ **A conflicting pre-existing record is a REFUSAL, not an exception.** A raise mid-batch escapes
after some records are already written to a tracked file, so `close()` returns `(False, msg)` like
every other refusal and the conflict lands in the refusals log.

**Refuses to write when:**

1. the minted id matches no live node — and prints the ids the document *does* mint, so the caller
   sees real section numbers instead of guessing. This is the difference between a tool that
   prevents the orphan class and one that complains about it;
2. `evidence` is under the bar;
3. no anchor is supplied;
4. a `--verify` command is supplied and exits non-zero.

**Multiple sections write one record each**, sharing the evidence string — meeting the need that
produced `…:D5:5.1+5.2+5.3` without breaking the one-id-per-record invariant the reader depends on.

**Writes are atomic** (temp-and-replace). A crash midway through rewriting the only closure channel
produces exactly the malformed-ledger state every reader is told to fail closed on.

**A conflicting existing record is a refusal, not a second append.** Four duplicate `finding_id`s
already exist; the reader is last-wins and does not say so. Appending a second record with a
different status under an undocumented selection rule is the "silently does nothing" class this
script exists to remove.

### The bar

Two changes, both inside the mechanism that already exists — never beside it (ADR-012 C8).

1. **Remove the severity scoping.** It is gated on `severity in ('critical','major','blocker')`;
   below that line any two-key record closes a finding. Since `- **Severity:**` is body-declarable
   and beats the heading glyph, and `_SEVERITY_DECL_MAP` maps `recommended → minor` (verified at
   HEAD), a 🔴 heading declaring `recommended` closes on two keys. Filed, open across four rounds,
   reproducing at HEAD.

   **Measured blast radius: 0.** All 231 currently-closed non-blocking findings carry a record and
   every record meets the bar. Measured before the change rather than discovered after it.

2. **Require `verified_by`** when the finding carries a `verify` command. ⚠️ **This is inert unless
   §1 ships with it** — no finding can carry a `verify` command until the extractor parses one, and
   a parameter with no producer is a leg that cannot fire on any input. That is why routing and
   closure are one build.

The bar is extracted to a module-scope predicate so a test binds the real implementation rather than
re-deriving it.

### ⚠️ The ledger-integrity check already exists — do not build a second one

`ledger_ids_resolve` runs today as a leg inside `check_graph_integrity`
(`scripts/validation/checks/graph_atlas.py`), pinned at `_LEDGER_DANGLING_BASELINE = 66` with zero
headroom, mutation-verified against the correct host. It is deliberately scoped to the `review:`
scheme with the reason stated in code: legacy `bundle-stage*` records were never graph nodes.

**This spec's first version proposed `ledger_finding_ids_resolve` at a ceiling of 247, claiming
nothing had measured it.** 247 is the aggregate over three schemes; the live `review:`-scheme count
is 66, which is the existing baseline exactly. The proposed replacement was also weaker: one ratchet
over 190 permanently-inert legacy records plus 57 live ones means deleting a legacy record silently
buys a free slot for a real dangling closure.

Two permitted moves:

- **Promote** the leg to a registered check in `reviews.py` — defensible on its merits (independent
  `--check` run, own constant, own mutation entry) — **and delete the leg in the same commit**;
- **Widen** to the legacy schemes only with a reason that engages the existing exclusion rationale,
  and only as a **separately-ratcheted second population**.

A promotion carries every registration obligation a new check carries, and the plan must name each:
`validate._CANONICAL_ORDER` (whose absence **raises**, taking the suite down rather than failing one
test), the `validate.py` re-export, a `MUTATION_VERIFIED` entry naming a real **production-seeded**
test (`AWAITING_MUTATION_TEST` is empty and `AWAITING_CEILING` is 0, so deferral is unavailable),
`CI_MIN_CHECKS_RUN`, and a regenerated `SURFACE_INVENTORY.md` **in the same commit**.

### Schema amendment

`_entry_format` gains the anchors the reader actually accepts — it declares `date` while
`build_graph` accepts `commit`, `date`, `closed_date` or `applied_at` — and one new field:

```
verified_by: {command: string, exit_code: int, run_at: ISO-8601} | null
```

`superseded_by` remains optional. Nine records whose keys carry suffixes no minted id has
(`…:3.1-residual`, `…:5.1-5.3`) are re-keyed, each carrying a note naming its former key. ⚠️ The
pipeline law calls the ledger **append-only**; re-keying edits in place, so the exception is stated
in `WAVE_EXECUTION_PIPELINE.md` in the same change rather than taken silently.

---

## 5. The operator control surface (ADR-012 D15)

The loop routes work away from the operator. The dashboard is how they keep oversight while that
happens, and how they sign off on publication content. **Shipping the loop without it produces a
system that is more autonomous and less observable at the same time**, which is why this is not a
follow-on.

### Five surfaces

| # | surface | answers | built from |
|---|---|---|---|
| **S1** | **Finding drill-through.** Gate-cell blockers resolve to the `ReviewFinding` itself — severity, lane, target, `verify`, closure record, `blocked_by`, and the ledger record that closed it | *what exactly blocks this, and what is its disposition?* | the 4,879 `FLAGS` edges, currently discarded at render; the 145 gates whose `blockers` are prose |
| **S2** | **Portfolio Flow board** — roster rows × pipeline-stage columns, overlaid with open findings by lane | *where is everything, and what is the bottleneck?* | `stage*_status` + gate states + `lane` |
| **S3** | **Attention** — four feeds side by side, unmerged | *what needs me, and what can I decide well right now?* | four separate stores |
| **S4** | **Reading-while-blocked.** A margin marker in Paper Provenance v2 when a sentence's backing artifact carries an open finding | *I am reading §4 — is anything under it broken?* | existing `BACKED_BY` chains + `FLAGS` |

S1 and S4 are render changes over data already in the graph. S2 and S3 are new views; their content
is pinned below and their **layout** is iterated against real use.

⚠️ **Dashboard work carries two gates the `infra` lane does not otherwise name.** `validate.py` and
the plugin surface tests cannot see a rendering defect, and a Flask test client **never executes page
JavaScript** — so a template rendering an empty panel passes everything. Every surface here ships
with a **template-contract test** (the server hands the template the keys it reads) and a **real
browser test** driving the rendered page. Without both, an empty surface is indistinguishable from a
clean one, which is this repository's signature defect.

### S2 — the Flow board

**Rows** come from `bundle_registry.BUNDLE_CODES`, never a hand-written list.

| column | source | note |
|---|---|---|
| draft exists | `papers/<B>/paper_draft.tex` + compiled PDF | |
| §7.5 read-through | *(no field today)* | `prose-reviewer` mints nothing by design — renders **not tracked**, never passed |
| S9 figure | `stage9_status` | |
| S10 claims | `stage10_status` + `claims_review.json` presence | absence is its own state |
| S12 sync | freshness checks | |
| S13 adversarial | `stage13_status` + `stage13_review_kind` + `stage13_redo_required` | only `full-adversarial` earns green |
| submission | `readiness_submission_gate` + `blockers_open` | |

⚠️ The status enum has drifted — three of the five live values are undeclared (`pending-redo`,
`skeleton`, `not_started`). An unrecognised value renders **as itself**, never coerced to the nearest
known state, on the same discipline `BUNDLE_READINESS_HEATMAP.md` already follows.

**The overlay is the bottleneck signal:** open findings per bundle, broken down by lane. That is what
turns "D3 is yellow" into "D3 is held by six substrate findings".

⚠️ **`/goal`-level activity IS surfaced (§5.2); subagent slots are not.** A loop runs for hours to
days and already emits a marker, a per-compaction heartbeat and a convergence signal. Worktree slots
turn over in minutes and are deliberately excluded — a board tracking them would be stale between
renders.

⚠️ **Two of this board's own fields rest on known-soft signals.** `ARCHITECTURE_TODOs` D50 (a bundle
can register Lean modules the build does not contain) and D51 (the length gate keys on mtime, so one
identical rewrite blanks all 21) are open and are not this spec's to fix. S2 renders both; it must
name what guards each rather than present either as authoritative.

### S3 — Attention: four feeds, not one list

Operator ruling: *"could be the same page, separate pages — not forcing aggregation/combination is
fine."* Merging them would destroy the property that makes each legible.

| pane | feed | store | state today |
|---|---|---|---|
| **Publication** | System-1 findings needing a call | `ReviewFinding` nodes + `docs/QI_REGISTER.md` | exists; QI derivation emits 0 until repaired |
| **Process** | System-2 dev-loop/harness findings from `/skeft-qa:harvest` | `docs/dev-loops/SYSTEM2_REGISTER.md` — `## Open`, `### <slug>`, tiered | exists; **gitignored, local-only, 840 KB** |
| **Decisions** | PD-3's second legitimate stop | **`.claude/dev-harness/blocked_questions.jsonl`** | written by the guard **and already read** — see below |
| **Parked** | authorized work on an external release condition | roadmap prose across 119 files | **no machine-readable state — §5.1** |
| **Loops** | armed `/goal` instances (ADR-012 D20) | `.claude/dev-harness/managed/` + `snapshot_*` + `stall_history/` | **exists today; never surfaced — §5.2** |

⚠️ **The blocked-question log is not unread.** `coach` reads it in-time (the `PreToolUse` guard
denies, logs, redirects, and the coach returns one decision plus one next action), and the harvest
skill hands a watermarked span to `harvest-extractor` → consolidator → System-2 register →
`/skeft-qa:debrief`. **The gap is a surface and a latency floor**, not a reader: a question reaches
the operator only after a harvest (cadence 4 h) through an 840 KB gitignored register, with no view
saying any are waiting. Feed C shortens that path for questions the coach could not settle.

⚠️ **Feed B should read `active_issues.json`, not the 840 KB register.** That file is written by every
harvest and **read by nothing** (`_read_active_issues` has zero callers), and it already carries
`{title, tier, tally, kind}` — aggregated and tiered, exactly the pane's shape. This turns a
documented dead artifact into the backing store.

**Process is read-only.** `/skeft-qa:debrief` is the structurally human-only governor for promotion,
closure and misfiling; a second write path would break the `_clamp_tier` guarantee that no other
writer exceeds `agent-reviewed`.

**The Decisions pane carries a graduation loop.** The mechanism the operator wants already exists —
`/debrief` graduates a recurring lesson into a standing pre-decision, and `PRE_DECISIONS.md` has a
`Graduated pre-decisions` section for it. What is missing is the **feedback signal**. So the pane
adds: a graduation affordance on every resolution, and **ask-rate against graduation-rate**, with
recurring un-graduated classes called out. A class asked twice with no pre-decision behind it is a
process defect, and it is the specific defect that makes the operator a bottleneck.

⚠️ PD-3 constrains this feed at source: *"Stops, ONLY two: a kernel-checked no-go, or a genuine
user-only decision (ask once, keep shipping)."* **A long Decisions pane is not a busy operator; it is
a loop escaping through the question channel**, and the pane should read as such.

### 5.1 Parked work — the fourth feed has no store

The named case is the staged MLX RHMC campaign, on hold awaiting results, with no surface saying so.
The pattern exists across the roadmaps in several prose dialects and is machine-readable by nothing:
`Status: ⏸ PARKED / HOLDING … Gated on 5q.G` · `PARKED as landmark … NOT queued for spare capacity` ·
`on hold pending publication`.

**Every one names a release condition**, which is the design: a parked item is structurally a finding
whose blocker is external to the finding graph. `blocked_by` therefore accepts external tokens
alongside finding ids — `run:<id>` · `phase:<id>` · `pub:<citekey>` · `research:<task>` — evaluated on each build, so a satisfied condition makes the item dispatchable
automatically. That is the "route todos and blockers back to planning" path.

✅ **There is no `operator:` token.** An operator decision that gates work is itself a queue item (a
`needs_operator` finding, D12/D21), so it has a node id and parking behind it is the plain
`blocked_by: <id>` case. A separate token would be a second decision-record channel beside the queue.

⚠️ Roadmaps are **not** converted into finding streams. The declaration is one opt-in block; the 119
existing files are untouched until something is parked deliberately. And this narrows rather than
closes a pre-existing hole: `END_TO_END_MAP.md` §2 records that the roadmap layer is entirely
unmechanized, and it remains so.

### 5.2 Loops — `/goal` activity, from state that already exists (ADR-012 D20)

No new writer. Everything below is written on every loop today, under `.claude/dev-harness/`
(**gitignored**, so the pane is empty on a fresh clone and must say so rather than render an empty
roster as "no loops running"):

| artifact | writer | carries |
|---|---|---|
| `managed/<session>.json` | `/skeft-qa:goal-prompt` at arming | `role` · `goal` · `goal_id` · **`roadmap_path`** · **`notebook_path`** · `jsonl_path` · `repo` · `question_guard` |
| `snapshot_<goal_id>.json` | `harness_precompact.py` | git HEAD + last assistant text; **mtime = per-compaction heartbeat** |
| `stall_history/<goal_id>.json` | `stall_detector.py` via the harvest consolidator | `residual_id` + `status` per compact event — **the same residual repeating is non-convergence**, computed against the derived atlas |
| `coaching/<goal_id>.json` | the harvest consolidator | the SessionStart coaching block |
| `harvest_state.json`, `watermarks/` | harvest | `last_run_ts`, `cadence_hours`, read positions |

Per armed goal the pane shows: goal text, repo, last heartbeat, question-guard state, outstanding
blocked questions, and **residual-repeat count** — a bottleneck detector that already exists and has
never been surfaced.

⚠️ **`roadmap_path` and `notebook_path` are why this is worth building, not merely cheap.** They are a
live edge from a running loop to the planning artifact that authorized it — the one direction the
system cannot currently traverse. With §5.1's parked items keyed on the same roadmaps, one join
answers *what is running against this roadmap, what is parked behind it, and what is queued.*

### 5.3 `docs/DASHBOARD.md` moves under `docs/architecture/` (ADR-012 D22)

The document drifted **because** it sits outside the governed set. Moving it buys three mechanical
guarantees:

1. **every path-like reference must resolve** — the two nonexistent declared inputs become a hard
   failure of `architecture_inventory_fresh`, or must be declared in its reasoned-exception set;
2. **no counts in the narrative** — the stale roster and graph-type figures move to the derived
   census or go;
3. **a required-content contract** — a `> **Answers:**` line plus a `README.md` ownership row, held
   verbatim-equal by the check, so it becomes an assigned review target.

Cost: `scripts/architecture_inventory.py`'s exception set gains the two deliberately-absent paths
with reasons; every inbound reference updates in the same commit; the move is a `git mv`.

### Two repairs, which are prerequisites

**Un-saturate the QI derivation.** 1,631 findings in, 0 items out. The recurrent-failure-mode
detector the operator asked for exists, is wired to the Process Health tab, and is switched off —
`END_TO_END_MAP.md` §8 names the cause: every gate-id sits in Closed Items and `unclassified` is
skipped. ⚠️ Regenerating naively replaces the curated Open items with nothing, and Invariant #13
preserves Closed Items verbatim. **This is a derivation fix, not a re-run.**

**Make sign-off persist.** The Parameters tab's confirm action renders a green **HUMAN VERIFIED**
badge for a change it never writes (Invariant #8); `--write` now raises, naming
`scripts/wave2_flip_provenance.py` as the working route. A control surface whose approve button lies
is worse than none, and this one is the publication sign-off path.

### `docs/DASHBOARD.md` is corrected in the same change

Four claims are false at HEAD: `docs/verification_log.jsonl` (the cross-tab change bus) and
`docs/submission_state.json` (the submission-event log) **do not exist and are not gitignored**; the
roster figure predates the current bundle count; the graph-type figures predate the current schema.
The document is not in `docs/architecture/`, so the no-counts rule does not machine-apply — which is
precisely why it drifted.

---

## 6. What the loop terminates on (ADR-012 D16)

A finding is done when **all five** hold, not when its ledger record is written:

1. its `verify` command passes;
2. the ledger record is written through `close_finding.py`;
3. every document the change made wrong is corrected **in the same commit** (architecture rule 2);
4. the wave close-out artifact is updated;
5. the relevant gates are green and the change is merged.

Steps 3 and 4 are where this project's documented failures concentrate: `tables_fresh` and the
`stage*_status` gap both shipped as code changes whose describing documents were never updated.

---

## Data flow

```
reviewer emits finding  ──  severity · blocks · target · lane · verify · blocked_by · needs_operator
  → extract_review_finding_nodes         mints the id, parses all seven
  → FLAGS → paper/bundle                 BLOCKED_BY → prior findings
  → open BLOCKER  → ReadinessGate blocked → readiness_submission_gate refuses
  → open REQUIRED → bundle-green blocked  (ratcheted per bundle)
  → needs_operator → decision package → Operator Queue (S3)
  → dispatchable?  (no unclosed blocked_by, target known)
       → route by lane → per-lane gates → fix
       → run `verify`
  → close_finding.py  ── re-mints the id, runs --verify, appends atomically ──> ledger
  → next graph build applies the override through the closure bar
  → BLOCKED_BY dependents re-evaluated → cascade
  → docs + wave close-out updated, gates green, merged
  → dashboard S1/S2/S4 reflect it
```

---

## Error handling

- **Unresolvable id** — refuse, and print the ids that *do* exist for that document.
- **`--verify` fails** — refuse, print the command's output.
- **`blocked_by` names no node** — fail loudly at extraction. Silence here is the orphan class.
- **`blocked_by` carries an unrecognised scheme prefix** — fail. A token nothing can satisfy is worse
  than a broken reference, because it reads as *waiting* rather than as *stuck*.
- **Unreadable or malformed ledger** — fail closed. An absent ledger is not a licence to write one.
- **Concurrent writes** — re-read immediately before appending; write atomically.
- **A lane token the map cannot resolve** — fail, on the same shape as
  `review_severity_declared`'s existing unknown-token leg.

---

## Testing

Per ADR-012 D8, every refusal path and every new check leg ships with a **production-seeded**
mutation that observes red. A fixture-only mutation proves the test works, not that the check can
fail in production, and `FIXTURE_ONLY_CEILING` may only shrink.

Four matter more than the rest:

- **the minter is shared, not copied** — a test that binds the real `build_graph` function, so a
  future divergence fails rather than silently re-creating the orphan class;
- **round-trip** — write a record, rebuild nodes, assert the status actually flipped. Without this,
  every other test can pass while the ledger change reaches nothing;
- **`BLOCKED_BY` has a consumer that sees it** — the dead-edge-type failure has shipped three times
  in this graph;
- **the ratchets have zero headroom** — asserted against the live population, not against their own
  definition.

---

## Architecture documents updated in this change

Per architecture rule 2, each lands **in the commit that makes it wrong**, not batched at the end.

| document | why it goes stale | change |
|---|---|---|
| `docs/READINESS_GATES.md` | canonical gate doc; **zero** mentions of the ledger, so a reader cannot learn how a gate un-blocks | the closure contract: open-by-default, the ledger as sole channel, the bar, the REQUIRED tier |
| `docs/architecture/END_TO_END_MAP.md` | models the writer as `HUMAN` — accurate today, wrong after this | route the edge through `close_finding.py`; note the REQUIRED tier in §8's promotion path |
| `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md` | shows the ledger as an append-only input with no writer named; §3's silent-drop list predates `BLOCKED_BY` | name the writer; add the new drop points |
| `docs/WAVE_EXECUTION_PIPELINE.md` | §13 describes emission and re-invocation but not closure, the lanes, or the append-only exception | add the closure step and the lane taxonomy, cross-referencing `READINESS_GATES.md` rather than restating it |
| `docs/KNOWLEDGE_GRAPH.md` | `SUPERSEDES` is documented as unimplemented; `BLOCKED_BY` is a new edge type | note the writer; add `BLOCKED_BY` with its emitter and consumer |
| `docs/DASHBOARD.md` → **`docs/architecture/DASHBOARD.md`** | four false claims (§5); drifted because it sits outside the governed set | `git mv`; add the Answers contract line + README ownership row; strip counts; correct the claims; extend the inventory check's exception set; update inbound references (§5.3) |
| `docs/architecture/SURFACE_INVENTORY.md` | derived | regenerate — picks up new checks, edge types and scripts |
| `docs/adrs/ADR-012-…md` | this spec carries D6/D13/D15 in more detail than the ADR | add the pointer; mark phases as they land |

**Verified as not needing changes:** `docs/architecture/CHECK_AUTHORING_GUIDE.md` (the new checks
follow it; the guide does not change) and `docs/architecture/VALIDATION_GATE_TOPOLOGY.md` §4's gate
table — the REQUIRED tier is a bundle-green gate, not a readiness gate, so it belongs in
`END_TO_END_MAP.md` §8's promotion path instead. `docs/architecture/README.md` needs no change.

---

## Sequencing

Ordered by dependency, not by what ships fastest.

1. **Document the closure contract** (`READINESS_GATES.md`) — every later step depends on a rule
   that is currently only a code comment.
2. **Emission + extraction** — the six fields, `BLOCKED_BY`, the extended
   `review_severity_declared`, the per-finding brief.
3. **The REQUIRED tier**, ratcheted per bundle at the live count.
4. **Closure** — `close_finding.py`, the unscoped bar, `verified_by`, the schema amendment, and
   `ledger_ids_resolve` promoted or widened per §4.
5. **Write the pilot's closure records** — deliberately after step 4, so no closure rests on a bar
   that could be walked around. Re-derive the population first: the pilot's 117 is 152 today.
   ⚠️ **This batch does not exercise `verified_by`**: the triage manifest carries no `verify` column,
   so every record it writes takes the no-verify path. The `verified_by` requirement is proven by its
   seeded-defect tests and by the first forward finding that carries a command, not by this backlog.
6. **Substrate lane wiring** — re-file D45–D49; `ARCHITECTURE_TODOs.MD` back inside its charter.
7. **The control surface** — S1, S4, the QI de-saturation and the sign-off repair first (they are
   over existing data); then S2 and S3, thin and iterated.
8. **Orchestration** — route by lane, fan out on disjoint `target`, traverse `BLOCKED_BY`, worktree
   per lane, terminate at a merged wave. Last, because it is the only step whose design genuinely
   depends on what the earlier ones reveal.

⚠️ Steps 2 and 4 are **one build**, not two. `verified_by` cannot fire without a `verify` field to
require it.

---

## Out of scope

- **Migrating the 190 legacy-scheme ledger orphans.** They were never graph nodes; the existing
  guard excludes them with a stated reason, and this spec does not overturn that reason.
- **Backfilling `lane` and `verify` across 1,631 historical findings.** Forward-only, plus the
  one-time typing pass the pilot already completed for the open criticals.
- **The `/skeft-qa:close-finding` plugin command.** A later thin wrapper over the script; the script
  is the contract, the command is ergonomics.
- **Changing what any reviewer looks for.** The finding classes are unchanged.
- **A scheduled CI runner.** Unrelated, and separately assessed under
  `docs/audits/2026-08-04-qa-qi-infrastructure/CI_DEFAULTS_ASSESSMENT.md`.
