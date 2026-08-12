# The remediation loop — design

**Date:** 2026-08-12 (rewritten same day, scope expanded on operator ruling)
**Status:** spec, pending implementation plan
**Implements:** ADR-012 in full — D1 through D18
**Supersedes:** this file's own first version, which covered only the ledger's write side. That
scope was a strict subset and is preserved below as §6.

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
| **the dashboard** | the operator's control surface | **four surfaces, two repairs** |

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

### Orientation is generated (D17)

`scripts/review_runner.py --prep-brief` already generates a review-prep brief. The same generator
gains a **per-finding** mode keyed on `target`: source files, the Lean declarations in its closure,
the formulas and constants it touches, the authorizing roadmap, and the relevant git history.

The finding carries its pointers; the worker does not go looking. This is also what makes the
decision package (§3) affordable — four of its five elements are generated rather than researched.

---

## 2. Gating (ADR-012 D9)

**A `major`-severity open finding blocks `stage13_status: green` for its bundle.** It does not block
submission; `readiness_submission_gate` keeps its current, stricter meaning so the two tiers stay
distinguishable.

This is the decision that closes the originating problem. Until it lands, only BLOCKER flips a gate,
and REQUIRED findings are schedulable but not enforcing.

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

### Four surfaces

| # | surface | answers | built from |
|---|---|---|---|
| **S1** | **Finding drill-through.** Gate-cell blockers resolve to the `ReviewFinding` itself — severity, lane, target, `verify`, closure record, `blocked_by`, and the ledger record that closed it | *what exactly blocks this, and what is its disposition?* | the 4,879 `FLAGS` edges, currently discarded at render; the 145 gates whose `blockers` are prose |
| **S2** | **Portfolio Flow board.** One row per bundle; columns are the pipeline stages (draft → §7.5 read-through → S9 → S10 → S12 → S13 → submission); each cell shows position and what is in flight, overlaid with open findings **by lane** | *where is everything, and what is the bottleneck?* | `stage*_status` + gate states + `lane` |
| **S3** | **Operator Queue.** Every decision waiting on the human, each with its decision package, split by urgency | *what needs me, and what can I decide well right now?* | §3's aggregation |
| **S4** | **Reading-while-blocked.** A margin marker in Paper Provenance v2 when a sentence's backing artifact carries an open finding | *I am reading §4 — is anything under it broken?* | existing `BACKED_BY` chains + `FLAGS` |

S1 and S4 are render changes over data already in the graph. S2 and S3 are new views whose value
depends on layout; they are built thin and iterated against real use rather than specified
exhaustively here.

**S3 aggregates what is currently scattered across at least six surfaces:** `needs_operator`
findings · ADR-010 §Open's operator-owned items · axiom sign-off (Invariant #15) · apex declaration
(ADR-010 §D5a) · `/skeft-qa:debrief`'s structurally human-only calls · the System-2 register's
promotion tier. Nothing aggregates them today, which is why "what needs me?" currently requires
reading six files.

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
| `docs/DASHBOARD.md` | four false claims (§5) | correct them; document S1–S4 |
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
