# ADR-012 — The remediation loop: routing, closure, and the operator control surface

- **Status:** 🏗️ **ACCEPTED — SUBSTANTIALLY BUILT (drafted 2026-08-12, scope expanded 2026-08-12).**
  **§Plan is the authority on what is built**; read it rather than this line. P1–P7, P8, P8b, P8d
  and P9a-S1 are complete; P8c, the rest of P9, P10 and P11 are open.
  It was written before the code deliberately, per the architecture rule that *a doc written
  afterwards is a changelog; only one written first is a specification.*

  ⚠️ **CORRECTED 2026-08-12. This line read "The triage pilot ran and is complete. Nothing else in
  this document is implemented" while §Plan already marked seven phases ✅ COMPLETE and D17 was
  headed `✅ IMPLEMENTED`.** The header was written first and never re-derived — the same failure
  the ADR documents elsewhere, in the ADR's own status field. **One owner per fact:** the phase
  table owns build state, and this line now points at it instead of restating it.

  **This document has been corrected three times, each by a different instrument, and the
  correction history is the reason to trust the current text over any earlier quotation of it:**

  1. **The pilot** (117 open criticals, dispositioned) materially *reduced* the first draft's
     scope — most of what it proposed to build already existed. D1 and D6 were rewritten; C7 and
     C8 were added.
  2. **An adversarial review of this ADR, its spec and its plan** (2026-08-12) found that the
     spec proposed to build a check that **already exists** (`ledger_ids_resolve`), that one
     proposed guard could never fire in production, and that the plan omitted every registration
     obligation a new check carries. D13 and D14 record the corrections; §Measurements carries
     the numbers.
  3. **An intent-drift assessment against the operator's original specification** found that the
     first draft solved the *closure* half of the loop and silently dropped the *routing* half —
     including the problem that started the thread. D9 through D22 exist because of that
     assessment. **Operator ruling 2026-08-12: the REQUIRED-population ratchet ships, routing folds
     into one plan, and scope expansion is accepted rather than bolted on later.**

- **Scope:** the full remediation loop — how a finding is emitted, typed, routed, scheduled,
  executed, verified, closed, and surfaced to a human. It does **not** change what the reviewers
  look for.
- **Does not supersede:** `ARCHITECTURE_TODOs.MD`. That file's charter is the architecture-accuracy
  pass, under a standing operator build-freeze; this ADR corrects a drift *into* it (§C1) rather
  than absorbing it.
- **Governed by:** the architecture rules in `CLAUDE.md` — read before designing, update before
  shipping in the same commit, never write a census count into a `docs/architecture/` narrative.

---

## Context

### The problem that started this

An I1 review pass closed with *"17 REQUIRED and 7 RECOMMENDED findings below blocker level, and
`tetrad_gap_solution` still returning a non-solution above saturation."* The operator's question was
whether a DAG directs the work a review creates, and the honest answer was that a **dependency**
graph exists and a **work-routing** graph does not.

⚠️ **CORRECTED 2026-08-12, and the correction shrank this ADR again.** Every earlier draft of this
section said those findings *"blocked nothing and routed nowhere."* **The first half was false, and
it was never traced to code before being written down three times.** Measured at HEAD:

- `readiness_gates.py:856` — `BLOCKING_SEVERITIES = frozenset({'critical', 'blocker', 'major'})`,
  so an open REQUIRED finding escalates `FixPropagation` to a **blocked P1 gate** (since 2026-07-31);
- `bundle_readiness.py:391` — `n_blockers = sum(sev_counter[s] for s in ("critical", "major"))`, so
  an open REQUIRED finding already forces the bundle to **RED**;
- `bundle_stage13_claim_consistent` compares a `green` claim against that same count, so a bundle
  claiming Stage-13 green with an open REQUIRED **already fails**.

**REQUIRED has been a blocking severity since before this thread began.** What was true — and is the
whole problem — is the second half: those findings **route nowhere.** No lane, no target, no
verification command, no owner, no dependency edges, nothing to schedule or parallelize on. The
operator's ask was a *workflow* ask; the gating diagnosis was added later and was wrong.

RECOMMENDED (`minor`) findings genuinely do block nothing, and that remains accurate.

**The loop the operator specified**, which this ADR is measured against:

1. **Gather orientation** — source, targets, formulas, constants, git history, roadmaps. What is
   ground truth, what is best-case, are we aiming at the right target, has the substrate moved,
   is research required?
2. **Decide the next step** — new roadmap, deferred item, closed roadmap? Lean, Python/Rust,
   architecture? Blocked on operator input or a research result?
3. **Route and orchestrate** per lane, with different gates per lane; update the docs and
   artifacts the work touches; merge when green.
4. **Orchestrate what this unblocks** and follow through until green.

Two operator constraints shaped everything below. **Lean and Python/Rust are different lanes with
different gates** — Python and Rust go through the superpowers flow. And a finding that cannot be
auto-closed must still arrive *"way beyond 'we have a problem'"* — with the diligence already
done, research already run, so the operator's decision is a high-value judgment rather than a
request for more information.

### What runs today

A reviewer emits a markdown report; `build_graph.py`'s `extract_review_finding_nodes` parses
`### N.N — 🔴 …` headings into `ReviewFinding` nodes with `severity` and `status`; `FLAGS` edges
attach each to its paper and bundle; a BLOCKER flips the affected `ReadinessGate` to `blocked`;
`readiness_submission_gate` then refuses submission.

**Status is `open` by default, and only a ledger can close it.** A finding's status is *inferred*
as `open` unless `docs/review_finding_supersessions.json` carries a record for it. For a
blocking-severity finding that record must additionally carry an explicit closing status, at
least forty characters of rationale, and a commit or date anchor. This design was reached over
four rounds of repair, each of which found a way through a narrower rule, and the code records
why the current shape was chosen: *making the ledger the only transition channel removes the class
instead of narrowing it.*

**The instrument is working.** `readiness_submission_gate` is RED. This ADR is not a response to a
broken gate; it is a response to a gate whose output nobody could act on efficiently.

### Measurements

All figures re-measured at HEAD on 2026-08-12. **Re-derive before acting on any of them** — this
project's own standing rule, and §Pilot records what happens when it is skipped.

| quantity | value |
|---|---|
| `ReviewFinding` nodes | 1,631 |
| status | open 1,028 · fixed 481 · accepted 122 |
| severity | advisory 462 · major 430 · minor 426 · critical 313 |
| **open critical** | **152** (the pilot's 117 was measured before that day's own reviews landed) |
| **open major** | **219** |
| supersession-ledger records | 870 |
| ledger orphans, all schemes | 256 |
| ledger orphans, `review:` scheme | **66 — exactly the existing guard's frozen baseline** |
| ledger orphans, legacy schemes | 190 (`bundle-stage13` 150 · `bundle-stage10` 29 · `bundle-stage9` 8 · `policy_`/`session_` 3) |
| `ReadinessGate` nodes | 704 — passed 483 · blocked 113 · open 69 · needs-recheck 39 |
| gates carrying a `blockers` payload | 145, as **prose strings**, not finding references |
| `FLAGS` edges | 4,879 |
| `qi_register.py --stats` | **1,631 findings in, 0 QI items out** |

### Three problems follow

1. **A finding records what is wrong and nothing about who repairs it.** No lane, no target, no
   verification command, and no relation to any other finding. Scheduling and parallelizing have
   nothing to key on, and every remediation re-derives orientation from cold context.
2. **The closure contract is invisible where it matters.** `READINESS_GATES.md` is the canonical
   gate document and does not mention the ledger. The open-by-default rule and the closure bar
   exist only as a comment inside `build_graph.py`.
3. **Substrate defects found outside a wave have no queue.** A defect like `tetrad_gap_solution`
   returning a non-solution above the saturation coupling is not a proof obligation (the atlas
   covers those), not an architecture-accuracy defect, and not a paper finding once the paper
   discloses it honestly. During the I1 pilot these were filed into `ARCHITECTURE_TODOs.MD`
   because it was the nearest open drawer. That was drift, and §C1 records it as such.

### And a fourth, found by the intent-drift assessment

4. **The human control surface does not show the work.** The dashboard is the operator's approval
   and sign-off tool. Every tab answers *"is it green?"*; none answers *"what is being done, by
   whom, and where is it stuck?"* With many agents drafting, reviewing, developing and
   researching in parallel, that is the view the operator will live in, and it does not exist.
   Worse, its two finding-facing surfaces are a single integer per bundle and a Process Health
   tab that is **empty by construction**.

---

## Constraints — verified, and load-bearing for the design

**C1. `ARCHITECTURE_TODOs.MD` is a working doc, not infrastructure.** Its stated charter is what
one architecture-accuracy pass found, under a standing operator constraint that *nothing in this
file is authorized to be built*. Nothing in `scripts/`, `src/`, `tests/` or `.claude/` parses it;
every reference is inside a comment. Filing substrate defects there (D45–D49, 2026-08-11) put work
items into a file with no reader. This ADR does not fix that by making the file machine-readable —
it fixes it by giving those defects a queue that already has teeth.

**C2. The Lean substrate queue already exists and is derived.** `lean/atlas_view.json` carries the
open assumptions, the frontier, and the settled obstructions, computed from `lean_deps.json` and
therefore incapable of drifting from the build. Any Lean-lane routing must *point into* the atlas,
not duplicate it.

**C3. Only one of the reviewer output formats is graph-extracted.** The markdown reports from the
adversarial, claims (bundle mode) and figure reviewers are parsed into `ReviewFinding` nodes.
`papers/<B>/claims_review.json` is a different object — per-sentence verdicts under
`sentence_state.py`, not work items. `prose-reviewer` emits a restructuring instruction and no
findings **by design**, which is what makes it the fourth reviewer rather than a second adversarial
one. The emission contract therefore binds three emitters, not five.

**C4. This exact mechanism has already failed vacuously.** The BLOCKER→gate propagation once
evaluated as passed for ten bundles because their findings produced zero edges — the gate reported
"all P1 passed" while blockers sat unclosed on disk. It was made unconditional 2026-07-31. The
code's own conclusion is the constraint: *an unrecordable finding is indistinguishable from no
finding.* Any layer added here ships with a seeded-defect test or it does not ship.

**C5. Lean and Python/Rust are different lanes with different gates.** Lean work is driven by the
atlas and the `lean4` MCP loop and gated on a clean `lake build`, zero `sorry`, kernel-purity and
the axiom allowlist. Python and Rust work goes through the superpowers flow and is gated on
pytest, `verify_scope`, and dependency declaration. Routing them through one lane would either
under-gate the Lean side or impose irrelevant gates on the Python side. **Operator constraint,
stated directly.**

**C6. The existing ledger records predate any verification requirement.** 718 records already
assert `fixed`. None was required to name a command that proves it. During the I1 pilot a defect
recorded as fixed twice was found still live, because the repair had landed in a comment claiming
the code was fixed rather than in the code. A verification requirement is therefore load-bearing
rather than hygienic — but it cannot be applied retroactively without re-litigating 718 records.

**C7. The routing data mostly already exists, and the extractor throws it away.**
`.claude/plugins/skeft-qa/agents/adversarial-reviewer.md` has carried a per-finding field template
since before this ADR: `- **Gate:**`, `- **Location:**`, `- **Observed:**`, `- **Evidence:**`,
`- **Expected:**`, `- **Fix:**`, and `- **Severity:**` (required from 2026-08-01). Measured across
the review corpus, of the findings carrying a severity glyph **93% carry `Gate:`, 92% carry
`Location:` and 87% carry `Fix:`**. But `extract_review_finding_nodes` parses only severity and
status. `Gate:` and `Location:` — which are exactly the `blocks` and `target` this ADR set out to
invent — are written by the reviewer, sit in the markdown, and are discarded at extraction. **The
first draft of D1 would have added a second name for data the system already collects.**

**C8. Two mechanisms already enforce closure quality; a third would be duplication.**
`build_graph.py` applies the blocking-closure bar (explicit closing status, ≥40 characters of
rationale, and a commit or date anchor). `reviews.py::accepted_findings_carry_rationale` separately
pins that `accepted` records justify acceptance in writing, and its own docstring records why:
`accepted` had become "the cheapest way to make a blocking finding disappear from Gate 11". Any
verification requirement belongs **inside the existing bar**, not beside it.

⚠️ The ledger's declared `_entry_format` is already out of step with the code that reads it: the
format names `date` as the only temporal field, while `build_graph` accepts any of `commit`,
`date`, `closed_date` or `applied_at` as the anchor. Whatever amends the ledger schema fixes that
drift in the same change.

**C9. The ledger-integrity check the spec proposed to build ALREADY EXISTS.** `ledger_ids_resolve`
runs today as a leg inside `check_graph_integrity`
(`scripts/validation/checks/graph_atlas.py`), pinned at `_LEDGER_DANGLING_BASELINE = 66` with
**zero headroom**, and mutation-verified against the correct host after a reviewer's own retracted
false finding. It is deliberately scoped to the `review:` scheme, with the reason stated in the
code: legacy `bundle-stage*` records were never graph nodes, so flagging them would be noise.

The measurements agree exactly: 66 `review:`-scheme orphans, 66 baseline. **The spec's "256 of 870,
nothing measured this" was the aggregate over three schemes, presented as an unmeasured deviation.**
Building a second check would be the "second mechanism beside one that already exists" failure that
`CLAUDE.md` rule 1 names, landing inside the change written to prevent it — and it would be
*weaker*: an aggregate ceiling mixes the permanently-inert legacy records with the live ones,
so deleting one legacy record silently buys a free slot for a real dangling closure. **See D13.**

⚠️ **CORRECTED 2026-08-12 — this sentence carried arithmetic that never reconciled with
§Measurements.** It read *"an aggregate ceiling of 247 mixes 190 permanently-inert legacy records
with 57 live ones"*, while §Measurements gave 256 orphans as 190 legacy + 66 `review:`-scheme.
190 + 57 = 247 and 190 + 66 = 256 are both internally consistent and cannot both be the corpus;
the live figure at drafting was 66, so 57/247 was wrong when written. Re-measured 2026-08-12 after
the P7 closures: **249 orphans = 190 legacy + 59 `review:`-scheme**, matching the check's baseline
of 59. **The argument is unaffected** — it turns on the *mixing*, not on the magnitude — which is
exactly why the numbers should not have been in the prose at all. Read them from
`validate.py --check ledger_ids_resolve`.

**C10. The dashboard's own documentation over-describes it.** `docs/architecture/DASHBOARD.md` declares a
cross-tab change bus (`docs/verification_log.jsonl`) and a submission-event log
(`docs/submission_state.json`); **neither file exists**, and neither is gitignored.
`END_TO_END_MAP.md` §6 already names the first as the reason the entire freshness layer is inert.
The Parameters tab's confirm action renders a green **HUMAN VERIFIED** badge for a change it never
persists (Invariant #8; `--write` now raises, naming `wave2_flip_provenance.py` as the working
route). The document is also stale on roster and graph-type counts. **A control surface whose
approve button does not persist cannot be the sign-off tool.**

---

## Decision

**D1 through D8 keep their numbers** — they are cited from the spec, the plan and the memory index.
D9 onward are the routing, control-surface and loop-closure decisions the first draft dropped.

### D1 — Parse the routing information that already exists; add only what is missing

Rewritten after the pilot (C7). The reviewer template is not extended by four fields, because two
of them are already written on 92–93% of findings and merely discarded:

| field | source | change required | corpus |
|---|---|---|---|
| `blocks` | the existing `- **Gate:**` line | **parse it** — no reviewer change | whole corpus, immediately |
| `target` | the existing `- **Location:**` line | **parse it** — no reviewer change | whole corpus, immediately |
| `lane` | new: `lean` · `pyrust` · `substrate` · `prose` · `research` · `infra` | add one line to the template | forward-only |
| `verify` | new: a runnable command naming its invariant | add one line to the template | forward-only |
| `blocked_by` | new, optional: finding ids this one waits on | add one line to the template | forward-only (D10) |
| `needs_operator` | new, optional: `now` · `queue` (D12) | add one line to the template | forward-only |

`extract_review_finding_nodes` gains these meta keys. `blocks` and `target` are populated for the
existing corpus at extraction time with **no backfill and no re-review** — the retrofit the first
draft called unaffordable turns out to be a parser change. The forward-only fields read
`unclassified` when absent rather than failing the historical corpus.

⚠️ `verify` must name the invariant it asserts, not merely run. The pilot produced two independent
demonstrations: a bibitem agreeing with `CITATION_REGISTRY` does not close a finding that says
*both* are wrong against the real paper, and `doi_verified: True` recorded that a DOI **resolves**,
not that it resolves **to the cited work** — which is how `Wang2024` carried another paper's venue
and DOI through three months and a Stage-13 fix-pass. A command that checks a weaker property than
its name implies is worse than no command, because it manufactures confidence.

⚠️ **These fields buy the orchestrator, not the gates.** `FixPropagation` is the only readiness gate
that reads `FLAGS` at all; the other ten are blind to findings. Adding `lane` and `target` does not
widen gate coverage, and must not be read as though it does.

### D2 — Six lanes, with Lean and Python/Rust kept separate (C5)

| lane | scope | agent profile / flow | gates |
|---|---|---|---|
| `lean` | proof obligations on the physics substrate | atlas target → `lean4` skill + MCP loop → `lean-worker` in a `wtN` worktree slot → Aristotle fallback | `lake build` clean, zero `sorry`, kernel-purity, axiom allowlist |
| `substrate` | the theorem and the implementation disagree | both of the above **and** the `pyrust` flow | **both** gate sets, plus a test that fails before the fix |
| `pyrust` | the physics code — `src/`, `rust/`, their tests | superpowers: brainstorm → spec → plan → subagent dev → pr-review-toolkit | pytest, `verify_scope`, dependency declaration |
| `prose` | manuscripts, figures, citations | paper agents (drafter, claims, figure, prose reviewers) | Stage 9/10 sub-gates |
| `research` | a question the corpus cannot answer | three-tier ladder (`Lit-Search` → `research-scout` → async dispatch) | cited report vetted by the lead before filing |
| `infra` | **the machine itself** — architecture docs, validation checks, the wave pipeline, the harness and plugin, the dashboard | three dispositions — see below | `validate.py` + plugin surface tests + §the dashboard exception |

⚠️ **`lean`/`substrate` and `infra` are different lanes because they need different agent
profiles, not merely different gates** (operator clarification, 2026-08-12). Substrate work is
proof work: it runs through the atlas, the `lean4` MCP loop and a `lean-worker` holding a build-
isolated worktree slot. Infrastructure work is work on the machine that runs the physics —
architecture, workflows, harness, plugin, dashboard — and routes to entirely different workers with
entirely different context. A finding that says "the Lean bound and the solver disagree" and a
finding that says "the dashboard shows a stale gate" have nothing operationally in common.

`substrate` is its own lane, distinct from both of its neighbours, because a defect of that kind
needs a Lean-side statement, a Python-side repair, and a regression test asserting the two agree.
It is the class that had no queue at all.

⚠️ **The `infra` lane's gate set is incomplete for dashboard work, and this ADR adds dashboard
work.** `validate.py` and the plugin surface tests cannot see a rendering defect, and a Flask test
client **never executes page JavaScript** — so a template that renders an empty panel passes every
gate the `infra` lane currently names. Dashboard changes carry two additional gates: a
**template-contract test** (the server hands the template the keys it reads) and a **real browser
test** driving the rendered page. Without both, D15 ships surfaces whose emptiness is
indistinguishable from a clean state, which is this repository's signature defect.

**Measured 2026-08-12 — one of those two already exists, the other does not.** `tests/e2e/` is a
real Playwright suite (13 files) whose `conftest.py` boots the actual dashboard as a subprocess on
an ephemeral port and collects console errors; its own docstring gives this ADR's reasoning
verbatim — *"a server-side `test_client` can never catch Datastar / SSE / data-on JS regressions."*
It is excluded from the default run (`pyproject.toml` `addopts = -m 'not slow and not e2e'`) and is
run with `-m e2e`. **So the browser gate is infrastructure that exists and needs cases, not a system
to build.** The template-contract gate genuinely does not exist: nothing cross-checks
`render_template(...)`'s kwargs against the variables the Jinja templates dereference, the app
leaves Jinja's default `Undefined` rather than `StrictUndefined`, and **no test anywhere uses
`app.test_client()`** — the two dashboard test files assert substrings against template *text* read
off disk.

**The `infra` lane carries three dispositions, not one.** The first draft collapsed the operator's
specification to "fix when mechanically obvious, else queue to the operator", losing the urgency
dimension entirely:

1. **Fix now** — mechanically obvious. Defined, so it is not a judgment call: no physics judgment
   required, no public API change, and a test can be written that fails before the fix and passes
   after. All three, or it is not obvious.
2. **Ask now, non-blocking** — urgent and needs the operator. Surfaces immediately (D12), and the
   loop keeps working everything else meanwhile.
3. **Queue for the operator** — non-urgent. Enters the operator queue with its decision package
   (D11) and the operator is told it is there. This is the "suggestion box" the operator asked
   for, and it is where the `/skeft-qa:harvest` System-2 register splices in.

### D3 — The closure contract moves into the canonical gate document

`READINESS_GATES.md` gains a section stating: status is `open` until a ledger record says
otherwise; the ledger is the only transition channel; a closure requires an explicit status, a
rationale of at least forty characters, and a commit or date anchor; a finding carrying a `verify`
command additionally requires a passing `verified_by`; records are written with
`scripts/close_finding.py`. The rule stops living exclusively in a code comment. Per architecture
rule 2 this lands **before** the code that depends on it.

### D4 — Substrate defects file as findings, not into the working doc

A substrate defect discovered outside a wave is emitted as a `ReviewFinding` with `lane=substrate`
and enters the same queue as every other finding. `ARCHITECTURE_TODOs.MD` reverts to its charter
(C1). The D45–D49 entries filed there during the I1 pilot are re-filed as findings; the file keeps
D50 and D51, which are architecture-accuracy defects and belong to it.

### D5 — Triage precedes intake typing, and is the pilot

✅ **COMPLETE 2026-08-12.** See §Pilot. All 117 open criticals dispositioned; the exercise
materially reduced this ADR's scope.

### D6 — Extend the existing closure bar; do not add a check beside it

Rewritten after the pilot (C8). Two changes, both inside the mechanism that is already there:

1. **Remove the severity scoping.** The bar is currently gated on
   `severity in ('critical','major','blocker')`. Below that line, any two-key ledger record closes
   a finding with no evidence and no anchor. Because `- **Severity:**` is declarable in the finding
   body and the declared value beats the heading glyph — and `_SEVERITY_DECL_MAP` maps
   `recommended → minor`, **verified at HEAD** — a 🔴 BLOCKER heading declaring `recommended` closes
   on `{"finding_id": X, "status": "fixed"}`. This is a filed finding, open across four consecutive
   rounds, and it reproduced byte-for-byte at HEAD during this pilot. The bar applies to every
   severity.

   ⚠️ **Measured blast radius: ZERO.** All 231 currently-closed non-blocking findings carry a ledger
   record, and every one of those records already meets the bar. Unscoping flips nothing today; it
   closes a forward hole. This was measured before the change rather than discovered after it, and
   it is the reason the change is cheap.

2. **Require `verified_by`** for closures of findings that carry a `verify` command: the record
   names the command run and its result. The 718 existing records are grandfathered — re-litigating
   them costs more than it returns — and the ledger's declared `_entry_format` is corrected in the
   same change (C8).

   ⚠️ **(2) is inert unless D1 ships in the same plan.** No finding can carry a `verify` command
   until the extractor parses one, so a `finding_has_verify` parameter with no producer is a leg
   that cannot fire on any input — item 1 on `CHECK_AUTHORING_GUIDE.md` §6's checklist. The
   adversarial review caught this in the plan; it is why routing and closure are one build (D18).

### D7 — The pre-bundle-era criticals are in scope

18 of the 117 sit in review documents that predate the bundle era and resolve to no bundle.
Operator ruling (2026-08-12): treat them as in-scope for review — *"worst case it's a teaching
lesson that might be fruitful."* They are triaged with the rest rather than declared out of scope
by age.

### D8 — Non-vacuity is a shipping requirement, not a review note (C4)

Every check introduced here ships with a test that seeds the defect it claims to catch **into the
production artifact the check reads**, and observes red. A fixture-only mutation proves the test
works, not that the check can fail in production (`CHECK_AUTHORING_GUIDE.md` §2.4), and
`FIXTURE_ONLY_CEILING` may only shrink — so a fixture-only test is not merely weaker here, it is
blocked. A check whose population can be empty while it reports PASS does not count as built.

### D9 — Ratchet the open-REQUIRED population down, per bundle

⚠️ **REWRITTEN 2026-08-12 after the premise failed verification.** This decision previously read
*"REQUIRED blocks bundle-green"* and justified itself on *"today only a BLOCKER flips a gate."*
**Both are false** — see §Context. REQUIRED already blocks: the gate, the readiness verdict and the
green-claim consistency check all treat `major` as blocking.

**What is genuinely missing is a population guard, and that is what D9 now is.** Every existing
mechanism asserts *consistency* — a green claim against live blockers — and **none asserts that the
open-REQUIRED population cannot grow.** `bundle_stage13_claim_consistent` additionally fires on
**zero rows today**, because no bundle currently claims `stage13_status: green`: it is a correct
guard over an empty population. So a bundle can accumulate REQUIRED findings indefinitely without
tripping anything, which is the state the roster is in.

**D9 is therefore a down-only ratchet on the open-REQUIRED population**, per bundle, hosted on
`bundle_stage13_claim_consistent` as a new leg — not a new severity tier, which already exists.

**It mechanizes a standing operator pre-decision.** PD-5
(`docs/dev-loops/PRE_DECISIONS.md`, operator-set 2026-07-29) already states that
BLOCKER/MAJOR/IMPORTANT findings *"are never deferred"* and that *"deferral requires an explicit
operator sign-off asked for as a question — never assumed."* That rule has bound the autonomous
loop for two weeks and binds no gate. D9 gives it teeth.

⚠️ **The ratchet is not a deferral, and the distinction is exactly PD-5's.** PD-5 governs a finding
you have just found: fix it in-session, at full strength. The ratchet governs the *population*: it
cannot grow. A new major in a bundle takes that bundle above its ceiling and blocks its green,
which is PD-5 firing mechanically. The pre-existing 219 are visible debt with a down-only
obligation, not tolerated deferrals — and making them visible is the first time they have been
anything other than invisible.

**It extends `bundle_stage13_claim_consistent`; it does not sit beside it.** A sibling check would be
the C9 failure — a second mechanism beside a working one — in the very ADR that names it.

The gate ships with a **per-bundle down-only ratchet frozen at the live count**, exactly like
`NATIVE_DECIDE_BUNDLE_DEBT` and `UNDECLARED_APEX_CEILING`. 219 open majors distributed across the
roster would otherwise take every bundle non-green on the first run — a gate that fires on the
existing corpus gets switched off, and this project has that lesson recorded twice already
(`bundle_source_freshness` under `--strict`, and the pre-ADR-011 figure-prefix literal).

Zero headroom per bundle. Lower the ceiling in the commit that lowers the population; never raise
it. The ratchet is the on-ramp, not the destination: a bundle at zero open majors is the target
state and the ceiling records the distance.

⚠️ **MEASURED NON-VACUITY, and it is not total (2026-08-12).** ⚠️ The figures below are over `inferred_bundle`; the check reads a wider aggregation, so read them as the SHAPE of the gap, never as the constant. The constants are measured at implementation: **47** genuinely unattributed (carrying neither key), because 24 of the 71 missing `inferred_bundle` still carry `inferred_paper` and already reach the aggregation. A per-bundle ratchet can only see
findings that resolve to a bundle. Measured at HEAD: **52 of 219 open majors (23%) carry no
`inferred_bundle`** — and 19 of 152 open criticals — so they attach to no bundle's ceiling and D9
blocks nothing for them. They are silent-drop point 1 in
`QA_QI_INFRASTRUCTURE_MAP.md` §3: a finding with neither `inferred_paper` nor `inferred_bundle` is
dropped from bundle aggregation. **D9 as a per-bundle gate covers 167 of 219.**

**That gap is also a perverse incentive, which is why it cannot be left as a footnote.** If the only
ratchet is per-bundle, a finding that *loses* its attribution silently leaves the ratchet, and "no
bundle carries an open major" becomes reachable by degrading attribution rather than by fixing
anything — absence rendered as success, one level up from where this ADR usually catches it.

**So D9 ships with two ratchets, not one:** the per-bundle ceiling, and a corpus-wide down-only count
of **the open blocking findings the per-bundle aggregation does not reach**. Both may only shrink.
The second is what makes the first honest.

⚠️ **CORRECTED 2026-08-12 — this sentence stated the constant as "52 majors / 19 criticals" while
the paragraph above it had already established 47.** The two are not a contradiction in the
measurements (52 + 19 = 71 lack `inferred_bundle`, and 71 − 24 = 47 lack *both* keys); the defect
was that the correction landed one paragraph up and never reached the sentence that names the
frozen value. A number stated twice in one decision is a number that will disagree with itself.

⚠️ **And the predicate has since changed, which voids all of these figures as constants.** Leg 2
keyed on *"carries neither key"* — a **proxy** for *"the aggregation did not reach it"* — and it was
wrong for the pre-bundle-era corpus (D7): those findings carry an `inferred_paper`, so leg 2 skipped
them, and map to no bundle, so leg 1 never saw them. **Eight open blocking findings sat outside both
legs.** Leg 2 now keys on the ids the aggregation returned, so the two legs are complements over one
id set and the coverage holds by construction rather than by argument. **Read the constants from
`scripts/validation/checks/bundles_readiness.py`, never from this paragraph** — every figure here is
scoped by a predicate that has now moved twice.

### D10 — The queue is a DAG, not a list: findings carry `blocked_by`

Four typed fields give a **sortable list**. The operator asked for a graph — *"orchestrate the
subsequent steps that this unblocks, follow through until green"* — and a cascade needs edges.

A finding may declare `blocked_by: [finding_id, …]`. The extractor emits a `BLOCKED_BY` edge
between `ReviewFinding` nodes. A finding with an unclosed `blocked_by` is **not dispatchable**, and
closing a finding re-evaluates everything that named it — which is the cascade.

⚠️ Two obligations, both from failures this project has already shipped. The edge must be
**non-vacuous**: `KNOWLEDGE_GRAPH.md` already carries three edge types that gates query and nothing
emits, and `PRODUCES` sat expired for a full wave because a working fallback masked it. And a
`blocked_by` naming an id that mints no node must **fail loudly**, not silently drop — that is
exactly the 29% orphan class one layer up. Both ship with seeded-defect tests (D8).

⚠️ **This rule and D19's external tokens share one field, so the discrimination must be explicit.**
An entry whose prefix matches a **declared** external scheme (`run:` · `phase:` · `pub:` ·
`research:`) is a release condition and is never expected to resolve to a node.
Everything else must resolve to a minted node id or fail loudly — **including an unrecognised
scheme**, so that a typo like `runs:42` fails rather than becoming a blocker nothing can ever
satisfy. The scheme list is declared in one place and validated against, on the same shape as
`_SEVERITY_DECL_MAP`.

### D11 — A finding routed to the operator arrives as a decision package

The operator's requirement, quoted because the paraphrase keeps losing it: the loop should get a
finding *"way beyond 'we have a problem' to having already made sufficient attempts to anticipate
and move towards a solution, using research tools if/as needed, so that the conversation and
decision process are more likely to produce stellar results."*

A finding carrying `needs_operator` is not routed until it carries all five:

1. **Orientation, generated** — the target's source, its Lean declarations, its formulas and
   constants, its git history and the roadmap that authorized it (D17).
2. **Ground truth vs. best case** — what is true now, what the correct end state is, and the
   distance between them.
3. **Substrate delta** — has anything moved that should change the target? An explicit answer,
   including "no".
4. **Research done or dispatched** — the three-tier ladder run to whatever tier the question needs,
   with the cited report vetted. A `research` finding that has not run the ladder is not ready for
   the operator.
5. **Two or more options with tradeoffs, a recommendation, and what changes if the answer goes the
   other way.**

**A finding surfaced without a decision package is deferred, not routed.** Making that a definition
rather than an aspiration is the whole point: the failure mode is an agent escalating early with a
question the agent could have answered, which is the bottleneck this ADR exists to remove.

### D12 — The operator queue is a first-class surface with urgency, and it notifies

`needs_operator` is **orthogonal to `lane`**, not a seventh lane. A `lean` finding can need a
physics call; a `substrate` finding can need a scope decision. Overloading `infra` with it — the
first draft's shape — hides exactly the findings the operator most needs to see.

Two values. `now` surfaces immediately and non-blockingly, and the loop keeps working everything
else. `queue` enters the operator queue and the operator is told it is there.

**Four feeds, surfaced together but NOT merged** (operator ruling 2026-08-12: *"could be the same
page, separate pages — not forcing aggregation/combination is fine"*). They have different stores,
different semantics and different actions, and flattening them into one list would destroy the only
property that makes each legible.

| # | feed | store today | machine-readable? |
|---|---|---|---|
| **A** | **System-1 — publication findings needing a call.** `needs_operator` `ReviewFinding`s with their decision packages | `ReviewFinding` nodes; `docs/QI_REGISTER.md` | yes — though the QI derivation currently emits zero (D15) |
| **B** | **System-2 — dev-loop and harness process findings** from `/skeft-qa:harvest`, at their tier | `docs/dev-loops/SYSTEM2_REGISTER.md` — **gitignored, local-only**, `## Open` with `### <slug>` entries | headings and tiers only; not derived |
| **C** | **Decisions — PD-3's second legitimate stop.** A genuine operator-only call | **`.claude/dev-harness/blocked_questions.jsonl`**, written by the `AskUserQuestion` guard | yes, and **already consumed** — see below |
| **D** | **Parked work** — authorized work waiting on an external release condition (D19) | 119 roadmap markdown files, prose | **no** |

⚠️ **Correction (operator challenge, 2026-08-12).** An earlier draft of this section said the
blocked-question log *"is read by nothing."* **That is false.** The log has two live consumers and a
documented path to a human:

- **`coach` (in-time).** The `PreToolUse(AskUserQuestion)` guard denies the question, logs it, and
  redirects to the `coach` agent, which reads the log plus the pre-decisions store and returns one
  decision and one concrete next action. This is the loop's *first* answer, and it resolves most
  questions without the operator.
- **`harvest-extractor` (asynchronous).** The harvest skill locates the log span since the last
  `watermarks/bqlog.json` position and hands it to the extractor; the consolidator files it into the
  System-2 register, and `/skeft-qa:debrief` is the human governor.

So the operator path exists and is designed. **What is missing is not a reader — it is an
operator-facing surface and a latency floor.** A blocked question reaches the human only after a
harvest (cadence 4 h, per `harvest_state.json`), through an 840 KB gitignored register, with no view
that says "three questions are waiting." Feed C's job is to shorten that path for the questions the
coach could not settle, not to invent a channel.

⚠️ **A second live gap, already recorded and worth carrying here.** `active_issues.json` is written by
every harvest and **read by nothing** — `_read_active_issues` has zero callers repo-wide, while
`HARNESS_GUIDE.md` describes it as feeding the re-injection. It carries exactly what feed B's pane
needs (`{title, tier, tally, kind}`, already aggregated and already tiered). Feed B should consume it
rather than re-parsing 840 KB of markdown, which turns a documented dead artifact into the pane's
backing store.

Feed B is read-only in the dashboard and stays that way: `/skeft-qa:debrief` is the structurally
human-only governor for promotion, closure and misfiling, and a second write path would break the
`_clamp_tier` guarantee that no other writer exceeds `agent-reviewed`.

### The graduation loop — why feed C should shrink over time

The operator's standing requirement: *"each time i weigh in on something, we should be able to
generalize so that the pre-decisions list and operating principles expand over time and cover more
cases."* **That mechanism already exists** — `/skeft-qa:debrief` graduates a recurring lesson into a
standing pre-decision, and `PRE_DECISIONS.md` carries a `Graduated pre-decisions` section for
exactly this. What is missing is not the mechanism but the **feedback signal**: nothing measures
whether graduation is keeping up with asking.

So feed C carries two things beyond the question itself:

1. **A graduation affordance on resolution.** When the operator decides, the decision is a candidate
   pre-decision, routed to `/debrief`. Deciding without considering generalization is how the same
   class gets asked twice.
2. **Ask-rate against graduation-rate, and recurring un-graduated classes.** A class asked more than
   once with no graduated pre-decision behind it is a **process defect**, and it is exactly the
   defect that makes the operator a bottleneck. Surfacing it is what turns "these should be rare"
   from an aspiration into something observable.

⚠️ PD-3 already constrains this feed at its source: *"Stops, ONLY two: a kernel-checked no-go, or a
genuine user-only decision (ask once, keep shipping)."* Feed C should therefore be **short by
construction**. A long feed C is not a busy operator; it is a loop escaping through the question
channel, and the dashboard should make that readable as such.

### D13 — Do not build a second ledger-integrity check; extend or promote the one that exists (C9)

`ledger_ids_resolve` is live, correctly scoped, zero-headroom and mutation-verified. The permitted
moves are:

- **Promote** it from a `graph_integrity` leg to a registered check in `reviews.py` — defensible on
  its merits (independent `--check` run, its own constant, its own mutation entry) — **and delete
  the leg in the same commit.** Two copies is the defect.
- **Widen** its scope to the legacy schemes only with a stated reason that engages with the
  existing exclusion rationale, and only as a **second, separately-ratcheted** population. One
  ratchet over two populations lets motion in the inert one buy headroom in the live one.

Either way, a new check is not added beside it. **A promotion carries every registration obligation
a new check carries** — `_CANONICAL_ORDER` (whose absence *raises*, taking the suite down), the
`validate.py` re-export, a `MUTATION_VERIFIED` entry naming a real production-seeded test
(`AWAITING_MUTATION_TEST` is empty and `AWAITING_CEILING` is 0, so deferral is not available),
`CI_MIN_CHECKS_RUN`, and a regenerated `SURFACE_INVENTORY.md` **in the same commit**.

### D14 — The ledger gets a writer

`docs/review_finding_supersessions.json` is the only channel that can close a blocking finding and
it has **no writer**. All 870 records were hand-typed, and 66 of the `review:`-scheme ones name no
node — they are inert, and the findings they meant to close still read `open`.

`scripts/close_finding.py` becomes the only supported writer, modelled on `scripts/record_review.py`
— which closed this exact class of gap for bundle status, and whose docstring calls itself *"the
writer transition 2 never had"*. It refuses to write when the minted id matches no live node, when
evidence is under the bar, when no anchor is supplied, or when a supplied `--verify` command exits
non-zero.

**Load-bearing constraint: it imports the id minter from `build_graph`; it does not reimplement it.**
A second minter reproduces the orphan class by construction. Precedent: `_recurrence_norm` was moved
to module scope after the production matcher could have been deleted with its test still green.

The write is atomic (temp-and-replace), because a crash midway through rewriting the only closure
channel produces the malformed-ledger state the readers are told to fail closed on.

### D15 — The dashboard is the operator control surface, and it ships with the loop

Not a follow-on. The loop's whole purpose is to route work away from the operator; the dashboard is
how the operator keeps oversight while that happens, and how they sign off on publication content.
Shipping the loop without it produces a system that is more autonomous and less observable at the
same time.

**Five surfaces** (S1–S4 below, plus the Loops pane added by D20).

⚠️ **CORRECTED 2026-08-12, from a read of the code rather than of this table.** An earlier draft
said "three are render changes over data already in the graph." **S1 is not a render change**, and
S4's stated data source is not the one the page uses. Both corrections enlarge the work; neither
changes the design. See the `data` column below and §S1/S4 notes.

| # | surface | what it answers | data |
|---|---|---|---|
| **S1** | **Finding drill-through** — gate-cell blockers resolve to the `ReviewFinding` itself: severity, lane, target, `verify`, closure record, `blocked_by` | *what exactly is blocking this, and what is its disposition?* | ⚠️ **NOT a render fix.** The id is destroyed in the evaluator: `readiness_gates.py:911` holds the whole finding and keeps `f['label'][:60]`. `GateResult.blockers` is `list[str]`, `to_node_payload` (`:104`) serializes it as such, and the dashboard never touches `FLAGS` at all (zero occurrences in `provenance_dashboard.py`). The change spans evaluator → `GateResult` → node payload → render |
| **S2** | **Portfolio Flow board** — see below | *where is everything, and what is the bottleneck?* | `stage*_status` + gate states + `lane` |
| **S3** | **Attention** — D12's four feeds, side by side, unmerged | *what needs me, and what can I decide well right now?* | four separate stores; see D12 |
| **S4** | **Reading-while-blocked** — a margin marker in Paper Provenance v2 when a sentence's backing artifact carries an open finding | *I am reading §4; is anything under it broken?* | ⚠️ **Not the graph.** Paper Provenance v2 reconstructs its chains from `claims_review.json` (`_pp_sentence_chain_link_states`, `provenance_dashboard.py:2662`); it reads no `BACKED_BY` edge and no `FLAGS` edge. A sentence→finding resolution has to be built. The attachment point exists and is clean: the per-sentence `<span>` at `:4439` already carries a state-driven class list (`:4427`) |

#### S2 — the Flow board, specified

**Rows:** the bundle roster, from `bundle_registry.BUNDLE_CODES` — never a hand-written list
(`bundle_registry_consistency` Leg C exists because that pattern is known-bad).

**Columns**, restricted to stages that carry real machine state:

| column | source | note |
|---|---|---|
| draft exists | `papers/<B>/paper_draft.tex` + compiled PDF | |
| §7.5 read-through | *(no field today)* | the `prose-reviewer` mints nothing by design (C3) — renders as **not tracked**, never as passed |
| S9 figure | `stage9_status` | |
| S10 claims | `stage10_status` + presence of `claims_review.json` | absence is its own state (ADR-011 Phase 2d) |
| S12 sync | freshness checks | |
| S13 adversarial | `stage13_status` + `stage13_review_kind` + `stage13_redo_required` | only `full-adversarial` earns green |
| submission | `readiness_submission_gate` + `blockers_open` | |

⚠️ **The status enum has drifted and the board must not hide it.** `Phase7a_Roadmap.md` declares
`pending | green | red`; the live corpus uses five values, three undeclared
(`pending-redo`, `skeleton`, `not_started`). `BUNDLE_READINESS_HEATMAP.md` already surfaces non-enum
values verbatim rather than rejecting them, and the board does the same — an unrecognised value
renders as itself, never coerced to the nearest known state.

**The overlay is the bottleneck signal:** open findings per bundle, broken down by `lane`. That is
what turns "D3 is yellow" into "D3 is held by six substrate findings" — the difference between a
status board and a routing instrument.

**Live activity: `/goal` level is in scope, subagent level is not** (operator ruling, corrected
2026-08-12 — see D20). An earlier draft claimed activity had no writer at all. It does, at the level
that matters: a `/goal` loop runs for hours to days and already emits a machine-readable marker,
a per-compaction snapshot and a convergence signal. Subagent worktree slots turn over in minutes and
are deliberately left out — a board tracking them would be stale between renders.

#### S3 — Attention, specified

Four panes, one page, **not merged** (D12). Each keeps its own store, vocabulary and actions:

- **Publication** (feed A) — `needs_operator` findings with their decision packages, plus the QI
  register's open items once its derivation is repaired.
- **Process** (feed B) — the System-2 register's `## Open` items at their tier. **Read-only**;
  `/skeft-qa:debrief` remains the sole governor, and its tier clamp must not gain a second writer.
- **Decisions** (feed C) — from `blocked_questions.jsonl` and `needs_operator: now`, each with its
  package, its graduation affordance, and the ask-vs-graduation signal (D12).
- **Parked** (feed D) — D19's items with their release conditions, and whether each condition is
  now satisfied.

**Two repairs, which are prerequisites rather than extras:**

- **Un-saturate the QI derivation.** 1,631 findings in, 0 items out. The recurrent-failure-mode
  detector the operator asked for exists, is wired to the dashboard, and is switched off:
  `END_TO_END_MAP.md` §8 names the cause (every gate-id sits in Closed Items and `unclassified` is
  skipped). Regenerating naively would replace the curated Open items with nothing, and Invariant
  #13 preserves Closed Items verbatim — so this is a derivation fix, not a re-run.
- **Make sign-off persist.** The Parameters confirm action renders a green HUMAN VERIFIED badge for
  a change it never writes (C10, Invariant #8). A control surface whose approve button lies is
  worse than no control surface, and this one is the publication sign-off path.

`docs/architecture/DASHBOARD.md` is corrected in the same change: two declared inputs do not exist, the roster
and graph-type figures are stale, and the change-bus it describes has never carried an event.

### D16 — The loop terminates at a closed-out, merged wave, not at a ledger record

The operator's steps 3.6 and 3.7 — *"ensure any relevant docs / artifacts are updated (e.g. wave
closeout)"* and *"when everything relevant's green, merge changes to main"* — were dropped entirely
by the first draft. A finding is not done when its ledger record is written. It is done when:

1. its `verify` command passes;
2. the ledger record is written through `close_finding.py`;
3. every document the change made wrong is corrected **in the same commit** (architecture rule 2);
4. the wave close-out artifact is updated;
5. the relevant gates are green and the change is merged.

Steps 3 and 4 are where this project's documented failures concentrate — `tables_fresh` and the
`stage*_status` gap both shipped as code changes whose describing documents were never updated.

### D17 — Orientation is generated, not gathered ✅ IMPLEMENTED 2026-08-12 (`36edada9`)

Re-deriving orientation per finding, from cold context, is the expensive way and it is what the
operator's step 1 was reacting to. `scripts/review_runner.py --prep-brief` already generates a
review-prep brief; `emit_finding_brief` is a **second entry point on the same script**, sharing its
CLI, that emits a per-finding brief from the finding's own `target`: the source files, the Lean
declarations in its closure, the formulas and constants it touches, the authorizing roadmap, the
relevant git history, and whether every declared blocker has closed or released.

The finding carries its pointers; the worker does not go looking. This is also what makes D11's
decision package affordable — four of its five elements are generated rather than researched.

⚠️ **An unknown finding id RAISES; it does not emit an empty brief.** An empty brief reads as
"nothing to orient on" when the truth is "not found" — absence rendered as success, in the one
artifact a worker trusts. `--finding` is also handled *before* the `--bundle` gate, which would
otherwise exit 1 while printing nothing.

### D18 — Routing and closure are one build, and this process is the pilot for a repeatable one

**Operator ruling 2026-08-12: fold routing into one plan.** The adversarial review's finding is the
argument — D6.2 cannot fire without D1, so shipping closure alone produces a guard that is green in
tests and dead in production. The plan builds the emission contract, the routing fields, the DAG,
the closure writer, the bar corrections and the control surface as one sequence.

Separately: the operator asked twice for the *process itself* — brainstorm → spec → ADR →
subagent-driven dev → review → docs synchronized in the same commit — to become repeatable rather
than remembered. It is codified as a `skeft-qa` skill, with this ADR as its worked example,
including its three correction rounds. The correction rounds are the most valuable part: a process
that produces a specification nobody adversarially reviews produces this document's first draft.

### D19 — Parked work is a first-class item with a release condition

**This is the one genuinely new build in the set, and it is the operator's fourth category:**
authorized work that is not blocked by a defect but is waiting on something external. The named
example is the staged MLX RHMC campaign, which has been *"on hold awaiting results"* with no surface
that says so.

**The pattern already exists in the corpus, in four or five prose dialects, machine-readable by
nothing.** Measured across the 119 roadmap files:

- `**Status: ⏸ PARKED / HOLDING (2026-06-30).** Gated on 5q.G … until 5q.G's L2 clears` (Phase6CC)
- `⏳ **PARKED as landmark** — eliminability: very_hard … NOT queued for spare capacity` (Phase6o′)
- `If the paper has not yet been published, Track 1 is on hold pending publication` (Phase6s)

Every one of them names a **release condition**. That is the whole insight: **a parked item is
structurally a finding whose blocker is external to the finding graph.** It has a target, a lane, an
owner and a condition; the only difference from D10's `blocked_by` is what the blocker points at.

**Decision.** `blocked_by` accepts external release-condition tokens alongside finding ids:

| token | released when |
|---|---|
| `run:<id>` | a production/campaign run completes — the MLX case |
| `phase:<id>` | another phase or wave closes |
| `pub:<citekey>` | an external publication becomes available |
| ~~`operator:<slug>`~~ | **DROPPED 2026-08-12 — it was unnecessary. See below.** |
| `research:<task>` | a `Lit-Search/Tasks/` dispatch returns |

✅ **`operator:` is DROPPED, and neither proposed store is built.** The adversarial pass found it had
no store and offered two fixes; on specification both were wrong, because **the token is redundant.**

An operator decision that gates work **is already a queue item**: under D12 it is a finding carrying
`needs_operator`, and under D21 every operator-owned open item of a prior ADR is filed the same way.
It therefore has a node id. Parking behind it is `blocked_by: <that finding's id>` — the plain
node-id case, which D10 already builds, already validates, and already cascades on closure.

Adding `operator:` would have meant a second decision-record channel beside the queue, with its own
store, its own writer and its own staleness — the exact shape `CLAUDE.md` rule 1 forbids and C9
caught once already in this ADR. **Four tokens ship** (`run:` · `phase:` · `pub:` · `research:`), each
resolving against an artifact that exists. A decision is not an external condition; it is work.

A roadmap declares a parked item in one opt-in block; the extractor mints it into the same queue as
every other item, and the release condition is evaluated on each build. When the MLX run lands,
`run:<id>` is satisfied and the item becomes dispatchable **automatically** — which is precisely the
operator's *"routing todos / blockers / findings back to the planning stages."*

⚠️ **Roadmaps are NOT converted into finding streams.** The block is additive and opt-in; the 119
existing files are untouched until someone parks something deliberately. Converting the roadmap
layer wholesale would be a far larger change than this ADR should make, and roadmaps are where
scope is declared — a different job from where work is tracked.

⚠️ **This only partially addresses a pre-existing hole, and the ADR should not pretend otherwise.**
`END_TO_END_MAP.md` §2 records that the roadmap layer is *entirely unmechanized* and calls it *"the
single largest ungated seam in the map"*: no check references `docs/roadmaps/`, and no `*_close.md`
files exist. D19 gives parked work a surface. It does not gate roadmaps, and the seam stays open.

### D20 — `/goal`-level activity is surfaced from the state the harness already writes

**Operator ruling 2026-08-12:** subagent worktree slots are fast-moving and out of scope, but a
`/goal` instance typically runs for many hours to days with a coordinating agent driving workers,
and *"machine-readable info that we're already using in our hooks/context bootstrap and harvest
infrastructure is low-enough hanging fruit that it's worth our time to plan a legitimate
integration."* Verified: it is, and there is more of it than the previous draft credited.

**Everything below already exists and is written on every loop, under `.claude/dev-harness/`:**

| artifact | writer | carries |
|---|---|---|
| `managed/<session>.json` | `/skeft-qa:goal-prompt` at arming | `role` · `goal` (the settled goal text) · `goal_id` · **`roadmap_path`** · **`notebook_path`** · `jsonl_path` · `repo` · `question_guard` |
| `snapshot_<goal_id>.json` | `harness_precompact.py` on every PreCompact | git HEAD + last assistant text; **its mtime is a per-compaction heartbeat** |
| `stall_history/<goal_id>.json` | `stall_detector.py` via the harvest consolidator | one record per compact event: `residual_id` + `status` — **the same residual repeating is a non-convergence signal**, computed against the derived atlas |
| `coaching/<goal_id>.json` | the harvest consolidator | the forward-framed coaching block re-injected at SessionStart |
| `watermarks/`, `harvest_state.json` | harvest | read positions; `last_run_ts` + `cadence_hours` |

**A Loops pane therefore needs no new writer.** Per armed goal it can show: the goal text, the repo,
last heartbeat, whether the question guard is on, how many blocked questions are outstanding, and —
from `stall_history` — whether the loop has been on the same residual across N compactions. The last
of these is a genuine bottleneck detector that already exists and has never been surfaced.

⚠️ **`roadmap_path` and `notebook_path` are the load-bearing fields**, and they are why this is worth
doing rather than merely cheap. They are a live edge from a *running loop* to the *planning artifact
that authorized it* — the one direction the system currently cannot traverse. With D19's parked items
keyed on the same roadmaps, the Flow board can answer *"what is running against this roadmap, what is
parked behind it, and what is queued"* from one join.

⚠️ **Everything here is gitignored and local.** Correct for a local dashboard; it means the Loops pane
shows nothing on a fresh clone, and it must say so rather than render an empty roster as "no loops
running."

### D21 — The open items of prior ADRs enter this queue

**The operator's regression concern, stated directly:** the ADR-009/010/011 work paused before the
last merge must not be re-derived from cold context when it resumes, and must not be designed against
an architecture that has since moved.

Re-evaluated against this ADR:

| prior item | state | disposition under ADR-012 |
|---|---|---|
| **ADR-009 §Deferred 0–7** | ✅ **all eight dispositioned** (fixed, or declined with measurements) | closed; no queue entry. The residue is the standing lesson that every item's scope figure was unverified — which is now D1's `target` and D17's generated brief |
| **ADR-010 D2** — per-target purpose statements re-derived from the manuscripts | **OPEN** | 21 findings, `lane=prose`, one per bundle, disjoint `target` — **the exact shape ADR-012's fan-out exists for** |
| **ADR-010 D4** — merge/split/retire | ✅ discharged 2026-08-08; all six proposed merges failed against the manuscripts | closed |
| **ADR-010 D5** — homing dispositions for the un-homed substrate, measured at **1,403–1,633 modules**, not the charter's ~340 | **OPEN, and the largest single item in the portfolio** | `lane=substrate`, structured as a `BLOCKED_BY` tree: per-**arc** dispositions first, modules beneath them. ADR-010 itself anticipates that the 4–5× scope change may change the shape of the answer |
| **ADR-010 D7** — the roster-drift change-set | **OPEN** | `lane=infra`/`prose`, doc work |
| **ADR-010 §Open** — operator-owned questions | **OPEN by design** | feed A/C of the Attention surface; and work parks behind the *finding id* of the decision itself (D19), not a separate token |
| **ADR-011 P1–P8** | ✅ complete | closed |
| **`ARCHITECTURE_TODOs.MD` D50, D51** | open, under the standing build-freeze | stay in the working doc per C1 — they are architecture-accuracy defects and belong to it |

**The synchronization rule:** an open item in a prior ADR is filed as a `ReviewFinding` with its
lane and target, *pointing back at* the ADR that owns the decision. The ADR stays the decision
record; the queue becomes the work record. This is the same move D4 makes for the D45–D49 entries,
and it is what prevents the resumed work from re-deriving orientation the queue already holds.

⚠️ **ADR-010's own standing warning applies to every row above:** *"Re-derive an item before acting
on it, including its evidence line."* Roughly a third of its drift ledger is about a document's own
count, several items' *correcting evidence* has itself gone stale, and one filed claim was withdrawn
the day after it was written. The table above records state, not permission to skip re-measurement.

### D22 — `docs/architecture/DASHBOARD.md` is canonicalized into `docs/architecture/`

**Operator question, answered: yes.** The dashboard is now a governed surface with four new views and
two repairs, and its describing document has four false claims — which is precisely the drift that
`docs/architecture/` exists to prevent, and which happened *because* the document sits outside it.

Moving it buys three mechanical guarantees it does not currently have:

1. **Every path-like reference must resolve** (`architecture_inventory_fresh`). Today
   `docs/verification_log.jsonl` and `docs/submission_state.json` are named and do not exist. Under
   the check, that is a hard failure on arrival — the false claims must be corrected, or declared
   missing in the check's explicit reasoned-exception set. Either way the lie stops being free.
2. **No counts in the narrative** (rule 3). The stale roster and graph-type figures move to the
   derived `SURFACE_INVENTORY.md` or disappear.
3. **A required-content contract.** It gains a `> **Answers:**` line and a row in `README.md`'s
   ownership table, and the check asserts the two agree verbatim — so it becomes an obvious review
   target alongside the other seven rather than a document nobody is assigned to read.

Costs, stated: the exception set in `scripts/architecture_inventory.py` must gain the two
deliberately-absent paths with their reasons, every inbound reference to `docs/architecture/DASHBOARD.md` is
updated in the same commit, and the move is a `git mv` so history follows.

---

## Overlap reconciliation with prior ADRs (keep the ADR set one system)

Following ADR-009's convention. Each row states what the prior ADR owns and what this one does
**not** touch, so the set stays one system rather than twelve.

- **[ADR-002](ADR-002-native-decide-policy.md)** owns the `native_decide` policy and its ratchet.
  **D9 copies its per-bundle ratchet *shape*** (`NATIVE_DECIDE_BUNDLE_DEBT`, down-only, zero
  headroom) and changes nothing about it. `TODO-D39` — *"re-state the axiom-purity claim once
  `native_decide` is eliminated"* — is a textbook **D19** parked item: its release condition is
  ADR-002's elimination programme, expressible as a `phase:` token.
- **[ADR-004](ADR-004-substrate-integrity-gates.md)** owns the R1–R5 substrate gates and the
  **single-writer posture** for generated artifacts. **D14 extends that posture rather than
  weakening it**: the ledger currently has *no* writer, and `close_finding.py` becomes its single
  one. ADR-004's rule is the reason it must be the only one.
- **[ADR-005](ADR-005-derived-proof-atlas.md) / [ADR-007](ADR-007-kernel-nogo-ledger-and-negative-frontier.md)**
  own the derived atlas and the kernel-no-go ledger. **C2 is binding: the `lean` lane points *into*
  the atlas and never duplicates it.** D20's stall signal is already computed against
  `lean/atlas_view.json`; surfacing it adds no second derivation.
- **[ADR-006](ADR-006-aristotle-submission-rewrite.md)** owns the submission CLI and the
  verify-then-graft gauntlet. The `lean` lane's Aristotle fallback (D2) **is** that gauntlet,
  unchanged; no lane may bypass it.
- **[ADR-008](ADR-008-shared-lean-slot-control-plane.md)** owns the worktree slot control plane the
  `lean` lane fans out into, and established that *shared infrastructure must be compatible before
  any client activates*. D15's surfaces follow it: each lands behind its own gates, and none is a
  precondition for another. `QA_QI_INFRASTRUCTURE_MAP.md` §6 records that the control plane has zero
  references to `validate.py`, `build_graph` or `bundle_readiness`; **this ADR introduces no
  coupling to it.**
- **[ADR-009](ADR-009-validation-suite-modularization.md)** owns the check framework, hazards H1–H5,
  and the registration contract. **D13's promotion obligations are ADR-009's, quoted not invented** —
  `_CANONICAL_ORDER`, the re-export, the mutation entry, the CI floor. Its §Deferred items 0–7 are
  **all eight dispositioned** (D21), so nothing there is queued.
- **[ADR-010](ADR-010-publication-portfolio-reassessment.md)** owns the portfolio, the §D5a apex
  intake model — which is what D15's Flow-board rows key on — and its own open items, queued by
  **D21**.

  ⚠️ **ADR-010 §6a constrains this ADR directly**, and the constraint was met rather than waived:
  *no new check, gate or script without approval — establish what existing machinery covers the
  defect by reading the code, describe the residue, ask, then build.* **C9 is that reading**
  (`ledger_ids_resolve` already exists), **D13 is that residue** (promote or widen, never duplicate),
  and this document is the asking.
- **[ADR-011](ADR-011-manuscript-quality-layer.md)** owns the manuscript quality layer: the Stage
  9/10 sub-gates that are the `prose` lane's gate set, the reader-facing-voice and em-dash checks,
  and `scripts/record_review.py` — **the writer D14 is modelled on**. Its Phase 2 promotion path is
  what D9's ratchet attaches to. D9 adds no blocking condition — `major` was already blocking —
  and it does not change who writes the field.

### Overlap with `ARCHITECTURE_TODOs.MD` (the working doc, per C1)

The file's charter is one architecture-accuracy pass, under a standing operator build-freeze. **C1
holds: this ADR does not absorb it, parse it, or make it infrastructure.** Where the two touch:

| item | state | relationship |
|---|---|---|
| **B4** — chain-of-backing links name Lean targets that do not exist | ✅ GATED, backlog ratcheted (`chain_backing_targets_resolve`) | the **precedent** for D9's and D13's ratchets over a pre-existing population — a do-not-grow guard, not a defect count |
| **C1** — `lean_zero_sorry` reads a derived artifact rather than the extraction | `WATCH` | untouched |
| **TODO-D39** — circle back once `native_decide` is eliminated | parked | **the worked example for D19**; release condition is ADR-002's programme |
| **D40–D44** — pytest outcome drift · `verify_scope` residue · plugin-dev residue · skill-listing budget · `bundle_append --bookkeeping-only` | open, non-blocking | `lane=infra` on re-filing, if and when the freeze lifts. **Not re-filed by this ADR** — they are the file's own residue |
| **D45–D49** — the I1 drafting-wave defects | filed there during the pilot; **that was drift** | **re-filed as findings under D4.** Mixed lanes, not all substrate: D48 is a Lean strengthening, D47 and D49 are prose. Each is re-measured at filing and assigned its own lane — the ADR does not pre-assign them |
| **D50, D51** — bundles register Lean modules that were never built · the length gate keys on mtime and one identical rewrite blanks all 21 | open | **stay in the working doc.** Both are architecture-accuracy defects and belong to its charter |

⚠️ **Two of the file's own items are load-bearing for surfaces this ADR builds.** D50 means a bundle's
registered module list can name modules the build does not contain, and D51 means the manuscript-length
signal can blank for the whole roster on one rewrite. **The Flow board (S2) renders both fields.**
Neither is this ADR's to fix, and S2 must not present either as authoritative without saying what
guards it — the alternative is a control surface that inherits a known-soft signal and displays it as
fact.

---

## Pilot — the 117, dispositioned 2026-08-12

Manifest: `docs/audits/2026-08-12-critical-triage/manifest.json`. Every row carries a disposition,
evidence, lane and target. Six read-only agents ran the read-each slices; the lead took the
mechanical slice and re-verified every claim that changed a decision.

| disposition | count |
|---|---|
| fixed | 98 |
| still-open | 11 |
| superseded | 6 |
| not-a-defect | 2 |

**The backlog was a recording gap, not a defect backlog — 84% were already repaired.** The mechanism
is specific and was found during the pilot: several review documents were formally closed by later
re-reviews that were **never written into the ledger**. Three such re-reviews account for 14 fixed
verdicts in a single slice. Two further findings could not close **at the time of this pilot**
because their ledger keys carried suffixes (`…:I1:3.1-residual`) that match no id
`extract_review_finding_nodes` mints. ⚠️ That class was **re-keyed in `f86178e3`** and is no longer
inert — which is also how three of P7's five refusals came about, the records having become live.

**Triage behaved as a review pass in its own right.** It surfaced defects no finding had recorded: a
live severity-scoped closure bypass (D6); a false closure in the ledger (57 entries); D2
contradicting itself by a factor of seven within one document; two Lean predicates with
byte-identical bodies presented as distinct results (`IsCramerIIDUpperBound` /
`IsCramerLowerBoundEsscher`); a contraction field that reduces to `∀ y, I y ≤ I y` at the
instantiation used; a load-bearing "one downstream consumer exists" claim naming the wrong theorem;
a retracted priority claim surviving in the Lean source the paper points at; and the `Wang2024`
wrong-target citation above. **This is a result about process, not luck: disposition requires reading
the artifact, which is the same act as reviewing it.**

**Defects mutate rather than close.** The pattern recurred independently across slices — a count
literal corrected to the review-era value then re-drifted past it; a `Prop := True` predicate
replaced by a conjunction still trivially true at its instantiation; a figure whose repair landed in
a *comment* while the code kept its invented labels; a closure bypass that moved from the heading to
the ledger when the heading route was closed. **A fix verified once at a point in time, with no
mechanism attached, is a fix that will re-break.** This is the strongest argument for `verify` and it
was not anticipated by the first draft.

**A defect survived a lift and was strengthened by it.** `ChangeOfRings.hom_tensor_adjunction_dim` is
`rank = rank := rfl`. The source paper was corrected to say the module "does not itself supply a
machine-checked proof"; the bundle that absorbed it says the theorem "substantively discharges the H2
hypothesis" and proposes upstreaming the module to Mathlib. Lift is a place where a closed finding
can reopen silently, and nothing currently checks that.

**Self-review is not a substitute for independent review.** The lead's own I1 remediation, checked by
an agent instructed to be adversarial about it, contained two real errors: a false attribution
imported from an unverified docstring *while fixing a finding about unverified attribution*, and a
census of "six" where the population is seven. Both are corrected. Neither would have been caught by
the author. **The same lesson repeated one level up when an adversarial review of this ADR found C9,
D6.2's inert parameter, and the omitted registration obligations.**

---

## Plan

Phases are ordered by what unblocks the most. **P1–P7 and P8b are complete**, on
`feat/adr012-remediation-loop` against the plan
[`../superpowers/plans/2026-08-12-remediation-loop-core.md`](../superpowers/plans/2026-08-12-remediation-loop-core.md).
P8, P8c, P8d, P9, P10 and P11 remain open, each needing its own plan.

**P1 — Document the closure contract (D3). ✅ COMPLETE 2026-08-12 (`10c04da9`).**
`READINESS_GATES.md` gains the lifecycle section; `WAVE_EXECUTION_PIPELINE.md` §13
cross-references it rather than restating it. No code. First, because every later phase depended
on a rule that was only a comment.

**P2 — Triage the 117 (D5, D7). ✅ COMPLETE 2026-08-12.** See §Pilot. The ledger records were
deliberately **not written here** — that was P7, ordered after the bar was fixed, and it has
since run.

**P3 — Amend this ADR from what P2 taught. ✅ COMPLETE 2026-08-12**, and amended twice more from the
adversarial review and the intent-drift assessment.

**P4 — Emission and extraction (D1, D2, D10, D17). ✅ COMPLETE 2026-08-12** (`4e45d1d8`,
`46654641`, `ace9d8bf`, `6d41fc2e`, `36edada9`). The three markdown emitters gain `lane`,
`verify`, `blocked_by` and `needs_operator`; `extract_review_finding_nodes` parses all of them plus
`Gate:` and `Location:`; `BLOCKED_BY` edges emit; `review_runner.py` gains per-finding orientation
(D17). Enforcement extended `review_severity_declared` rather than adding a sibling check — it
already validated a declared token against a map. Ships with seeded-defect tests (D8).

⚠️ **`lane` is absent-tolerant by design** — an undeclared lane reads `unclassified`, never a
default lane, so an unrouted finding cannot be mistaken for a routed one. An *unknown* lane is
preserved verbatim and fails the check, which is a different signal from absence.

**P5 — The population guard (D9). ✅ COMPLETE 2026-08-12** (`ae623cb7`; both ratchets lowered
again in `eb878f5e` alongside the population they measure). The open-REQUIRED population ratchets
down per bundle, frozen at the live count, plus a corpus-wide ratchet on the unattributed
population. Not a severity tier: `major` has been blocking since 2026-07-31.

**P6 — Closure (D6, D13, D14). ✅ COMPLETE 2026-08-12.** `close_finding.py`, the only supported
writer (`792b3f45`); the bar unscoped from severity and extended with `verified_by` (`73bce19f`);
the ledger schema amended and its dead keys re-keyed (`f86178e3`); `ledger_ids_resolve` promoted to
a registered check **and its `graph_integrity` leg deleted in the same commit** (`0d35c85b`).
D13's "promoted or widened — never duplicated" was load-bearing: the check already existed at
dangling-baseline 66, and the first draft of this ADR proposed building it.

**P7 — Write the pilot's closure records, after P6. ✅ COMPLETE 2026-08-12** (`eb878f5e`).
Ordering mattered: closing a backlog through a bar that could still be walked around would have
baked the defect into every record. **Re-derived first, as required** — the pilot's 117 was 152 by
the time the writer existed. The manifest holds 117 rows, **106 of which carry a closing
disposition**; of those, **101 wrote cleanly and 5 were refused, none forced.** Open criticals
fell to 48. Every refusal is the same class — a record already exists with
a different status, and the reader is last-wins — and each is recorded with its open decision in
[`../audits/2026-08-12-critical-triage/refusals.md`](../audits/2026-08-12-critical-triage/refusals.md).

⚠️ **Three of those five refusals were *created* by this branch, not inherited.** The `f86178e3`
re-key moved inert records onto ids that now mint nodes, and several of those ids are also manifest
targets. That is the re-key working — the records became live — but it means those dispositions
need reconciling by hand rather than by a second batch.

**P8 — Substrate lane wiring (D4).** Re-file D45–D49 as `lane=substrate` findings; document the lane
in the pipeline; confirm `ARCHITECTURE_TODOs.MD` is back inside its charter.

**P8b — Parked work (D19). ✅ COMPLETE 2026-08-12** (`1a354d90`). The roadmap opt-in block, the
external release-condition tokens on `blocked_by`, and their evaluation. Independent of P9 and a
prerequisite for its Parked pane.

⚠️ **`release_condition_met` returns three values, and `None` is not `False`.** An unresolvable
condition is *unknown*, not *unmet*: rendering it unmet would leave a released item parked
forever, and rendering it met would release work on no evidence. `run:` is deliberately always
`None` until a run registry exists. The roadmap corpus is untouched — the block is opt-in, and
nothing is parked yet, so this narrows the unmechanized roadmap seam without closing it.

**P8c — Prior-ADR open items enter the queue (D21).** ADR-010 D2, D5 and D7 filed as findings with
lanes and targets, pointing back at ADR-010 as the decision record. Re-measure each before filing.

**P8d — Canonicalize `docs/architecture/DASHBOARD.md` (D22). ✅ COMPLETE 2026-08-12.** `git mv`
into `docs/architecture/`; the Answers contract line and README ownership row added (the check now
covers eight owned documents); the bundle roster, tier split and graph-type counts replaced with
pointers to the census; the false claims corrected **and marked in place** rather than silently
deleted, because a corrected mistake with no scar gets re-litigated.

⚠️ **The move immediately earned its keep, and in a way D22 did not predict.** `doc_refs_resolve`
fired on **three** references the moment the file entered the directory, and only two were the
expected deliberate absences. The third, `docker/docker-compose.graph.yml`, **exists** — the
scanner's `roots` tuple simply never walked `docker/`. A root missing from that tuple makes a live
file indistinguishable from a deleted one, which inverts the leg's whole purpose, so the fix was
the root and not an exception entry. `docs/submission_state.json` joined the reasoned-exception set
with its own note; `docs/verification_log.jsonl` was already there.

**Measured, not inherited:** every claim was checked against the tree rather than copied from C10.
`/api/save` was documented as *"Save accumulated verification actions"* and the string appears
**nowhere** in the app — a persistence path a reviewer could have believed in that has never
existed. `/api/verify` is really `/verify`. `BACKED_BY` appears **zero** times in the dashboard.

**P9 — The operator control surface (D15, D20).** In three waves, because they carry different risk. **P9a:**
S1, S4, the QI de-saturation and the sign-off persistence repair — all over data that already exists,
all with a template-contract test and a browser test per D2's dashboard exception. **P9b:** S2 and S3,
built thin against the specifications in D15 and iterated. **P9c:** the Loops pane (D20) over the
harness state that already exists — no new writer. `docs/architecture/DASHBOARD.md` corrected in the commit
that makes each claim wrong.

**P10 — Orchestration (D2, D10, D11, D16).** Route by lane, fan out on disjoint `target`, traverse
`BLOCKED_BY` for the cascade, worktree per lane, close by running `verify`, terminate at a merged
wave. Last, because it is the only phase whose design genuinely depends on what the earlier ones
reveal.

**P11 — The repeatable architecture-change skill (D18).**

---

## Consequences

**Accepted.** Findings become more expensive to emit. A reviewer decides a lane, writes a
verification command, and may owe a decision package. That cost is paid once, by the agent holding
the most context, instead of repeatedly by whoever picks the finding up later.

**Accepted.** Grandfathering 718 ledger records (D6) means the historical closure record is weaker
than the forward one, and a pre-2026-08-12 `fixed` does not imply a verification was run. Stated
rather than hidden.

**Accepted.** D9's ratchet enforces "no worse" immediately and "better" only as the population is
worked down. It deliberately does not re-litigate the 219 open majors, which already block their
bundles today; what it adds is that the population cannot grow.

**Accepted, and this is the largest one.** Scope roughly tripled between the first draft and this
version. The operator's ruling was explicit: *"I understand this may significantly increase scope of
ADR / spec / plans — but it's worth it to get it right vs. discover and bolt on later."* The first
draft's narrower scope was not a smaller version of this design; it was a different design that
solved the closure half and left the routing half without an owner.

**Risk.** The lane taxonomy may still be wrong. Six lanes survived a 117-finding pilot, which is
evidence but not proof; D2 may move again.

**Risk.** A `verify` command can rot — it may pass for reasons unrelated to the finding. Same class
as a test that cannot fail, same mitigation: the command must fail against the unrepaired artifact
at the time it is written.

**Risk.** S2 and S3 were the least-specified part of this ADR and are now specified (D15) at the
operator's request. What remains genuinely uncertain is **layout**, not content: the columns, the
feeds and their stores are pinned, and the arrangement is iterated against real use.

**Risk — named rather than designed around, and NARROWED.** The Flow board shows queue depth and
stage position; it cannot show which *subagents* are running, and a board implying otherwise would
be absence-rendered-as-success in a new location, so v1 states the limit on its face.

⚠️ **CORRECTED 2026-08-12: this paragraph read "live agent activity has no writer", which D20
explicitly retracts** — *"An earlier draft claimed activity had no writer at all. It does, at the
level that matters."* `/goal`-level activity has five writers under `.claude/dev-harness/`, including
a per-compaction heartbeat and a non-convergence signal. The correction landed in D20 and S2 and
never reached §Consequences. The residual risk is real but smaller than stated: **subagent** slots
turn over in minutes and are deliberately out of scope; a `/goal` loop is observable today.

**Risk — a pre-existing hole D19 only narrows.** The roadmap layer stays unmechanized: no check
reads `docs/roadmaps/`, and D19 adds an opt-in surface for parked work rather than gating the layer.
`END_TO_END_MAP.md` §2 already calls this the single largest ungated seam, and it remains one.

**Risk.** Feed B (System-2) reads a **gitignored** 840 KB local file. That is correct for a local
dashboard, but it means the Process pane is not reproducible across machines and shows nothing on a
fresh clone. Stated rather than discovered.

---

## Alternatives considered

**Make `ARCHITECTURE_TODOs.MD` machine-readable and gate on it.** Rejected. It has a charter and an
operator build-freeze; parsing it would convert a working doc into infrastructure by accident, which
is precisely the drift this ADR corrects.

**Retrofit routing fields onto all historical findings.** Partly obsolete: C7 showed `blocks` and
`target` need no backfill at all, because the reviewer already writes them. For `lane` and `verify`
the answer stands — forward-only, with a one-time typing pass over the open blocking population,
which P2 has now done for the criticals.

**One adversarial reviewer covering both papers and code.** Rejected (C5). The paper reviewer's
finding classes are paper-facing and correctly so; code review already has a proven chunked
discipline of its own. The gap was never that one agent should cover both — it was that the second
lane was never wired into the pipeline.

**Skip triage, type new findings only.** Rejected (D5). It produces a well-typed intake queue feeding
a blocked one.

**Ship closure now, routing later.** Rejected 2026-08-12 (D18). It was the first draft's implicit
choice and it produced D6.2 — a guard whose enabling condition no production code path can set.

**A seventh `operator` lane instead of an orthogonal flag.** Rejected (D12). A finding that needs the
operator still belongs to a lane; folding the two collapses "who does the work" into "who decides",
and hides operator-owned Lean and substrate findings inside `infra`.

---

## References

**Prior ADRs** — reconciled individually in §Overlap reconciliation; listed here so a reader lands on
the owner of each surface this ADR touches:
[ADR-002](ADR-002-native-decide-policy.md) (the ratchet shape D9 copies) ·
[ADR-004](ADR-004-substrate-integrity-gates.md) (the single-writer posture D14 extends) ·
[ADR-005](ADR-005-derived-proof-atlas.md) + [ADR-007](ADR-007-kernel-nogo-ledger-and-negative-frontier.md)
(the atlas the `lean` lane points into, C2) ·
[ADR-006](ADR-006-aristotle-submission-rewrite.md) (the gauntlet the `lean` lane ends in) ·
[ADR-008](ADR-008-shared-lean-slot-control-plane.md) (the worktree slots the fan-out uses) ·
[ADR-009](ADR-009-validation-suite-modularization.md) (the check contract D13 obeys; §Deferred all
eight dispositioned) · [ADR-010](ADR-010-publication-portfolio-reassessment.md) (§D5a's apex model,
§6a's build-approval constraint, and the open items D21 queues) ·
[ADR-011](ADR-011-manuscript-quality-layer.md) (the `prose` lane's gates, and `record_review.py`,
the writer D14 is modelled on).

**Implementation and artifacts:**

- `scripts/build_graph.py::extract_review_finding_nodes` — status inference, the closure bar, and the
  vacuity repair recorded in its comments
- `scripts/validation/checks/graph_atlas.py` — `ledger_ids_resolve`, the existing ledger-integrity
  guard (C9, D13)
- `docs/review_finding_supersessions.json` — the closure ledger; its `_purpose` and `_consumed_by`
  fields name its single consumer
- `scripts/record_review.py` — the precedent writer for D14
- `docs/WAVE_EXECUTION_PIPELINE.md` §Stage 13 — emission, and the re-invocation rule
- `docs/READINESS_GATES.md` — canonical gate definitions; target of P1
- `docs/architecture/DASHBOARD.md` — the control surface's governing document; corrected under D15
- `docs/architecture/CHECK_AUTHORING_GUIDE.md` — the obligations D8 and D13 inherit
- `lean/atlas_view.json` — the derived Lean substrate queue (C2)
- `docs/architecture/.working-docs/REVIEW_COVERAGE_LEDGER.md` — the chunking discipline the `pyrust`
  lane inherits
- `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` — charter and build-freeze (C1); D50 and
  D51 remain its own
