# ADR-012 — The finding lifecycle: routing contract, closure bar, and the untriaged backlog

- **Status:** 📝 **PROPOSED — NOT BUILT (drafted 2026-08-12).** Nothing in this document has
  been implemented. It is written before the code deliberately, per the architecture rule that
  *a doc written afterwards is a changelog; only one written first is a specification.*

  **The pilot ran and this document changed under it.** The operator's direction was to draft
  it, triage the 117 open critical findings against it, and amend. That happened on 2026-08-12:
  all 117 were dispositioned, and the result **materially reduced the scope of this ADR** — most
  of what the first draft proposed to build already exists and is being discarded rather than
  missing. §Pilot records the evidence; D1 and D6 were rewritten because of it.

  The single most important correction: the first draft proposed four new finding fields and a
  new check. Two of the four fields **already exist** in the reviewer's own template, and two
  existing mechanisms already enforce closure quality. Building as first drafted would have been
  the "second mechanism beside one that already exists" failure the architecture rules name.

- **Scope:** the lifecycle of a `ReviewFinding` from emission through routing to closure. It does
  **not** change what the reviewers look for, only what they record and how a finding is
  scheduled and retired.
- **Does not supersede:** `ARCHITECTURE_TODOs.MD`. That file's charter is the architecture-accuracy
  pass, under a standing operator build-freeze; this ADR corrects a drift *into* it (§C1) rather
  than absorbing it.
- **Governed by:** the architecture rules in `CLAUDE.md` — read before designing, update before
  shipping in the same commit, never write a census count into a narrative.

---

## Context

The finding lifecycle already exists, is deliberately hardened, and works. It is also
undocumented at the point where it decides everything, and it discards the information that
would let findings be scheduled.

**What runs today.** A reviewer emits a markdown report; `build_graph.py`'s
`extract_review_finding_nodes` parses `### N.N — 🔴 …` headings into `ReviewFinding` nodes with
`severity` and `status`; `FLAGS` edges attach each to its paper and bundle; a BLOCKER flips the
affected `ReadinessGate` to `blocked`; `readiness_submission_gate` then refuses submission.

**Status is `open` by default, and only a ledger can close it.** A finding's status is *inferred*
as `open` unless `docs/review_finding_supersessions.json` carries a record for it. For a
blocking-severity finding that record must additionally carry an explicit closing status, at
least forty characters of rationale, and a commit or date anchor; otherwise the closure is
rejected and the finding stays open, tagged `blocking_closure_rejected`. This design was reached
over four rounds of repair, each of which found a way through a narrower rule, and the code
records why the current shape was chosen: *making the ledger the only transition channel removes
the class instead of narrowing it.*

**The instrument is working.** `readiness_submission_gate` is RED as of this drafting. It is one
of the two checks `validate.py` is deliberately red on. This ADR is not a response to a broken
gate; it is a response to a gate whose output nobody could act on efficiently.

**What is measured.** Across the review corpus:

| severity | open |
|---|---|
| critical | 117 |
| major | 219 |
| minor + advisory | 657 |

Every one of the 117 open criticals is **untriaged** — not one had a ledger record that failed
the closure bar. They are not sloppily closed; no closure was ever attempted. The ledger holds
870 records against a far larger finding population, so the majority of findings have never been
dispositioned either way. An unknown fraction of the 117 is very likely *fixed and unrecorded*,
which is itself the finding: the system cannot distinguish "still broken" from "repaired
silently," and it is correct to refuse to guess.

**Three problems follow.**

1. **A finding records what is wrong and nothing about who repairs it.** There is no lane, no
   target, and no verification command. Scheduling and parallelizing therefore have nothing to
   key on, and every remediation re-derives orientation from cold context.
2. **The closure contract is invisible where it matters.** `READINESS_GATES.md` is the canonical
   gate document and does not mention the ledger. The open-by-default rule and the closure bar —
   the rules that determine what "117 open" *means* — exist only as a comment inside
   `build_graph.py`.
3. **Substrate defects found outside a wave have no queue.** A defect like `tetrad_gap_solution`
   returning a non-solution above the saturation coupling is not a proof obligation (the atlas
   covers those), not an architecture-accuracy defect, and not a paper finding once the paper
   discloses it honestly. During the I1 pilot these were filed into `ARCHITECTURE_TODOs.MD`
   because it was the nearest open drawer. That was drift, and §C1 records it as such.

---

## Constraints — verified, and load-bearing for the design

**C1. `ARCHITECTURE_TODOs.MD` is a working doc, not infrastructure.** Its stated charter is what
one architecture-accuracy pass found, under a standing operator constraint that *nothing in this
file is authorized to be built*. Nothing in `scripts/`, `src/`, `tests/` or `.claude/` parses it;
every reference is inside a comment. Filing substrate defects there (D45–D49, 2026-08-11) put
work items into a file with no reader. This ADR does not fix that by making the file
machine-readable — it fixes it by giving those defects a queue that already has teeth.

**C2. The Lean substrate queue already exists and is derived.** `lean/atlas_view.json` carries
the open assumptions, the frontier, and the settled obstructions, computed from `lean_deps.json`
and therefore incapable of drifting from the build. Any Lean-lane routing must *point into* the
atlas, not duplicate it.

**C3. Only one of the reviewer output formats is graph-extracted.** The markdown reports from the
adversarial, claims (bundle mode) and figure reviewers are parsed into `ReviewFinding` nodes.
`papers/<B>/claims_review.json` is a different object — per-sentence verdicts under
`sentence_state.py`, not work items. `prose-reviewer` emits a restructuring instruction and no
findings **by design**, which is what makes it the fourth reviewer rather than a second
adversarial one. The routing contract therefore binds three emitters, not five.

**C4. This exact mechanism has already failed vacuously.** The BLOCKER→gate propagation once
evaluated as passed for ten bundles because their findings produced zero edges — the gate
reported "all P1 passed" while blockers sat unclosed on disk. It was made unconditional
2026-07-31. The code's own conclusion is the constraint: *an unrecordable finding is
indistinguishable from no finding.* Any layer added here ships with a seeded-defect test or it
does not ship.

**C5. Lean and Python/Rust are different lanes with different gates.** Lean work is driven by the
atlas and the `lean4` MCP loop and gated on a clean `lake build`, zero `sorry`, kernel-purity and
the axiom allowlist. Python and Rust work goes through the superpowers flow and is gated on
pytest, `verify_scope`, and dependency declaration. Routing them through one lane would either
under-gate the Lean side or impose irrelevant gates on the Python side.

**C7. The routing data mostly already exists, and the extractor throws it away.**
`.claude/plugins/skeft-qa/agents/adversarial-reviewer.md` has carried a per-finding field
template since before this ADR: `- **Gate:**`, `- **Location:**`, `- **Observed:**`,
`- **Evidence:**`, `- **Expected:**`, `- **Fix:**`, and `- **Severity:**` (required from
2026-08-01). Measured across the review corpus, of the findings carrying a severity glyph
**93% carry `Gate:`, 92% carry `Location:` and 87% carry `Fix:`**. But
`extract_review_finding_nodes` parses only severity and status: a `ReviewFinding` node's meta is
`{inferred_bundle, inferred_paper, review_date, review_file, review_name, section, severity,
status}`. `Gate:` and `Location:` — which are exactly the `blocks` and `target` this ADR set out
to invent — are written by the reviewer, sit in the markdown, and are discarded at extraction.
**The first draft of D1 would have added a second name for data the system already collects.**

**C8. Two mechanisms already enforce closure quality; a third would be duplication.**
`build_graph.py:1954-1967` applies the blocking-closure bar (explicit closing status, ≥40
characters of rationale, and a commit or date anchor). `reviews.py::accepted_findings_carry_rationale`
separately pins that `accepted` records justify acceptance in writing, and its own docstring
records why: `accepted` had become "the cheapest way to make a blocking finding disappear from
Gate 11". Any verification requirement belongs **inside the existing bar**, not beside it.

⚠️ The ledger's declared `_entry_format` is already out of step with the code that reads it: the
format names `date` as the only temporal field, while `build_graph` accepts any of `commit`,
`date`, `closed_date` or `applied_at` as the anchor. Whatever amends the ledger schema fixes that
drift in the same change.

**C6. The existing ledger records predate any verification requirement.** 718 records already
assert `fixed`. None was required to name a command that proves it. During the I1 pilot a defect
recorded as fixed twice was found still live, because the repair had landed in a comment claiming
the code was fixed rather than in the code. A verification requirement is therefore load-bearing
rather than hygienic — but it cannot be applied retroactively without re-litigating 718 records.

---

## Decision

**D1 — Parse the routing information that already exists; add only what is missing.**
Rewritten after the pilot (C7). The reviewer template is not extended by four fields, because two
of them are already written on 92–93% of findings and merely discarded:

| field | source | change required |
|---|---|---|
| `blocks` | the existing `- **Gate:**` line | **parse it** — no reviewer change |
| `target` | the existing `- **Location:**` line | **parse it** — no reviewer change |
| `lane` | new: `lean` · `pyrust` · `substrate` · `prose` · `research` · `infra` | add one line to the template |
| `verify` | new: a runnable command naming its invariant | add one line to the template |

`extract_review_finding_nodes` gains four meta keys. `blocks` and `target` are populated for the
existing corpus at extraction time with **no backfill and no re-review** — the retrofit the first
draft called unaffordable turns out to be a parser change. `lane` and `verify` apply forward-only;
absent, they read `unclassified` rather than failing the historical corpus.

⚠️ `verify` must name the invariant it asserts, not merely run. The pilot produced two independent
demonstrations: a bibitem agreeing with `CITATION_REGISTRY` does not close a finding that says
*both* are wrong against the real paper, and `doi_verified: True` recorded that a DOI **resolves**,
not that it resolves **to the cited work** — which is how `Wang2024` carried another paper's venue
and DOI through three months and a Stage-13 fix-pass. A command that checks a weaker property than
its name implies is worse than no command, because it manufactures confidence.

**D2 — Six lanes, with Lean and Python/Rust kept separate (C5).**

| lane | flow | gates |
|---|---|---|
| `lean` | atlas target → `lean4` skill + MCP loop → worktree slot → Aristotle fallback | `lake build` clean, zero `sorry`, kernel-purity, axiom allowlist |
| `pyrust` | superpowers: brainstorm → plan → subagent dev → pr-review-toolkit | pytest, `verify_scope`, dependency declaration |
| `substrate` | theorem and implementation disagree | **both** gate sets, plus a test that fails before the fix |
| `prose` | paper agents | Stage 9/10 sub-gates |
| `research` | three-tier ladder | cited report vetted before filing |
| `infra` | fix when mechanically obvious, else queue to the operator | `validate.py` + plugin surface tests |

`substrate` is its own lane because a defect of that kind needs a Lean-side statement, a
Python-side repair, and a regression test asserting the two agree — which is neither adjacent
lane, and is the class that had no queue at all (§Context 3).

**D3 — The closure contract moves into the canonical gate document.** `READINESS_GATES.md` gains
a section stating: status is `open` until a ledger record says otherwise; the ledger is the only
transition channel; a blocking-severity closure additionally requires an explicit status, a
rationale of at least forty characters, and a commit or date anchor. The rule stops living
exclusively in a code comment. Per architecture rule 2 this lands **before** the code that
depends on it.

**D4 — Substrate defects file as findings, not into the working doc.** A substrate defect
discovered outside a wave is emitted as a `ReviewFinding` with `lane=substrate` and enters the
same queue as every other finding. `ARCHITECTURE_TODOs.MD` reverts to its charter (C1). The
D45–D49 entries filed there during the I1 pilot are re-filed as findings; the file keeps D50 and
D51, which are architecture-accuracy defects and belong to it.

**D5 — Triage precedes intake typing, and is the pilot.** ⏳ **PILOT-PENDING.** Typing new
findings while the queue behind the gate is untriaged optimizes intake into a blockage. The 117
open criticals are dispositioned first, and that exercise is the pilot for D1's field set: any
field that proves unfillable or useless in triage is wrong and gets amended here before the
contract is enforced on emission.

**D6 — Extend the existing closure bar; do not add a check beside it.** Rewritten after the
pilot (C8). Two changes to `build_graph.py:1954-1967`, both inside the mechanism that is already
there:

1. **Remove the severity scoping.** The bar is currently gated on
   `severity in ('critical','major','blocker')`. Below that line, any two-key ledger record closes
   a finding with no evidence and no anchor. Combined with the body-declarable `- **Severity:**`
   (whose declared value wins over the heading glyph), a 🔴 BLOCKER heading declaring
   `recommended` closes on `{"finding_id": X, "status": "fixed"}`. **This is not a hypothetical:
   it is a filed finding, open across four consecutive rounds, and it reproduced byte-for-byte at
   HEAD during this pilot.** The bar applies to every severity.
2. **Add `verified_by` to the bar's required fields** for closures of findings that carry a
   `verify` command: the record names the command run and its result. The 718 existing records are
   grandfathered — re-litigating them costs more than it returns — and the ledger's declared
   `_entry_format` is corrected in the same change (C7).

The pilot's justification for (2) is not theoretical either: a ledger record asserts it "cleaned
up duplicate `inprep`/`primary_source_path` lines"; **57 registry entries still carry them**, and
on 20 the duplicate flips the effective value. The one artifact the system treats as authoritative
contained a false closure, and one second of machine time would have caught it.

**D7 — The pre-bundle-era criticals are in scope.** 18 of the 117 sit in review documents that
predate the bundle era and resolve to no bundle. Operator ruling (2026-08-12): treat them as
in-scope for review — *"worst case it's a teaching lesson that might be fruitful."* They are
triaged with the rest rather than declared out of scope by age.

**D8 — Non-vacuity is a shipping requirement, not a review note (C4).** Every check introduced
here ships with a test that seeds the defect it claims to catch and observes red: a finding
emitted without a `lane` must turn the check red; a finding with an unknown lane must turn it
red. A check whose population can be empty while it reports PASS does not count as built.

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

**The backlog was a recording gap, not a defect backlog — 84% were already repaired.** The
mechanism is specific and was found during the pilot: several review documents were formally
closed by later re-reviews that were **never written into the ledger**. Three such re-reviews
account for 14 fixed verdicts in a single slice. Two further findings can never close because
their ledger keys carry suffixes (`…:I1:3.1-residual`) that do not match the ids
`extract_review_finding_nodes` mints.

**Triage behaved as a review pass in its own right.** It surfaced defects no finding had recorded:
a live severity-scoped closure bypass (D6); a false closure in the ledger (57 entries); D2
contradicting itself by a factor of seven within one document (Δ=2 at one site, Δ=14 at another,
after a partial fix); two Lean predicates with byte-identical bodies presented as distinct results
(`IsCramerIIDUpperBound` / `IsCramerLowerBoundEsscher`); a contraction field that reduces to
`∀ y, I y ≤ I y` at the instantiation used; a load-bearing "one downstream consumer exists" claim
naming the wrong theorem; a retracted priority claim surviving in the Lean source the paper points
at; and the `Wang2024` wrong-target citation above. **This is a result about process, not luck:
disposition requires reading the artifact, which is the same act as reviewing it.**

**Defects mutate rather than close.** The pattern recurred independently across slices — a count
literal corrected to the review-era value then re-drifted past it; a `Prop := True` predicate
replaced by a conjunction still trivially true at its instantiation; a figure whose repair landed
in a *comment* while the code kept its invented labels; a closure bypass that moved from the
heading to the ledger when the heading route was closed. **A fix verified once at a point in time,
with no mechanism attached, is a fix that will re-break.** This is the strongest argument for
`verify` and it was not anticipated by the first draft.

**A defect survived a lift and was strengthened by it.** `ChangeOfRings.hom_tensor_adjunction_dim`
is `rank = rank := rfl`. The source paper was corrected to say the module "does not itself supply
a machine-checked proof"; the bundle that absorbed it says the theorem "substantively discharges
the H2 hypothesis" and proposes upstreaming the module to Mathlib. Lift is a place where a closed
finding can reopen silently, and nothing currently checks that.

**Self-review is not a substitute for independent review.** The lead's own I1 remediation, checked
by an agent instructed to be adversarial about it, contained two real errors: a false attribution
imported from an unverified docstring *while fixing a finding about unverified attribution*, and a
census of "six" where the population is seven (the seventh splits `: Prop :=` and `True` across
lines, which a line-oriented scan cannot see). Both are corrected. Neither would have been caught
by the author.

---

## Plan

Phases are ordered by what unblocks the most, not by what ships fastest. **P2 is complete**; the
rest are revised against what it taught.

**P1 — Document the closure contract (D3).** `READINESS_GATES.md` gains the lifecycle section;
`WAVE_EXECUTION_PIPELINE.md` §13 cross-references it rather than restating it. No code. This is
first because every later phase is meaningless if the rule it depends on is only a comment.

**P2 — Triage the 117 (D5, D7). ✅ COMPLETE 2026-08-12.** See §Pilot. Manifest written; 117 of 117
dispositioned. The ledger records for the 98 `fixed` are **not yet written** — that is P2b, and it
is deliberately separated because writing 98 closures under a bar that is currently bypassable
(D6.1) would bake in the defect.

**P2b — Write the closure records, after D6.1.** Ordering matters: the bypass is fixed first, then
the backlog is closed through a bar that cannot be walked around. Two malformed ledger keys are
re-keyed in the same pass so their findings can close at all.

**P3 — Amend this ADR from what P2 taught. ✅ COMPLETE 2026-08-12.** D1 and D6 were rewritten,
C7 and C8 added, and the §Pilot section records the evidence. The amendment materially shrank the
build: two of four fields already exist, and the closure requirement folds into an existing bar.

**P4 — Extraction and emission (D1, D2).** `extract_review_finding_nodes` parses `Gate:` and
`Location:` into `blocks` and `target` (immediate, whole-corpus, no backfill). The reviewer
template gains `lane` and `verify`. Enforcement extends the existing `review_severity_declared`
rather than adding a sibling check — it already validates a declared token against a map, which is
the same shape as validating a lane. Ships with its seeded-defect test (D8).

**P5 — Substrate lane wiring (D4).** Re-file D45–D49 as `lane=substrate` findings; document the
lane in the pipeline; confirm `ARCHITECTURE_TODOs.MD` is back inside its charter.

**P6 — Orchestration.** ⏳ **PILOT-PENDING and deliberately last.** Route by lane, fan out on
disjoint `target`, worktree per lane, close by running `verify`. Nothing here is designed until
P2 has shown what the queue actually looks like.

---

## Consequences

**Accepted.** The triage in P2 is real work with no new capability at the end of it — its output
is an accurate queue, not a shipped feature. That is the point: the current queue's contents are
unknown, and every downstream automation multiplies whatever error is in it.

**Accepted.** Findings become more expensive to emit. A reviewer must decide a lane and write a
verification command. That cost is paid once, by the agent holding the most context, instead of
repeatedly by whoever picks the finding up later.

**Accepted.** Grandfathering 718 ledger records (D6) means the historical closure record is
weaker than the forward one, and a pre-2026-08-12 `fixed` does not imply a verification was run.
Stated rather than hidden.

**Risk.** The lane taxonomy may be wrong. Six lanes is a guess informed by one pilot bundle; P2
will exercise it against 117 real findings, and D2 is expected to move.

**Risk.** A `verify` command can rot — it may pass for reasons unrelated to the finding. This is
the same class as a test that cannot fail, and the mitigation is the same: the command must fail
against the unrepaired artifact at the time it is written.

---

## Alternatives considered

**Make `ARCHITECTURE_TODOs.MD` machine-readable and gate on it.** Rejected. It has a charter and
an operator build-freeze; parsing it would convert a working doc into infrastructure by accident,
which is precisely the drift this ADR corrects.

**Retrofit routing fields onto all historical findings.** Rejected as first move. The corpus is
large enough that a full backfill would dominate the effort while the criticals — the only
findings holding a gate red — are a far smaller set. Triage the blocking population first; the
rest can be typed opportunistically or left as `unclassified`.

**One adversarial reviewer covering both papers and code.** Rejected (C5). The paper reviewer's
finding classes are paper-facing and correctly so; code review already has a proven chunked
discipline of its own. The gap was never that one agent should cover both — it was that the
second lane was never wired into the pipeline.

**Skip triage, type new findings only.** Rejected (D5). It produces a well-typed intake queue
feeding a blocked one, and leaves the number that started this — 117 untriaged criticals —
untouched behind a red gate.

---

## References

- `scripts/build_graph.py::extract_review_finding_nodes` — status inference, the closure bar, and
  the vacuity repair recorded in its comments
- `docs/review_finding_supersessions.json` — the closure ledger; its `_purpose` and `_consumed_by`
  fields name its single consumer
- `docs/WAVE_EXECUTION_PIPELINE.md` §Stage 13 — emission, and the re-invocation rule
- `docs/READINESS_GATES.md` — canonical gate definitions; target of P1
- `lean/atlas_view.json` — the derived Lean substrate queue (C2)
- `docs/architecture/.working-docs/REVIEW_COVERAGE_LEDGER.md` — the chunking discipline the
  `pyrust` lane inherits
- `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` — charter and build-freeze (C1); D50 and
  D51 remain its own
