# Adversarial review — ADR-011 addendum (C6, D5, Phase 9)

**Target:** `docs/adrs/ADR-011-manuscript-quality-layer.md`, the 92-line uncommitted addendum
(`git diff --stat` confirms 92 insertions, 0 deletions — the whole addendum is new). Read in full,
plus C1–C5, D1–D4, References, and the sibling audit that fed it
(`docs/audits/2026-08-17-process-review/{FINDINGS.md,wave2/BRIEF.md}`).

**Scope of this review:** step 4 of `architecture-change` only — is any of this already built,
unbuildable, or unregistered. Not a judgment on whether the addendum is a good idea.

---

## Axis 1 — ALREADY BUILT

**PASS.** No author-side brief contract exists anywhere in the tree.

Searched and read in full: `.claude/plugins/skeft-qa/skills/paper-authoring/` (`SKILL.md` +
its only reference, `references/prohibited-patterns.md` — no brief-authoring content),
`.claude/plugins/skeft-qa/agents/paper-drafter.md` (reader-side only — see axis 2),
`.claude/plugins/skeft-qa/agents/` and `commands/` (no `redraft-lead.md` or brief-related
command), `docs/BUNDLE_LIFT_PROCEDURE.md` (`grep -n -i brief` → 2 hits, both
`review_runner.py --prep-brief`, neither a brief-content spec), `docs/WAVE_EXECUTION_PIPELINE.md`
§Stage 10 (read in full — "each with a brief... The lead owns the outline" and nothing further),
`docs/PAPER_STRATEGY.md` (zero "brief" hits), `docs/agents/` (`claims_reviewer.md`,
`claims-reviewer-bundle-prompts.md` — neither mentions Stage-10 dispatch briefs),
`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` (one hit, again `--prep-brief`).

`scripts/review_runner.py --prep-brief` is a genuinely different artifact, confirmed by reading
`emit_prep_brief()` (lines 84-140+): it emits a **Stage-13** review-prep brief (tier, source
list, anchor pointer) for the four **reviewer** agents, not a Stage-10 dispatch brief for
`paper-drafter`. No overlap in stage, consumer, or content.

This finding is independently corroborated by this same audit tree: `wave2/BRIEF.md`
(BRIEF-1-01) ran the identical exhaustive search in an earlier wave and reached the same
CONFIRMED verdict, and `FINDINGS.md` §5 restates it. C6/D5 are not duplicating undiscovered
work; they are formalizing an already-independently-confirmed gap.

---

## Axis 2 — DUPLICATE MECHANISM

**DEFECT** (partial). The "inversion, not a second enumeration" framing is honest only for a
narrow reading of the contract, and that narrow reading does not cover what C6 itself cites as
evidence.

`paper-drafter.md` "Read first" item 4 is the entire reader-side enumeration, quoted in full:

> "Your brief — bundle, section, charter role, the substrate you may draw on, and an absolute
> path for every source your section cites."

That is five fields. D5 claims the author-side contract is "that list read in the other
direction, with one column added" and "enumerates nothing the agent definition does not already
name." Taken literally, a contract built from those five fields plus a provenance column is a
true inversion, not a second roster — rule 1 is satisfied.

But `wave2/BRIEF.md`'s own 2026-08-17 pilot against the **real** D9 dispatch brief found a
de-facto contract far richer than those five fields: "worktree and branch, why the redraft
exists, settled bundle context, the assemble-incrementally rule, a seven-point verification
discipline, an explicit 'REQUIRED: report contradictions...', the findings format, git
discipline." None of that is named in `paper-drafter.md`'s five-field list — searched, confirmed
absent. C6 itself leans on part of that richer set as evidence ("the same holds for the
'assemble incrementally' rule"). So there is a real tension the addendum does not resolve:

- If the shipped contract is strictly the five-field inversion (as D5's text implies), it is
  honestly *not* a duplicate mechanism, but it does not address the "assemble incrementally"
  decay or the unsourced-claim pattern C6 cites as motivating evidence (neither is a brief
  *field*; both are process/sourcing rules absent from `paper-drafter.md` entirely).
- If Phase 9 intends the contract to also capture those richer, currently-undocumented
  elements (which is what would actually close the gap C6 measures), then it is **not** simply
  "the list read in the other direction" — it adds substantial content the reader-side agent
  definition never named, which is the second-roster shape rule 1 prohibits.

Recommend: scope Phase 9's item 1 explicitly to one of the two, and if the broader scope is
intended, extend `paper-drafter.md`'s own enumeration first so the "inversion" claim stays true
by construction.

---

## Axis 3 — THE MEASUREMENT

**DEFECT, severe.** C6's central population claim does not reproduce and is directly
contradicted by a sibling, already-corrected document in this same audit tree.

C6: *"Of thirteen Stage-10 redraft finding sets, five carry one [a CONTRADICTIONS section] —
D1, D4, D8, E1, L3, all dated 2026-08-15 — and none of the three dispatched on 2026-08-17
does."*

Re-derivation:

1. `grep -n "CONTRADICTIONS"` (exact string, case-sensitive, any position) across all 13 filed
   finding docs (`papers/AutomatedReviews/2026-08-1[57]-*-stage10-redraft/*.md`) returns **zero
   hits in all 13 files**, including D1, D4, D8, E1, L3. No finding file — not even the five C6
   names — contains the literal string "CONTRADICTIONS" anywhere.
2. Loosening to `-i "contradict"` shows what actually produced the five-name list: D1, D4, D8,
   E1, L3 each happen to contain the ordinary English word "contradicts" inside an unrelated
   physics/prose finding (e.g. D1 §1.1 "carries a factor of two that contradicts
   `noise_floor_eq_delta_diss`"; D8 §1.1 "`PAPER_STRATEGY.md` §D8 contradicts itself"). These
   are findings *about the paper's content*, not instances of the drafter's report-back
   CONTRADICTIONS section that `paper-drafter.md:212` requires. D2, which also contains
   "contradict" three times and is *not* in C6's five, shows the substring match is not even
   applied consistently.
3. **D9 — one of the three C6 claims carries zero — literally contains the sentence "See the
   contradictions section of my report"** (`papers/AutomatedReviews/2026-08-17-d9-stage10-redraft/D9.md:673`),
   directly describing content from the required report-back field. C6's claim that none of the
   2026-08-17 bundles carries one is backwards for the one case checkable from the filed
   artifact itself.

This is not a fresh finding — it is the exact defect the working tree's own
`docs/audits/2026-08-17-process-review/FINDINGS.md` §5 already names and retracts (uncommitted,
alongside the ADR): *"The second [revision] claimed the CONTRADICTIONS requirement had decayed
to zero across the Aug-17 dispatches — measured by scanning **findings files** for the heading,
when the brief asks for it in the **report-back**. The D9 brief carries the requirement
verbatim."* C6 is that already-disavowed measurement, unrevised, promoted into the ADR.

**Corrected statement:** the CONTRADICTIONS instrument is a report-back field the drafter
returns to the lead in-session (dispatch transcript / redraft-lead sub-transcript), not content
that lands in the filed `papers/AutomatedReviews/.../<bundle>.md` document. Scanning the filed
docs for the heading is the wrong population and the wrong predicate; it will read near-zero
regardless of whether the underlying discipline holds, because that was never where the signal
was expected to land. `wave2/BRIEF.md`'s own re-measurement (grepping the actual dispatch-brief
transcripts, not the findings files) found the requirement present verbatim in **9 of 13**
bundles' briefs (including all three of D9/D10/D7), not present-then-decayed as C6 states. C6
must be rewritten against that corrected population and predicate, or dropped in favor of citing
`wave2/BRIEF.md`/`FINDINGS.md` §5 directly.

---

## Axis 4 — UNREGISTERED

**DEFECT, minor.** Phase 9's four-artifact list omits `docs/WAVE_PIPELINE_RATIONALE.md`.

That document exists specifically because "Phase 7... created" it to hold "the provenance
behind each pipeline rule," stated in its own header: *"Entries are keyed to the stage or
invariant they explain... Every entry below is a rule that was paid for: an incident, an audit
finding, or a measurement."* Phase 9's item 2 amends `WAVE_EXECUTION_PIPELINE.md` §Stage 10 to
add a new rule ("names the contract as the brief's owner"), and that rule is paid for by exactly
this audit's finding — the textbook case the rationale doc's own header describes. `grep -n -i
"stage 10\|dispatch brief\|paper-drafter" docs/WAVE_PIPELINE_RATIONALE.md` shows three existing
"Stage 10 — why..." entries and no fourth for the dispatch-brief contract. Since Phase 9 runs
after Phase 7 established this convention, and every other post-Phase-7 law amendment in this
ADR is expected to follow it, Phase 9 should add a "Stage 10 — why the dispatch brief has an
owning contract" entry as a fifth artifact, or explain why this rule is exempt.

Checked and clean: the plugin `README.md` roster (paper-drafter's row describes behavior, not
brief field contents — unaffected), `tests/test_architecture_claims.py` (no existing pin on
`paper-drafter.md`'s brief enumeration or on brief content — nothing to update or break),
`docs/architecture/SURFACE_INVENTORY.md` (paper-drafter's entry is pulled from the agent's
frontmatter `description:`, which Phase 9 does not touch — unaffected),
`docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md` (mentions `paper-drafter` at the diagram/prose
level; its claim that "nothing downstream records that an agent produced the prose" is
orthogonal to the brief-authoring gap and stays true either way).

The `docs/architecture/README.md` ownership-table row Phase 9 item 3 proposes is the right shape
and follows the two prior instances (ADR-014, ADR-008) correctly, both independently confirmed
present at the cited lines.

---

## Axis 5 — SCOPE HONESTY

**DEFECT.** As written, D5's verification plan inherits axis 3's flawed predicate, which makes
it unfalsifiable in practice rather than merely deferred.

D5: *"Verification... a redraft that files no brief contradiction against a brief whose claims
were all sourced."* Phase 9: *"...its bundle's finding set read for whether a contradiction was
filed against a claim whose origin the brief named. C6's population is the baseline."*

Both point at the same artifact axis 3 shows is the wrong one: the filed
`papers/AutomatedReviews/.../<bundle>.md` finding set. Zero of the 13 precedent bundles contain
the literal report-back content there (axis 3, point 1) — it lives in the dispatch transcript.
So a pilot run under this plan will read "no contradiction filed" **regardless of whether the
new contract improved anything**, for the same structural reason C6's baseline count is wrong:
the signal was never expected to land in that file. That is the shape of an unfalsifiable
design — not because no check exists (D5 is explicit and correct that no check is warranted for
free-prose input), but because the one thing that *is* proposed as evidence is scoped to a
location that cannot show the failure mode even when it occurs.

**What would falsify it, if corrected:** read the next dispatch's actual brief text (as sent to
`paper-drafter`, e.g. captured in the redraft-lead's session transcript or a `_prep/` artifact
the lead deliberately retains) for whether each claim names its source per the contract, and
read the drafter's **returned report** (not the filed findings doc) for a CONTRADICTIONS entry
against an unsourced claim. If the drafter still contradicts a brief claim that the contract
required to carry a named origin, the contract failed to prevent what it exists to prevent.
That is checkable and would falsify D5's "no check needed" premise if it happened twice.
Recommend Phase 9 fix its own verification pointer before shipping, not defer it to "the next
dispatch" using the same broken pointer.

---

## Verdict

1. ALREADY BUILT — PASS. Exhaustive search confirms no author-side brief contract exists
   anywhere; corroborated independently by `wave2/BRIEF.md` (BRIEF-1-01).
2. DUPLICATE MECHANISM — DEFECT. "Inversion of paper-drafter's five fields" is honest only if
   the contract stays that narrow, but that narrow scope does not cover the richer de-facto
   brief content (assemble-incrementally, verification discipline, sourcing rules) that C6
   itself cites as evidence; the addendum doesn't say which it is.
3. THE MEASUREMENT — DEFECT, severe. C6's "5 of 13, none of the Aug-17 three" does not
   reproduce (0 of 13 contain the literal string "CONTRADICTIONS"); the five names trace to an
   unrelated-word substring match; D9, one of the three claimed zero, explicitly references its
   own contradictions section. This is the exact predicate `FINDINGS.md` §5 already retracted in
   the same working tree, unpropagated into the ADR.
4. UNREGISTERED — DEFECT, minor. Phase 9's four-artifact list omits
   `docs/WAVE_PIPELINE_RATIONALE.md`, which Phase 7 established as the required home for every
   pipeline rule's "why," and this rule is a textbook case of what belongs there.
5. SCOPE HONESTY — DEFECT. D5's "no check, verify at next dispatch" plan points its own
   verification at the same wrong artifact axis 3 identifies, making it read as passing
   regardless of outcome; a corrected pointer (the drafter's returned report, not the filed
   findings doc) would restore falsifiability.

**Overall: REVISE.** The underlying diagnosis (no author-side brief contract exists, and
`docs/architecture/README.md`'s two prior "surface with no home" precedents apply) is sound and
independently corroborated. But C6's measurement must be rewritten against the corrected
population before this ships — it currently asserts a factually backwards claim about D9 that a
one-line grep refutes — and D5/Phase 9's own verification plan must point at the corrected
artifact (the drafter's report-back, not the filed findings doc) or it will falsely read as
successful on the next dispatch regardless of whether the contract works. Axis 2's scope
ambiguity should also be resolved explicitly. None of this requires killing the phase; all three
defects are fixable by re-pointing the same paragraphs at what the sibling audit documents
(`wave2/BRIEF.md`, `FINDINGS.md` §5) already got right.
