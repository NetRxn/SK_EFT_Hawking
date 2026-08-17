# Wave 2 — Cluster BRIEF: the Stage-10 dispatch brief

Verifies the two claims about how the lead constructs and reuses the Stage-10 redraft brief
handed to `paper-drafter`. Window: t0 = 2026-08-15 09:46 CDT to HEAD (`4c81c2ec`). Loaded
plugin cache = `f33dc0a1` (2026-08-15 09:44:39). Four later plugin commits were never loaded
in the window: `fd6cac3d` (Aug 15 12:02), `e9e5e314` (Aug 15 16:24), `c4b1a1ca` (Aug 15
16:26), `f58a3fe4` (Aug 17 03:01).

---

### BRIEF-1-01 — No governing artifact specifies what the lead's Stage-10 dispatch brief must contain or where its claims come from

- **Wave-1 source IDs:** G-02, C-06, C-10, B-04, B-05, B-09, B-10, D-02, D-06, F-05, F-06,
  F-15, H-06, H-02, H-05

- **Verdict:** CONFIRMED (re-diagnosed on mechanism and population)

- **Evidence at HEAD:**
  - `.claude/plugins/skeft-qa/agents/paper-drafter.md` — read in full. Governs what the
    **drafter** must do on receipt of a brief (read the charter, read the substrate, read
    every cited source in full, unfold carrier types, return a "Contradictions" section). It
    contains **zero** instructions for the **lead** on how to author the brief itself, or
    that the lead's own claims in it must trace to a measured read rather than memory.
  - `.claude/plugins/skeft-qa/skills/paper-authoring/SKILL.md` — read in full. "Before
    writing a section" (its only pre-writing checklist) is addressed to whoever drafts, not
    to a brief-authoring step; no section is titled or scoped to brief construction.
  - `docs/BUNDLE_LIFT_PROCEDURE.md` §7 ("Paper-draft authoring") — read in full; the only
    other "brief" mentions in the whole file are `review_runner.py --prep-brief` (Stage 13's
    *adversarial-review* brief, a different artifact) and one generic use of the adjective
    "briefed." Command: `grep -n -i "brief" docs/BUNDLE_LIFT_PROCEDURE.md` → 2 hits, neither
    is a brief-content spec.
  - `docs/WAVE_EXECUTION_PIPELINE.md` Stage 10 section (lines 384-424, read in full): "Draft
    either in-context or by dispatching `skeft-qa:paper-drafter`, one agent per disjoint
    section, each with a brief. The lead owns the outline, the argument's spine and
    integration." No further specification of the brief's required contents or provenance.
  - `.claude/plugins/skeft-qa/agents/` (`ls`) has no `redraft-lead.md` or equivalent; the
    lead role is the ambient session, governed only by the files above. There is no agent or
    skill whose job is "author a Stage-10 brief."
  - The four unloaded commits were read in full (`git show --stat` + full diff review) and
    none of them adds a lead-side brief-authoring spec. `e9e5e314` adds substrate-timeline
    and carrier-type-unfolding guidance to all four **paper agents** (drafter, prose-,
    claims-, adversarial-reviewer) — still drafter/reviewer-side, not a brief template for
    the lead.

- **Population:** Every one of the 13 dispatched bundles' Stage-10 findings files shows the
  brief's substrate (the bundle's `bundle_metadata.json` apex/claims list, or its charter)
  contradicted by a measured re-read. Command run:
  `for d in papers/AutomatedReviews/2026-08-1[57]-*-stage10-redraft; do f=$(find "$d" -maxdepth 1 -iname "*.md"|head -1); grep -icE "metadata (claims|says|asserts)|apex.*claims.*does not|charter (says|is wrong|still)|bundle_metadata" "$f"; done`
  → D1:14, D2:6, D3:5, D4:11, D6:13, D8:11, E1:1, E2:1, L2:15, L3:9, D10:5, D7:3, D9:11 — **13
  of 13 bundles, zero at 0.** This is the metadata/charter substrate the brief is built from
  (`paper-drafter.md` §"Read first" item 3 names `bundle_metadata.json` as "the contract");
  every bundle's own filed findings show that substrate was wrong when the drafter actually
  read the Lean declarations and primary sources. This supersedes wave 1's per-slot counts
  (C-06's "3", G-02's "6/10") — those undercounted because they were read off the transcript
  narrative, not measured against the filed artifacts.

- **Already-addressed by:** no. Confirmed absent from all governing files at HEAD, including
  the four unloaded commits.

- **Mechanism:** The pipeline has a strong, durable, *downstream* catch — `paper-drafter.md`
  has required "sources read in full," "claims you could not ground," and "**Contradictions**
  between your brief and what the sources actually say" as mandatory report fields since the
  agent's creation (`91807779`, 2026-08-10), unaffected by the plugin-cache staleness. That
  is why every bundle's drafter caught its own brief's errors — the safety net works. What is
  missing is the *upstream* half: nothing tells the lead, before dispatch, to ground the
  brief in a measured read of `lean_deps.json` / primary sources rather than in memory of
  `bundle_metadata.json`, prior drafts, or an earlier bundle's resolved state. The system
  therefore relies entirely on the drafter refuting a wrong brief after the fact, every time,
  rather than preventing the wrong brief from being dispatched.

- **Recurs on next bundle?** YES. The gap is structural — no file anywhere assigns the lead an
  obligation or a checklist for brief construction — and nothing in this window's four
  unloaded commits closes it. The next bundle's brief will again be lead-authored from
  memory/prior documents with the same downstream-only correction path.

---

### BRIEF-2-01 — "Assemble incrementally" is real, was NOT missing on Aug-17, but has no durable home and survives only by the lead hand-retyping it into every fresh brief

- **Wave-1 source IDs:** G-05, G-08 (H-01's incrementally-adjacent framing addressed
  separately in BRIEF-2-02)

- **Verdict:** RE-DIAGNOSED

- **Evidence at HEAD:** `grep -rln "assemble incrementally\|runway on analysis\|zero manuscript\|zero prose" .` (excluding `.lake/`) returns hits only in this audit's own wave-1 report
  (`docs/audits/2026-08-17-process-review/wave1/G.md`) and three unrelated false positives
  (`ACCURACY_LEDGER.md`, `ADR-012...md`, `QA_QI_INFRASTRUCTURE_MAP.md` — checked, all are
  a different "zero manuscript" phrase, not this rule). `paper-drafter.md`,
  `paper-authoring/SKILL.md`, and `BUNDLE_LIFT_PROCEDURE.md` were each read in full: the
  instruction is in none of them. **The claim that it is undocumented in any durable
  artifact is TRUE.**

  But the specific wave-1 narrative — that the Aug-17 redrafts (D9, D10, D7) "re-derived"
  this discipline because it was missing from their brief — is **false**. The per-bundle
  redraft-lead transcripts (`.../audit/sub/*.md`) were grepped for the literal instruction:
  `grep -ic "assemble incrementally\|RULE THAT OVERRIDES" <file>` for all 16 sub-transcripts.
  It is present, verbatim as "## THE RULE THAT OVERRIDES EVERYTHING ELSE: assemble
  incrementally," in the briefs actually dispatched for **D9** (`ab4fadc1...md:16`), **D10**
  (`a186bc62...md:16`), and **D7** (`adecf367...md:16`) — i.e. all three Aug-17 bundles had
  it, word for word, before drafting started.

  Mapping the same grep across all 13 bundles' brief transcripts: **present** for D1, D4, D6,
  D8, E1, E2 (Aug 15, matching G-05's list) **and** D9, D10, D7 (Aug 17) — 9 of 13. **Absent**
  for D2, D3, L2, L3 — the four bundles that predate the lesson (D3/L3 are literally the
  "two prior leads" the rule's own text cites as its origin).

  Wording differs slightly release to release (D9/D10 read "Never accumulate and integrate at
  the end"; D7 reads "Never accumulate sections and integrate at the end... Get a skeleton in
  early, then fill it" — an extra clause). Byte-identical text would indicate a shared
  template file; this variation indicates the lead is re-composing it from memory/notes each
  time, not pulling it from one canonical source (there is no such source, confirmed above).

  G-08's companion rule ("every bundle restarts at prose") shows the same propagation
  pattern and its failure mode: `grep -ln "restarts at prose" .../audit/sub/*.md` hits E2,
  D10, D6, D9, D7, D8 — hand-copied the same way. D9's own transcript (`ab4fadc1...md:228`)
  flags that this copied rule was **wrong for D9**: *"The brief's framing that 'every bundle
  restarts at prose' does not fit D9 ... Had I taken the brief's framing at face value I
  would have spent the runway on style."* A hand-copied lesson from one bundle's shape was
  carried into a bundle it did not fit, and only the drafter's own read caught the mismatch.

- **Population:** 9 of 13 bundles carry the instruction (measured above); 4 of 13 (D2, D3,
  L2, L3) predate it. 0 of 13 briefs pull it from a shared file, because no shared file
  exists.

- **Already-addressed by:** no.

- **Mechanism:** A real, hard-won process lesson exists and — this time — propagated
  correctly for 9 straight bundles across a two-day gap and a plugin-cache staleness window,
  entirely because the lead retyped it into each new dispatch from memory of the prior
  session. Nothing anchors it to `paper-drafter.md`, `paper-authoring/SKILL.md`, or
  `BUNDLE_LIFT_PROCEDURE.md`, so there is no mechanism that would catch its omission the way
  `paper-drafter.md`'s "Contradictions" requirement is caught (that one is enforced because
  it is a **report field the agent definition demands back**; "assemble incrementally" is
  advice with no corresponding enforcement point). The rule also travels un-versioned:
  because it is retyped, not templated, a future retyping can drop a clause, apply it
  verbatim to a bundle it does not fit (as D9 shows), or simply not get typed at all if the
  lead session restarts without the transcript in context.

- **Recurs on next bundle?** YES, as a latent risk rather than a demonstrated failure — it
  worked 9/9 times it was tried in this window, but the channel is the lead's session memory,
  which is exactly the channel this audit's own trigger condition (a fresh /goal session,
  compaction, or new lead) removes.

---

### BRIEF-2-02 — Substrate-staleness and statement-reading-discipline gaps (E-6, H-01) are ALREADY-ADDRESSED at HEAD, just not during the observed window

- **Wave-1 source IDs:** E-6, H-01

- **Verdict:** ALREADY-ADDRESSED

- **Evidence at HEAD:** `git show --stat e9e5e314` shows this commit (2026-08-15 16:24:24,
  one of the four never-loaded commits) added, to all four paper agents
  (`paper-drafter.md`, `prose-reviewer.md`, `claims-reviewer.md`,
  `adversarial-reviewer.md`): a mandatory step to consult the phase roadmap, the derived
  proof atlas, the module's git history, and near-neighbor declarations before citing a
  theorem as backing (closing E-6's "papers predate substrate, brief doesn't account for
  staleness"), plus the four-level carrier-type-unfolding check and the explicit warning that
  `lean_local_search` returns empty for declarations that exist (closing H-01's "verification
  discipline regresses" / "D10 redraft ... re-learning that `lean_local_search` returns
  empty" pattern). At HEAD, `.claude/plugins/skeft-qa/agents/paper-drafter.md:117-186`
  carries this content in full (read directly).

  Causal trace for E-6: the spine line E.md cites (`main-2026-08-15.md:26192`, user message
  *"let's make sure our prompts to the subagents... should be checking relevant roadmaps and
  context and git history — since these papers were originally drafted before we did
  significant substrate work"*) is the direct order that produced `e9e5e314`'s commit message
  *"Teach the paper agents that the substrate has a TIMELINE."* The finding and the fix are
  the same event.

  Per the wave-2 brief's own rule, a defect fixed by one of the four unloaded commits is
  already addressed. It was not active for **any** bundle in the window (Aug 15 or Aug 17)
  because the loaded cache (`f33dc0a1`, 09:44:39) predates `e9e5e314` (16:24:24) by the whole
  window, so this is why D9/D10/D7 on Aug 17 still hit the same `lean_local_search`-empty and
  carrier-unfolding friction H-01 describes — the fix existed in git two days before D9/D10/D7
  ran, and simply was never loaded into their session.

- **Population:** Affects the substrate-recency-checking step for every future `paper-drafter`
  / `prose-reviewer` / `claims-reviewer` / `adversarial-reviewer` dispatch, all bundles,
  going forward — contingent on the plugin cache being refreshed (a documented, known
  operational step; CLAUDE.md references "refresh the plugin cache after edits").

- **Already-addressed by:** `e9e5e314` (2026-08-15 16:24:24).

- **Mechanism:** Unlike BRIEF-2-01's instruction, this fix landed where it belongs — in the
  governing agent definitions themselves, not in ephemeral brief prose — so once the plugin
  cache is refreshed it applies uniformly to every future dispatch with no retyping required.

- **Recurs on next bundle?** NO, provided the plugin cache is refreshed before the next
  dispatch (session-start plugin refresh is a separate, already-documented operational step,
  outside this cluster's scope).

---

## Compact table

| ID | Verdict | Population | Recurs |
|---|---|---|---|
| BRIEF-1-01 | CONFIRMED | 13/13 bundles' findings show metadata/charter contradicted by substrate | YES |
| BRIEF-2-01 | RE-DIAGNOSED | 9/13 bundles carry the instruction (hand-copied, no template); 4/13 predate it | YES (latent) |
| BRIEF-2-02 | ALREADY-ADDRESSED | all future paper-agent dispatches, once cache refreshed | NO |
