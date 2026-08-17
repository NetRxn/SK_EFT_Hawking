# Process review — 2026-08-17

**Window:** t0 = 2026-08-15 09:46 CDT (the session process bound to plugin cache `f33dc0a1b2e5`)
→ HEAD `4c81c2ec`. The plugin was refreshed to `4c81c2ec2d04` and the session restarted at the end of
this review; the delta is now zero.

**Scope:** the machine that produces the papers — plugin, harness, gates, orchestration, brief and
review process. Not the manuscripts' physics.

**Method.** Wave 1: eight haiku readers over a process spine extracted from the session transcript
and the redraft-lead subagent transcripts — 89 raw findings. Wave 2: four sonnet agents re-checking
every escalated finding **against the repository**, instructed to prefer killing to keeping. Wave 3:
lead-direct verification plus three targeted root-cause investigations.

Reports: `wave1/{A..H}.md` · `wave2/{BRIEF,GATE,SOURCE,ORCH,PLUGIN}.md` ·
`wave3/{WORKTREE,GATE7,NOTEBOOK-AND-AGEING}.md`.

---

## The finding

**A predicate is written against a proxy for what it means, and the proxy is wrong for part of the
population.** Four independent instances, four subsystems, all live in one window:

| subsystem | the predicate asserts | what it means to assert | who it is wrong for |
|---|---|---|---|
| `scripts/egress_policy.py:110` | is `harness_web_egress_guard.py` uncommitted? | is any plugin source uncommitted? | every non-egress plugin edit |
| `scripts/readiness_gates.py:693` | is there a `SUPPORTS` edge? | is this claim backed? | all 64 papers — no emitter exists |
| `scripts/validation/checks/citations.py:669` | is the extension `abstract.txt`? | does the cache hold body text? | 82 entries cached as `.json` |
| `notebook_lib._resolve_repo_relative` | is the directory absent? | is the notebook absent? | every partially-tracked loop dir |

The repo already names this class — "assert the decider, not the proxy" — and closed an instance of
it in the worker shell guard on 2026-08-15 (`c4b1a1ca`). It was not generalised. The cheapest durable
countermeasure is a review question in the `architecture-change` skill, not a new gate: *what does
this predicate actually assert, and is that the thing you mean?*

**The second-order finding is why these survive.** ADR-004, ADR-007 and ADR-016 each treat
**"disclosed" as a terminal compliant state** — the sanctioned escape valve from their ratchets —
never a staged state with a clock. Disclosure is not merely un-aged; it is the way to comply, so
every ratchet in the system rewards reaching it and none rewards leaving it. That is item 9, and it
is the mechanism behind items 7 and 8 both being registered, documented, and unfixed.

---

## 1. The plugin-sync mechanism exists, correctly built, namespaced to one domain

**Verdict:** CONFIRMED, root cause revised · **Detail:** [`wave2/PLUGIN.md`](wave2/PLUGIN.md)

A session binds `--plugin-dir` at process start and cannot rebind. During the window the bound cache
was `f33dc0a1b2e5` while HEAD advanced four commits. Six files differed; **four were the paper agents
that executed all thirteen Stage-10 redrafts**, and the missing blocks targeted defects wave 1
measured as recurring — `paper-drafter`'s substrate-timeline section (6/10 bundles),
`adversarial-reviewer`'s manuscript-older-than-substrate section (10/10), `claims-reviewer`'s
"Class SB — superseded backing", an entire detection class. The worker guard ran its evadable
predicate all window.

**`scripts/egress_policy.py` already implements the fix.** `cmd_sync` discovers every install record
from `installed_plugins.json`, runs `claude plugin marketplace update`, refreshes each record, reports
failures, and prints the restart notice. `_install_records()`, `_live_sha()` and `cmd_status` are
fully generic. It is repo-side, so it is immune to the staleness it manages. Its docstring already
records this exact incident and the trap that matters most:

> A RESTART DOES NOT REFRESH — the cache is keyed by the committed HEAD SHA and only
> `claude plugin update` moves it.

Two gaps, both narrow. It is *named for egress*, so nothing invokes it when a paper agent changes.
And its dirty check is the proxy defect above: one file standing in for the plugin source, so an
uncommitted `paper-drafter.md` edit is silently skipped by the guard that exists to prevent exactly
that.

**Remediation — promote, do not add beside** (architecture rule 1; a promotion deletes the original
in the same commit). Lift the plugin-lifecycle half into a repo-side surface with `status` / `sync` /
`delta`; widen the dirty check from one file to the whole `.claude/plugins/skeft-qa/` tree;
`egress_policy.py` keeps `add`/`_covered` and delegates the rest.

`delta` is what closes the mid-flight loop. Mid-flight auto-improvement is a *feature* — a long
`/goal` run cannot restart — so the delta must be reachable without one. It computes bound-SHA vs
HEAD-SHA on every invocation, renders the current authoritative text of each changed agent or skill
(the rule, not a diff — the Voice standard) to a stable absolute path in the main checkout, and emits
nothing when the SHAs match. **Derived, never maintained**, so it cannot go stale and a cache refresh
empties it as a side effect — the same guarantee `atlas_view.json` already carries. The dispatch brief
then carries the amendment pointer only when there is something to point at.

⚠️ Hooks bind at start and execute outside any prompt, so a stale guard stays stale until restart.
The amendment doc must say so rather than imply full coverage.

---

## 2. Worktrees accumulate because no teardown path was ever shipped

**Verdict:** CONFIRMED — **ongoing, not a one-off** · **Detail:** [`wave3/WORKTREE.md`](wave3/WORKTREE.md)

31 linked worktrees, **217 GB**. Creation spans **9 distinct dates over 61 days** (2026-06-17 →
2026-08-17), and **5 were created today** — two days after the Saturday usage-limit stop. The
one-off hypothesis is falsified by the timeline.

**Root cause.** Every ad-hoc worktree is created by a lead typing `git worktree add` inline for a
one-off fan-out, and **no script, hook, skill or doc anywhere in the repo or plugin ever calls
`git worktree remove`** — an exhaustive grep returns zero hits. The one population that *does* have a
lifecycle (`wt1`–`wt3`, via `slotctl`) is deliberately designed never to be torn down, so the only
worked example in the system teaches permanence, and the pattern generalised wrongly to the 28
worktrees that should be ephemeral.

**Safe to remove: 25 of 31** — all 13 `redraft-*`, both `subst-*`, `kzm`, `mathlib-bump`,
`mlx-hikappa`, the workspace-level `.feature-worktrees/SK_EFT_Hawking`, and all six `rv*`. Each is
merged into `main` with zero commits ahead; every uncommitted diff found is regenerated gate or
dependency cache, not authored work. **≈146 GB reclaimable**, dominated by `lean/.lake` build trees
(`.git` is ~4 KB per worktree — the object store is shared).

**Keep six:** `wt1`/`wt2`/`wt3` (managed slots; `slotctl` forbids deletion), `docs` (**11 unmerged
commits — real work**, the community-overhaul branch), and `py1`/`py2` (merged and clean but
referenced as an active external Codex resource — confirm before removing).

The cost is not only disk. Each worktree is a full tree copy, so every repo-wide grep counts hits
~18× over: this audit's phantom-reference count read **167 raw, 9 real**. Debris is corrupting
measurement inside an audit about corrupted measurement.

**Remediation.** A vacuum with a decider, not a schedule: remove a linked worktree whose branch is
merged into `main`, has zero commits ahead, and holds no unignored authored diff — with the managed
slots excluded by name. Belongs beside `reset_slot.py` in the same lifecycle surface, and wants a
`--dry-run` first pass given the 25-item blast radius.

---

## 3. A CrossRef metadata stub counts as a held primary source

**Verdict:** CONFIRMED · **Detail:** [`wave2/SOURCE.md`](wave2/SOURCE.md) SOURCE-1

`citations.py:565` — `EXTENSIONS = ["pdf", "tex", "abstract.txt", "json"]`. Existence in any of the
four marks the entry `cached`. ADR-014 D1 already recognised that presence is not fidelity and added a
discriminator at line 669:

```python
if ext == "abstract.txt":
    abstract_only.append((bibkey, sorted(usage[bibkey])))
```

It names one extension by spelling rather than asserting the decider, so `json` gets no branch and a
CrossRef metadata record is indistinguishable from a full PDF downstream.

Measured: **82 of 664 registry entries resolve via `.json`; 0 of 111 sampled `.json` caches contain
body text; 45 are cited live across 15 of the 21 submission bundles.**

**Remediation.** Classify a cache by whether it holds body text, not by its extension. 82 entries move
to a weaker state and the check goes red — debt becoming visible — so it lands with a ceiling entry in
`docs/required_open_ceilings.json` in the same commit. Also touches ADR-014, whose D1 decision text
describes the narrower fix.

---

## 4. Bundle staleness is enforced at submission, never at merge — and submission has not been run

**Verdict:** RE-DIAGNOSED — a deliberate stage assignment with an undeliberate consequence
**Detail:** [`wave2/GATE.md`](wave2/GATE.md) GATE-4

`gate_precheck.py:82` wires `"submission": ["__strict__"]`, and its comment explains the design:
`--strict` is a correct submission-time mode and what was missing was a caller.
`grep -n strict scripts/verify_scope.py` → **no hits** — the merge gate CLAUDE.md names as the actual
pre-landing check never runs it.

Measured: **68 sub-findings, 0 FAIL / 68 WARN / 0 PASS — all 20 bundles carry at least one stale
dimension now.** Under `--strict` all 68 become FAIL.

The gate is not mis-staged. The campaign is close enough to submission that a 68-item debt discovered
*at* the gate has no runway. **Remediation: run `gate_precheck.py submission` early, not move the
gate.** Six strict-only legs fire, so expect findings beyond freshness; they route through
`close_finding.py` as normal.

---

## 5. The Stage-10 dispatch brief has no contract

**Verdict:** CONFIRMED · **Detail:** [`wave2/BRIEF.md`](wave2/BRIEF.md)

Wave 2 read `paper-drafter.md`, the paper-authoring skill, `BUNDLE_LIFT_PROCEDURE.md` and
`WAVE_EXECUTION_PIPELINE.md` in full. **No artifact specifies what a Stage-10 dispatch brief must
contain or where its claims must come from.** It is composed fresh, from memory, each time.

**The detection works; the prevention does not exist.** `paper-drafter.md:64` enumerates what a brief
carries, `:80` ranks a rule above it, and `:217` instructs the agent to report *"contradictions
between your brief and what the sources actually say."* `WAVE_EXECUTION_PIPELINE.md:412-423` governs
the dispatch and likewise ranks a reading rule above the brief. Every brief defect is therefore caught
**downstream**, after an agent has read sources and formed prose, at full dispatch cost — because
nothing exists on the author's side to prevent it at near-zero cost.

**Piloted 2026-08-17 against the real D9 dispatch brief.** A de-facto contract exists and is strong —
worktree and branch, why the redraft exists, settled bundle context, the assemble-incrementally rule,
a seven-point verification discipline, an explicit *"REQUIRED: report contradictions between this
brief and the sources"*, the findings format, git discipline. It is retyped per dispatch and written
down nowhere.

So the defect is not that instructions go missing. It is that the contract **cannot improve
cumulatively**: a lesson learned on one bundle reaches the next only if the lead re-types it, and a
rule shaped for one bundle gets copied to another whose shape differs.

**What is measurably wrong is the unsourced factual claim.** That same brief asserts *"D9's
manuscript contains fifteen `\texttt` spans in total, so the audit's 169 references cannot be
prose."* No origin given. The receiving agent measured it and refuted it, and its filed finding
records the measurement — `papers/AutomatedReviews/2026-08-17-d9-stage10-redraft/D9.md` §3: fifteen
literal `\texttt` spans, 196 `\lean{}` spans over 176 distinct declaration names, because `\lean` is
`\texttt{#1}` in the preamble. The prose population is 176, and the token-scan trap that produced the
error is warned against two paragraphs above it in the same brief. Requiring each brief claim to name
its origin catches that while writing, free, rather than mid-dispatch, at full cost.

⚠️ **Three earlier revisions of this section were wrong, and the sequence is the finding.** The first
claimed *13 of 13 bundles filed a brief contradiction* — conflating wave 2's result (13/13 show
**metadata or charter** contradicted by substrate) with a claim about the **brief**. The second
claimed *5 of 13 carry a CONTRADICTIONS section, none of them from Aug-17*; the adversarial pass
showed both halves false — zero of thirteen findings files contain the string, the five traced to
`contradicts` matching inside ordinary physics findings, and D9, counted as carrying none, contains
*"See the contradictions section of my report."* The third located the section in the **findings
file** when the brief requires it in the **report-back**.

Each correction came from checking a different artifact, and the corrected claim is now about a
mechanism rather than a count — which is what the population figures kept failing to measure.

**Remediation.** A brief contract naming the required sections and, per claim class, the artifact its
claims must be read from — substrate → `lean_deps.json`; recency → the phase roadmap and module git
log; sources → the citation registry's *held* state. It carries the item-1 amendment pointer when a
delta exists, and absolute notebook paths by construction (item 8's residue). Placement is the open
question this audit did not settle: the plugin's `paper-authoring` skill governs *how to write*, while
`BUNDLE_LIFT_PROCEDURE.md` governs *the lift*. Decide the owner before writing, per architecture
rule 1 — do not add a third home.

---

## 6. Nine durable citations point at a file that exists only in private memory

**Verdict:** CONFIRMED · **Detail:** [`wave2/ORCH.md`](wave2/ORCH.md) ORCH-4

`reference-measurement-traps-false-absence` is cited as an authority at nine sites on `main`,
including two live production files — `scripts/dashboard_flow.py:301` and
`scripts/validation/checks/bundles_readiness.py:1045,1136`.

It exists only at
`~/.claude/projects/-Users-…/memory/reference-measurement-traps-false-absence.md` — the lead's private
cross-session memory. No subagent, no fresh context and no human reading the repository can follow it.

**Remediation.** Promote the note into a repo reference beside `SETTLED_FORKS.md` and re-point the
nine citations. Add the `lean_local_search` false-absence warning to `lean-worker.md` in the same
change — it is the highest-volume Lean-search agent and the only one of four missing it.

---

## 7. Gate 7 reads an orphaned stub; the layer that supersedes it already ships

**Verdict:** RE-DIAGNOSED — far cheaper than first priced · **Detail:** [`wave3/GATE7.md`](wave3/GATE7.md)

`grep -c SUPPORTS scripts/build_graph.py` → **0**. Papers with ≥1 `ProseClaim` tagged `interesting`
and no `SUPPORTS` edge are `blocked` permanently (**6 of 64**: D10, D5, D8, paper10 ×2, paper12,
paper6); papers with none `pass` vacuously (**58 of 64**).

**The resolver already exists and is already wired.** `claims-reviewer` — a plugin agent — writes
`papers/<bundle>/claims_review.json`, a per-sentence chain-of-backing verdict, and
`build_graph.py:3011-3245` (Phase 5v Wave 10b) already ingests it as `Sentence` nodes and `BACKED_BY`
edges into Formula / LeanTheorem / Parameter. **All six blocked papers already have that file on
disk.** Spot-check of `paper6_vestigial`: abstract sentences resolve to real theorems
(`SKEFTHawking.SO4Weingarten` among them), and the "Monte Carlo evidence" sentence the Wave-4 roadmap
named as Gate 7's motivating example is independently flagged unbacked by that same layer.

`ProseClaim`/`SUPPORTS` was declared in Wave 2a/2b (2026-04-15), never assigned an owning wiring wave,
and shipped as a disclosed defect. A richer layer superseded it; the gate never moved.

**Second defect, and the reason the blocked set looks arbitrary:** `interesting` is a **five-regex
lexical heuristic** in `build_graph.py` over abstract sentences — 7 live matches. Six papers are
blocked by a tag no author chose, produced by surface word-matching that `claims-reviewer`'s
per-sentence verdict already supersedes.

**Remediation — two changes, and only the first is scoped wiring.**

**A. Re-point Gate 7's backing query** from `SUPPORTS` to `BACKED_BY`. Touches
`readiness_gates.py:678-733`, `tests/test_readiness_gate_evaluators.py`, `docs/READINESS_GATES.md`,
`VALIDATION_GATE_TOPOLOGY.md`, the disclosure entry in `graph_atlas.py:480` (3 dead edges → 2), the
hard-coded list in `tests/test_architecture_inventory.py:58`, and the derived census in
`SURFACE_INVENTORY.md:157,159` (regenerated, not hand-edited). Unblocks D10 and D8, both already
redrafted.

**B. Retire `ProseClaim` as a node type — do NOT bundle this.** Measured at HEAD, the node is
load-bearing beyond Gate 7: `verification_state.py:86,144,166` carries it in the artifact-type list
and propagates verification state into it; `last_modified.py:53` routes `GROUNDED_IN`
(ProseClaim/Sentence → Formula); `provenance_dashboard.py:1516` documents that propagation.
Retirement additionally touches `build_graph.py`, `graph_atlas.py`, `tests/test_build_graph.py`,
`KNOWLEDGE_GRAPH.md`, `END_TO_END_MAP.md`, and the 26-node-type census. `Sentence` and `ProseClaim`
are not the same granularity, so B is a schema migration, not a deletion.

⚠️ **The decision A hides.** `claims_review.json` exists for **49 of 64 papers**; 15 have none. All
six currently-blocked papers have one. So A changes the gate's *population*: the 15 unreviewed papers
move from vacuous pass to whatever A decides — block (defensible: a paper with no claims review has
no narrative grounding) or pass (reproduces the vacuity in a new costume). That is a product
decision and must be made explicitly, not inherited from the wiring.

A second decision rides along: `claims-reviewer` emits its own per-sentence verdicts
(PASS/FAIL/WARN/UNGROUNDED/TRANSITION), so the gate could key on UNGROUNDED rather than on the
five-regex `interesting` tag. That is cleaner and retires the regex tagger, but it changes *what
Gate 7 asserts* — also a decision, not wiring.

Check separately whether `PRODUCES` or `CONTRADICTS` have superseding layers (item 9).

---

## 8. Notebook blindness is still live, and the fallback that exists for it is proxy-keyed

**Verdict:** CONFIRMED STILL-LIVE · **Detail:** [`wave3/NOTEBOOK-AND-AGEING.md`](wave3/NOTEBOOK-AND-AGEING.md)

`.gitignore:125` (`**/LAB_NOTEBOOK*.md`) unchanged. `88e2f434` filed the MAJOR; `73c04a8d` and
`825e88fd` documented a manual absolute-path workaround — no behaviour change. Nothing else landed
since 2026-08-14, checked by keyword and by path. The finding's **own declared `Verify:` command**
still exits 1, and it carries zero closure-ledger records, so by the repo's own instrument it is OPEN.

**Root cause, reproduced live from `.claude/worktrees/wt1`.** `notebook check docs/dev-loops/Phase6BC`
falsely reports "no LAB_NOTEBOOK_INDEX.md" because `notebook_lib._resolve_repo_relative` fires its
repo-root fallback **only when the path is entirely absent from the worktree**. The loop directory is
partially tracked, so the directory exists, so the fallback never triggers for the normal
directory-based invocation.

The fallback built for this case is keyed on *directory missing* as a proxy for *notebook missing*.

**Remediation.** Fix the resolver: fall back per-file on the notebook itself, not on the containing
directory. A few lines in `notebook_lib.py` plus a test that runs from a worktree. **Do not change
`.gitignore`** — notebooks are ignored deliberately, to keep private content out of public git. This
fixes the tool rather than routing around it, and demotes the brief-side absolute-path rule from a
requirement to a belt-and-braces.

---

## 9. "Disclosed" is a terminal compliant state

**Verdict:** NOT COVERED by any existing ADR · **Detail:** [`wave3/NOTEBOOK-AND-AGEING.md`](wave3/NOTEBOOK-AND-AGEING.md)

ADR-012's lifecycle governs only already-minted `ReviewFinding` nodes; its extractor parses reviewer
markdown and never reads `constants.py` registries, check docstrings or `SETTLED_FORKS.md`.
`close_finding.py` and `graph_atlas.py` contain no path that reads a disclosure and schedules or
escalates anything. The dashboard's only age field times operator-question latency, not disclosure
staleness.

ADR-004, ADR-007 and ADR-016 each treat disclosure as the **escape valve from their own ratchets** —
the sanctioned way to comply. So disclosure is an absorbing state by construction, not by neglect.

Concrete: `GATE_EDGE_TYPES_WITHOUT_EMITTERS` has disclosed **three** dead gate edges — `PRODUCES`,
`SUPPORTS`, `CONTRADICTS` — since at least 2026-08-06. Its ratchet blocks a fourth and flags a
disclosure that becomes factually wrong. It never forces the existing three closed. Item 7 is one of
the three; nothing would ever have surfaced it.

**Remediation.** Deliberately unscoped — this is ADR-shaped and should be designed through the
`architecture-change` skill. The design question is narrow enough to state: a disclosure needs an
owner and a review date, and the ratchet that accepts it should require both. Do it last; items 1–8
are its instances and each is independently worth shipping.

---

## Killed on verification

The audit's value depends on it killing things.

| claim | wave-1 IDs | why it died |
|---|---|---|
| Ratchet ceilings frozen at 232 vs live population 6; gate unfireable | A-04 | Real at 15:22 Sat; fixed same day by `7a63e17f` and `d9f2f49a`. Remeasured, the ratchet is RED in the *opposite* direction — population grew past the freeze because primary-source re-reading found new blockers. Firing as designed. |
| `bundle_lean_module_coverage` punishes a legitimate module drop with no escape | G-10 | Fixed by `d8c3b858` in-window; escape path already used by 3 bundles. |
| A D7 prose-review subagent's output was lost, ~45 min wasted | H-08 | The agent completed. As a nested spawnDepth-2 background dispatch its notification routed to the top-level session, not to the subagent that spawned it. Output was on disk throughout. The real defect is notification routing. |
| "Assemble incrementally" was missing from the Aug-17 briefs | G-05 | Present verbatim in the D9/D10/D7 sub-transcripts. Re-diagnosed into item 5: it survives by hand-retyping. |
| `apex_theorem_claims_grounded` fails to verify claim semantics | D-03, G-07 | The check's own docstring scopes this out explicitly and names the residue. An instance of item 9, not a hidden defect. |
| Worktree accumulation was fallout from the Saturday usage-limit stop | — | Falsified by the timeline: 9 creation dates over 61 days, 5 created today. Ongoing lifecycle gap. |
| Gate 7 needs a `SUPPORTS` extractor built | FINDINGS item 7, first pass | The superseding layer (`Sentence`/`BACKED_BY`) already ships and already covers all six blocked papers. The fix is re-pointing, not construction. |
