# Live-Anchor Redesign — combined spec (Moves 1 + 2 + 3, one update)

**Status:** DRAFT for review (no code yet). **Author:** harvest-host analysis, 2026-06-24.
**Motivation:** the System-2 finding `compaction-summary-quality` (tally 23, ~20 recurrences)
is one mechanism: the loop's *positive structural state* (what's committed, the live sorry,
which forks are dead) is carried in **prose** (lab-notebook FRONTIER + compaction summary),
the prose drifts from the repo across every compaction, and the SessionStart re-injection then
feeds the drifted prose back as ground truth (`_frontier_for` → `extract_frontier`, asserted
"always current" — it is not). Result: re-derived `a3f217e1`, a false Aristotle request mooted
one turn later, summaries recommending superseded bridges, ~25-turn route re-discovery.

**Thesis.** Split *positive* state (compute live, never remember) from *negative/procedural*
state (carry in a small durable store). The repo IS the substrate; stop mirroring it in prose.

---

## Post-live finding (2026-06-24, v4 — the goal CONDITION is the strongest re-seed surface)

Observed during the first live PreCompact run on the L2 goal: the redesign hardened our injection
surfaces (removed the prose FRONTIER) but left the **native `/goal` condition** untouched — and it
is a *worse* re-seed vector than the FRONTIER was, on two counts: (1) native `/goal` re-states the
condition **every turn** (we ship no Stop hook; native `/goal` owns continuation), not just at
compaction; (2) we also pin it at the top of the SessionStart payload (≤4k, always-full). The L2
condition had baked **mutable tactical state** — `Close-path engines: kronecker_cap_eq_kronecker_rcap
(MatchLHS) + …` — and those engines were later BANNED/FALSE-POSITIVE in `SETTLED_FORKS.md`. So the
condition re-injected the dead route as "live state" every turn, **structurally out-ranking** the
lower SETTLED_FORKS / PRE_DECISIONS reads → a full ~49-commit session on the banned route before
catch-and-revert. The two adversarial reviews missed it because both audited *our* injection code,
not the native-`/goal` condition text feeding it.

**Fix (authoring discipline, not code):** the `/goal` condition must hold **DURABLE content only**
— success criteria, settled locks/non-negotiables, source-of-truth paths. **Mutable tactical state**
(current sorry, close-path engines, live/breakthrough lemma, commit SHAs, "next brick", progress
framing) is FORBIDDEN — it belongs in the live probe (`repo_state_probe.py`, recomputed each turn),
`SETTLED_FORKS.md`, and the notebook FRONTIER, which the condition POINTS at, never snapshots. A
route may be named only to BAN it (durable), never to PROMOTE it (mutable). This is the same
positive/negative split as Move 1, applied to the condition. Encoded in
`skills/goal-prompt/references/goal-prompt-authoring.md` (hard constraint + anti-pattern + the
per-line "true in 30 turns?" test) and summarized in `goal-prompt/SKILL.md`. **Existing goals with
baked tactical state should be scrubbed at next re-arm.**

## Implementation-review remediation (2026-06-24, v3 — fresh review of the BUILT code)

A second fresh-context adversarial pass reviewed the *implementation*; all 10 findings valid, all
remediated (125 plugin tests green):
- **BLOCKER B1** — the `atlas_view.py --write-boundary` flag the regen depended on **did not exist**
  (agent would fail, or run `--write` and dirty the tracked file). FIXED: added `--write-boundary`
  (writes the gitignored `.claude/dev-harness/atlas_view.boundary.json`) + embedded the EXACT
  macOS-portable single-flighted (`mkdir`-lock, not `flock`) regen command in the probe + FIRST_ACTION.
- **MAJOR M1** — `armed_ts` as a bare epoch made `git log --since=<int>` return ALL history (git
  ignores it). FIXED: emit `--since=@<epoch>`.
- **MAJOR M2** — `module_inventory` matched by module *tail* (`Basic`/`Predicates` collide across
  namespaces). FIXED: full dotted-module equality.
- **MAJOR M3** — the approved L2 `arm_sha` backfill was not applied. DONE: live marker now carries
  `mode=lean` + `arm_sha` (exact) + `armed_ts`.
- **m1** `_WRAPPER_RESERVE` 700→950 (covers the post-payload notes + HEAD anchor headroom);
  **m2** added a git-backed budget test exercising the anchor + atlas; **m3** exact regen command
  embedded; **m4** staleness demotion made reword-proof (exact-match on `frontier_stale_msg`, not a
  substring); **n1** launch-independence test now `chdir`s to a non-repo dir; **n2** stale "live
  FRONTIER" docstrings repointed to the HEAD anchor.
- Verified-correct by the review: hooks/probe never write a tracked path; RE_ANCHOR drift phrase
  gone; PreCompact is inert/synchronous/no-injection; Lean opt-in; leak-safe; launch-independent;
  the HEAD-anchor-in-shared-payload deviation (vs spec row D) judged **sound** (the guard redirect
  also benefits) and kept.

---

## Adversarial review corrections (2026-06-24, v2 — all findings validated against live code)

A fresh-context adversarial pass found 2 BLOCKER + 4 MAJOR + 5 MINOR + 2 NIT, all valid (the
three load-bearing claims were git-verified). Resolutions, applied in the sections below:

- **BLOCKER 1.2 — `lean/atlas_view.json` is git-TRACKED.** A hook writing it dirties the tree
  with a 4 MB diff every compaction. **Fix:** the boundary atlas regen writes a *gitignored*
  `.claude/dev-harness/atlas_view.boundary.json`; the probe prefers it when fresher. **New
  standing invariant (QI): a hook MUST NOT write a git-tracked path — harness artifacts live
  only under the gitignored `.claude/dev-harness/`.** (§E, §A.4)
  **Launch-independence (verified):** all artifacts land under `SK_EFT_Hawking/.claude/dev-harness/`
  regardless of launch point — the hooks anchor via `repo_root()`/`REPO_DIR_NAME` (resolves to
  SK_EFT_Hawking from the workspace parent OR inside the repo), and the repo scripts (`atlas_view.py`,
  `repo_state_probe.py`) anchor on `__file__` (`parent.parent == <repo>`), NOT on cwd. The probe's
  original cwd-`git rev-parse` resolution was a bug — it fails from the workspace parent (a
  deliberately-non-git dir) — now fixed to `__file__`-anchoring. The destination is gitignored
  (never committed/pushed) and, because `REPO_DIR_NAME` is this repo's own name, never the parent
  and never a private sibling repo (whose own harness projection writes its own dir).
- **BLOCKER 1.5 — RE_ANCHOR is NOT byte-identical-safe.** Its live text points at "the live
  LAB-NOTEBOOK FRONTIER below," which we remove. **Fix:** RE_ANCHOR joins the edited set (§C):
  repoint the cross-check at the live-anchor probe; delete the false "always current" phrasing.
- **MAJOR 1.6 — PreCompact capability unverified (and the harness deliberately omitted it).**
  Confirmed via claude-code-guide: PreCompact has a ~60s timeout, **cannot reliably inject
  context / steer the summary**, and **cannot safely fire-and-forget** a 134s child (reaping
  undocumented). **Fix (§E redesign):** the hook does ONLY fast synchronous work — write the
  snapshot artifact + a `regen_requested` flag (staging, per ruling #1). The heavy atlas regen
  EXECUTES later via the **agent's** reliable backgrounded Bash (post-compact FIRST_ACTION reads
  the flag), never from the hook. No context injection anywhere.
- **MAJOR 1.7 — ENFILE gate racy.** **Fix:** the deferred regen is lockfile single-flighted,
  count-gated (`pgrep -fc 'lake|lean-lsp-mcp' < N`), swallows ENFILE, and defaults to SKIP under
  any doubt (a stale atlas is already fail-soft). (§E)
- **MAJOR 1.10 — agent may skip the FIRST_ACTION probe → ZERO positive state (worse than today).**
  **Fix:** SessionStart injects a *minimal* git-computed anchor line (`HEAD=<sha8>` + active file
  from `git rev-parse`/`git log -1 --name-only`, ~60 chars, hook-cheap, no LSP) so the skip case
  still has a true anchor; the full unbounded probe stays the FIRST_ACTION. Still net-negative on
  budget. This is a pointer-grade fact, not script output — consistent with principle 1. (§C)
- **MAJOR 1.4 — `atlas['frontier']` is the open-HYPOTHESIS list, not sorry-bearing theorems.**
  **Fix:** §A.5 "open-sorry modules" = scan `atlas['nodes']` for `atlas_status ==
  'CONDITIONALLY_PROVED'`; the "frontier keystone" pointer (§A.7) = `atlas['frontier'][0]` (the
  most-gating open hypothesis). Distinct objects — disambiguated.
- **MAJOR→MINOR 1.12 — two-source completeness is conditional on atlas freshness.** **Fix:** §A.2
  softened: "complete *given a current atlas*; a stale atlas degrades prior-session coverage —
  widen the git rung / `git log` manually."
- **MINOR 1.3** — §A.4/A.5 require an explicit O(nodes) scan (no per-module index); stated.
- **MINOR 1.8** — the frontier-staleness warning lives in `notebook_lib._frontier_stale`/`op_check`,
  not `harness_reinject.notebook_note`; §D names the real edit site.
- **MINOR 1.9** — removed-size figure corrected to ~1780 chars (1600 `extract_frontier` cap + ~180
  label); conclusion (net-negative) unchanged.
- **MINOR 1.11 / NIT 1.13** — snapshot path is correctly gitignored; probe is local-only, output
  is injected context never egress (web-egress guard is the backstop). Stated.
- **NIT 1.14 / 1.1** — tests use SYNTHETIC goal_id/marker fixtures (not `20260617T231250`) and
  assert `payload_len < PAYLOAD_MAX_CHARS` (the symbol, not the literal 9300).

---

## Design principles (locked)

1. **The 10k SessionStart inject cap is sacred.** No script output, no git log, no exact-state
   text goes into the payload. The exact-state is a **command the agent runs** (progressive
   disclosure, identical to how `PRE_DECISIONS.md` is a *mandated read*, not an injection).
   Net effect on the payload: **shrinks** (we remove the prose frontier, add a ~2-line pointer).
2. **Coaching block is never touched.** Not dropped, not truncated, not reordered. It is the
   self-improvement mechanism. Same for the SETTLED GOAL (≤4k always-full) and RE_ANCHOR.
3. **Unbounded by construction.** A multi-day L2-scale session needs far more than a truncated
   "recent commits" list. Because the exact-state is *run by the agent*, its output is bounded
   only by the agent's own context, not the hook payload — so it can carry the full since-arm
   delta, the whole active-module engine inventory, etc.
4. **Programmatic, never grep.** Sorry detection uses the LSP diagnostic + the kernel
   `sorryAx`-closure, both comment-proof. Grep is banned (comments/docstrings/identifiers
   false-match — already a known burn).
5. **Git is a superset, framed honestly.** `git log <arm>..HEAD` includes parallel-session,
   manual, and (if present) other-goal commits. Framed as "repo delta since arm," scoped to
   `lean/` + active modules, never as authorship.
6. **Fail-open always.** Any probe/hook error degrades silently to today's behavior and never
   blocks the durability re-inject. Matches the existing harness law + 41-test discipline.
7. **Align to autocompact, never own it (ruling 2026-06-24).** Durable state survives compaction
   via two channels ONLY — **persistent artifacts** (files on disk the probe re-reads) and
   **Claude memory** (persists by design). We NEVER attempt to force content through the
   post-compact *context* / steer the summary (best case non-deterministic; worst case it fights
   CC's native autocompact, which we want to align to, not own). Context is allowed to be lossy;
   Move 1 recomputes the anchor from durable sources afterward.
8. **Two-layer scope gating — Lean behavior is opt-in, never assumed (ruling 2026-06-24).**
   - **Gate 1 (session/marker, existing):** the entire harness is inert for any session without a
     managed-goal marker (`read_marker → None`). A non-goal session — a chat, this harvest run —
     gets NONE of this. Verified: this session has no marker.
   - **Gate 2 (goal-mode, NEW):** within a managed goal, a marker `mode` field
     (`lean | general`, **default `general`**) gates the Lean-specific behavior. A goal can be
     non-Lean (e.g. "implement this harness update" is a goal *in this repo* but not a proof
     loop); assuming Lean for it is a detriment. **Mode-agnostic** (any goal): HEAD anchor, git
     delta, working-tree dirty/untracked surfacing, SETTLED_FORKS, PRE_DECISIONS, the snapshot
     artifact. **Lean-only** (`mode=lean`): the atlas engine inventory, the `lean_diagnostic_messages`
     FIRST_ACTION mandate, the ExtractDeps boundary regen + `regen_requested.flag`, the `-- lean/`
     git-delta path scope, the "Lean slots idle" check. Unknown/absent `mode` ⇒ `general` (safe:
     a mis-tagged Lean goal loses the extras but keeps a correct general anchor — far better than
     a general goal getting spurious Lean directives). This also generalizes the harness to a
     non-Lean sibling deployment for free.

---

## Unified change set (one PR)

| # | File | Change | Move |
|---|------|--------|------|
| A | `scripts/repo_state_probe.py` *(new)* | The live exact-state report (git + atlas + transcript-tail snapshot), run by the agent | 1 |
| B | goal-prompt skill + marker schema | Record `arm_sha` + (optional) `active_hint` at arm time | 1 |
| C | `harness_common.py` | Remove `_frontier_for` from payload; **edit `RE_ANCHOR`** (drop the dangling "FRONTIER below / always current", repoint to the live probe, 1.5); inject the minimal git HEAD anchor (1.10); add live-anchor + settled-forks + regen-trigger `FIRST_ACTION` lines; else byte-identical | 1, 2 |
| D | `notebook_lib.py` (+ `harness_reinject.py`) | Demote the frontier-staleness warning at its real source (`_frontier_stale`/`op_check`, 1.8); inject the §C HEAD anchor in `harness_reinject.main` | 1 |
| E | `harness_precompact.py` *(new hook)* + agent FIRST_ACTION | Hook (synchronous only): write the gitignored snapshot artifact + a `regen_requested` flag. Agent (post-compact): run the ENFILE-single-flighted boundary atlas regen to the **gitignored** `atlas_view.boundary.json` (NOT the tracked file, 1.2). No context injection (1.6) | 3, +memory |
| F | `docs/dev-loops/SETTLED_FORKS.md` *(new)* | Structured, commit-keyed dead/banned/superseded register; mandated-read | 2 |
| G | tests | Deterministic tests: probe shape + cascade + mode-gating; payload budget bound; tracked-path invariant; fail-soft sweep | all |
| H | `HARNESS_GUIDE.md` / `README.md` doc update | Document the live-anchor flow + the standing QI invariant (**a hook MUST NOT write a git-tracked path** — artifacts only under gitignored `.claude/dev-harness/`) + launch-independence | all |

---

## A. `repo_state_probe.py` — the live exact-state report

**Invocation:** `uv run python scripts/repo_state_probe.py` (auto-resolves the current session's
marker → `goal_id`, `arm_sha`, `notebook_path`; `--goal-id` / `--arm-sha` override for tests).
Run by the agent as a FIRST_ACTION; **not** by the hook (the hook can't reach the LSP, and we
don't want its output in the payload). Fast (~1s: git + a JSON read; no extraction).

**Output sections (plain text, unbounded, printed to stdout):**

1. **HEAD + arm anchor.** `HEAD=<sha> (<subject>)`; `armed-at=<arm_sha>` (the **per-session**
   anchor — HEAD when *this session* armed the goal, see §B) or a degraded line naming which
   cascade rung is in effect (§A.2a).
2. **Repo delta since arm — `git log --oneline <arm>..HEAD -- lean/`.** Framed verbatim:
   *"Commits to lean/ since this goal armed. SUPERSET — may include parallel-session, manual,
   or other-goal work; reconcile, do not assume authorship."* Full list (no truncation). A
   second sub-list scoped to the **active modules** (see §A.4) is highlighted as the likely
   working set.

   **Two-source split (the design's spine — git delta + atlas answer different questions):**
   the git delta is the **this-session** recent-work window (where the re-discovery tax bites —
   you keep re-deriving what you committed hours/a-day ago). **Prior sessions** of a multi-day
   goal are covered NOT by the git delta but by the **atlas inventory** (§A.4: "engines that
   exist in this module *right now, regardless of when committed*"). old work → atlas inventory;
   new work → git delta. **Completeness is conditional on atlas freshness (1.12):** prior-session
   work committed but not yet re-extracted into the atlas falls in neither bucket (before this
   session's anchor, absent from a stale atlas). The §E.2 boundary regen plugs this, but it is
   best-effort — when the atlas is stale, the agent widens the git rung (last-N / a manual
   `git log`) to recover the gap. This is why a per-session anchor (not a days-old per-goal
   origin) is correct — it bounds the delta to one session and never balloons to hundreds of
   long-internalized commits.

2a. **Degrade cascade for the "since-when" anchor** — each rung still delivers the core value
   (surface recently-committed engines so the loop doesn't re-derive them); only the precision
   of the window degrades, never blocking:
   - **`arm_sha` (exact)** → `git log <arm_sha>..HEAD -- lean/`.
   - **`armed_ts` / goal_id timestamp (approximate, same question)** → `git log --since=<ts> --
     lean/`, used when `arm_sha` is absent OR present-but-unresolvable (commit GC'd by a
     rebase/force-push → `git log` errors on the bad revision → fall through here).
   - **last-N (coarse)** → `git log -n 40 --oneline -- lean/` when no usable timestamp; loses the
     "since arm" boundary but last-N recent commits ARE the re-discovery-prone set.
   - **atlas-only (no git)** → drop the delta; rely on the atlas inventory (§A.4) + the live LSP
     sorry. No "when," still "what exists now."
   The printed line states which rung is active so freshness/precision is never silently implied.
3. **Working-tree state — `git status --porcelain`.** Dirty/untracked `*.lean` surfaced
   explicitly (directly fixes the `:70468642` "untracked scaffold diverged from summary"
   finding — the divergence becomes a stated fact to reconcile first).
4. **Active-module engine inventory.** For each active module, the committed theorems with atlas
   status: `PROVED·kernel-pure`, `CONDITIONALLY_PROVED` (rests on a sorry), or `AXIOM_TAINTED`.
   **Source (1.2):** prefer the gitignored `.claude/dev-harness/atlas_view.boundary.json` when it
   is fresher (mtime) than the tracked `lean/atlas_view.json`; else the tracked file. **Scan
   (1.3):** the atlas has no per-module index — iterate `atlas['nodes']`, filter
   `node['module'] ∈ active set`, read `atlas_status` + `kernel_pure` (~12 ms over ~14k nodes).
   Flagged `[atlas as of <mtime>]` so the agent knows the freshness (stale-tolerant, closure-true,
   comment-proof). *This is the "what engines exist right now" answer that kills the re-discovery
   tax — and (§A.2) the half that covers prior/cross-session committed work.*
5. **Open-sorry modules (project-wide).** The `CONDITIONALLY_PROVED` node set from the atlas —
   a broad "where are the open sorries" map. Authoritative *live* per-file sorry is the agent's
   separate `lean_diagnostic_messages` call (mandated in FIRST_ACTION) — stated in the output as
   the next step, so the two programmatic sources are explicit and neither is grep.
6. **Pre-loss snapshot (if present).** The last substantive assistant message captured by the
   PreCompact hook (§E) — the next-brick the summary may have dropped (fixes the null-summary
   `:34141867` finding). `snapshot as of <ts>, transcript hwm <offset>`.
7. **Pointers.** One line each: `SETTLED_FORKS.md` count + IDs, `PRE_DECISIONS.md`,
   the atlas frontier keystone. (Pointers, not contents.)

**Active-module detection (§A.4).** Goal-agnostic: the `lean/SKEFTHawking/*.lean` files most
frequently/recently touched in `git log --name-only <anchor>..HEAD` (the anchor = whichever
cascade rung §A.2a resolved), top ~3, `active_hint` (§B) as a tie-breaker. No goal-text parsing
(fragile). Degrades to "all modules with open sorries (from atlas)" if no anchor at all. The
atlas inventory itself is what carries **cross-session / prior-session** committed engines (the
git delta only sees this session) — so §A.4's inventory is complete regardless of the cascade rung.

**Multi-goal / parallel-commit semantics.** The probe resolves **the current session's** marker
only (never iterates all markers), so two simultaneous goals each see their own arm anchor and
active set. The git delta is honestly a repo superset (principle 5); scoping to active modules
is the noise filter, reconciliation is the agent's job — we surface, we do not over-claim.

**Fail-soft.** No marker → print a minimal `HEAD` + "unmanaged; no goal anchor" and exit 0.
git/atlas/snapshot each independently optional; any failure prints `(<section> unavailable)`
and continues. Never nonzero-exits in a way that blocks the loop.

---

## B. Marker schema delta + goal-prompt

Add fields at arm time (goal-prompt skill). **Semantic: per-session** — these are recorded into
*this session's* marker (markers are keyed by session_id), so `arm_sha` = HEAD when *this
session* armed the goal, NOT the goal's original-arm sha days ago. That is the intended behavior
(§A.2 two-source split: the git delta is this-session recent work; cross-session/older engines
are covered by the atlas inventory). A new session resuming the same `goal_id` gets a fresh
`arm_sha` at its own arm — correct, since it bounds the delta to that session's window. (Inheriting
the original-arm sha across sessions was considered and rejected: it balloons the delta to
hundreds of long-internalized commits.)

- `arm_sha`: `git rev-parse HEAD` at arm — the exact, rebase-safe "since arm" origin (rung 1).
- `armed_ts`: arm wall-clock (epoch) — the cascade's rung-2 fallback (`git log --since`) when
  `arm_sha` is absent or unresolvable. The `goal_id` timestamp is a secondary source for it.
- `mode`: `lean | general` (**default `general`** — principle 8). Set by the agent when it writes
  the marker, via a single bare skill line — *"if this is a Lean goal, set `mode: lean`, else
  `general`."* Deliberately NOT enumerating how to detect Lean: the agent composing the goal
  already knows; over-specifying criteria is the over-complication to avoid. Default + absent ⇒
  `general`. Drives the Lean-vs-general branch in the probe (§A) / hooks (§C/§E).
- `active_hint` *(optional)*: the primary file named in the goal text, if cheaply parseable, as
  a tie-breaker for §A.4. Never load-bearing.

Capture is best-effort: if `git rev-parse` fails at arm (git absent / corrupt `.git`), `arm_sha`
is simply omitted and the probe degrades down the cascade (§A.2a) — arming never blocks on it.

**Backfill for the live goal** (`20260617T231250`, armed before this field existed) —
**APPROVED as a one-time migration (ruling 2026-06-24):** hand-set `arm_sha` once into the live
marker (= the commit at goal-prompt-file creation, or the first commit at/after arm). The
graceful degrade (§A.1: `arm_sha=UNKNOWN` → last-N lean commits + atlas inventory) remains the
permanent fallback for any future pre-field marker, but is not relied on for the active goal.

---

## C. `harness_common.py` — payload changes (surgical)

`build_reorientation_payload`:
- **REMOVE** the `_frontier_for(marker)` block ([:479-484]) — the prose frontier is the proven
  drift vector. (`_frontier_for` / `notebook_lib.extract_frontier` stay in the module for the
  `/skeft-qa:notebook` skill, just no longer injected.)
- **EDIT `RE_ANCHOR`** (BLOCKER 1.5 — it is NOT safe to keep byte-identical): its live text
  (`harness_common.py:376-379`) tells the agent to cross-check against "the live LAB-NOTEBOOK
  FRONTIER below (always current — the loop's own latest state)" — a dangling pointer once the
  FRONTIER block is removed, and the exact false "always current" claim the motivation indicts.
  Repoint it: *"...confirm it still matches the close-path: the LIVE REPO-STATE ANCHOR (your
  FIRST_ACTION probe — git/Lean/atlas, computed now) and the COACHING BLOCK if present..."* Drop
  "always current — the loop's own latest state" entirely.
- **INJECT a minimal git-computed anchor (MAJOR 1.10 — skip-resilience).** SessionStart computes,
  cheaply and without the LSP, `HEAD=<sha8>` + the most-recently-touched active `lean/*.lean`
  file (`git rev-parse`, `git log -1 --name-only`; ~5 ms, fail-open) and injects ONE line. So if
  the agent skips the FIRST_ACTION probe, the post-compact turn still has a true HEAD anchor
  (today's drifted-but-present frontier is replaced by a small *accurate* anchor, not nothing).
  Pointer-grade fact, ~60 chars — not script output; principle 1 intact.
- **`FIRST_ACTION` gains the live-anchor + settled-forks + regen-trigger directives:**
  - *"(0) Establish the LIVE ANCHOR — run `uv run python scripts/repo_state_probe.py` and
    `lean_diagnostic_messages` on the active file. This computed repo state SUPERSEDES any
    narrated frontier/summary; if they disagree, the live state wins."*
  - *"If `.claude/dev-harness/regen_requested.flag` exists and Lean slots are idle, kick the
    boundary atlas regen in the background (lockfile-guarded, §E.2), then clear the flag."*
  - *"Read `docs/dev-loops/SETTLED_FORKS.md` before any 'impossible / needs a banned route'
    reasoning — grep the register FIRST; record any NEW dead-end/fork/crux-map/tactic to it /
    the notebook / project memory (the summary won't preserve what isn't written)."*
- Everything else **byte-identical**: SETTLED GOAL (full), atlas frontier (droppable, unchanged),
  COACHING BLOCK (full, never truncated), CLAUDE.md pointer.

**Budget accounting.** Removed: the prose frontier block — up to ~1780 chars (1600
`extract_frontier` cap + ~180 label, 1.9). Added: the ~60-char injected HEAD anchor + ~3
FIRST_ACTION lines (~480 chars). **Net payload change: negative** for any non-trivial frontier
(the common case). The unbounded exact-state lives entirely in the agent-run probe output —
principle 1 satisfied with margin; the 10k cap is *less* pressured than today.

---

## D. `harness_reinject.py`

`notebook_note` (`harness_reinject.py:55-73`) joins ALL `notebook_lib.op_check` warnings — the
frontier-staleness warning is produced inside `op_check`/`_frontier_stale` (`notebook_lib.py:
~280`), NOT in `notebook_note` (1.8). Since the frontier is no longer the anchor, demote that
warning from "drift risk" to "notebook hygiene": the real edit is in `notebook_lib` (gate
`_frontier_stale` behind a `severity=hygiene` flag, or filter `frontier_stale` out of the
warnings `notebook_note` surfaces). Keep the over-budget-shard + missing-DECISIONS warnings.
`harness_reinject.main()` flow otherwise identical (plus the §C injected HEAD anchor).

---

## E. `harness_precompact.py` — new PreCompact hook (Move 3 + memory)

Fires once per compaction (infrequent — ~per 950k tokens). **Capability-bounded (verified via
claude-code-guide, finding 1.6): a PreCompact hook has a ~60s timeout, CANNOT reliably inject
context / steer the summary, and CANNOT safely fire-and-forget a long child (reaping
undocumented). It CAN reliably do fast synchronous file writes.** So the hook does ONLY fast,
synchronous, deterministic work — it **stages** (ruling #1); it never spawns the heavy job and
never injects context. **Impl pre-flight — CONFIRMED (2026-06-24, official Claude Code hooks docs):**
PreCompact **fires on auto-compaction**, distinguished by a stdin **`trigger` field (`"manual"` |
`"auto"`)**, and supplies `transcript_path` + `session_id` + `cwd` + `custom_instructions`. So Move 3
is viable; the hook fires on both manual `/compact` and the context-window auto-compact (a snapshot +
flag helps both, so it does not branch on `trigger`). `additionalContext` capability is moot —
principle 7 forbids PreCompact context injection regardless. The harness previously omitted PreCompact
deliberately ("harvest is off-hot-loop") — this adds it for *synchronous staging only*, consistent with
that posture. (Sources: docs.claude.com/en/docs/claude-code/hooks-guide; docs.anthropic.com/en/docs/
claude-code/hooks.)

1. **Snapshot artifact (synchronous, reliable).** Tail the transcript (`jsonl_path` from the
   marker) for the last substantive assistant text-block (same extraction the harvest uses) and
   write the **gitignored** `.claude/dev-harness/snapshot_<goal_id>.json` =
   `{ts, transcript_hwm, head_sha, last_message}`. A file the probe (§A.6) re-reads — so the
   next-brick survives even a null summary (`:34141867`) via the artifact channel, NOT context.
   Fast (transcript-tail + one write), completes well inside the timeout.
2. **Stage the atlas regen — write a flag, do NOT run it.** Write the gitignored
   `.claude/dev-harness/regen_requested.flag` (`{ts, head_sha}`). The hook does **not** spawn
   `lake build` (1.6: unsafe from a hook). The regen EXECUTES post-compact via the **agent's**
   reliable backgrounded Bash, triggered by the §C FIRST_ACTION reading the flag: it runs
   `lake build SKEFTHawking.ExtractDeps && python scripts/atlas_view.py --write-boundary`
   (writing the **gitignored** `.claude/dev-harness/atlas_view.boundary.json`, NOT the tracked
   `lean/atlas_view.json` — BLOCKER 1.2) when slots are idle, then clears the flag. **ENFILE
   single-flight (1.7):** the agent step is lockfile-guarded + count-gated
   (`pgrep -fc 'lake|lean-lsp-mcp' < N`), swallows ENFILE, and SKIPS under any doubt (a stale
   atlas is fail-soft — `frontier_from_atlas`/probe already degrade). The probe (§A.4) prefers
   `atlas_view.boundary.json` over the tracked file when it is fresher.
3. **Durable-capture: mechanical, not LLM-synthesized at the hook.** Pre-loss LLM synthesis is
   not reliably inducible from a hook (no context injection, 1.6). So capture is mechanical: the
   snapshot (job 1) preserves the agent's last-stated next-brick/learning verbatim from the
   transcript tail. The *going-forward* discipline — record any new dead-end / fork / crux-map /
   tactic to SETTLED_FORKS.md / notebook / project memory — rides the §C FIRST_ACTION (a turn the
   agent owns), generalized by category + destination, never a specific theorem. No dependency:
   if it doesn't fire, Move 1 recomputes from the artifacts regardless.

---

## F. `docs/dev-loops/SETTLED_FORKS.md` — structured negative knowledge (Move 2, additive)

The SETTLED FORKS register already exists as prose at the top of `LAB_NOTEBOOK_INDEX.md` and is
*proven effective* (both compact-delta findings this harvest = it catching a re-seed). Move 2 is
**additive structuring**, not replacement: a tracked, commit-keyed, grep-able file —

```
## <route-id>            e.g. routeC-snake-mv-ses
- verdict: dead | banned | superseded
- tier: automatic | agent-reviewed | human-reviewed   # governance, mirrors System-2
- authored_by: kernel-no-go | coach | harvest | debrief
- killed_by: <commit-sha>            # the commit/kernel-check that settled it
- reason: <one line>                 # why; what it would have needed (e.g. the banned formula)
- memory: [[note-slug]]              # cross-link to project memory
- created_ts: <ISO-8601>             # REQUIRED
- reviewed_ts: <ISO-8601>            # set when /debrief reviews or modifies
```

- **Mandated read** via FIRST_ACTION (§C) — same progressive-disclosure pattern as
  PRE_DECISIONS (the register's own prescription: "grep the register / git history FIRST").
- The probe (§A.7) surfaces only the **count + IDs** as a pointer (no payload contents).
- The atlas's `OBSTRUCTION` nodes (proved no-gos) feed the *proved* negative front; SETTLED_FORKS
  carries the *procedural* bans (route thrash, altitude locks) that no code artifact records.

**Authoring & governance (ruling 2026-06-24):**
- **A kernel-checked no-go settles a fork decisively** — `verdict: dead`, `authored_by:
  kernel-no-go`, tier `automatic`. The kernel (not human judgment) is the authority, so the
  autonomous loop / agent MAY record these mid-run when it has the kernel artifact (a proved
  `¬`/obstruction or a `lean_verify`-confirmed impossibility). `killed_by` cites the commit.
- **The coach may author / influence** entries (`authored_by: coach`, tier `agent-reviewed`) —
  e.g. a route ban it resolved during a dispatch. The harvest may *propose* (tier `automatic`).
- **Every entry carries datetime metadata** (`created_ts` REQUIRED; `reviewed_ts` on review).
- **`/debrief` is the review/modify layer** (human governor): it can promote tier
  (`agent-reviewed`→`human-reviewed`), edit, or retire any entry — the same human-vs-agent
  review surface as the System-2 register. No entry is immutable; all are `/debrief`-modifiable.

---

## Failure-mode / fail-soft matrix

| Failure | Behavior |
|---|---|
| No marker / unmanaged session | probe prints minimal HEAD, exits 0; payload unchanged |
| `arm_sha` absent (pre-field goal) | cascade §A.2a: timestamp → last-N lean commits → atlas-only |
| `arm_sha` present but unresolvable (commit GC'd) | `git log` errors → fall through to timestamp rung |
| `atlas_view.json` stale/missing | inventory section says `(atlas unavailable — run extraction)`; live sorry still from LSP |
| PreCompact regen would ENFILE | gate skips it; atlas stays stale; fail-soft to `None` |
| PreCompact memory nudge doesn't fire | NO dependency — post-compact recovers via the probe + snapshot/atlas artifacts (recompute from durable stores, never from context) |
| git unavailable | each git section prints `(unavailable)`; rest proceeds |
| probe nonzero / throws | FIRST_ACTION still mandates `lean_diagnostic_messages`; loop proceeds |

---

## Test list (deterministic, no live LLM)

1. `repo_state_probe` output shape on a fixture marker + fixture `atlas_view.json` (golden text).
2. Multi-marker: two markers, each resolves its own `arm_sha`/active set (no cross-read).
3. Cascade (§A.2a): `arm_sha` present→exact; absent→timestamp rung; unresolvable sha→timestamp;
   no timestamp→last-N; git absent→atlas-only. Each rung names itself in output; no crash.
4. `build_reorientation_payload`: `_frontier_for` absent; FIRST_ACTION carries the live-anchor +
   settled-forks + regen-trigger lines; coaching block byte-identical and present; assert
   `len(payload) < PAYLOAD_MAX_CHARS` (the symbol, NOT the literal 9300 — 1.1).
4b. **RE_ANCHOR (1.5):** the emitted RE_ANCHOR contains NO "FRONTIER below" / "always current"
   substring and DOES reference the live probe.
4c. **Injected HEAD anchor (1.10):** `harness_reinject` output contains `HEAD=<sha8>` + a
   `lean/*.lean` filename even when the probe is never run; absent git → line omitted, no crash.
5. Budget regression: max-size coaching block + atlas + the injected anchor still under cap.
6. PreCompact snapshot writes `{ts,hwm,head,last_message}` to the gitignored path; probe reads it;
   absent → graceful.
6b. **Tracked-path invariant (1.2/QI):** assert no harness hook/probe writes a `git ls-files`-tracked
   path; the boundary regen targets `.claude/dev-harness/atlas_view.boundary.json`; the probe
   prefers it over `lean/atlas_view.json` when fresher.
7. ENFILE single-flight (1.7): simulated `pgrep` over-threshold OR held lockfile → regen skipped,
   flag left for next attempt; swallows a simulated ENFILE.
8. SETTLED_FORKS parse: malformed entry → skipped, not fatal; `created_ts` required; count/IDs
   surfaced; tiers respected.
9. Fail-soft sweep: git missing, atlas missing, marker missing, probe-throws — each degrades,
   never blocks; FIRST_ACTION still mandates `lean_diagnostic_messages`.
10. **Synthetic fixtures (1.14):** all fixtures use a synthetic `goal_id`/marker, never the live
   `20260617T231250`, so tests don't couple to this deployment.

---

## Sequencing within the single update

All land together, but build/verify order:
1. F (`SETTLED_FORKS.md` seed from the existing LAB_NOTEBOOK register) — no behavior change.
2. A + B (probe + arm_sha) — additive; verify output by hand on the live goal.
3. C + D (payload swap) — the behavioral change; gated by tests 4–5.
4. E (PreCompact) — last; artifact + memory-nudge only (no summary-steer), so it cannot block
   the rest and has no context-survival dependency.

## Resolved decisions (2026-06-24 review)

1. **PreCompact scope — RESOLVED.** Durable channels ONLY: write artifacts (snapshot, background
   atlas regen) + nudge Claude memory. **Do NOT** attempt to steer the summary or make content
   survive post-compact context (non-deterministic at best; overrides CC autocompact at worst —
   we align to it, not own it). Recovery post-compact is recompute-from-artifacts (Move 1).
2. **arm_sha backfill — RESOLVED:** yes, a one-time backwards-compat migration for the active
   goal `20260617T231250` (§B). Degrade path stays as the permanent fallback for future markers.
3. **SETTLED_FORKS authority — RESOLVED (§F):** kernel-checked no-gos settle a fork decisively
   (tier `automatic`); the coach may author/influence (`agent-reviewed`); datetime metadata
   required on every entry; all entries reviewable/modifiable at `/debrief` (human-vs-agent).

## Resolved impl-time item (2026-06-24)

- **Atlas regen trigger redundancy — KEEP BOTH (different cadences).** The per-compaction-boundary
  regen (agent-executed via the `regen_requested.flag` the PreCompact hook stages) and the existing
  wave-close regen coexist. **Clarification:** neither is bound by the ~60s PreCompact hook timeout
  — the hook only *stages* (snapshot + flag, <1s); the 134s ExtractDeps+atlas regen runs as the
  agent's backgrounded Bash (no 60s limit). Keeping both especially benefits the L2 corner case (a
  long session has many compactions but few wave-closes — boundary regen keeps the atlas fresh
  where wave-close-only would lag).
