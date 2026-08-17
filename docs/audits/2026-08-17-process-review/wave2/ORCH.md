# Cluster ORCH — worktree orchestration and search-tooling false absence

Window: t0 = 2026-08-15 09:46 CDT to HEAD (`4c81c2ec`). Unloaded plugin commits checked against
every claim: `fd6cac3d`, `e9e5e314`, `c4b1a1ca`, `f58a3fe4` (none touch worktree/notebook/gitignore
mechanics or Lean-search tooling — confirmed by reading each commit's diff).

---

### ORCH-1 — worktree agents are structurally blind to gitignored durable state (notebooks, `data/`, `.lake`)

- **Wave-1 source IDs:** F-07, F-14, H-05, E-9, D-05
- **Verdict:** CONFIRMED (mitigated by documentation, not by a structural fix); H-05's specific
  framing is RE-DIAGNOSED.
- **Evidence at HEAD:**
  - `.gitignore:125` — `**/LAB_NOTEBOOK*.md` — unchanged at HEAD.
    `grep -n "LAB_NOTEBOOK" .gitignore` → `125:**/LAB_NOTEBOOK*.md`.
  - Direct reproduction in a live worktree:
    `find .claude/worktrees/redraft-D10/docs/dev-loops/D10_Discharge -iname "LAB_NOTEBOOK*"` →
    empty; `ls .claude/worktrees/redraft-D10/docs/dev-loops/D10_Discharge/` → only
    `goal_prompt_20260630T063621.md`. On main: `ls -la docs/dev-loops/D10_Discharge/LAB_NOTEBOOK*.md`
    → both files present (`LAB_NOTEBOOK.md` 35673 bytes, `LAB_NOTEBOOK_INDEX.md` 21842 bytes,
    mtime 2026-06-30 — i.e. they exist and are old, not newly written).
  - `data/` is independently gitignored (`.gitignore:55`) and **entirely absent** from a worktree:
    `find .claude/worktrees/redraft-D10/data -maxdepth 1` → `No such file or directory`.
  - D-05's distinct sub-mechanism (build isolation, not gitignore visibility) also reproduces:
    `.claude/worktrees/redraft-L2/lean/.lake` exists but is **empty** (`ls -la` → only `.`/`..`),
    so `native_decide`/`ExtractDeps` gates genuinely cannot run in that worktree.
- **Population:**
  - Notebook files in the main checkout: `find docs -iname "LAB_NOTEBOOK*.md" | wc -l` → **92**.
  - Roadmap loops (`docs/dev-loops/*`, excluding the non-loop `assets`/`proposals` dirs):
    **18**, of which **15** carry a notebook and **3** (`Phase5qF`, `Phase5qG`, `ADR010_retrofit`)
    do not yet. Plus one legacy notebook outside the standard layout:
    `docs/roadmaps/Phase5qB_LabNotebook.md`.
  - Worktrees: `git worktree list | wc -l` → **32** (main + 31 linked). Every linked worktree is
    structurally blind by the same mechanism (`git worktree add` materialises tracked files only),
    so the population of affected worktrees is **all 31**, not just the 13 redraft ones.
- **Already-addressed by:** no. Commit `88e2f434` (2026-08-17, in-window) **filed** this as a MAJOR
  finding (`papers/AutomatedReviews/2026-08-17-worktree-agents-cannot-read-notebooks/infra.md`) with
  a `Verify` that exits 1 at HEAD. A second in-window commit, `73c04a8d`, added an ownership row to
  `docs/architecture/README.md` and a new `docs/dev-loops/HARNESS_GUIDE.md §8b` documenting the
  mechanism and three **procedural** rules (cite notebooks by absolute path; never conclude absence
  from a worktree-relative miss; never let a worker write a notebook into its own worktree). Neither
  commit changes `.gitignore`, the notebook tooling's path resolution, or worktree materialization —
  the structural blindness itself is **unfixed**; only a workaround is now documented. None of the
  four unloaded plugin commits touch this surface (checked their diffs directly).
- **Mechanism:** `git worktree add` materialises only **tracked** files, and `**/LAB_NOTEBOOK*.md`
  (and separately `data/`) are gitignored, so no worktree ever has one. The failure is asymmetric:
  `/skeft-qa:notebook` resolves paths against the repo root rather than the caller's cwd, so a
  worker's `notebook new` **writes** to the main checkout while its **reads** from inside the
  worktree come back empty — a worker consults the tracker, finds nothing, proceeds uninformed, and
  its own contribution still lands on main. Separately, `.lake` is never built inside a fresh
  worktree, so ExtractDeps/native-decide gates cannot self-verify there either (D-05).
- **Recurs on the next bundle?** YES. Every future worktree-dispatched agent — 15 active loops with
  a notebook, and any of the 31 current or future worktrees — hits the same blindness unless the
  dispatching lead manually follows the new absolute-path rule every time. The mechanism itself was
  deliberately left undecided in both commits ("whether these should be gitignored at all").
- **Re-diagnosis of H-05:** wave 1 reported the D10 brief's claim as *"file does not exist."* That
  is imprecise: `docs/dev-loops/D10_Discharge/LAB_NOTEBOOK_INDEX.md` exists on **main** (mtime
  2026-06-30, i.e. months before the brief). It does not exist **in the D10 worktree**, which is
  exactly the F-07/F-14/88e2f434 mechanism. H-05's "brief is internally inconsistent" framing folds
  into ORCH-1 rather than standing as a separate defect — same root cause, not a brief-authoring bug.

---

### ORCH-2 — a background subagent dispatched from inside another subagent orphans its result

- **Wave-1 source IDs:** H-08
- **Verdict:** RE-DIAGNOSED.
- **Evidence at HEAD:** Reconstructed from
  `~/.claude/projects/.../6cf37aa2.../subagents/` and
  `.../scratchpad/audit/spine/main-2026-08-17.md`.
  - The D7 redraft lead-subagent (`agentId adecf3677aa796a72`, spawnDepth 1, "Redraft D7 at Stage
    10") itself dispatched a **nested** background agent at 07:40:04 —
    `agentId ad85015a93f274342`, spawnDepth 2, `parentAgentId adecf3677aa796a72`,
    `"Prose-review the finished D7 draft"`, `run_in_background: true`
    (`grep -n "toolu_01QtbyAkZSaoQrvQXQW5xMen" .../agent-ad85015a93f274342*`).
  - That nested agent **completed successfully** at 07:47:32 with a full review (verdict table,
    findings, deletion list) — 18 JSONL events, final event carries both a `thinking` block and a
    21373-char `text` block. Its completion notification (`status: completed`) was delivered — but
    to the **top-level/main session** (`main-2026-08-17.md:1575-1583`), never back to
    `adecf3677aa796a72`, the subagent that actually dispatched it.
  - `adecf3677aa796a72`'s own transcript shows a ~58-minute dead gap: its last real activity is at
    `07:45:54`, then nothing until `08:44:05`, when a bash wait-loop it had started
    (`bk7rmwjdm`, "Wait until reviewer output stops growing") was killed and it gave up, reporting
    in its own final message: *"the optional second prose review never returned, so I have nothing
    from it to report."* That statement is accurate **from that subagent's own vantage point** — it
    never received the result — but the result was not lost: it is fully persisted (258525-byte
    transcript at `subagents/agent-ad85015a93f274342.jsonl`, identical copy at
    `/private/tmp/.../tasks/ad85015a93f274342.output`) and was visible to, and read by, the
    top-level session.
  - Separately, the top-level lead recovered the work: it dispatched its own top-level
    `"Execute the D7 prose review"` agent (`a57b4fdea41aedce2`, spawnDepth 1, **not** nested),
    which ran 07:49–08:15 and returned a full, usable result that the lead then used to merge
    `redraft/D7-revision` (`main-2026-08-17.md:2496-2551`, merge commit visible in
    `git log --oneline` as part of the D7 sequence).
- **Population:** searched all 770 subagent transcript files
  (`ls ~/.claude/projects/.../subagents/ | wc -l`) for `spawnDepth: 2` entries with
  `run_in_background: true` inside this window; only this one instance
  (`ad85015a93f274342`) was found for the D7 cluster. Not re-derived as a repo-wide count because
  the mechanism is a harness property, not something the repo's own code can be scanned for.
- **Already-addressed by:** no. Nothing in the four unloaded plugin commits or elsewhere in the
  window changes background-task notification routing; that is CLI/SDK infrastructure, not
  something `.claude/plugins/skeft-qa/` can patch. No repo or plugin script reads back a completed
  subagent's persisted transcript on the dispatcher's behalf (`grep -rln "subagent" .claude/plugins/
  skeft-qa/scripts/` finds only unrelated hook files that reference the *concept*, not a
  result-recovery mechanism).
- **Mechanism:** a background `Agent`/Task dispatched from *inside* a subagent's own turn delivers
  its completion notification to whichever session is live to receive it when it fires — which, once
  the dispatching subagent's own turn has ended, is the top-level session, not the subagent that
  asked for the work. The dispatching subagent has no channel back into that notification queue; it
  can only poll (e.g. a `Bash` wait-loop) or give up. Wave 1's framing — "no fallback mechanism, work
  lost" — overstates it: the artifact is never actually lost (full transcript + `.output` file
  persist regardless of where the notification routes), and in this instance the lead did recover
  equivalent work by re-dispatching. The real, narrower defect is that (a) a nested-dispatching
  subagent's own final report can be factually wrong ("never returned") about an artifact that in
  fact exists and was delivered elsewhere, and (b) recovery is not automatic — it happened here only
  because the top-level lead was paying attention and manually re-dispatched.
- **Recurs on the next bundle?** YES — any future workflow that has a subagent dispatch a
  `run_in_background: true` nested Agent call and then wait on it synchronously will hit the same
  routing gap. Nothing about the D7 case was bundle-specific.

---

### ORCH-3 — worktree accumulation: merged redraft branches, disk held, no cleanup path

- **Wave-1 source IDs:** (measurement task, no wave-1 ID — investigated per the brief directly)
- **Verdict:** CONFIRMED.
- **Evidence at HEAD:**
  - `git worktree list | wc -l` → **32** total (1 main + 31 linked), of which **13** are
    `redraft-*` worktrees on `redraft/<bundle>` branches (`D1, D2, D3, D4, D6, D7, D7-revision, D8,
    D9, D10, E1, E2, L2`).
  - All 13 branch tips are reachable from `main`:
    `git log --oneline main | grep "^<8-char-tip>"` returned exactly 1 match for every one of the
    13 tips (command run per-branch; e.g. `redraft/L2` tip `80e94b4a` →
    `git log --oneline main | grep "^80e94b4a"` → 1 hit). `git merge-base --is-ancestor`/
    `git branch --merged` were denied to this session by `harness_worker_shell_guard`
    ("integration is the orchestrator's"), so the ancestry check used the log-membership form
    instead.
  - Disk: `du -sh .claude/worktrees/redraft-*` → **32G combined**
    (`redraft-D3` alone is 15G, almost entirely `redraft-D3/lean` at 14G — a built `.lake` tree
    left behind). `du -sh .claude/worktrees` (all 31 linked worktrees, not just redrafts) → **217G**.
- **Population:** 13 of 13 redraft worktrees hold fully-merged branches; 32G reclaimable from those
  alone; 217G across the full worktree population if the same audit were run on the other 18
  (`wt1-3`, `rv1-6`, `subst-*`, `py1/2`, `mathlib-bump`, `kzm`, `mlx-hikappa`, `docs`,
  `.feature-worktrees/SK_EFT_Hawking`).
- **Already-addressed by:** no. `grep -rln "worktree remove\|worktree prune\|cleanup.*worktree" docs/
  scripts/ .claude/plugins/skeft-qa/` → no hits anywhere in the repo or plugin. `reset_slot.py`
  exists but only resets the three lean-slot worktrees (`wt1/wt2/wt3`) to a clean state — it does not
  remove them, and it has no equivalent for redraft worktrees. No later commit in the window touches
  worktree lifecycle, and none of the four unloaded plugin commits do either.
- **Mechanism:** the redraft dispatch procedure (brief text confirmed in the spine: *"Worktree: …
  Work only there"*) creates one worktree per bundle and merges its branch back to main on
  completion, but nothing in that procedure — nor any script, hook, or doc — issues
  `git worktree remove` afterward. A merged worktree is pure liability: its branch is fully
  contained in `main`, but the working copy (source tree + any built `.lake`) sits on disk
  indefinitely.
- **Recurs on the next bundle?** YES — the next redraft wave will create N more worktrees via the
  same procedure with the same absence of a teardown step, unless the lead manually runs
  `git worktree remove` (or the ADR010_retrofit-style `commit-commands:clean_gone`-shaped cleanup)
  after each merge.

---

### ORCH-4 — search tooling reports false absence, and the workflow does not durably compensate

- **Wave-1 source IDs:** E-7, F-02, F-01, A-01, A-11, A-07
- **Verdict:** CONFIRMED.
- **Evidence at HEAD:**
  - `lean_local_search` false-absence: the explicit "`lean_deps.json` is the authority" warning
    exists in only **2 of 4** agent prompts that use Lean search tooling —
    `.claude/plugins/skeft-qa/agents/claims-reviewer.md:405` and
    `.../adversarial-reviewer.md:125` both state it verbatim. `.../paper-drafter.md:142` carries an
    equivalent warning in different wording. `.../lean-worker.md` — the agent dispatched into the
    parallel `wt1/wt2/wt3` slots and therefore the single highest-volume user of `lean_local_search`
    — has **no such warning**; it only says "search before prove" (`lean-worker.md:33,72`). The
    canonical lead-facing Lean-development docs also lack it: `grep -n "lean_local_search"
    .claude/plugins/skeft-qa/skills/goal-dev/SKILL.md .../lean-dev.md` returns only "search before
    prove" guidance, no false-absence caveat; the top-level `CLAUDE.md`'s own MCP tool description
    for `lean_local_search` ("Fast local declaration search. Use BEFORE trying a lemma name.") does
    not mention it either.
  - The "correct probe order" reference agents keep citing by name,
    `reference-measurement-traps-false-absence`, **does not exist as a file anywhere in this
    repository**: `grep -rln "reference-measurement-traps-false-absence" . | grep -v .git` → 6 hits,
    all of them *citations* to it (`scripts/dashboard_flow.py:301`,
    `scripts/validation/checks/bundles_readiness.py:1045,1136`,
    `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD`, `.../ACCURACY_LEDGER.md`,
    `docs/audits/2026-08-07-d11-retrofit/FINDINGS.md`, plus one filed finding
    `papers/AutomatedReviews/2026-08-15-d6-d9-overlap-population/infra.md`) — none of them is the
    document itself. It exists only as a personal cross-session memory note outside this repository
    (confirmed against this session's own injected memory index), invisible to any subagent, fresh
    worktree, or different operator.
  - `PRE_DECISIONS.md` — the doc the harness explicitly re-injects at every SessionStart/post-compact
    boundary — has **zero** mentions of the false-absence trap:
    `grep -n -i "false.absen\|absence.*trap\|seed.*known.present" docs/dev-loops/PRE_DECISIONS.md`
    → no output.
- **Population:** 9 total citations to the nonexistent reference doc across the repo; 4 agent
  prompts are candidates for the Lean-specific warning, 3 carry it in some form, 1
  (`lean-worker.md`) does not; 0 of the canonical dev-loop docs (`SKILL.md`, `lean-dev.md`,
  `CLAUDE.md`, `PRE_DECISIONS.md`) state either rule.
- **Already-addressed by:** no. None of the four unloaded plugin commits touch
  `lean-worker.md`, `goal-dev/`, or `PRE_DECISIONS.md`.
- **Mechanism:** two distinct but related gaps. (1) `lean_local_search` is a fast index that
  silently misses declarations that exist and build — this is a documented tool limitation, but the
  warning that compensates for it is copy-pasted per-agent rather than centralized, so it is present
  in 3 of the agents that need it and absent from the one with the highest search volume. (2) The
  general "measure the wrong shape three times before finding the table that holds the answer"
  failure (A-01, A-07, A-11) has an informally-agreed name and lesson that gets **cited by path** as
  if it were a shared, locatable artifact, but the artifact itself was never committed to the repo —
  it lives only in one person's cross-session memory. Any fresh context (a subagent, a new operator,
  a different machine) that hits the same measurement trap has no way to resolve the citation and
  will re-derive the lesson from scratch, exactly as A-01/A-07/A-11 show happening three times in one
  session.
- **Recurs on the next bundle?** YES — both gaps are structural rather than incident-specific: a
  fifth agent added to the roster with Lean-search needs will not inherit the warning unless someone
  remembers to add it by hand, and the next "is X missing" measurement has no committed reference to
  consult before probing three wrong shapes.

---

## Compact table

| ID | Verdict | Population | Recurs |
|---|---|---|---|
| ORCH-1 | CONFIRMED (mitigated by doc, not fixed) | 92 notebook files, 15/18 active loops, all 31 linked worktrees blind, `.lake` also empty per D-05 | YES |
| ORCH-2 | RE-DIAGNOSED | 1 confirmed instance (nested spawnDepth-2 background dispatch); notification routes to top-level session, not the dispatching subagent; artifact never actually lost | YES |
| ORCH-3 | CONFIRMED | 13/13 redraft worktrees hold fully-merged branches, 32G reclaimable (217G across all 31 linked worktrees), no cleanup script/doc found | YES |
| ORCH-4 | CONFIRMED | 9 citations to a nonexistent reference doc; 1 of 4 Lean-search agents (`lean-worker.md`, the highest-volume one) lacks the false-absence warning; 0 canonical dev-loop docs state either rule | YES |
