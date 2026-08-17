# Worktree accumulation — creation, teardown, timeline, disk, safety

**Scope:** all 31 linked git worktrees of `SK_EFT_Hawking` (32 with main) plus the workspace-level
`.feature-worktrees/SK_EFT_Hawking`. Read-only investigation; no worktree, branch or file touched.

**Verdict up front:** **ongoing, not a one-off.** Worktrees were created across nine distinct dates
spanning 61 days (2026-06-17 → 2026-08-17, today), and five of the 31 were created *today* — two days
after the Saturday 2026-08-15 session that was killed by usage limits. The root cause is structural:
**every ad-hoc worktree in this repo is created by a lead session typing `git worktree add` inline for
a one-off parallel-fan-out task, and no script, hook, skill or CLAUDE.md procedure anywhere in the repo
or plugin ever calls `git worktree remove` afterward** — confirmed by an exhaustive grep
(`git worktree remove|prune|cleanup.*worktree`) across `docs/`, `scripts/`, `.claude/plugins/skeft-qa/`
returning zero hits outside worktree-internal copies. The one exception — the three `wt1-3` Lean slots
— has a control plane (`slotctl`) precisely *because* they are meant to persist, not be torn down; every
other worktree gets neither.

**Bottom line:** 25 of 31 worktrees are safe to remove today (merged into `main`, zero commits ahead,
no irreplaceable uncommitted work). Removing them reclaims **≈146 GB** of the 217 GB total. 6 worktrees
should stay: `wt1`/`wt2`/`wt3` (managed slots, `slotctl` forbids deletion), `docs` (11 unmerged commits,
real work awaiting operator merge), and `py1`/`py2` (merged and clean, but referenced in the operator's
own cross-session notes as an active Codex-side delegation resource — confirm before removing rather
than bucket with the rest).

---

## 1. Creation — two entirely different lifecycles

**Managed slots (`wt1`, `wt2`, `wt3`) — a real control plane.** `scripts/setup_lean_worktree_slots.sh`
creates them once (`git worktree add "$SLOT" -b "$BR"`, then an APFS `cp -c` copy-on-write clone of
`lean/.lake`). Ongoing lifecycle is owned by `scripts/lean_slots/` (the `slotctl` CLI): `acquire` →
`prepare` (reset to a lease's base, install the published build epoch) → dispatch a `lean-worker` → `ready`
→ `absorb` (rebase, fast-forward-only merge, rebuild, release). Documented explicitly:
`.claude/plugins/skeft-qa/skills/goal-dev/references/parallel-worktrees.md:77` — *"The slot stays for
the next task — never delete it."* This is the **only** worktree population in the repo with a written
lifecycle contract.

**`py1`/`py2`** are structurally identical in shape to `wt1-3` (persistent, `worktree-py1`/`worktree-py2`
branches) but **no script or doc in this repo manages them** — `grep -rn "py1\|py2"` across
`scripts/lean_slots/`, `HARNESS_GUIDE.md` and `goal-dev/references/` returns nothing. The operator's own
memory record (`reference_codex_delegation_worktrees_fable_targets`) describes them as Codex-side
Python delegation slots added alongside `wt1-3`; whatever manages their lifecycle lives outside this
repo (Codex's own config), which is why no in-repo mechanism appears.

**Everything else (`redraft-*` ×13, `subst-ext`, `subst-sixteen`, `rv1`–`rv6`, `mathlib-bump`, `kzm`,
`mlx-hikappa`, `docs`) has no creation mechanism in the repo at all.** No template, no CLI wrapper, no
skill step. Each was `git worktree add`-ed inline by whatever lead session needed isolation for one task:
- **`rv1`–`rv6`** (2026-08-05): six parallel-reviewer worktrees for a one-off 6-reviewer PR-review pass —
  confirmed by `docs/audits/2026-08-05-pr-review-3/H1-goal-fit.md:4` ("Tree: `db430c65`, worktree `rv1`")
  and five sibling reviewer reports. All six still sit on that single shared review commit, untouched
  since.
- **`redraft-*` ×13** (2026-08-15/17): one worktree per publication bundle for the Stage-10 redraft
  campaign. The dispatch brief's own text — *"Worktree: … Work only there"* — is composed fresh each
  time per session transcript (also the subject of `FINDINGS.md` item 5, "the Stage-10 dispatch brief has
  no contract"); it is never a template that includes a teardown step.
- **`.feature-worktrees/SK_EFT_Hawking`** (2026-07-22, workspace-level, outside the repo tree): shape and
  location match the Claude Code Agent tool's own `isolation: "worktree"` feature, which the tool
  description states is "automatically cleaned up if the agent makes no changes; otherwise the path and
  branch are returned in the result" — i.e. auto-cleanup is a no-op unless the worktree is untouched. This
  one has real merged commits, so the harness's own auto-cleanup never fired, and — same as every other
  ad-hoc worktree — nothing removed it afterward either.
- **`subst-ext`, `subst-sixteen`, `mathlib-bump`, `kzm`, `mlx-hikappa`, `docs`**: same pattern, one
  worktree per substantive branch of work, created ad hoc, no discovered dispatch template or script.

## 2. Intended teardown — nothing exists for the ad-hoc population

Exhaustive search (`grep -rln "worktree remove\|worktree prune\|cleanup.*worktree"` over `docs/`,
`scripts/`, `.claude/plugins/skeft-qa/`) finds **zero hits** anywhere in the repo or plugin — not "a
command exists but nothing calls it," but **no command exists**. Specifically:

- `slotctl` (`scripts/lean_slots/`) resets and rebuilds `wt1-3`; it has no `remove`/`destroy` verb and no
  equivalent for any other worktree.
- The plugin's `/reset-slot` command (`${CLAUDE_PLUGIN_ROOT}/scripts/reset_slot.py`) resets an unleased
  `wt1-3` slot to `main` via `checkout -B`; it never removes the worktree, and is hard-scoped to `wt1-3`
  by name.
- `wave-close` (`.claude/plugins/skeft-qa/skills/wave-close/SKILL.md`) mentions "worktree/worker can't
  race the same regen" once, in passing, about concurrency — not cleanup.
- `goal-dev`'s `parallel-worktrees.md` documents the slot *harvest* (`absorb`) but explicitly says the
  slot is kept, not removed.
- The generic (non-project) `superpowers:finishing-a-development-branch` skill **does** contain a real
  `git worktree remove` + `git worktree prune` step (Step 6, gated on the worktree path living under a
  `worktrees/` directory — which `.claude/worktrees/redraft-D1` etc. would match). But nothing in the
  redraft dispatch procedure invokes it, and its own contract requires an interactive menu ("Merge / Keep
  for PR / Keep as-is") with a typed `discard` confirmation — incompatible by design with this repo's
  autonomous `/goal` posture, where "the operator is intentionally out of the loop" and the loop must
  never stop to ask (workspace `CLAUDE.md` § Autonomous `/goal` mode). Even if it were wired in, its
  default menu would not fire non-interactively.

So the honest state is: one population (`wt1-3`) has a lifecycle that deliberately never deletes, and
every other population has no lifecycle at all — not merely an unused one.

## 3. Timeline — ongoing across 61 days, not a Saturday-only burst

Creation dates below are the mtime of each worktree's administrative pointer file
(`.git/worktrees/<name>/gitdir`, main repo) — written once at `git worktree add` time and never touched
again, so it is a reliable creation timestamp:

| date created | worktrees | count | context |
|---|---|---|---|
| 2026-06-17 | `wt1`, `wt2`, `wt3` | 3 | initial Lean slot setup (ADR-008) |
| 2026-07-11 | `docs` | 1 | docs/community-overhaul |
| 2026-07-16 | `mlx-hikappa` | 1 | mlx-rhmc-hikappa-chrono |
| 2026-07-20 | `py1`, `py2` | 2 | Codex Python delegation slots |
| 2026-07-22 | `.feature-worktrees/SK_EFT_Hawking` | 1 | agent-isolation worktree (adr-008-quarantine-doctor) |
| 2026-07-28 | `mathlib-bump` | 1 | bump/mathlib-v4.32 |
| 2026-08-05 | `rv1`–`rv6` | 6 | one-off 6-reviewer PR-review-3 pass |
| 2026-08-15 14:19–16:13 | `redraft-D2/D3/L2`, then `D1/D4/E1`, then `D6/D8/E2`, then `subst-ext/subst-sixteen` | 11 | Stage-10 redraft campaign, 3 dispatch sub-bursts + 2 substantiate branches |
| 2026-08-17 02:09–03:03 | `redraft-D10/D7/D9`, `kzm`, `redraft-D7-rev` | 5 | **today** — redraft campaign continuing |

That is nine distinct creation events, none of them a single burst, and the most recent is **today**,
two days after the Saturday session in question. Last-commit dates on the branches show the same spread
— e.g. `mathlib-bump` last touched 2026-07-29, `mlx-hikappa` 2026-07-17, `py2` 2026-07-20, `rv1-6` never
touched since 2026-08-05 — meaning worktrees are also abandoned steadily over time, not just created in
bulk. **This has been happening every 1–3 weeks for two months; Saturday's redraft campaign is the
latest and largest instance of an existing pattern, not the pattern's origin.**

## 4. Disk — dominated by `.lake` build trees, not `.git` or working files

`du -sh` per worktree, largest first (GB, `.claude/worktrees/` unless noted):

| worktree | size | dominant contents |
|---|---|---|
| `rv4` | 31G | `lean/.lake` = 29G |
| `mathlib-bump` | 24G | `lean/.lake` = 23G |
| `wt1` | 23G | `lean/.lake` = 22G (APFS `cp -c` clone — see caveat) |
| `wt2` | 23G | same |
| `wt3` | 23G | same |
| `subst-ext` | 23G | `lean/.lake` = 22G |
| `rv5` | 23G | `lean/.lake` = 22G |
| `redraft-D3` | 15G | `lean/.lake` = 14G |
| `rv2` | 5.4G | |
| `rv3` | 4.1G | |
| 6 × `redraft-{L2,E2,E1,D8,D6,D2}` | 1.8G each | |
| `py2` | 1.7G | |
| `mlx-hikappa` | 1.6G | |
| `subst-sixteen`, `redraft-{D9,D7,D7-rev,D4,D1}`, `rv1`, `py1` | 1.0–1.1G each | |
| `redraft-D10`, `kzm`, `docs`, `rv6`, `.feature-worktrees/SK_EFT_Hawking` | 236–252M each | |
| **Total** | **217G + 236M** | |

Every worktree checked has `.git` at **4.0K** — worktrees share the main repo's object store, so `.git`
never duplicates history. The near-entirety of the 217 GB is `lean/.lake` (compiled Lean/Mathlib build
artifacts); source files, `data/` (independently gitignored and absent from every worktree) and other
working files are negligible by comparison. **This decides the question directly: a "vacuum" should
remove whole worktrees, not just prune `.lake`** — `.lake` is already gitignored and worthless without
the source tree it was built against, and the source trees themselves are all disposable (see §5).

⚠️ **COW caveat, `wt1-3` only.** `setup_lean_worktree_slots.sh` explicitly clones `.lake` with `cp -c`
(APFS copy-on-write), and the repo's own `parallel-worktrees.md` states this makes `du` "COW-blind" —
3 slots show ~43 GB logical for ~500 MB real disk. **No other worktree's `.lake` (`rv4`, `rv5`,
`mathlib-bump`, `subst-ext`, `redraft-D3`, etc.) has a documented COW-clone origin** — they were built ad
hoc, most plausibly via a genuine `lake build` inside each — so their `du` figures should be read as real
disk, not discounted the way `wt1-3`'s are. The reclaimable-GB estimate below already excludes `wt1-3`.

## 5. Safety — per-worktree branch, merge, dirty and ahead status

`git branch --merged main` and `git rev-list --count main..<branch>` for every named-branch worktree;
`git log --oneline main | grep <sha>` (log-membership, since `git merge-base` is denied to this session
by the worker-shell guard) for the six detached `rv*` worktrees, which all share commit `db430c65` —
confirmed present in `main`'s history, so all six are fully contained.

| worktree | branch | merged into main | ahead of main | uncommitted changes | verdict |
|---|---|---|---|---|---|
| `wt1`/`wt2`/`wt3` | `worktree-wt{1,2,3}` | yes (trivially — reset to main) | 0 | none | **KEEP** — managed slot, `slotctl` forbids deletion |
| `py1`/`py2` | `worktree-py{1,2}` | yes | 0 | none | merged & clean, but no in-repo control plane found; operator notes describe active external (Codex) use — **confirm before removing** |
| `docs` | `docs/community-overhaul` | **no** | **11** | 1 untracked dir (`docs/community/`) | **KEEP** — real unmerged work, "AWAITING OPERATOR MERGE" per operator record |
| `redraft-D1`,`D4`,`D6`,`D7`,`D7-rev`,`D8`,`D9`,`D10`,`E1`,`E2`,`L2` (11) | `redraft/*` | yes | 0 | none | **SAFE TO REMOVE** |
| `redraft-D2` | `redraft/D2` | yes | 0 | 20 lines, `papers/*/bundle_metadata.json` | **SAFE TO REMOVE** — diff is regenerated gate-cache state (`blocked_p1_gates` etc.), not authored content |
| `redraft-D3` | `redraft/D3` | yes | 0 | 18 lines, same `bundle_metadata.json` cache pattern | **SAFE TO REMOVE** |
| `subst-ext` | `substantiate/a1-kernel-pure` | yes | 0 | 2 files, `lean/lean_deps.json` + `.hash` | **SAFE TO REMOVE** — regenerated dependency-graph cache |
| `subst-sixteen` | `substantiate/sixteen-repoint` | yes | 0 | none | **SAFE TO REMOVE** |
| `kzm` | `substrate/kzm-exponent` | yes | 0 | none | **SAFE TO REMOVE** |
| `mathlib-bump` | `bump/mathlib-v4.32` | yes | 0 | none | **SAFE TO REMOVE** |
| `mlx-hikappa` | `mlx-rhmc-hikappa-chrono` | yes | 0 | none | **SAFE TO REMOVE** (note: an older operator memory note calls this branch "UNMERGED, NEXT = merge → main" — current git state contradicts that; re-verify the memory note is stale before treating this as settled, but the measurement here is unambiguous) |
| `.feature-worktrees/SK_EFT_Hawking` | `agent/adr-008-quarantine-doctor` | yes | 0 | none | **SAFE TO REMOVE** |
| `rv1`, `rv3`, `rv4` | detached @ `db430c65` | contained in main | n/a | none | **SAFE TO REMOVE** |
| `rv2`, `rv6` | detached @ `db430c65` | contained in main | n/a | 9 lines, `bundle_metadata.json` cache | **SAFE TO REMOVE** |
| `rv5` | detached @ `db430c65` | contained in main | n/a | 12 lines, `counts.json`/`counts.tex`/`bundle_metadata.json` cache | **SAFE TO REMOVE** |

**25 of 31 worktrees are safe to remove today**: all 13 `redraft-*`, both `subst-*`, `kzm`,
`mathlib-bump`, `mlx-hikappa`, the workspace-level `.feature-worktrees/SK_EFT_Hawking`, and all six `rv*`.
Every uncommitted diff found across those 25 is regenerated validation/gate cache (`bundle_metadata.json`
readiness fields, `lean_deps.json`), never hand-authored content — losing it costs a re-run of `sync`,
not lost work. Sum of their `du` figures: **≈146 GB** (13 redraft ≈31.6G + both subst ≈24.1G + kzm
≈0.25G + mathlib-bump ≈24G + mlx-hikappa ≈1.6G + feature-worktree ≈0.24G + six `rv*` ≈64.7G).

**6 should stay for now**: `wt1`/`wt2`/`wt3` (≈69G logical, mostly COW-shared — do not remove, the slot
control plane depends on them persisting), `docs` (≈0.25G, real unmerged work), `py1`/`py2` (≈2.7G,
merged and clean but flagged for operator confirmation rather than assumed disposable).

---

**Suggested mechanical fix, for the record (out of scope to execute here — read-only task):**
`git worktree remove .claude/worktrees/<name>` for each of the 25, then `git worktree prune`, would
reclaim ≈146 GB with zero code changes — exactly the remediation ORCH-3 already proposed. The recurring
gap is upstream of any one cleanup pass: no dispatch procedure that creates a one-off worktree (redraft,
substantiate, reviewer-fan-out) currently ends with a removal step, so the next campaign will reproduce
this finding unless a teardown step is added to whichever brief/skill/script creates the next batch.
