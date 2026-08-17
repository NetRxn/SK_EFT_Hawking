---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-17T03:00:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# Every worktree agent is structurally blind to every lab notebook

## Summary

**1 MAJOR.** `.gitignore:125` ignores `**/LAB_NOTEBOOK*.md`. Lab notebooks are therefore
**untracked**, and `git worktree add` materialises only tracked files — so **no lab notebook
exists in any worktree**, ever.

Every subagent in this campaign has been dispatched into a worktree. So the artifact the
project calls *"the authoritative living tracker, re-read on every bootstrap / after every
compact"* has been invisible to the entire agent fleet, by construction, for the whole campaign.

**Measured 2026-08-17, from a live collision.** The D10 redraft brief instructed the agent to
read `docs/dev-loops/D10_Discharge/LAB_NOTEBOOK_INDEX.md` "first — it is the durable entry
point". The agent reported both files absent and declined the instruction. The lead had seen
both with `find` minutes earlier. **Both were correct**: they exist in the main checkout
(35 673 and 21 842 bytes) and in no worktree.

## The asymmetry that makes it worse

Notebooks are **written** to the main checkout even from a worktree — `/skeft-qa:notebook`
resolves against the repo root, not the caller's cwd (cf. `feedback_harness_cli_cwd_fails_open`:
`harness_common_cli.py` resolves the repo from cwd and **fails open**). Verified: Wave T3's agent,
working in `.claude/worktrees/subst-ext`, created `docs/dev-loops/Phase5qT/LAB_NOTEBOOK{,_INDEX}.md`
and they landed on **main**, not in its worktree.

So the loop is: **writes land, reads fail.** An agent can be told to consult the tracker, find
nothing, proceed uninformed, and its own contribution to that tracker still lands — which is
precisely the shape that keeps a defect invisible while looking like it works.

## Why this is not cosmetic

The notebook is where `Log tried-and-FAILED so we never repeat post-compact` lives — the
goldfish-reseed guard. Phase 5q.T ran two and a half months with no notebook at all, and
accumulated **three** route errors in its roadmap that nothing caught: the T4 coinduction
variance refutation, an entry-state table silent about T1's substantive half, and a sidedness
error (`ModuleCat A1` is not typeable; the resolution lives over `A1subᵐᵒᵖ`). A tracker the
workers cannot read cannot prevent any of that.

### 1.1 — 🔴 MAJOR — the durable tracker is unreachable from where the work happens

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && git worktree add -b probe/nb-read /tmp/nb-probe HEAD >/dev/null 2>&1; test -f /tmp/nb-probe/docs/dev-loops/D10_Discharge/LAB_NOTEBOOK_INDEX.md; rc=$?; git worktree remove --force /tmp/nb-probe >/dev/null 2>&1; exit $rc`
  *What it asserts:* that a freshly created worktree can see a lab notebook that exists on main. Exits 1 at HEAD.
- **Gate:** HarnessIntegrity
- **Location:** `.gitignore:125`; `.claude/plugins/skeft-qa/scripts/notebook_lib.py`; every worktree-based dispatch
- **Observed:** notebooks untracked ⇒ absent from worktrees; notebook tooling still writes to the repo root.
- **Expected:** an agent told to read the tracker can read it, or is told where it actually is.
- **Fix:** cheapest first. **(a)** Dispatch briefs cite the notebook by **absolute path into the main checkout**, not a repo-relative one — the lead knows that path and the worker does not. **(b)** Have the dispatch step copy the relevant `docs/dev-loops/<loop>/` into the worktree, read-only. **(c)** Reconsider whether `**/LAB_NOTEBOOK*.md` should be ignored at all: the stated purpose is a durable cross-session tracker, and untracked files do not survive a fresh clone, a new worktree, or a machine change either. That is a bigger decision than this finding — raise it, do not take it here.
  ⚠️ Do **not** "fix" this by having agents write notebooks into their worktree: gitignored files there are invisible to the merge and would be destroyed with the worktree.
- **Related:** same family as `reference-worktree-gitignored-data-gaps` (a fresh worktree lacks gitignored `data/` and the notebook skip-cache). That entry recorded the data case; this is the tracker case, and the tracker is load-bearing for process memory rather than for a measurement.
- **Cache:** N/A.

---

## AMENDED 2026-08-17 — the tooling half is closed; the finding stays OPEN

**What changed.** `notebook_lib._resolve_repo_relative` short-circuited on `p.exists()`. For a
directory that is the wrong decider: `git worktree add` materialises a loop directory whenever any
sibling in it is tracked — a `goal_prompt_<id>.md` suffices — so the directory exists and holds no
notebook, and the repo-root fallback never fired. It now asks whether the directory **carries a
notebook** (`_carries_notebook`), so `/skeft-qa:notebook` and `extract_frontier` reach the main
checkout from inside a worktree. A path naming a file keeps `exists()`, which for a file is the
same question.

**This explains both halves of the asymmetry recorded above.** `Phase5qT` has no tracked file, so
its directory never materialised, the fallback fired, and Wave T3's writes landed on main.
`D10_Discharge` has one, so its directory did materialise and the read failed. Writes landing while
reads failed was one bug seen from two sides.

**Measured 2026-08-17, corrected the same day.** A notebook is the tracker for a **unit of
development work**; a managed `/goal` loop is the preferred way to run one, not a precondition for
having one. **Notebook homes nest** — when a roadmap grows past what can be reasoned about
correctly, the work splits into a sub-roadmap carrying its own notebook, as `Phase5qH` has done into
`E1_SubstrateG_Topology` … `E5_SubstrateS_Spectral`.

**Twenty-one directories hold notebooks at any depth. Nine are affected** — `D10_Discharge`,
`Phase5qH`, `Phase5qH/E4_GenuineCarrier_Assembly`, `Phase6BA`, `Phase6BB`, `Phase6BC`, `Phase6EA`,
`Phase6EB`, `Phase6EE` — and twelve carry no tracked file, so their directories never materialise
and they were already resolving correctly.

⚠️ A first pass reported eight of fifteen, enumerating with `docs/dev-loops/*/` — one level of
children as a proxy for *notebook homes*. It missed `Phase5qH/E4_GenuineCarrier_Assembly` and every
nested sibling. `.gitignore` matches `**/LAB_NOTEBOOK*.md` at any depth, so any scan of this
population must too: enumerate by finding the notebooks, not by listing a directory.

**Verified against production, not a fixture:** from `.claude/worktrees/wt1`, which holds only
`goal_prompt_20260629T191903.md` under `docs/dev-loops/Phase6BC/`,
`notebook_lib.py check docs/dev-loops/Phase6BC` now reports the live shard size and a stale-FRONTIER
warning. Before, it reported the INDEX absent and advised `notebook new` over a live loop.

### Why this finding is NOT closed, and why its `Verify` cannot pass

The declared `Verify` asserts that `LAB_NOTEBOOK_INDEX.md` **exists inside a fresh worktree**. Re-run
after the fix: still exit 1, and it will stay that way. Only un-ignoring `**/LAB_NOTEBOOK*.md` could
satisfy it, and that is prohibited — the ignore exists to keep private loop content out of public
git.

**The `Verify` asserts a proxy.** File materialisation stands in for the thing that matters, *can an
agent reach the notebook*, and the two come apart precisely because the correct fix routes around
materialisation rather than achieving it.

**Residue, genuinely open:** a **direct file read** from a worktree still finds nothing, so a brief
citing a notebook must still use an absolute path into the main checkout. Closing this finding needs
either a `Verify` re-keyed to the decider, or a mechanism that makes a direct read resolve.
