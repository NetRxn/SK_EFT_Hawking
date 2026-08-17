# Cluster PLUGIN — the running plugin is not the plugin in git, and nothing says so

Lead-verified, 2026-08-17. This cluster was not raised by wave 1; it surfaced from establishing t0.

## PLUGIN-1 — a session binds its plugin at start and never learns the repo moved

- **Verdict:** CONFIRMED
- **Wave-1 source IDs:** none — found while pinning t0

### Evidence at HEAD

The live process binds one immutable cache directory:

```
ps -p 79295 -o command
  → …/claude --resume=6cf37aa2-… --plugin-dir …/skeft-qa/f33dc0a1b2e5
```

`installed_plugins.json` agrees: `"version": "f33dc0a1b2e5"`, `"gitCommitSha":
"f33dc0a1b2e56f26c397b03e92138e7bf365a73e"`, `"lastUpdated": "2026-08-15T14:44:56Z"`. That cache
holds the only `.in_use` marker (`f33dc0a1b2e5/.in_use/79295`).

Repo HEAD is `4c81c2ec`. Four plugin commits post-date the bound version and have never executed
in this session:

| commit | when | what it changes |
|---|---|---|
| `fd6cac3d` | 08-15 12:02 | `reader_facing_voice` — a paper may not tell the reader it never read a source it cites |
| `e9e5e314` | 08-15 16:24 | teaches the paper agents that the substrate has a TIMELINE, and that a strong-looking theorem can be a posit |
| `c4b1a1ca` | 08-15 16:26 | worker guard asserts the decider (`.lake` is touched), not a flag spelling |
| `f58a3fe4` | 08-17 03:01 | Voice: durable comments state the invariant |

Six files differ between the bound cache and HEAD:

```
diff -rq …/f33dc0a1b2e5 .claude/plugins/skeft-qa --exclude=__pycache__ --exclude=.in_use
  agents/adversarial-reviewer.md
  agents/claims-reviewer.md
  agents/paper-drafter.md
  agents/prose-reviewer.md
  scripts/harness_worker_shell_guard.py
  skills/paper-authoring/references/prohibited-patterns.md
```

### Population

**Four of the six are the paper agents that executed every Stage-10 redraft in the window** — L3,
D2, D3, L2, D1, D4, E1, E2, D6, D8 on Aug 15; D9, D10, D7 on Aug 17. Thirteen bundles.

The inert content is not incidental. Each missing block targets a defect wave 1 measured as
recurring:

| bound version lacks | lines | wave-1 defect it targets | measured recurrence |
|---|---|---|---|
| `paper-drafter` § "The substrate is usually AHEAD of the manuscript" | 71 | briefs asserting stale substrate; agents rediscovering recency | G-02 (6/10), C-06, E-6, H-02 |
| `adversarial-reviewer` § "the manuscript is older than the substrate" + "strong in appearance only" | 48 | review passes that never re-read the source | G-01 (10/10) |
| `claims-reviewer` § "Class SB — superseded backing" | 57 | an entire detection class, absent | G-01, G-07 |
| `prose-reviewer` § roadmap-reading + carrier trap | 19 | uninhabited carriers cited as physics | H-02 |
| `prohibited-patterns` § "never tell the reader you did not read a source you cite" | 23 | citations held as metadata stubs | B-03, B-06, C-08, G-09 |

The worker guard is the same story in miniature. Bound version, line 32:

```python
(r"\bcp\s+-[a-zA-Z]*R[a-zA-Z]*\b[^\n]*\.lake\b", "cache seeding is the orchestrator's"),
```

HEAD, line 37:

```python
(r"\bcp\b[^\n|;&]*\.lake\b", "cache seeding is the orchestrator's"),
```

Every subagent dispatched in this window ran the evadable predicate: `cp -a` names no `R`.

### Already-addressed by

**No.** The commits exist; the mechanism that would make them take effect does not. `git log` on
the plugin path shows the fixes landing; nothing in the tree compares a bound cache SHA against the
repo's plugin HEAD.

### Mechanism

Claude Code resolves `--plugin-dir` once, at process start, from `installed_plugins.json`. Editing
`.claude/plugins/skeft-qa/` in the repo changes the *source*; it does not change the *bound copy*,
and a long-lived resumed session can outlive many commits to that source.

**The refresh procedure is not the gap — the trigger is.** `docs/dev-loops/HARNESS_GUIDE.md` §7
documents the refresh (`claude plugin update skeft-qa@skeft-local --scope local`, then restart), and
its troubleshooting table lists three triggers for running it: `command not found` on a
`/skeft-qa:*` invocation (line 92), a skill printing `UNRESOLVED` (line 93), and the bare `/goal-prompt`
alias erroring where the namespaced form works (line 94). **Every listed trigger is a loud failure.**
The failure actually observed is silent: the agents load, run, and return well-formed work — they
merely lack a section that was added after the bind. A cache that is stale only in *guidance* is
behaviourally indistinguishable from a current one, so no trigger in the table ever fires.

This is the exact defect class ADR-014 names for citations: *holding a cache file is not holding the
source*. The plugin cache is an uncovered instance of the repo's own rule.

### Remediation blast radius

Small, and the insertion point already exists.

`harness_reinject.py` (`SessionStart`, `source ∈ {compact, resume}`) already emits exactly this shape
of nudge for a different staleness — `drift_note()` compares `harvest_state.last_run_ts` against a
cadence and appends a one-line warning. A plugin-version note is the same pattern:

- read `gitCommitSha` for the bound install from `~/.claude/plugins/installed_plugins.json`
- compare against `git log -1 --format=%H -- .claude/plugins/skeft-qa/` in the resolved repo root
- if behind, append one line naming the commit count and the §7 refresh command

Touches: one pure function plus its call site in `harness_reinject.py`; one unit test beside
`drift_note`'s (`.claude/plugins/skeft-qa/tests/test_harness_core.py`); one row in HARNESS_GUIDE §7's
trigger table for the silent case. Fail-open, consistent with every other hook in that file.

⚠️ **Bootstrap caveat, and it must be stated rather than discovered.** The detector ships *inside the
plugin*, so the session that most needs it is the one that cannot run it. Adding it fixes every
session after the next refresh and does nothing for the current one. That is not a reason to place
it elsewhere — it is a reason to pair shipping it with a refresh.

### Recurs on the next bundle?

**YES, and it is currently active.** D11, I2, I3, D12 and F are still to run, and as of now they
will run the same inert agents. The recurrence is not probabilistic — it is certain until either the
session restarts or a drift detector exists.
