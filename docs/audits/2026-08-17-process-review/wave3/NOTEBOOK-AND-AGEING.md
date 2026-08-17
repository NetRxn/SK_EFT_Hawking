# Worktree notebook-blindness, and the "ages a disclosure into a repair" gap

Two independent questions, each re-derived from the repository directly (git history, live
code execution inside a real worktree, and the finding system's own instrument) rather than
from prior write-ups. Read-only pass; nothing in `SK_EFT_Hawking` was modified.

---

## Question A — was worktree notebook-blindness already fixed?

**Verdict: STILL-LIVE at the root cause, WORKED-AROUND only as a manual dispatch discipline,
and that workaround has a demonstrated hole in its own tooling.**

### What each commit actually did

- **`88e2f434` (filed)** — a `papers/AutomatedReviews/` finding
  (`2026-08-17-worktree-agents-cannot-read-notebooks/infra.md`), MAJOR, lane `infra`. Diagnoses
  that `.gitignore:125` (`**/LAB_NOTEBOOK*.md`) makes notebooks untracked, so `git worktree add`
  never materialises them, while the tooling still *writes* to the main checkout from a worktree
  — writes land, reads fail. Proposes fixes but ships none.
- **`73c04a8d` (documented)** — added `docs/dev-loops/HARNESS_GUIDE.md` §8b and an ownership row
  in `docs/architecture/README.md`. Pure documentation: the mechanics, three dispatch rules
  (absolute-path citation, confirm-before-reporting-absent, never write inside a worktree), and
  an explicitly **undecided** open question ("should these be gitignored at all").
- **`825e88fd` (voice rewrite)** — rewrote §8b and the README row to state mechanism/rule rather
  than incident narrative (per the workspace `CLAUDE.md` voice rule). No behavior change.

**No commit fixes the underlying defect.** `.gitignore:125` is unchanged today —
`**/LAB_NOTEBOOK*.md` still matches, verified by direct read.

### Nothing else landed since 2026-08-14

`git log --since=2026-08-14` filtered on notebook/worktree/gitignore keywords and on the four
relevant paths (`.gitignore`, `HARNESS_GUIDE.md`, `notebook_lib.py`, `lab-notebook.md`) turns up
exactly the three commits above, plus three commits (`bccded2a`, `ffcce32d`, `27a92648`) that
touch `.gitignore`/`HARNESS_GUIDE.md` for **unrelated** reasons (seed-journal residue, an egress
doc retraction) — confirmed by reading each diff; none touches the notebook mechanism.

### The workaround, tested concretely

`notebook_lib.py`'s `_resolve_repo_relative` falls back from a repo-relative path to the main
checkout (`harness_common.repo_root()`) — but **only when the path does not already exist
relative to the caller's cwd**. I ran this from inside a real worktree
(`.claude/worktrees/wt1`, verified via its `.git` gitlink to
`SK_EFT_Hawking/.git/worktrees/wt1`):

```
$ cd .claude/worktrees/wt1
$ python3 .claude/plugins/skeft-qa/scripts/notebook_lib.py check docs/dev-loops/Phase6BC
[notebook check] ok
  ⚠ no LAB_NOTEBOOK_INDEX.md in docs/dev-loops/Phase6BC — run `notebook new` to scaffold it.
  ⚠ no LAB_NOTEBOOK.md in docs/dev-loops/Phase6BC — run `notebook new`.
```

This is a **false negative**, reproduced live: `docs/dev-loops/Phase6BC/LAB_NOTEBOOK_INDEX.md`
exists on the main checkout (confirmed by `find`). The failure mechanism: `docs/dev-loops/
Phase6BC/` is not wholly gitignored — it holds the tracked `goal_prompt_*.md` — so the
*directory* exists in the worktree, `Path(home).exists()` short-circuits `True`, and
`_resolve_repo_relative` never falls back to the main checkout. This is exactly the shape of
the original defect (`88e2f434`'s "writes land, reads fail... an agent consults the tracker,
finds nothing"), reproduced through the tool the "fix" shipped.

By contrast, passing the **exact file path** (not the directory) does trigger the fallback
correctly — `extract_frontier('docs/dev-loops/Phase6BC/LAB_NOTEBOOK_INDEX.md')`, run from the
same worktree cwd, correctly resolved to the main-checkout file and returned its live FRONTIER
content. So the mechanism only rescues a caller that already names the exact notebook file —
which is precisely what §8b's Rule 1 tells a *human dispatcher* to do by hand ("cite the
ABSOLUTE path"), not something the tooling enforces automatically. `/skeft-qa:notebook check`
as normally invoked (home resolved from the marker, a directory) does not get this benefit, as
demonstrated above.

**No live worktree has a notebook.** Checked every directory under `.claude/worktrees/` (`wt1`,
`kzm`, all `redraft-*`, all `rv*`, `subst-ext`, `subst-sixteen`, `mlx-hikappa`, `mathlib-bump`,
`py1`, `py2`, `docs`) — zero `LAB_NOTEBOOK*` files anywhere; the main checkout carries dozens.

### The finding's own state, per the repo's instrument

- `docs/review_finding_supersessions.json` (the only channel that can close a finding, per
  ADR-012) has **zero** records mentioning `2026-08-17-worktree-agents-cannot-read-notebooks`.
- The finding file itself carries **zero** `✅`/`✓` markers on its 1.1 entry (status defaults to
  `open` unless one is present, per `build_graph.py`'s `extract_review_finding_nodes`).
- Its own declared `Verify:` command — create a fresh worktree, `test -f` the D10_Discharge
  notebook index — was run exactly as written and **still exits 1** (notebook invisible) at
  current HEAD.

All three signals agree: **the finding is OPEN**, exactly as filed.

### Residue

The `.gitignore` question §8b explicitly left undecided is still undecided. The only reliable
mitigation in production is a human (or dispatching lead) remembering to embed an absolute
main-checkout path in every worker brief — nothing checks that a brief did so, and the
notebook tooling's own directory-based resolution silently produces false "notebook missing"
reports from inside a worktree, which is the same failure shape the original finding described.

---

## Question B — does an ADR already cover "nothing ages a disclosure into a repair"?

**Verdict: NOT-COVERED.**

### What the candidate ADRs actually own

- **ADR-004 (substrate integrity gates)** and **ADR-007 (kernel no-go ledger)** treat
  *disclosure* as a **terminal, compliant state** — the explicit escape valve from their
  ratchets. ADR-004: "A struct-field/definitional assumption with a complete docstring + a
  ledger entry ... is **compliant, not a defect**." ADR-007: a disclosed no-go is "never to be
  re-derived," full stop. Neither has any notion of a disclosure later maturing into an
  obligation.
- **ADR-016 (apex claims / vacuity registers)** is the same shape: `D5 — The escape from the
  ratchet is DISCLOSURE IN THE CLAIMS STRING, not an exemption.` Disclosing moves a row out of
  the *undisclosed* ratchet population permanently — there is no re-entry, no clock.
- **ADR-005 (derived proof atlas)** explicitly defers to ADR-004 here: an atlas open/UNKNOWN
  node "surfaces, never re-litigates" the disclosure already made under ADR-004/007.
- **ADR-012 (finding lifecycle, routing and closure)** — read in full — governs the lifecycle
  of a **filed `ReviewFinding` only**: emission (reviewer markdown → `extract_review_finding_
  nodes`), routing (`lane`, `blocks`, `target`, `blocked_by`), and closure (the supersession
  ledger, `close_finding.py`). Its one population-level ratchet, **D9**, is a down-only ceiling
  on the count of *already-filed* open REQUIRED/MAJOR findings per bundle — frozen at a
  point-in-time count, not a per-item clock, and it never touches anything that isn't already a
  minted `ReviewFinding` node. D19 ("parked work") is the nearest-sounding mechanism but is the
  opposite direction: it lets **authorized work** wait on an external release condition
  (`run:`/`phase:`/`pub:`/`research:` tokens); it is not a mechanism that promotes a passive
  disclosure into active work.

### Does a disclosure enter the finding lifecycle at all?

No. `mint_finding_id`/`extract_review_finding_nodes` parse only `### N.N — 🔴 …` headings inside
`papers/AutomatedReviews/*.md` review reports (ADR-012 §C3: "three emitters, not five"). A
disclosure living in `constants.py`'s registries (`GATE_EDGE_TYPES_WITHOUT_EMITTERS`,
`MODELING_ASSUMPTION_THEOREMS`, `HYPOTHESIS_REGISTRY`), a scoped check docstring, the QI
register, or `SETTLED_FORKS.md` is never read by that extractor and never becomes a graph node.
`scripts/close_finding.py` writes closures for finding ids that already exist in the graph; it
has no code path that reads a disclosure registry and mints or schedules anything. Grepped both
files for "disclosure" directly: `close_finding.py` — zero hits; `graph_atlas.py` — one hit,
`stale_disclosure` (next section), which checks the disclosure's own factual accuracy, not
whether it should be repaired.

### A live, concrete instance of exactly this gap

`GATE_EDGE_TYPES_WITHOUT_EMITTERS` (`scripts/validation/checks/graph_atlas.py:501`) names three
gate-queried edge types with no emitter — `PRODUCES`, `SUPPORTS`, `CONTRADICTS` — each with a
one-line reason. The `gate_edge_types_are_emitted` check (same file) does exactly two things:

1. Fails if a **new**, undisclosed dead edge type appears (`no_new_dead_edge_type`) — this is
   the ratchet, and it only bounds *new* debt.
2. Fails if a **listed** entry has become stale, i.e. is now actually emitted but still sits in
   the disclosure dict (`stale_disclosure`) — this checks the disclosure's own truth value, not
   whether the underlying gap should be closed.

Neither leg ever requires or schedules fixing `PRODUCES`/`SUPPORTS`/`CONTRADICTS` themselves.
An audit already on record in this same directory (`docs/audits/2026-08-06-e2e-map/
PLANE-publication.md:186`) verified this live and stated it plainly: the check "prevents a 4th
but does not force the 3 closed." That was true on 2026-08-06 and remains true today — those
three disclosures can sit forever with zero pressure toward repair.

### The dashboard's only "age" concept

`scripts/dashboard_attention.py` has exactly one `age`/`age_days` field in the whole file, and
it is scoped to **feed C — blocked operator questions** (`decisions()`, `_age_days(ts, now)`):
a purely informational "how long has this ask been pending" surfaced to shorten operator
latency (ADR-012 D12's stated gap — "not a reader, a latency floor"). It never touches a
disclosure, a filed finding's age, or a registry entry. `docs/architecture/DASHBOARD.md` has no
staleness/escalation concept beyond this. No other surface in the finding system ages anything
by time.

### Corroboration

This audit's own consolidated `FINDINGS.md` (item 9, "Nothing ages a disclosure into a
repair," CONFIRMED) and `wave2/GATE.md` independently reached the identical conclusion, citing
the same `GATE_EDGE_TYPES_WITHOUT_EMITTERS` example and the same notebook finding as
corroborating instances. That write-up explicitly declines to specify a fix and recommends
routing any repair through the `architecture-change` skill as a genuine ADR-shaped design
question — a recommendation this independent pass agrees with.

---

## Summary for the operator

**A.** Worktree notebook-blindness is **STILL-LIVE**, not fixed: `.gitignore` is unchanged, no
worktree has a notebook (checked all of them), the finding's own `Verify:` command still fails,
and the finding carries no closure record. `73c04a8d`/`825e88fd` only documented a manual
absolute-path dispatch discipline — and that discipline's automated fallback has a demonstrated
hole (`notebook check <dir>` from inside a worktree silently reports "missing" for a notebook
that exists on main, reproduced live).

**B.** No existing ADR covers ageing a disclosure into a repair. ADR-004/007/016 treat
disclosure as the terminal compliant state; ADR-012's lifecycle and ratchets govern only
already-filed `ReviewFinding`s and never ingest a disclosure; the one "age" field anywhere in
the finding system times operator-question latency, not disclosure staleness. **NOT-COVERED.**
This is a genuine open design question, not something a fresh reading of the ADRs resolves.
