# Goal-prompt authoring discipline

How to compose the native `/goal` **condition** (the string passed to `/goal`). Loaded on
demand by the `goal-prompt` skill at launch.

## Hard constraints

- **≤ 4,000 characters.** The condition is the native `/goal` Stop-hook condition; it has a
  hard length cap (goal.md).
- **Transcript-evaluable ONLY.** After every turn the condition + conversation go to a small
  fast evaluator (Haiku default) that **cannot run tools** — it judges only what is *surfaced
  in the transcript*. So every completion criterion must be demonstrable as text in the
  transcript. "validate.py prints 43/43 in the transcript" is checkable; "the code is correct"
  is not.
- **Self-describing.** Name the **tracked** source-of-truth paths so a fresh post-compaction
  turn can re-read them: `roadmap_path` (`docs/dev-loops/<roadmap>/...`) and the lab-notebook
  **INDEX** (`<home>/LAB_NOTEBOOK_INDEX.md` — the entry point; its FRONTIER + DECISIONS blocks are
  the re-grounding read, shards are opened on demand).
- **DURABLE CONTENT ONLY — never mutable tactical state (the #1 authoring failure).** The
  condition is re-stated to the model **every single turn** by native `/goal` (we ship no Stop
  hook of our own — native `/goal` owns continuation), and it is also pinned at the top of the
  SessionStart re-injection. So **anything in it is asserted as "live" on every turn forever.**
  That is fine for DURABLE facts (the success criteria; settled locks / non-negotiables; the
  source-of-truth paths) — they don't change. It is **toxic** for MUTABLE tactical state, which
  goes stale within turns and then re-seeds whatever it names:
  - **FORBIDDEN in the condition:** the current sorry line/number, "close-path engines: X/Y/Z",
    which lemma/route is "live" or "the breakthrough", current commit SHAs, "NEXT BRICK", progress
    framing ("one brick from closing"). These are **mutable** — the moment the proof moves, the
    condition is lying, and native `/goal` keeps re-injecting the lie every turn, **out-ranking**
    the lower-priority SETTLED_FORKS / PRE_DECISIONS reads. **Worked failure mode:** a condition
    baked `Close-path engines: <lemmaA> + <lemmaB>` (the routes that looked live when it was
    authored); a later turn proved those routes dead and recorded them in `SETTLED_FORKS.md`, but
    the condition kept re-injecting them as the live close-path every turn — out-ranking the
    recorded ban — so an entire multi-commit session was built on the dead route before it was
    caught and reverted.
  - **Where mutable state lives instead:** the **live probe** `scripts/repo_state_probe.py`
    (recomputes the *real* current sorry + committed engines fresh each turn — run as FIRST_ACTION),
    `docs/dev-loops/SETTLED_FORKS.md` (dead/banned/superseded routes), and the lab-notebook FRONTIER
    (the loop's own next-brick, which the loop updates). The condition POINTS at these; it never
    snapshots them.
  - **Naming a route is allowed ONLY to BAN it** (a durable lock: "never re-open Route C"), never
    to PROMOTE it as the live close-path (mutable). Prefer "see SETTLED_FORKS.md" over inlining.

## What the condition must contain

1. **Posture (anti-escape).** State plainly: *scope is settled; build the next brick; a
   stop-hook firing is a GO signal, never a cue to stop/hold/re-scope; legitimate stops =
   a kernel-checked no-go or a genuine user-only decision.* This is the in-condition defense
   the evaluator re-reads every turn.
2. **One measurable end state with a transcript-visible check.** e.g. "the wave's bricks are
   shipped (kernel-pure, zero new sorry/axiom), `validate.py` prints N/N in the transcript,
   and the theorem/brick count reached <target>."
3. **GAP-B acceptance criterion (mandatory).** "NOT complete until the
   `skeft-qa:adversarial-reviewer` (and `skeft-qa:claims-reviewer` for paper-shaped output)
   ran in a **fresh context** with **zero BLOCKER findings, surfaced in the transcript**."
   Because the evaluator judges only the transcript, the loop cannot mark itself complete
   until that review evidence is literally present. (`/skeft-qa:wave-close` is the explicit
   companion path; this bakes the same bar into `/goal` itself.)

## Template

```
GOAL: <one-sentence outcome>. Source-of-truth: <roadmap_path> + <notebook_index_path> (re-read
the roadmap + the notebook INDEX after any compaction; open shards on demand). SCOPE IS SETTLED —
build the next brick THIS turn; a stop-hook
firing is a GO signal, never a cue to stop/hold/re-scope/hand back. Legitimate stops ONLY:
a kernel-checked no-go, or a genuine user-only decision (ask once, keep shipping meanwhile).
DONE when: (1) <measurable end state>; (2) validate.py prints N/N in the transcript;
(3) the fresh-context skeft-qa:adversarial-reviewer [+ claims-reviewer for papers] ran with
ZERO BLOCKER findings surfaced in the transcript.
```

## Anti-patterns (do not write)

- **Mutable tactical state in the condition** — current sorry line, "close-path engines: …",
  the "live"/"breakthrough" lemma, commit SHAs, "NEXT BRICK", "one brick from closing". It is
  re-injected EVERY turn by native `/goal`, goes stale the moment the proof moves, and re-seeds
  whatever route it names — out-ranking SETTLED_FORKS/PRE_DECISIONS (this has cost an entire
  session built on a route that was already recorded as dead).
  Tactical state belongs in the live probe (`repo_state_probe.py`) / `SETTLED_FORKS.md` / the
  notebook FRONTIER. The condition points at them; it never snapshots them. **Test before writing
  each line: "will this still be true in 30 turns?" If no, it does not go in the condition.**
- Vibes-based completion ("the physics is right") — not transcript-checkable.
- Open scope ("do the rest of the phase") — that is the *whole wave*, not a `/goal`; pick a
  measurable wave-sized end state.
- Omitting the fresh-context-review criterion (self-audit is insufficient — the
  `qi-gate-5-self-audit-blind-spot` lesson).
