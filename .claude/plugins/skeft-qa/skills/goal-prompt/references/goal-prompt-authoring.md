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
  turn can re-read them: `roadmap_path` (`docs/dev-loops/<roadmap>/...`) and the lab notebook.

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
4. **Runtime bound.** End with `or stop after N turns` so the loop has a hard ceiling.

## Template

```
GOAL: <one-sentence outcome>. Source-of-truth: <roadmap_path> + <notebook_path> (re-read
them after any compaction). SCOPE IS SETTLED — build the next brick THIS turn; a stop-hook
firing is a GO signal, never a cue to stop/hold/re-scope/hand back. Legitimate stops ONLY:
a kernel-checked no-go, or a genuine user-only decision (ask once, keep shipping meanwhile).
DONE when: (1) <measurable end state>; (2) validate.py prints N/N in the transcript;
(3) the fresh-context skeft-qa:adversarial-reviewer [+ claims-reviewer for papers] ran with
ZERO BLOCKER findings surfaced in the transcript. — or stop after <N> turns.
```

## Anti-patterns (do not write)

- Vibes-based completion ("the physics is right") — not transcript-checkable.
- Open scope ("do the rest of the phase") — that is the *whole wave*, not a `/goal`; pick a
  measurable wave-sized end state.
- Omitting the fresh-context-review criterion (self-audit is insufficient — the
  `qi-gate-5-self-audit-blind-spot` lesson).
