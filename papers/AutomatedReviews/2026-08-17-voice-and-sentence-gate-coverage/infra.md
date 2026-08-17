---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-17T00:00:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# Two prose gates miss populations they were built to cover

## Summary

**2 MINOR.** Both surfaced during D7's Stage-10 revision, both confirmed by executing the
gate rather than reading it.

`bundle_reader_facing_voice` **does** descend into LaTeX macro arguments — established by
injecting `"an earlier draft of this paper omitted"` into a `\figuredeferred` second
argument and observing the gate fire and name the line. The scope is right; the pattern set
is short.

### 1.1 — 🟡 MINOR — `_SELF_NARRATION` does not cover "blocked on our own unfinished work"

- **Severity:** MINOR
- **Lane:** infra

**Where:** `scripts/validation/checks/` — the ten `_SELF_NARRATION` patterns behind
`bundle_reader_facing_voice`.

Passages of the shape *"blocked only on drawing time"*, *"blocked on a small enumeration
script … that does not exist yet"* and *"so the deeper panel cannot be drawn honestly yet"*
render to a referee and none of the ten patterns matches them. They are the same class the
gate exists to stop — the paper narrating its own unfinished diligence — differing only in
naming a missing artifact of ours rather than a correction we made.

**Bar:** a pattern covering "blocked on / pending / awaiting" + our own artifact, with the
new pattern's non-vacuity proved by seeding one of these exact strings into a production
draft (CHECK_AUTHORING_GUIDE §2.4) rather than a fixture.

Verify: `cd "$REPO" && uv run python scripts/validate.py --check bundle_reader_facing_voice`

*What it asserts:* today it passes a draft carrying "blocked only on drawing time"; after
the fix that draft is red.

### 1.2 — 🟡 MINOR — `bundle_sentence_length` counts a `tikzpicture` body as one sentence

- **Severity:** MINOR
- **Lane:** infra

**Where:** the macro-blanking path in `bundle_sentence_length`.

A `tikzpicture` body has no sentence-ending punctuation, so the whole picture joins into one
run — a 133-word "sentence" of drawing commands no reader parses — and pushes the down-only
over-100 ratchet. The check already solves exactly this for tables via its `_rows_as_sentences`
clause; picture environments have no counterpart, so drawing a figure raises a prose ratchet.

This is a **ratchet-integrity** defect, not a cosmetic one: it charges prose debt for
non-prose, so the only ways to keep the ratchet green are to not draw figures or to move
drawing commands to the preamble. The gate should not price a figure as prose.

**Bar:** a `tikzpicture` (and `pgfplots`) clause parallel to the tabular one, with the
ratchet re-derived downward in the same commit if it drops.

Verify: `cd "$REPO" && uv run python scripts/validate.py --check bundle_sentence_length`

*What it asserts:* the over-100 count does not move when a draft gains a picture environment.
