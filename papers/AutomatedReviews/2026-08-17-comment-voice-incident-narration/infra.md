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

# Durable code comments narrate incidents where they should state the rule

## Summary

**1 MINOR.** Workspace `CLAUDE.md` § Voice requires a source-of-truth artifact — including a
durable code comment — to state the mechanism and the rule rather than recount the incident
that produced it. A scan of `scripts/`, `tests/`, `src/` and the plugin's `scripts/` finds
**61 comment or docstring lines across 34 files** carrying incident-narration markers
(`previously asserted`, `used to read`, `an earlier version`, `the old form`, `was wrong`,
`Found by … audit`).

The population is **not uniformly defective**. Some of these lines correctly name a
superseded formula as a standing rule ("the ln(2/X) form is superseded; a draft carrying it
must change"), which is exactly what the Voice rule asks for. Distinguishing those from
genuine narration requires reading each comment against the code it sits on. **Do not
regex-sweep this.**

## Why it matters beyond style

A comment in this register can carry a *false* claim in the reassuring direction and be
believed because it reads as settled history. `scripts/seed_journal.py`'s module docstring
asserted that the graph extractor refuses to mint a marker-bearing finding — the opposite of
what `scripts/build_graph.py` documents and the code does — and that claim survived into the
`_require_marker` error message. Both were corrected on 2026-08-17 and the behaviour is now
pinned by `tests/test_build_graph.py::TestSeedMarkerDoesNotSuppressMinting`. That instance is
closed; the class is what this finding tracks.

### 1.1 — 🟡 MINOR — durable comments carry incident narrative instead of the invariant

- **Severity:** MINOR
- **Lane:** infra

**Where:** 34 files; heaviest concentrations are
`scripts/validation/checks/bundles_readiness.py` (8 lines), `src/core/citations.py` (5),
`src/core/constants.py` (4), and `scripts/readiness_gates.py`,
`tests/test_d5_bundles_readiness.py`, `tests/test_build_graph.py`,
`scripts/validation/checks/physics.py` (3 each).

**Bar:** each comment either (a) states an invariant, why the asserted predicate is the
decider, and — where a reader needs the evidence — a path to the finding; or (b) is removed.
Dates, agent attribution, discovery narrative and "an earlier version was wrong" belong in
the finding, the QI register or git history.

**Out of scope:** comments whose subject genuinely *is* a superseded artifact, where naming
the superseded form is the operative instruction.

Verify: `cd "$REPO" && grep -rEn --include='*.py' '(previously (asserted|read|required|emitted|counted)|used to (read|be|assert|build|glob)|an earlier version|the old (leg|form|expression|way|glob)|was wrong|Found by .* audit|self-disclosed)' scripts tests src .claude/plugins/skeft-qa/scripts | wc -l`

*What it asserts:* reports 61 at HEAD. This count is a **scan, not a defect count** —
closure requires a per-comment disposition, not driving the number to zero.
