# Bundle E1 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01 — Lift-companion from `paper12_polariton` (§1)

- Source title: Polariton analog Hawking
- Lift action: Lift-companion
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: E1 PRL/PRR experimental letter: Paris-LKB polariton Hawking spectrum + stimulated-Hawking amplification + falsifiable frequency window at LKB device parameters

## 2026-05-06 — Lift-section from `_phase6o_W1a_lean_only` (§3)

- Source title: Boostless / Carrollian soft-theorem program: `SoftTheorems/Boostless.lean` (I...
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1a universal noise floor n_noise/Hawking-flux Wilson-coefficient-independence at Paris-LKB device parameters; falsifiable prediction

## 2026-05-06 — Lift-section from `_phase6o_W1b_lean_only` (§4)

- Source title: G4 Kerr-Schild double-copy on Petrov-D analog gravity
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1b polariton ringdown signature from Kerr-Schild single-copy

## 2026-05-11 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event for Stage-13-sweep freshness cleanup)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-11 Stage-13-sweep freshness cleanup: paper12_polariton tables (3 tables) regenerated at 12:56. E1 bundle paper_draft.tex does NOT \input source paper tables; bundle compile path unaffected. No bundle content change required; last_lift bumped.

## 2026-05-31 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: Freshness-bookkeeping (LATE_PHASE6_ABSORPTION_PROTOCOL §3d case 1): source-paper mtime drift is ENTIRELY from auto-regenerated tables/*.tex artifacts (verified: the only files newer than last_lift in each stale source are tables/*.tex; every source paper_draft.tex mtime is OLD <= last_lift; git status clean so regenerated tables match committed content byte-for-byte = zero content change). Bundle compile path is decoupled: this bundle \input's only ../../docs/counts.tex, never any source-paper tables/ dir. No content lift warranted; no Stage-13 redo; reviewer triple remains valid (bundle stays GREEN).
