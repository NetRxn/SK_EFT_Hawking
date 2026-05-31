# Bundle D1 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-04 — Lift-section from `paper1_first_order` (§2)

- Source title: First-order dissipative analog Hawking
- Lift action: Lift-section
- Insertion point: §2
- Stage-13 redo required: yes
- Notes: First-order SK-EFT corrections + CGL FDR derivation + parity alternation; BEC fiducial setup

## 2026-05-04 — Lift-section from `paper2_second_order` (§3)

- Source title: Second-order SK-EFT
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: Second-order: positivity-forced relations + KMS optimality + transport coefficient counting

## 2026-05-04 — Lift-section from `paper4_wkb_connection` (§4)

- Source title: Exact WKB connection
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: Exact WKB connection formula with three non-perturbative effects (broken unitarity, FDR-mandated noise floor, spectral floor 6 T_H)

## 2026-05-04 — Lift-companion from `paper12_polariton` (§6)

- Source title: Polariton analog Hawking
- Lift action: Lift-companion
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: Polariton Tier-1 platform predictions; stimulated-Hawking amplification; companion to E1 PRL letter (already shipped GREEN 2026-05-04)

## 2026-05-04 — Lift-companion from `paper16_graphene_sk_eft` (§7)

- Source title: Graphene Dirac-fluid SK-EFT
- Lift action: Lift-companion
- Insertion point: §7
- Stage-13 redo required: yes
- Notes: Graphene Dirac-fluid Hawking; 92% Lean theorem reuse; W-F violation; closed-form noise from Keldysh FDT + Landauer-Buttiker; companion to E2 PRL letter (already shipped GREEN 2026-05-04)

## 2026-05-06 — Lift-section from `_phase6n_W1a_lean_only` (§3)

- Source title: BEC SK-EFT geometric envelope (NOT Gevrey-1)
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W1a kinematic-dispersive geometric envelope (NOT Gevrey-1); IsGeometric predicate; closed-form γ_n

## 2026-05-06 — Lift-section from `_phase6n_W2c_lean_only` (§5)

- Source title: LDP linear-response framework
- Lift action: Lift-section
- Insertion point: §5
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W2c FDR W-form GC + abstract IsLDPRateFunction; LinearResponseRateFunction

## 2026-05-06 — Lift-section from `_phase6n_W2b_lean_only` (§6)

- Source title: Quantum Crooks no-go (Perarnau-Llobet)
- Lift action: Lift-section
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W2b BEC + polariton quantum-Crooks landscape; Perarnau-Llobet typeclass connections

## 2026-05-06 — Lift-section from `_phase6o_W1a_lean_only` (§6)

- Source title: Boostless / Carrollian soft-theorem program: `SoftTheorems/Boostless.lean` (I...
- Lift action: Lift-section
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1a boostless / Carrollian soft theorems on BEC + polariton; Strominger-triangle closure

## 2026-05-11 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event for Stage-13-sweep freshness cleanup)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-11 Stage-13-sweep freshness cleanup: auto-generated tables in paper1_first_order, paper2_second_order, paper12_polariton (and 1 more) regenerated today by render_paper_tables.py at ~12:56 local. D1 bundle paper_draft.tex does NOT \input source paper tables (only \input{../../docs/counts.tex}); regenerated source-side tables are decoupled from bundle compile path. No bundle content change required; last_lift bumped to acknowledge source-mtime drift is benign.

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper1_first_order abstract ('first systematic computation' -> 'a systematic computation'), paper2_second_order conclusion ('first formally machine-verified' -> 'formally machine-verified'), paper16_graphene_sk_eft two experimental physics claims softened ('first measurement' / 'first observation' -> 'a measurement' / 'an observation'). No claims added; no numerical results changed.

## 2026-05-31 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: Freshness-bookkeeping (LATE_PHASE6_ABSORPTION_PROTOCOL §3d case 1): source-paper mtime drift is ENTIRELY from auto-regenerated tables/*.tex artifacts (verified: the only files newer than last_lift in each stale source are tables/*.tex; every source paper_draft.tex mtime is OLD <= last_lift; git status clean so regenerated tables match committed content byte-for-byte = zero content change). Bundle compile path is decoupled: this bundle \input's only ../../docs/counts.tex, never any source-paper tables/ dir. No content lift warranted; no Stage-13 redo; reviewer triple remains valid (bundle stays GREEN).
