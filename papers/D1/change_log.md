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

## 2026-06-10 — Source-reconciliation pass post external-review remediation

- Scope: reconcile D1 against the 4 sources flagged by `validate.py --check bundle_source_freshness` after the 2026-06-10 external-review remediation sweep (`da05d435..14c7ee5b` + same-day follow-ups), per the bundle-source-freshness reconciliation task.
- Flagged-source triage (last_lift baseline 2026-05-31T17:24:47Z):
  - `paper12_polariton` — REAL committed content change (`5207b72b`): abstract axiom clause extended to record `gapped_interface_axiom` "since retired into the tracked Prop `TPFConjecture`". D1 counterpart check: D1 carries NO textual project-axiom-count claim (verification counts are macro-driven via `\input{../../docs/counts.tex}`: `\substantivetheorems{}` / `\aristotleproved{}`; every "axiom" mention in D1 prose refers to the SK-EFT physics axioms / `FirstOrderKMS`, not the Lean project-local axiom count). NO residual divergence.
  - `paper4_wkb_connection` — REAL committed content change (`5207b72b`): same axiom-retirement note ("one axiom (`gapped_interface_axiom`; since retired into the tracked Prop `TPFConjecture`, 2026-05-19)"). D1 §4 (WKB) carries no axiom-count claim. NO residual divergence.
  - `paper1_first_order` — mtime-only: sole drifted file `tables/table1_experimental_params.tex`, auto-regenerated byte-identical to committed content (git diff empty; zero commits since last_lift). Bundle does not `\input` source tables. No action.
  - `paper2_second_order` — mtime-only: sole drifted file `tables/table2_hierarchy.tex`, same verification. No action.
- Remediation themes verified already consistent in D1 (bundle was edited in tandem with the sweep): Geurs supersonic-flow scope framing + Majumdar cross-device modeling-assumption disclosure in abstract + Wiedemann-Franz subsection (`c574c1d0`); deterministic 106/114 ≈ 93% theorem-reuse count (`67157912`); theorem-name reference fixes `hawking_universality` + `bp_convergence_iff_ldp_rate_zero` (`5207b72b`). All-occurrence greps clean: no `92%` / `109/119` / "measured at the same device" residue. Vergeles RPA-window and Halenka-Miller attributions: not referenced anywhere in D1 (grep empty).
- CHANGE (only edit this pass): standard AI-disclosure block per `docs/DISCLOSURE_TEXT.md` — **Variant A** (register-derived: `scripts/aristotle_usage_by_bundle.py` verdict D1 aristotle_used=yes, S1 yes / S2 yes, 6 witness modules / 41 witness theorems) — inserted as `\section*{Methods and tools disclosure}` immediately before `\begin{thebibliography}`. Block was clearly absent; no pre-existing ad-hoc AI-disclosure text to normalize (the Aristotle acknowledgements line is tool credit in a Variant-A bundle, consistent). Manuscript content change → `stage13_redo_required=true`.
- Compile gate: `pdflatex` ×2 clean — 0 errors, 0 undefined references, 9 pages.
- Metadata: `freshness_stale` intentionally left `true` and `last_lift` left at 2026-05-31T17:24:47Z per task constraint (final clearance owned by the queued AttributionContentSweep pass); `stage13_redo_required` set `true` for the disclosure-block insertion.

## 2026-06-10 — Prose-revision-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-06-10 source-reconciliation pass post external-review remediation: 4 flagged sources triaged — paper12_polariton + paper4_wkb_connection carry the real committed change (5207b72b axiom-retirement note: gapped_interface_axiom retired into tracked Prop TPFConjecture) with NO D1 counterpart claim (D1 axiom-count prose is macro-driven via counts.tex; all D1 'axiom' mentions are SK-EFT physics axioms); paper1_first_order + paper2_second_order are mtime-only (auto-regenerated tables byte-identical to committed content, zero commits since last_lift). Sweep themes (Geurs scope c574c1d0, 93% reuse 67157912, theorem renames 5207b72b) verified already applied in tandem to D1; Vergeles/Halenka not referenced. Standard DISCLOSURE_TEXT.md Variant A block inserted before bibliography (register-derived; pdflatex x2 clean). stage13_redo_required set true + freshness_stale deliberately retained by the reconciliation session (post-script metadata restore).
