# Bundle D2 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-04 — Lift-letter from `paper10_modular_generation` (§2)

- Source title: Modular generation constraint
- Lift action: Lift-letter
- Insertion point: §2
- Stage-13 redo required: yes
- Notes: L2 PRL splash already extracted from this source; D2 §2 is the FULL derivation including Ext^n_{A(1)}(F2,F2) computation + change-of-rings discharge of H2

## 2026-05-04 — Lift-section from `paper9_sm_anomaly_drinfeld` (§3)

- Source title: SM anomaly + Drinfeld center
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: Z16 anomaly + minimum Drinfeld center anchor (Z(Vec_Z2) toric code only); D4 §4 owns full Z(Vec_S3) + D(G) Hopf

## 2026-05-04 — Lift-section from `paper7_chirality_formal` (§4)

- Source title: Chirality formal
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: Pillar 1: GS no-go conditions formalized + TPF evasion; reorganized as part of three-pillar synthesis with paper8

## 2026-05-04 — Lift-section from `paper8_chirality_master` (§4)

- Source title: Chirality master
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: Pillars 2+3 + bridges + master TPF-evasion + 1+1D/2+1D gapped-interface evidence; merges with paper7 content under unified §4

## 2026-05-06 — Lift-section from `_phase6n_W1b_lean_only` (§3)

- Source title: SymTFT audit substrate
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W1b SymTFT audit substrate cross-bridge (DrinfeldCenter/Witt class/categorical cc additivity)

## 2026-05-06 — Lift-section from `_phase6o_W2a_lean_only` (§3)

- Source title: APS-η for analog horizons
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W2a APS-η Witten-Yonekura η/16 mod 1 cross-bridge to Z₁₆ Dai-Freed

## 2026-05-11 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event for Stage-13-sweep freshness cleanup)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-11 Stage-13-sweep freshness cleanup + inline-absorption-record: paper7_chirality_formal/paper_draft.tex edited 2026-05-11T09:50 + paper8_chirality_master/paper_draft.tex edited 2026-05-11T09:51 (substantive paper-draft edits, contents not diff-able without git). D2 own paper_draft.tex edited at 09:58 directly after, content-aligned at §4 (Pillar 1 / 2+3 paragraphs grep-verified: Golterman-Shamir, TPF, Drinfeld doubles, Steenrod A(1), FK gapped-interface). Today's 09:58 D2 edit was effectively an inline absorption that bypassed the formal bundle_append.py cycle; this event formally records that absorption. Also auto-regenerated tables across the source-paper tree at 12:56 (see D1 event).

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper7_chirality_formal + paper8_chirality_master + paper10_modular_generation abstracts + body + conclusions had primacy framing rewritten to descriptive prose ('We present a formal verification of X' rather than 'the first formal verification of X'); Steenrod Ext + FK gapped-interface + Onsager-algebra wording softened. D2 bundle own draft Onsager paragraph also rewritten (dropped 'to our knowledge the first formalisation of the Onsager algebra' hedge). D2 bundle content remains aligned (paper7/paper8 absorbed material in D2 §4 unchanged in substance).

## 2026-05-31 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: Freshness-bookkeeping (LATE_PHASE6_ABSORPTION_PROTOCOL §3d case 1): source-paper mtime drift is ENTIRELY from auto-regenerated tables/*.tex artifacts (verified: the only files newer than last_lift in each stale source are tables/*.tex; every source paper_draft.tex mtime is OLD <= last_lift; git status clean so regenerated tables match committed content byte-for-byte = zero content change). Bundle compile path is decoupled: this bundle \input's only ../../docs/counts.tex, never any source-paper tables/ dir. No content lift warranted; no Stage-13 redo; reviewer triple remains valid (bundle stays GREEN).
