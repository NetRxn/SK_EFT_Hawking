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

## 2026-06-10 — External-review prose fixes (D2-EV1/SYS-EV4 + D2-Y3)

- Source: (none — direct prose revision per review-2026-06-05 findings)
- Lift action: Prose-revision (direct edit, no content lift)
- Insertion point: abstract + §1 intro + §4 chirality-wall (Pillar 1, bridges) + outlook tracked-hypotheses + bibliography comment block
- Stage-13 redo required: no (framing-precision + epistemic-labeling fixes; no claims added/removed)
- Notes: (1) D2-EV1/SYS-EV4 — Golterman-Shamir framing corrected from "GS no-go theorem" to GS's own conditional-constraints presentation, verified against the cached primary source `Lit-Search/Phase-5e/primary-sources/GoltermanShamir2026.pdf` (arXiv:2603.15985 abstract: "we discuss the conditions for the applicability of the Nielsen-Ninomiya theorem... If these conditions are satisfied, the massless fermion spectrum must be vector-like"). Pillar 1 now states explicitly that GS frame the result as conditions for NN applicability, not a stand-alone no-go; "evading GS" defined as exiting the joint scope of the nine conditions. Five-of-nine violation structure unchanged. Companion docstring fix in `lean/SKEFTHawking/GoltermanShamir.lean` (comments only; module builds green). (2) D2-Y3 — H1-H4 epistemic-status labels added in abstract + outlook §tracked-hypotheses: all four are established algebraic-topology results tracked pending Mathlib formalization, epistemically distinct from the genuinely open TPFConjecture (Lean ground truth verified: H1-H4 live only in `ExtBordismBridge.lean`, consumed only by the bridge theorem `generation_constraint_chain`, not by the kernel-pure Rokhlin headline). pdflatex ×2 clean, 0 undefined refs.

## 2026-06-10 — Prose-revision-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-06-10 freshness reconciliation vs post-2026-05-31 source commits (non-paper10 scope only; paper10 deltas OWNED by active Phase 5q.B session — NOT reconciled here). Real committed deltas inspected: paper7+paper9 (5207b72b, 2026-06-10 13:12 — historical '1 axiom' snapshot prose annotated 'since retired into a tracked Prop / TPFConjecture' at 3+2 sites) and paper8 (3036ffd7, 2026-06-08 — axiomcount{} macro + TPFConjecture reframing; SPTClassification '20 theorems + 1 axiom' -> '20 theorems'). D2 verified ALREADY CONSISTENT with all of these: D2 carries the axiomcount{}/TPFConjecture framing from f6048c48 + 1bb62842 (which edited D2 in tandem), uses counts.tex macros throughout (no stale 4049/2237/170 literals — grep-verified), GoltermanShamir2026 bibitem title matches the corrected CITATION_REGISTRY title ('Symmetric mass generation and the Nielsen-Ninomiya theorem', arXiv:2603.15985), GS conditional-constraints framing present (Pillar 1), Mathlib pin 5e932f97. CHECKs 24/25/26 PASS. Source tables/*.tex + paper_draftNotes.bib mtime drift = recompile noise (git status clean; D2 inputs only ../../docs/counts.tex). ONE bundle edit this event: standard Variant-A 'Methods and tools disclosure' block installed before bibliography per docs/DISCLOSURE_TEXT.md (was clearly absent; register verdict D2=Variant A via scripts/aristotle_usage_by_bundle.py). Boilerplate only — no scientific claims added/removed; stage13 redo NOT required. pdflatex x2 clean (11 pp, 0 errors, 0 undefined refs). freshness_stale deliberately RE-SET to true after this event: paper10 (modified 2026-06-08, RESTRICTED) remains unreconciled pending Phase 5q.B supersession records.
