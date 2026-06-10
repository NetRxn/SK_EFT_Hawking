# Bundle D4 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-31 — Stage-13 finding remediation: RED → 🟢 GREEN

Closed the 4 pre-existing open findings that held D4 at 🔴 RED in the readiness heatmap (the bundle aggregates findings from its source papers; these had never been recorded in the supersession ledger even though `bundle_metadata.json` read green):

- **MAJOR (blocker) — `review:2026-05-11-1251-bundle-stage13:L2:1.3` (CitationIntegrity):** FIXED. `Kitaev2009` registry `used_in` was `[paper18, L2]`; completed to all four actual consumers (D2, L2, paper10_modular_generation, paper18_doublon_gate), verified by `grep -rlE 'cite\{[^}]*Kitaev2009'`. (`src/core/citations.py`.) Also clears the same finding for D2 and L2.
- **minor — `…I2:4.1` (CrossPaperConsistency):** ACCEPTED — identical Turaev book, cosmetic bibitem variance; full unification is a flagship-bibliography task.
- **minor — `…paper18_doublon_gate:5.2` (LeanProofSubstance):** ACCEPTED — `geometric_phase_minus_one_on_pi_loop` name is defensible (the conjunction establishes the −1 geometric phase).
- **minor — `…paper18_doublon_gate:2.1` (ParameterProvenance):** ACCEPTED — symbolic-parameter paper; provenance genuinely N/A.

All four recorded in `docs/review_finding_supersessions.json`. Post-remediation: D4 open=0, blockers=0 → 🟢 GREEN. (Side effect: D2, L2, I2 also cleared their shared findings.) Pre-existing source-paper freshness (paper11 modified 2026-05-29) is a separate D.2/D.3 content-absorption matter, not a review-finding blocker.

## 2026-05-06 — Lift-section from `_phase6n_W1b_lean_only` (§3)

- Source title: SymTFT audit substrate
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W1b DrinfeldCenter / DeligneTensor / FreeKLinear / PseudoUnitary / categorical cc additivity (Mathlib-grade in-program builds; longest verified math chain extension)

## 2026-05-06 — Lift-section from `_phase6o_W1a_lean_only` (§6)

- Source title: Boostless / Carrollian soft-theorem program: `SoftTheorems/Boostless.lean` (I...
- Lift action: Lift-section
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1a Lindbladian S-matrix axiomatization NO-GO joining D4's NO-GO landscape (KMS-broken regime; cross-bridge to bootstrap-uniqueness NO-GO at structural amplitude level)

## 2026-05-06 — Lift-section from `_phase6o_W3a_lean_only` (§8)

- Source title: G10 ETH-α productive-value refutation tableau: `ETH/Predicates.lean` (5 candi...
- Lift action: Lift-section
- Insertion point: §8
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W3a G10 ETH-α refutation tableau (3 concrete refutation theorems: Inozemcev-Volovich gap, ETP doesn't imply Srednicki, free-cumulant doesn't imply Srednicki); RT/CH Phase 6c W5 cross-bridge

## 2026-05-11 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event for Stage-13-sweep freshness cleanup)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-11 Stage-13-sweep freshness cleanup: paper11_quantum_group/tables/table1_chain.tex regenerated at 12:56. D4 bundle paper_draft.tex does NOT \input source paper tables; bundle compile path unaffected. No bundle content change required; last_lift bumped.

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper11_quantum_group abstract + introduction + conclusions rewritten (multiple primacy claims removed including 'first quantum group library', 'first verified MTC instances', 'first Hopf algebra', 'first parameterized quantum group definition' - replaced with descriptive content); paper14_braided_mtc title changed ('First Formally Verified ...' -> 'Formally Verified ...'), abstract + body + conclusion rewritten to descriptive; paper16_wrt_tqft title changed ('The First Formalization of the' -> 'A Formalization of the'), abstract + body + conclusion rewritten.

## 2026-05-23 — Lift-section from `_phase6p_W2cd_lean_only` (§9)

- Source title: F.21 Fibonacci-anyon density in SU(2) reduced to UNCONDITIONAL closure
- Lift action: Lift-section
- Insertion point: §9
- Stage-13 redo required: yes
- Notes: Late absorption: Phase 6p F.21 unconditional density via Cartan v4 IFT 3-direction discharge (Trotter limit + linftyOp absolute SU(2) bound)

## 2026-05-23 — Lift-section from `_phase6t_lean_only` (§9)

- Source title: Quantitative Solovay-Kitaev length bound + Lean-extracted reference compiler...
- Lift action: Lift-section
- Insertion point: §9
- Stage-13 redo required: yes
- Notes: Late absorption: Phase 6t Dawson-Nielsen quantitative SK length bound + Lean-verified reference compiler skeleton + Path A constructive variant

## 2026-05-23 — Stage 10.E manual prose authoring (§9)

- Source: authored fresh as synthesis-driven new composition (no per-paper-draft source)
- Lift action: Stage10E-prose-authoring
- Insertion point: §9 (BEFORE bibliography; supersedes the two post-bibliography D.4 sourceless skeletons)
- Stage-13 redo required: yes
- Notes: User-authorized 2026-05-23 (originally deferred as non-autonomous per roadmap §17.3). Unified §9 "Fibonacci-anyon density and quantitative Solovay--Kitaev compilation" authored with five subsections (~3500 words LaTeX): F.21 density (Phase 6p), Dawson--Nielsen quantitative length bound (Phase 6t Wave 6), eight-module Lean pipeline, Path A constructive variant + tight-ε calibration disclosure, status + cross-bundle bridges. Three new bibitems added: AharonovArad2017, DawsonNielsen2006, KitaevShenVyalyi2002. The two post-bibliography skeletons (formerly at lines 947+960) reduced to bookkeeping audit pointers; conventional pre-bibliography section placement adopted. LaTeX compile clean (27pp / 368224B). Calibration disclosure honest: Path A unconditional on loose-ε regime + structural K_huge witness; tight-ε regime gated on Mathlib-PR-quality BCH cubic tightening (320·δ³ → ~140·δ³) deferred. Stage 9/10/13 reviews now unblocked; primary-source cache files for the 3 new bibitems are a separate follow-up before Stage 13.

## 2026-05-23 — Bundle D4 CLOSED at GREEN (Stage 9/10/13 round-2 cycle)

- Lift action: Stage9-Stage10-Stage13-close-out
- Insertion point: (n/a — review cycle, not content lift)
- Stage-13 redo required: no
- Notes: 2026-05-23 closeout cycle following the Stage 10.E §9 prose ship + Phase 6t Path A Option C unconditional discharge.
  - **Stage 9 (figures):** GREEN vacuous-PASS. D4 paper has 0 \includegraphics + 0 figure envs; figures/ dir empty by design. All 12 source papers audited; no source-side figure load-bearing for D4 anchors. Report: papers/D4/figures/figure_review_report.json.
  - **Stage 10 (claims, round 4):** GREEN-with-advisories. 34 sentences walked in new §9 (lines 823-1207); 21 PASS, 8 WARN, 1 INFO, 4 TRANSITION, 0 FAIL. All 11 load-bearing Phase 6t Lean theorem names verified by direct grep against `lean/SKEFTHawking/FKLW/` source. Commit SHAs `5eaa861` + `0ec1522` verified. Round-3 reconciliation: 4 prior advisories superseded (r2:3 QEC un-prefix + r3:5/6/7 ABSORB_STUBs). 5 new advisories raised; 4 of 5 FIXED in the round-4 fix-pass below.
  - **Round-4 fix-pass (advisory):** Applied fixes to fu:D4:r4:1+2 (LoC undercount — §9.3 total 2000→5640 + per-module Waves 2/4/5/Path A updated to actual wc -l: 762/852/504/2565), fu:D4:r4:3 (TN skLengthAtEpsilon case-ambiguity disambiguated to Prop SkLengthAtEpsilon + theorem skLengthAtEpsilon_unconditional), fu:D4:r4:4 (HD gapped_interface_axiom stale-name FIXED across 4 sites: abstract line 62, §8.5 heading + body lines 758-779, §9.3 footer lines 1043-1049, §9.5 axiom-inheritance paragraph 1204-1213 — now correctly reports project axiom count = 0 with TPFConjecture tracked-Prop replacement per 2026-05-19 SPTClassification.lean Phase 5h Wave 1 refactor).
  - **Stage 13 (adversarial, round 2 fresh-context):** GREEN-with-advisories. 0 BLOCKER, 0 REQUIRED, 1 RECOMMENDED (Lemma~6 vs 6.1 cosmetic — FIXED at line 900 in fix-pass), 4 ADVISORY (1 new Gate-3 K_huge factor descriptive drift — FIXED at line 1098 in fix-pass with explicit derivation; 3 carryover cross-bundle reciprocity advisories — r2:1, r2:4, r4:5 — all out-of-scope for D4-side revision). Independent verification confirmed: 17/17 bibkeys; 11/11 Lean theorem bodies (substantive, non-placeholder); all numerical constants; primacy claim verbatim-backed by Lit-Search/Phase-6t scan; counts.json axioms:[] confirmed; validate.py --check bundle_consistency PASS.
  - **Final bundle state:** stage9_status=green, stage10_status=green, stage13_status=green, stage13_redo_required=false, blockers_open=0, advisories_open=3 (all three are cross-bundle reciprocity carryovers needing D3/F-side revisions). LaTeX compile clean (28pp / 377844B). lake build 8627 jobs clean.
  - **Effort:** ~1 day (post-Phase-6t-Path-A-discharge ship). Phase 7f.
  - **QI candidate emitted:** validate.py --check bundle_reciprocity to auto-track cross-bundle one-sidedness across revisions in BUNDLE_READINESS_HEATMAP.md (the 3 residual advisories are all of this class).
  - **Review docs:** papers/D4/figures/figure_review_report.json + papers/D4/claims_review.json (round 4) + papers/AutomatedReviews/2026-05-23-bundle-stage13/D4.md.

## 2026-05-31 — Inline-absorption-record (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Inline-absorption-record
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: D8 cross-bridge absorption 2026-05-31: D4 paper_draft.tex edited to re-point/cross-reference the new D8 bundle (verified-quantum-compilation corpus). D4 retains Fibonacci/topological anchor; D6 consumes D8's SK primitive. Scoped adversarial re-check of the new cross-bridge paragraph only (additive cross-ref to already-GREEN D8).

## 2026-06-10 — Prose-revision-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: Source-paper reconciliation vs last_lift 2026-05-31: 3 flagged sources (paper11_quantum_group, paper18_doublon_gate, paper9_sm_anomaly_drinfeld) all carry REAL commits, not mtime noise — commit 5207b72b (2026-06-10) axiom-prose fixes ('1 axiom' -> retired into tracked Prop TPFConjecture) in all three drafts, plus commit 8b68fe13 paper11 tables/table1_chain.tex SU2kSMatrix.lean theorem-count regen 18->253. D4 prose verified already aligned: axiom posture fixed across D4 on 2026-05-23 (fu:D4:r4:4; abstract + section 8.5 + 9.3 + 9.5 all read 'zero project-local axioms' + TPFConjecture); D4 contains zero SU2kSMatrix per-module-count references and zero \input of source-paper tables (compile path decoupled). No content lift required. Disclosure block (DISCLOSURE_TEXT.md Variant B, register-verified aristotle_used=no) installed in same session as a separate draft edit; pdflatex x2 clean (31pp). freshness_stale deliberately NOT cleared per reconciliation-task constraint.

## 2026-06-10 — Standard AI-disclosure block installed (draft edit, non-substantive)

- Source: (none — DISCLOSURE_TEXT.md application)
- Edit: `\section*{Methods and tools disclosure}` (Variant B — register-derived `aristotle_used=no` per `scripts/aristotle_usage_by_bundle.py` 2026-06-10 run) inserted immediately before `\begin{thebibliography}{99}` (paper_draft.tex ~l.1391). No pre-existing ad-hoc disclosure text existed; nothing normalized away.
- Substantive prose: UNCHANGED — no claims, counts, citations, or Lean references touched; stage13_redo_required remains false.
- Compile gate: pdflatex ×2 clean, zero errors (31pp / 394440B).
- Metadata note: the Prose-revision-bookkeeping event above auto-bumped `last_lift` and cleared `freshness_stale`; both fields were deliberately restored (`last_lift=2026-05-31T15:37:22Z`, `freshness_stale=true`) per the reconciliation-task constraint that the staleness signal must persist.
