# Meta-process Quality Improvement Register

**Auto-generated:** 2026-04-28T23:58:39+00:00
**Generator:** `scripts/qi_register.py`
**Reads from:** current ReviewFinding graph nodes + this file's `## Closed Items` section for status continuity

This is the Stage 14 (advisory) register. Each QI item is a **process-level** issue — a failure class that has affected multiple papers or indicates a pipeline gap — not a paper-local issue. Stage 13 (adversarial review) surfaces paper-level issues; Stage 14 aggregates those into process improvements. Stage 14 never blocks submission; items here feed remediation waves.

## Summary

- **411** ReviewFinding nodes currently in the graph
- **22** QI items tracked (9 manually-curated open + 13 closed via `## Closed Items` section)
- **9** open, **13** closed

> 9 currently-open items: 3 from Phase 7b sub-wave 7b.4 (E1+E2 reviewer triples, 2026-05-04), 3 from Phase 7c sub-waves 7c.1-7c.4 (D1+D2+D3+D4 reviewer triples, 2026-05-04; `qi-leantheoremdrift` closed 2026-06-10 via structural prevention), 2 from Phase 7c sub-wave 7c.6 (D3 Stage-10 r3 prep + D4 Stage-13 r1, 2026-05-04), and 1 from Phase 6w D7 Stage-13 (`qi-gate-5-self-audit-blind-spot-on-sibling-tautologies`, 2026-05-26). All are manually-curated additions; none auto-detected from `ReviewFinding` graph nodes. The pair (`qi-bundle_skeleton_inline_bibliography` + `qi-citation_authoryear_metadata_match`) supersedes the prior `qi-bibfilename` (which is now retained as a narrower precursor of the broader bundle-skeleton-template fix). See "Open Items" section.

## Open Items

### qi-gate-5-self-audit-blind-spot-on-sibling-tautologies — opened 2026-05-26 PM by Phase 6w D7 Stage-13 adversarial-reviewer

- **First observed:** 2026-05-26 PM Phase 6w D7 Stage-13 fresh-context adversarial-reviewer pass.
- **Pattern summary:** Self-conducted P3/P5 audits applied to one theorem in a module systematically miss SIBLING theorems sharing the same defect class on the same definitional target. Specific Phase 6w instance: self-audit correctly remediated T2 of `AnalogHawkingDemarcation.lean` (`_iff_loopRate_ok_and_c1_zero` → `_iff_tree_and_nonneg_and_c1_zero`) but missed T4 + T5 — `analog_hawking_simulable_implies_both_conditions` (`:= h` identity-function on the same And) + `analog_hawking_simulable_of_both_conditions` (`⟨h_bp, h_c1⟩` trivial And-constructor on the same definitional target). Also missed `categoricalChernExpansion_uses_aperiodicLattice` in `ChernBridge.lean` (statement `(IsPeriodic2D L ∨ IsAperiodic2D L) ∧ already-proved`; first conjunct LEM-vacuous since `IsAperiodic2D := ¬ IsPeriodic2D`; second independent of `L`; decorative parameter). All three caught by fresh-context adversarial-reviewer; ZERO caught by self-audit. **Occurrence count: 3 within a single 7-module self-audit pass.**
- **Pipeline stage affected:** Stage 13 (adversarial review) when bypassed via self-conducted audit substitute. When `physics-qa:adversarial-reviewer` IS invoked, this pattern is caught; when it isn't, the pattern slips through.
- **Proposed structural prevention:** Two-layer fix:
  - **(a) Tighten self-audit checklist:** When one P5 is caught in a module, the auditor MUST inspect EVERY OTHER theorem in that module returning a hypothesis directly OR using `⟨_, _⟩` / `And.intro` / trivial-constructor bodies on the same definitional target, before clearing the module GREEN.
  - **(b) Stronger:** ALWAYS invoke `physics-qa:adversarial-reviewer` + `physics-qa:claims-reviewer` plugin agents at wave close. Self-conducted audits are insufficient substitutes for fresh-context independent review. Add this to `WAVE_EXECUTION_PIPELINE.md` Stage 13 as a hard rule.
- **Owner:** unassigned. **Target:** apply on next wave close (Phase 6x onward).
- **Status:** open (PARTIALLY MITIGATED 2026-06-13, ADR-004 R2). `validate.py --check proxy_body_audit` automatically flags the **structural-named** subset of this class (a theorem whose name claims a quantity but whose body is `rfl`/`cases<;>rfl`/identity-return), removing reliance on a self-audit catching siblings — a genuine pathway-#2 advance. **NOT fully closed:** identity-wrappers with non-structural names (e.g. the 6w `analog_hawking_simulable_implies_both_conditions` `:= h`) still depend on the Stage-13 fresh-context reviewer; the gate-5(b) rule ("ALWAYS invoke `physics-qa:adversarial-reviewer` at wave close") remains the residual process fix.
- **Evidence:** `papers/AutomatedReviews/2026-05-26-2112-internal-adversarial/D7.md` (findings 3.1, 3.2, 3.3 + QI Candidate section); commit `89cae29` remediation chain; ADR-004 R2 (`proxy_body_audit`).

### qi-bibfilename — opened 2026-05-04 by Phase 7c sub-wave 7c.1 (D3 Stage-10 r1)

- **First observed:** 2026-05-04 during D3 Stage 10 round 1 claims review.
- **Pattern summary:** D3 paper_draft.tex called `\bibliography{bibliography}` but the actual bib file is `papers/D3/paper_draftNotes.bib`. The compile-time error was silent (TeX falls back to "??" citations); `paper_draft.aux` had 0 `\bibcite` entries; PDF compiled with all citations rendered as "??". The bundle-skeleton template in `bundle_append.py` produced `\bibliography{bibliography}` but the per-bundle bib filename convention is `paper_draftNotes.bib`.
- **Pipeline stage affected:** Stage 10 (LaTeX-compile gate of bundle-lift procedure).
- **Proposed structural prevention:** add to `BUNDLE_LIFT_PROCEDURE.md` §7 LaTeX-compile gate a pre-flight grep that the `\bibliography{<filename>}` argument resolves to an existing `.bib` file in the bundle directory. Could be `validate.py --check bundle_bib_filename`.
- **Owner:** unassigned. **Target:** propagate to `bundle_append.py` template fix to use `paper_draftNotes` by default.
- **Evidence:** `papers/D3/paper_draft.tex:bibliography` line; `papers/D3/paper_draftNotes.bib` is the actual bib file; D3 Stage-10 r1 `block:4` Class-CI BLOCKER.
- **Severity:** moderate. The compile-output looks valid until grep verifies the citations didn't render.

### qi-prose_lean_numerical_bound_gap — opened 2026-05-04 by Phase 7c sub-wave 7c.1 (D3 Stage-10 r1)

- **First observed:** 2026-05-04 during D3 Stage 10 round 1 claims review.
- **Pattern summary:** D3 §21 prose claimed CC overshoot `~10^122` at 5 sites; the cited Lean theorem `MicroscopicCoefficientMatch.lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed` proves `>10^100` only. 22 orders of magnitude gap between formal bound and prose. The `~10^122` is a heuristic from formula evaluation; the formal bound is the more conservative `>10^100`.
- **Pipeline stage affected:** Stage 10 (claims review — Class IA numerical-claim).
- **Proposed structural prevention:** when a prose numerical bound cites a Lean theorem, the claims-reviewer should extract the theorem's statement and verify the prose claim is bounded by (or matches) the theorem's literal. Class-IA-LEAN sub-class would catch this systematically. Generalises QI-CLAIM-1 from 7b.4.
- **Owner:** unassigned. **Target:** before F flagship draft (which will lift D3's Lean-theorem references).
- **Evidence:** `papers/D3/claims_review.json` `block:3`; `lean/SKEFTHawking/MicroscopicCoefficientMatch.lean` line 182 docstring.
- **Severity:** advisory. Resolvable by softening prose to formal bound + heuristic-estimate caveat.
- **Status:** open (NOT closed by ADR-004 — recorded for honesty 2026-06-13). The Substrate Integrity Gates (R1–R5) do not cover the prose-numerical-bound-vs-Lean-literal comparison; this is a **claims-reviewer Class-IA-LEAN** concern (extract the cited theorem's literal and verify the prose claim is bounded by it). The audit's related finding #54 (`vestigial_phase_eta_violates_microscope_bound` compares bare literals `1.0 > 1e-15`, not the named constants) is the same family and likewise remains for the claims-reviewer. Residual fix: implement the Class-IA-LEAN sub-check.

### qi-bibitem_registry_drift — opened 2026-05-04 by Phase 7c sub-wave 7c.4 (D1 Stage-13 r1)

- **First observed:** 2026-05-04 during D1 Stage 13 round 1 adversarial review.
- **Pattern summary:** 4 D1 bibitems (Estrecho2021, Claude2023, Jacquet2022, Jacquet2023QNM) described different real papers from what the corresponding registry entries described. Both sets are real polariton-physics papers; they just don't agree. The bibitem text is what gets printed to readers; the registry is what `validate.py --check citation_primary_sources_present` verifies. When they disagree, a reader following the printed bibitem reaches a different paper than the project tracks as the canonical primary source.
- **Pipeline stage affected:** Stage 13 (CitationIntegrity gate).
- **Proposed structural prevention:** `validate.py --check bibitem_registry_character_match` that for every `\bibitem{key}` in a paper, parses the bibitem text (title, journal, volume, page, year) and verifies it matches `CITATION_REGISTRY[key]` to within character tolerance. Stage 13 currently does WebFetch verification of the registry entry itself but not the bibitem-vs-registry agreement.
- **Owner:** unassigned. **Target:** before F flagship draft (which will lift bibitems from all 12 sibling bundles).
- **Evidence:** `papers/AutomatedReviews/2026-05-04-bundle-stage13/D1.md` findings 1.1-1.4; commit `18f48e1` reconciliation.
- **Severity:** moderate-to-high. Reader-facing trust issue.

### qi-bundle_skeleton_inline_bibliography — opened 2026-05-04 by Phase 7c sub-wave 7c.6 (D3+D4 Stage-10/13 r2)

- **First observed:** 2026-05-04 across D3 Stage-10 r2 (BLOCKER 4) and D4 Stage-13 r1 (BLOCKER B-1) — the same class of failure: bundle-skeleton template (`bundle_append.py` initialization) emits `\bibliography{paper_draftNotes}` (D3) or `\bibliography{bibliography}` (D4) plus an empty `paper_draftNotes.bib`. PDF compiles 47-51 pages but every `\cite{}` renders as `??`. `paper_draft.aux` has 0 `\bibcite` entries; no `.bbl` file. Generalises and supersedes `qi-bibfilename`: the deeper fix is not to point at the right bib filename — it is to eliminate the .bib-file vector entirely by defaulting bundle skeletons to inline `\begin{thebibliography}{99}`. Sister GREEN bundles (D5, L1-L3, E1, E2, I1, D2) already use the inline form successfully.
- **Pattern summary:** any new bundle initialized via `bundle_append.py` ships with the `\bibliography{}` line and an empty .bib. Without an explicit population step, the compiled PDF carries `??` citations. The empty-bib state is silent on a `pdflatex` exit code; only `grep "Citation .* undefined" paper_draft.log` surfaces it.
- **Pipeline stage affected:** Stage 7 (bundle initialization) + Stage 10 (LaTeX-compile gate of bundle-lift procedure) + Stage 13 (adversarial review compile gate).
- **Proposed structural prevention:** (a) modify `bundle_append.py` initialization template to emit `\begin{thebibliography}{99}\n\n%% bibitems populated by per-bundle lift\n\n\end{thebibliography}` instead of `\bibliography{<name>}`; (b) add `validate.py --check bundle_latex_compile_clean_citations` that scans every `papers/<bundle>/paper_draft.log` for `Citation '.+' undefined` and `No file .+\.bbl` lines. Implements D4 reviewer's "QI-D4-1" suggestion. (c) optionally remove `\bibliographystyle{apsrev4-2}` from the skeleton since inline thebibliography doesn't need it.
- **Owner:** unassigned. **Target:** before F flagship initialization (which inherits the same skeleton).
- **Evidence:** `papers/D3/claims_review.json` round 2 `block:r2:4`; `papers/AutomatedReviews/2026-05-04-bundle-stage13/D4.md` round 1 B-1; commit `6c25ee0` fix for both. Subsumes prior `qi-bibfilename`.
- **Severity:** moderate-to-high. Empty-bib state is silent; only auto-CI scanning of log can preempt the problem.

### qi-citation_authoryear_metadata_match — opened 2026-05-04 by Phase 7c sub-wave 7c.6 (D3 Stage-10 r3 prep)

- **First observed:** 2026-05-04 during D3 BLOCKER 4 fix-up; agent-A research surfaced 2 author/year slips:
  - `KaulMajumdar1998` cited prose context references "logarithmic correction with explicitly negative coefficient" — canonical Kaul-Majumdar -3/2 log A coefficient is the 2000 PRL (`gr-qc/0002040`), not the 1998 PLB precursor. Bibkey-year mismatched the underlying canonical paper.
  - `SextyWetterich2009` cited prose context references "Sexty-Wetterich-type complex-Langevin acceleration" — the actual canonical paper is **Berges-Sexty 2008** (NPB 799, 306, `arXiv:0708.0779`); Wetterich is **not** an author. Bibkey-author mismatched the underlying canonical paper.
- **Pattern summary:** when a bibkey of form `<LastName1><Year>` (or `<LastName1><LastName2><Year>`) describes a paper whose first-author + year don't match the bibkey, registry-internal-consistency validators don't catch it. Reader following the bibkey expects paper metadata that disagrees with what's registered.
- **Pipeline stage affected:** Stage 1 (constants/refs) + Stage 10 (claims review) + Stage 13 (adversarial review).
- **Proposed structural prevention:** `validate.py --check citation_bibkey_form_matches_metadata` that for each `CITATION_REGISTRY[key]` parses the bibkey using a `<LastName>{<LastName>}*<Year>` regex, then verifies (a) the parsed last-name appears in the entry's `authors` field; (b) the parsed year matches `entry['year']` to within ±1 (allow arXiv-vs-journal year drift). Either fix the bibkey form or rename the cite in the using-paper to a more accurate bibkey. Both fixes happen with a single grep + Edit.
- **Owner:** unassigned. **Target:** before F flagship draft (which will inherit cite-keys from all 12 sibling bundles; misnamed bibkeys propagate).
- **Evidence:** D3 cite renames in commit `6c25ee0` (`KaulMajumdar1998` → `KaulMajumdar2000`; `SextyWetterich2009` → `BergesSexty2008` with prose updated to "Berges--Sexty-type"). Agent-A research dossier flagging both as uncertainty in metadata batch.
- **Severity:** moderate. Reader-facing accuracy issue. Each occurrence is a single-Edit fix once flagged.

### qi-vizdiscipline — opened 2026-05-04 by Phase 7b sub-wave 7b.4 (E1 lift)

- **First observed:** 2026-05-04 during E1 Stage 9 round 1 figure review.
- **Pattern summary:** Plotly `add_hrect(annotation_position=...)` annotation positioning is unreliable on log-scale y-axes. With `annotation_position="top left"` (default per project), labels render OUTSIDE the rect at the top — visually placing each band's label INSIDE the band ABOVE it (one-band shift). With `"inside top right"`, the same shift persists. The Stage 9 round 2 reviewer caught this as a "tier-assignment caption mismatch" FAIL, but the root cause was not a physics error — it was a plotly rendering behavior on log axes that no current visualization-discipline check enforces.
- **Pipeline stage affected:** Stage 8 (visualizations) + Stage 9 (figure review).
- **Reliable workaround:** drop the hrect annotation entirely; use a separate `go.Scatter(mode="text", textposition="middle left")` trace with x at the right edge of the data range and y at the geometric mean of each band. Validated in `src/core/visualizations.py` `fig_polariton_regime_map` (commit `ea1d944`).
- **Owner:** unassigned. **Target:** Phase 7+ wave that touches visualizations.
- **Evidence:** `papers/E1/figures/figure_review_report.json` round 2; `src/core/visualizations.py` diff in commit `ea1d944`; memory `project_phase7b_e1_e2_closed.md`.
- **Severity:** advisory. Does not block submission directly, but if a future log-axis figure ships with hrect annotations, the misplaced labels can read as a content drift to a Stage-13 reviewer (as happened with E1 round 2). A `validate.py --check viz_consistency` extension scanning `visualizations.py` for `add_hrect` + `annotation_position` + log-yaxis combinations would prevent recurrence.

### qi-numericalverification — opened 2026-05-04 by Phase 7b sub-wave 7b.4 (E1 Stage 10 r1)

- **First observed:** 2026-05-04 during E1 Stage 10 round 1 claims review.
- **Pattern summary:** A propagating arithmetic-drift in a paper-quoted threshold survived through paper12_polariton's full per-paper Stage-13 review and propagated unchanged into the E1 bundle lift. The paper claimed `G > 0.01` at `ω/κ = 0.175`, but recompute: `G(0.175κ) = 1/(exp(2π·0.175)−1) = 1/2 = 0.5`, not `0.01`. The companion photon-count claim (`>10⁴ probe photons` for `5σ`) was wrong by factor 25 (correct: `N_probe = 25/G² = 100` at `G=0.5`). The drift propagated across 4 sites: paper12 fig 1 caption + E1 abstract + body §4 + figure dashed-line position. The canonical project source (`provenance.py:3580`) had the correct value `G > 0.5` all along — the paper text just didn't follow it.
- **Pipeline stage affected:** Stage 9 (figure review) + Stage 10 (claims review). Specifically: Stage 9 LaTeX-compile gate currently does NOT include arithmetic verification of paper-quoted numerical thresholds against direct re-computation.
- **Proposed structural prevention:** add a pre-Stage-9 arithmetic-verification step to `BUNDLE_LIFT_PROCEDURE.md` §7 (LaTeX-compile gate). For every paper-quoted numerical threshold of the form "X ≈ value at parameter Y", verify by direct computation that the formula evaluation at Y produces value within tolerance. Could be implemented as a `validate.py --check threshold_arithmetic` that scans paper TeX for `≈|=`-quoted relations between named formula terms and numerical values, evaluates the formulas via `formulas.py`, and flags any > 0.5% disagreement.
- **Owner:** unassigned. **Target:** before D3 Stage 9/10/13 reviewer triple (next session).
- **Evidence:** `papers/E1/claims_review.json` round 1 finding `block:E1:1`; supersession ledger entry `bundle-stage10:E1-2026-05-04-r1:block:E1:1:propagating-G-threshold-drift`; commits `ea1d944` (E1 fix) + `ba3e329` (paper12 source fix); memory `project_phase7b_e1_e2_closed.md`.
- **Severity:** advisory but high-impact. The drift survived a full per-paper Stage-13 review of paper12 (which closed at GREEN at the time); the bundle-lift Stage-10 claims-reviewer caught it on the FIRST round of E1 review, fixing it before submission would have been damaging. Without the structural prevention, the same class of drift can recur in any future paper that quotes a function value at a specific argument.

### qi-leantheoremname — opened 2026-05-04 by Phase 7b sub-wave 7b.4 (E2 Stage 13 r1 finding F4)

- **First observed:** 2026-05-04 during E2 Stage 13 round 1 adversarial review (RECOMMENDED finding F4).
- **Pattern summary:** E2 paper text said "formally bounded at $\leq 1.8\%$ at $\omega_H$ in `QuasiOneDReduction.lean`" but the actual Lean theorem `quasi1D_validity_bound` (`QuasiOneDReduction.lean:233`) is a generic algebraic envelope; the `1.8%` lives in the docstring at line 226 as a numerical evaluation, not as a theorem literal. Prose theorem-name references should require explicit Lean theorem name match — i.e., the paper should either name the algebraic-envelope theorem T5 explicitly with the parameter set, or add a Dean-specialized `≤ 0.02` corollary as a substantive Lean theorem.
- **Pipeline stage affected:** Stage 10 (claims review — Class TN theorem-name reference drift) + Stage 13 (adversarial review).
- **Proposed structural prevention:** extend `claims-reviewer-v2` Class TN check to flag prose-quoted bounds (`"X ≤ Y" / "X = Y" / "X ≈ Y"`) that reference a Lean module by name but where the named module's theorems do not contain `Y` as a literal. Currently Class TN only checks that the theorem name resolves; it does not check that quoted numerical bounds are theorem-literal vs docstring-numeric.
- **Owner:** unassigned. **Target:** before D3 Stage 10 reviewer pass (D3's 27 sections include numerous Lean-theorem-named bounds; this discipline is highest-leverage there).
- **Evidence:** `papers/AutomatedReviews/2026-05-04-bundle-stage13/E2.md` finding F4; `lean/SKEFTHawking/QuasiOneDReduction.lean:226-233`; memory `project_phase7b_e1_e2_closed.md`.
- **Severity:** advisory. Caught at Stage 13 r1 as RECOMMENDED (not BLOCKER); does not block E2 submission. But the same class of drift could escalate to BLOCKER if the prose quotes a number that disagrees with the docstring as well as not being a theorem literal — at which point both the Class IA (numerical-claim disagreement) and Class TN (theorem-name reference drift) checks would need to fire.

## Closed Items

### qi-assumptiondisclosure — closed 2026-04-29 by Phase 6i Wave 5

- **Evidence on close:** `docs/phase6i_wave5_close.md`
- **Mechanism:** All 30 open AssumptionDisclosure ReviewFinding nodes
  flipped via supersession ledger entries (18 STALE + 11 ACCEPTED + 1
  body-marked-CLOSED). Triage anchors include `H_LeptonNumberViolated`
  refactored from `True` placeholder to substantive `G_LV ≠ 0`
  predicate (MajoranaRung.lean:221); paper22 §122-134 "Structure
  invariants" subsection ships disclosing all four EWFiniteTParams
  positivity invariants (closes 2026-04-25-2002 + 2026-04-26-1923
  cubic_coeff_nonneg findings); paper27 Wave-5 rewrite around Balbinot
  2005 anchor closes deep_research_analog_conflation; paper20
  H_ScalarChannelIsTetradBifurcationOutput disclosed at 9 sites in
  paper_draft.tex; paper35 §VII parametrized S_horizon disclosure;
  paper35 Technical notebook §6 ships scope-disclosure + tracked-Prop
  flag (already in current state). 1 content fix applied:
  Phase6d2_ChiralSSB_Technical.ipynb cell p37t-3-md updated via
  NotebookEdit to add explicit chiPT-leading-order + NLO-band
  disclosure paralleling Stakeholder §6 honest-scope.
- **Numerics:** open count 30 → 0 (100%); supersession ledger 107 →
  137 entries (+30 Wave-5 entries).
- **⚠ RECURRED + RE-CLOSED VIA STRUCTURAL PREVENTION (2026-06-13, ADR-004).**
  The 2026-04-29 closure was **pathway #1 (per-finding supersession)**. The
  2026-06-13 audit found the assumption-disclosure class recurring: the two
  hand-maintained tracked-hypothesis ledgers (`HYPOTHESIS_REGISTRY` vs the
  markdown doc) held **disjoint** contents, and ~21 consumed tracked Props were
  in neither ledger (audit #2). Re-closed via **pathway #2** — `HYPOTHESIS_REGISTRY`
  is now the single source of truth, the doc is auto-generated, and
  `validate.py --check tracked_hypothesis_ledger` (R3, **new Invariant #16**)
  hard-fails on any consumed-but-unregistered tracked Prop. Per the Stage-14
  closure-pathway policy this class closes ONLY via pathway #2.
  **Evidence:** ADR-004; commit `616cc35d`; `docs/audits/SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md`.

---

### qi-citationintegrity — closed 2026-04-28 by Phase 6i Wave 1

- **Evidence on close:** `docs/phase6i_wave1_close.md`
- **Mechanism:** Per-phase `Lit-Search/Phase-X/primary-sources/` cache
  rolled out (Pipeline Invariant #11). New `validate.py --check
  citation_primary_sources_present` (CHECK 19) mandatory at every
  Stage 13. Hallucinated-citation failure mode structurally
  non-recurrable.
- **Numerics:** Registry 218 → 339; cached 4 → 227.

### qi-computationcorrectness — closed 2026-04-29 by Phase 6i Wave 6

- **Evidence on close:** `docs/phase6i_wave6_close.md`
- **Mechanism:** All 22 open ComputationCorrectness ReviewFinding
  nodes flipped via supersession ledger entries (5 ACCEPTED — older
  motivational/scoped framings; 17 FIXED — most are Class-1
  cache-skip closure-note findings whose body content is itself a
  PASS verification, plus 2 active content fixes: paper17 SFDM count
  drift 31 → 29 and paper37 Technical notebook cell p37t-5-md
  two-conjunct → three-conjunct).
- **Numerics:** open count 22 → 0 (100%).

### qi-countfreshness — closed 2026-04-29 by Phase 6i Wave 6 (structural prevention)

- **Origin:** Surfaced by Wave 6 `qi_register.py` status-filter audit.
  Not in the Phase 6i entry-state-8 QI list; emerged from existing
  CountFreshness regex cluster after closing the 8 entry-state QI
  items. Per Phase 6i roadmap line 11 (append-only structure).
- **Evidence on close:** `docs/phase6i_wave6_close.md` +
  `scripts/update_counts.py` + `docs/counts.tex` (auto-regenerated
  central macro registry) + `validate.py --check counts_fresh`.
- **Mechanism:** Structural prevention via the counts.tex macro
  pipeline: every paper now consumes `\input{../../docs/counts.tex}`
  and references count via macros (`\fhdTotal`, `\heatKernelThms`,
  `\centerSymmThms`, `\bhThermoTotal`, etc.). The 18 representative
  open findings triage as: 9 PASS-verifications already-fixed
  (counts.tex stale → fresh, abstract count macro retrofits,
  Vergeles2025 used_in field expanded 2 → 7 papers, paper27 figure
  removal, EinsteinCartanExtension docstring numerical-claim correct,
  paper27 \\bhThermoTotal{20} matches actual); 5 INFO-level advisories
  about Stakeholder/Technical notebook count text (all currently
  match actual Lean source); 4 pre-Phase-6i advisories about counts
  superseded by the macro pipeline (paper10 130→195 modules,
  paper18 raw-literal → \\fhdTotal{}, paper20 definition-count
  removed in W2 strengthening, v2_reviewer pipeline-gap closed by
  Phase 5v Wave 10 sentence_state.py update).
- **Numerics:** open count 18 → 0 via QI-level structural closure;
  `qi_register.py` status filter (Wave 6 fix) now correctly excludes
  CountFreshness from Open Items aggregate.

---

### qi-crosspaperconsistency — closed 2026-04-29 by Phase 6i Wave 3

- **Evidence on close:** `docs/phase6i_wave3_close.md`
- **Mechanism:** All 35 open CrossPaperConsistency ReviewFinding nodes
  flipped via supersession ledger entries +/or content fixes.
- **Numerics:** open count 35 → 0 (100%).

### qi-fixpropagation-tracking — opened + closed 2026-04-28 by Phase 6i Wave 2 Stage 13 follow-up

- **Evidence on close:** `docs/phase6i_wave2_close.md` +
  `docs/review_finding_supersessions.json`.
- **Mechanism:** Project-level supersession ledger; `extract_review_finding_nodes`
  honours per-finding status overrides.
- **Numerics:** 13 paper40 nodes flipped open → fixed; FixPropagation
  gate flips needs-recheck → passed.

### qi-leantheoremdrift — closed 2026-06-10 by the external-review remediation process wave (structural prevention)

- **First observed:** 2026-05-04 across D1 (5 BLOCKERs), D2 (9 BLOCKERs), D3 (13 BLOCKERs), D4 (1 BLOCKER cluster) Stage-10 round-1 reviews — **~32 instances of Class TN theorem-name drift** in 4 first-pass drafts.
- **Pattern summary:** First-pass drafts repeatedly cite Lean theorems by *intended* module name (drafted from synthesis brief or memory) rather than *actual* qualified name in `lean_deps.json`. Examples: `NonlinearDiffInvariance.h_path_b_holds_iff_dirac_bundle` (intended) vs `diff_invariance_a4_iff_dirac_basis_consistent` (actual); `HoloQEC.admissible_iff` vs `QECHolographyBridge.HPCode.code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class`; `HigherCurvatureStelle.basis_change_identity` vs nonexistent module. Generalises QI-LEAN-1 from 7b.4.
- **Pipeline stage affected:** Stage 10 (claims review). Each occurrence triggers a Class-TN BLOCKER.
- **Proposed structural prevention:** add a pre-Stage-10 grep step to `BUNDLE_LIFT_PROCEDURE.md` §7 LaTeX-compile gate. For every `\texttt{ModuleX.theorem_name}` reference in `papers/<bundle>/paper_draft.tex`, verify that `ModuleX.theorem_name` appears as a fully-qualified declaration in `lean/lean_deps.json`. Could be implemented as `validate.py --check bundle_lean_refs_resolve` that scans paper TeX for `\\texttt\\{[A-Za-z]+\\.[a-zA-Z_]+\\}` patterns and verifies each resolves.
- **Owner:** unassigned. **Target:** before F flagship draft (which will inherit the same risk surface across 41 source papers).
- **Evidence:** `papers/D1/claims_review.json` (Stage 10 r1, 5 TN BLOCKERs); `papers/D2/claims_review.json` (9 TN BLOCKERs); `papers/D3/claims_review.json` (13 TN BLOCKERs); `papers/D4/claims_review.json` (1 TN BLOCKER cluster of 7 names with HPCode prefix).
- **Severity:** advisory but high-impact. Each first-pass draft suffers ~5-15 Class-TN BLOCKERs surfaced at Stage 10. Without the structural prevention, F flagship will surface ~40+ Class TN BLOCKERs.
- **Status:** closed (structural prevention, Stage-14 pathway 2).
- **Evidence on close:** `validate.py --check prose_theorem_reference_coverage` (CHECK 25, shipped 2026-06-10 in commit "feat(process): 3 new validators — axiom-prose consistency, prose-theorem coverage (closes qi-leantheoremdrift), theorem-name-embedded citations"). The check implements the proposed `bundle_lean_refs_resolve` mechanism: it extracts `\texttt{}` Lean-identifier candidates from all 17 bundle drafts, resolves each against `lean/lean_deps.json` declaration names (exact / project-qualified suffix / module-field-verified `<Module>.<thm>` documentation idiom / unqualified short name), plus module names and project Python registry keys, with disclaimer-context exemptions and a documented waiver list. Unresolved references hard-fail. Calibration on ship-day surfaced and fixed 13 live Class-TN drift sites (D1 `hawking_universality_main`→`hawking_universality`, `bp_convergence_iff_ldp_below_threshold`→`bp_convergence_iff_ldp_rate_zero`; D4 `valid_branch_K_chain_le_K_compose_numeric`→`_generic`; D3 ×3 + F ×2 + E1/E2 module-attribution corrections; F `T_H_polariton`/`T_H_graphene`→ canonical formula/provenance keys). Tests: `tests/test_validate_prose_checks.py`.

### qi-leanproofsubstance — closed 2026-04-29 by Phase 6i Wave 4

- **Evidence on close:** `docs/phase6i_wave4_close.md`
- **Mechanism:** All 26 open LeanProofSubstance ReviewFinding nodes
  flipped via supersession ledger entries (12 STALE + 8 ACCEPTED + 6
  body-marked-CLOSED-self-disclosed). New `scripts/audit_paper_lean_refs.py`
  ships as the durable mechanism: walks every paper_draft.tex,
  extracts `\texttt{}` Lean-ident candidates, cross-checks against
  `lean/lean_deps.json`. Codifies `feedback_python_lean_refs_drift.md`
  pattern.
- **Numerics:** open count 26 → 0 (100%); audit script: 786 candidate
  refs across 40 papers, 617 OK / 159 ABSENT (mostly Mathlib /
  module-name idioms) / 10 DRIFTED (paper-convention `<Module>.<thm>`
  notation, accepted as documentation idiom).
- **⚠ RECURRED + RE-CLOSED VIA STRUCTURAL PREVENTION (2026-06-13, ADR-004).**
  The 2026-04-29 closure was **pathway #1 (per-finding supersession)**, which
  left the generator alive: the 2026-06-13 whole-substrate weakness audit found
  the proof-substance class recurring in post-2026-04-29 modules (paper7 `True`-stub
  overclaim #3; `change_of_rings_ext_dim` `x=x`; entropic `cases<;>rfl` over a
  constant-true registry; 5× `N=N` decorative theorems). Re-closed via **pathway #2
  (structural prevention)** — the standing gates `validate.py --check
  placeholder_not_cited` (R5) + `proxy_body_audit` (R2), the `MODELING_ASSUMPTION_THEOREMS`
  disclosure whitelist, and the strengthened Invariant #9. Per the new Stage-14
  closure-pathway policy, this class may now close ONLY via pathway #2.
  **Evidence:** ADR-004; commits `6dc125ea`/`047d73cf`; `docs/audits/SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md`.

### qi-narrativegrounding — closed 2026-04-29 by Phase 6i Wave 3

- **Evidence on close:** `docs/phase6i_wave3_close.md`
- **Mechanism:** All 33 open NarrativeGrounding ReviewFinding nodes
  flipped via supersession ledger entries +/or targeted content fixes.
- **Numerics:** open count 33 → 0 (100%).

### qi-parameterprovenance — closed 2026-04-28 by Phase 6i Wave 2

- **Evidence on close:** `docs/phase6i_wave2_close.md`
- **Mechanism:** 124 of 174 PARAMETER_PROVENANCE entries flipped via
  bulk-flipper sweep; `--strict` flag added to `validate.py`.
- **Numerics:** human-verified 0 → 128 (74%); strict-blocker count = 2.

### qi-productionrunhealth — closed 2026-04-29 by Phase 6i Wave 6

- **Evidence on close:** `docs/phase6i_wave6_close.md`
- **Mechanism:** Single ProductionRunHealth ReviewFinding (paper27
  8.1) classified as no-applicable-scope: paper27 makes no
  production-run claims requiring backing data. The original review
  body explicitly states "STATUS UNCHANGED — No production runs
  claimed". Advisory accepted via supersession ledger.
- **Numerics:** open count 1 → 0.

### qi-provenance-citation-coverage — opened + closed 2026-04-28 by Phase 6i Wave 2 (cited_bibkeys side)

- **Evidence on close:** `docs/phase6i_wave2_close.md`
- **Mechanism:** New `validate.py --check provenance_doi_in_registry`
  (CHECK 20). Default mode advisory; `--strict` promotes to fail.
- **Numerics:** 70 of 99 provenance DOIs resolved at W2 close; 29
  advisory residuals queued for Wave 4.

### qi-provenance-doi-coverage — opened + closed 2026-04-29 by Phase 6i Wave 4

- **Origin:** Wave 2 close report — 29 advisory CHECK-20 missing-DOI
  residuals queued for Wave 4.
- **Evidence on close:** `docs/phase6i_wave4_close.md` +
  `src/core/citations.py` (13 new bibkey entries) +
  `src/core/provenance.py` (1 DOI typo fix).
- **Mechanism:** Registered 13 new bibkeys covering the 29 missing
  DOIs (PDG2024Particle covers 7 EW.* entries; LIGOSensitivity2015
  covers 2 GW frequency entries; Abbott2017GW170817Detection covers 2
  GW170817 inspiral entries; DESI2024DR2 covers 2 FLRW dark-energy
  entries; WaveDeepResearchSMG2024 covers 4 MAJORANA.C_SMG_*; etc.).
  Fixed the ChristensenDuff1979 DOI typo `(79)90516-4 → (79)90516-9`
  in PARAMETER_PROVENANCE['MICRO_MACRO.N_F_SM_DIRAC'].
- **Numerics:** missing DOIs 29 → 0; CHECK 20 now PASSES with 0
  warnings (was 1 advisory).

---

---

---

## Manual fields

The following fields are preserved across regenerations by matching on QI item `id`:

- `owner` — person responsible
- `target_date` — ISO 8601
- `status` — `open` / `in-progress` / `closed`
- `evidence_on_close` — commit hash or wave reference that remediated the pattern

To assign fields for a QI item, edit the item section inline. The generator does NOT overwrite manual fields (it matches on `id`). (Current generator is auto-regen-only; manual-field persistence is a follow-up.)
