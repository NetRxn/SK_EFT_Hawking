# Bundle D5 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-31 — Stage-13 finding remediation: 🔴 RED → 🟢 GREEN

Closed the 2 pre-existing CRITICAL findings holding D5 at RED (both CountFreshness on the paper34 EquivalencePrinciple stakeholder notebook; never recorded in the supersession ledger — both were stale, i.e. already fixed in the notebook but never closed):

- **`…paper34_equivalence_principle:1.1` (CountFreshness critical):** FIXED (stale) — notebook cell now reads "24 machine-checked Lean theorems", matching `grep -cE '^theorem ' lean/SKEFTHawking/EquivalencePrinciple.lean = 24`. The prior "25" claim is gone (grep confirms zero matches).
- **`…paper34_equivalence_principle:1.2` (CountFreshness critical):** FIXED (stale) — §7 cell now reads "24 theorems (12 original + 12 strengthening)" = 24, matching the Lean count.

Both closed via deterministic recheck in `docs/review_finding_supersessions.json`. Post-remediation: D5 open=5 (3 advisory + 2 minor), blockers=0 → 🟢 GREEN.

## 2026-05-01 — Lift-section from `paper17_dark_sector` (§2-§3)

- Source title: Dark-sector connections
- Lift action: Lift-section
- Insertion point: §2-§3
- Stage-13 redo required: yes
- Notes: Initial lift: paper17 dark-sector DM classification (§2 SFDM merger) + DE structural NO-GO architecture (§3 ADW + Volovik). Anchors D5 §2-§3 per PAPER_DRAFT_MAPPING.md row.

## 2026-05-01 — Lift-section from `paper29_bbn_unified` (§4)

- Source title: BBN classification
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: BBN classification of Phase 5x DM candidates

## 2026-05-01 — Lift-section from `paper32_strong_cp_de` (§5)

- Source title: Strong-CP + topological DE
- Lift action: Lift-section
- Insertion point: §5
- Stage-13 redo required: yes
- Notes: Zhitnitsky topological-DE absorption + combined-mechanism falsifier

## 2026-05-01 — Lift-section from `paper34_equivalence_principle` (§6)

- Source title: Equivalence-principle classification
- Lift action: Lift-section
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: EP-violation matrix; vestigial-only verdict

## 2026-05-01 — Lift-section from `paper42b_cc_emergent` (§7)

- Source title: Cosmological constant in emergent form
- Lift action: Lift-section
- Insertion point: §7
- Stage-13 redo required: yes
- Notes: CC-channel constraint contribution; secondary D5 (primary D3 §21)

## 2026-05-01 — Lift-section from `D5_phase6m_lean_only` (§8-§12)

- Source title: Phase 6m three-track Lean closure
- Lift action: Lift-section
- Insertion point: §8-§12
- Stage-13 redo required: yes
- Notes: D.4 sourceless late-absorption: Phase 6m three-track Lean closure (CSDE Track A NO-GO + 3 caveats incl. Barrow §10.5 + EGDE Track B 8/8 unanimous NO-GO paper-45-equivalent novelty + JTGR Track C f(R) Exp+ArcTanh CLEARED-R5 strongest + Sakharov §11.5 + DSCE 7-class GD taxonomy)

## 2026-05-01T19:50Z — First-pass content draft authored

Skeleton produced by `bundle_append.py` lifts (above) populated with substantive content
across all 6 sections + new abstract + intro + discussion. ~9 pages compiled (clean
`pdflatex` build; zero errors, zero undefined-reference warnings after second pass).

Section status:
- §1 Introduction: substantive narrative (program goals + Phase 6m novelty claim).
- §2-§3 paper17_dark_sector: condensed lift covering Z16 hidden sector + ADW CC magnitude
  + KV DE-dynamics withdrawal + honesty Derived/MCC/Heuristic split + SFDM merger forecast
  with all 5 cluster Mach numbers + single-cluster SNR (0.83 Euclid, 1.04 Roman).
- §4 paper29_bbn_unified: BBN classification of Phase 5x candidates; fracton mu > MeV
  sufficiency condition.
- §5 paper32_strong_cp_de: Zhitnitsky topological-DE + combined-mechanism falsifier
  (zhitnitskyDE_eV4 0.1 strict threshold) + theta_bar substrate-silent verdict.
- §6 paper34_equivalence_principle: EP-violation matrix; vestigial-relic unique
  measurable signature at MICROSCOPE/STEP/Galileo-Galileo-Galilei sensitivity.
- §7 paper42b_cc_emergent: CC-channel constraint excerpt — heat-kernel a_0 not
  sufficient for Lambda_obs without ADW Volovik tetrad-determinant self-tuning.
- §8 Phase 6m Track A: causal-set DE NO-GO (CSDE1-10) + 3 publishable structural
  caveats (GD inapplicability robust under prescriptions; Barrow >=40% prescription-
  dependence; BDG sigma_Lambda first-principles decomposition); §10.5 Barrow embedded
  short-note subsection with ~18KB outline pointer.
- §9 Phase 6m Track B: 8/8 unanimous NO-GO closure (the bundle's *substantive new
  contribution*; first complete-mechanism-family closure in Phase 6m); explicit
  enumeration of all 8 quantitative bounds exceeding Jeffreys-decisive; r_d-anchoring
  rescue does not save Class (b) or (d).
- §10 Phase 6m Track C: highest-survival; f(R) Exp+ArcTanh strongest CLEARED-R5
  (Plaza-Kraiselburd Delta AIC ~ Delta BIC >~ 20); Hu-Sawicki NO-GO chameleon at
  b ~= 0.21; Pure Lovelock NO-GO at Quintom-B box edge; KSS conditional path-(a);
  Volovik-Jannes substrate as Sakharov anchor.
- §11 Sakharov criterion cross-bridge: 4-criterion biconditional formalized;
  3He-A satisfies all four; FLS BEC violates universal coupling (ii); unimodular
  reformulation admits 5/6 Phase 6m candidates (NOT KSS); §11.5 Sakharov embedded
  short-note subsection with ~20KB outline pointer.
- §12 Unified 7-class GD taxonomy: 21 mechanisms organized; 3-tier applicability
  gradient; class (c) orthogonality-failure witness; ready for post-Phase-6m
  mechanism additions.
- §13 Discussion + DR3/Roman 2030 outlook + bundle counts.

Bibliography: 21 bibitems registered with arXiv IDs and DOI venues.

Compile gate: clean (9 pages, 378KB PDF, second-pass cross-references resolved).

Stages 9/10/13 reviewer triple is the next blocking step before bundle close.
Per BUNDLE_LIFT_PROCEDURE.md §11 BLOCKER resolution loop, the reviewers run sequentially
(claims-reviewer + figure-reviewer before adversarial-reviewer); same-bundle reviewers
must be sequential per refinement #11.

## 2026-05-01T20:30Z — Stage 9 round 1: 4 figure FAILs

Stage 9 round 1 RED. 4 FAILs:
- fig28 caption-figure physics mismatch (closed-form V_eff prose vs G/G_c parameterization plot).
- fig_zhitnitsky θ-scan caption vs Λ_QCD-axis figure.
- fig_lambda_emerg red/green palette violation (emerald + burgundy) + N_f curves overlap + verdict-band caption mismatch.
- fig_phase5x right-edge annotations clipped at margin.

3 cosmetic MINORs (SFDM cluster labels, BBN ΔN_eff annotations, EP η annotation overlap).

## 2026-05-01T20:45Z — Stage 10 round 1: 8 claim FAILs + 1 WARN

Stage 10 round 1 RED. 8 FAILs:
- §12 phase6m_mechanism_count "4+8+9=21" claim vs Lean theorem proves only B+C=17.
- Abstract "all 8 quantitative Bayesian bounds" overstates; Lean aggregator only checks 4.
- §9.1 itemize 10 entries vs prose "8 mechanisms" (2 DEC sub-supports listed as siblings).
- §4 wrong theorem names (phase5x_dm_bbn_violators_count_two / phase5x_dm_bbn_passers_count_three).
- §4 wrong module BBNUnified.lean (does not exist).
- §6 wrong modules EquivalencePrincipleClassification + VestigialPhaseEPViolation (do not exist).
- §7 wrong module CosmologicalConstantEmergent.lean (does not exist).
- §2.1 T-0/S-0 attributed to HiddenSectorMixedCharge.lean (actually live in DarkSectorSynthesis.lean).

1 WARN: §2.2 fig28 caption bare critical_coupling_pos without module prefix.

## 2026-05-01T21:00Z — Round 1 fixes applied (12 FAILs + 1 WARN)

11 paper_draft.tex edits + 2 figure regenerations + 13 supersession-ledger entries appended (401 → 414):
- Captions rewritten: fig28 (G/G_c parameterization + ADWMechanism.critical_coupling_pos), fig_zhitnitsky (Λ_QCD-axis + CC suppression bar chart), fig_lambda_emerg (4 N_f linestyles + Cividis heatmap with steel-blue/amber contour overlays).
- Module-name fixes: BBNUnified→BBN, EquivalencePrincipleClassification+VestigialPhaseEPViolation→EquivalencePrinciple, CosmologicalConstantEmergent→MicroscopicCoefficientMatch, T-0/S-0→DarkSectorSynthesis.lean.
- Theorem-name fixes: bbn_violators_share_n_eff_failure_mode + at_least_three_phase5x_candidates_bbn_conformant.
- Logic clarifications: abstract 4-quantitative+4-structural; §9.1 8-mechanism+2-DEC-supports merge; §12 17-vs-21 mechanism-count distinction.
- Figure regenerations: fig_lambda_emerg (palette steel_blue/amber/Heidelberg/cross + linestyles solid/dash/dot/dashdot, M_Pl Heidelberg, locus steel_blue), fig_phase5x (margin r=560, width=1500).
- LaTeX compile clean throughout (12 pages, 1.35 MB).

## 2026-05-01T21:15Z — Stage 9 round 2: 1 persistent FAIL (caption-color-words)

YELLOW. fig_lambda_emerg caption still used "green/yellow/red verdict bands" prose — colorblind violation independent of figure rendering. Plus "logμs" Plotly tick-rendering artifact at left margin (kaleido font fallback on clipped locus annotation at 2.83e-12 GeV outside [10^0, 10^20] range).

## 2026-05-01T21:25Z — Round 2 fixes

Caption rewritten to drop verdict-band color words; locus vline removed from visualizations.py (preserves locus value in MICRO_MACRO_PARAMS for cross-reference); axis titles simplified (drop parenthetical "log scale" to avoid kaleido font fallback). 2 supersession-ledger entries appended (414 → 416). PNG regenerated; "logμs" artifact gone.

## 2026-05-01T21:30Z — Stage 10 round 2: GREEN (14/14 PASS)

All 8 round-1 BLOCKERs verified resolved. WARN resolved. 1 advisory (DSCE9 docstring drift at DarkSectorClassificationExtension.lean:262-266) accepted as non-blocking; addressed in follow-up. 1 QI candidate raised: validator for prose-vs-Lean tracked-hypothesis name resolution.

## 2026-05-01T21:35Z — Stage 9 round 3: GREEN

All 4 round-1 FAILs verified resolved + round-2 caption + locus fixes confirmed. 3 cosmetic MINORs persist as advisory only (non-blocking).

## 2026-05-01T21:40Z — DSCE9 docstring fix

DarkSectorClassificationExtension.lean:262-271 docstring rewritten to align with theorem body (B+C=17 enumeration via length-aggregator, with Track A's 4 inductive constructors counted via case-exhaustion to reach the full 21-roster). Theorem signature + body unchanged. lake build clean (2186 jobs / 2.8s). 1 supersession-ledger entry appended (416 → 417).

## 2026-05-01T21:45Z — Stage 13 round 1: GREEN

Adversarial reviewer Tier-1 deep-paper profile sweep across 8 finding classes. Verdict: 0 BLOCKER / 0 RECOMMENDED / 2 ADVISORY. 7 load-bearing bibitems + 19 named theorems spot-verified; "first" claims corroborated against ARCHITECTURE_SCOPE / Phase6m_Roadmap / PAPER_DRAFT_MAPPING; freshness clean; tracked-hypothesis discipline in place. 1 QI Candidate (QI-D5-1) raised for prose-vs-Lean tracked-hypothesis-name validator. Cross-bundle re-check deferred to D2/D3 lift (those bundles not yet drafted).

Stage 13 review doc: `papers/AutomatedReviews/2026-05-01-1625-bundle-stage13/D5.md`.

## 2026-05-01T21:55Z — Bundle D5 CLOSED at GREEN

Phase 7b sub-wave 7b.2 ledger entry: 1 person-day effort for fresh first-pass + 3 reviewer-triple rounds with deterministic recheck. 12-page Tier-1 deep paper (target PRD) at GREEN at all three reviewer-triple stages. 17 supersession-ledger entries spanning the lift cycle (401 → 418 final). Bundle ready for the publication-length expansion pass (~50pp; current 12pp is condensed first-pass) before PRD submission.

## 2026-05-06 — Lift-section from `_phase6n_W1c_writeup` (§13)

- Source title: NO-GO writeup memo at `temporary/working-docs/phase6n/wave_1c_*`
- Lift action: Lift-section
- Insertion point: §13
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W1c NO-GO writeup memo joint with 6o.γ (NO-GO landscape: dissipative SK-EFT bootstrap-uniqueness obstructions)

## 2026-05-06 — Lift-section from `_phase6n_W2b_lean_only` (§13)

- Source title: Quantum Crooks no-go (Perarnau-Llobet)
- Lift action: Lift-section
- Insertion point: §13
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W2b Perarnau-Llobet quantum-Crooks parametric + ℂ-form NO-GO

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper17_dark_sector 'first deliverable to export' line softened to descriptive; D5 bundle own §11 Sakharov $\Lambda_J$ vs $\Lambda_{HK}$ paragraphs (3 places) had 'to the best of our knowledge ... the first systematic ...' framing dropped and replaced with descriptive prose; D5 discussion section 'first-complete-mechanism-family' -> 'complete-mechanism-family'.

## 2026-06-10 - Prose-revision-bookkeeping (review-2026-06-05 D5-EV1 arithmetic/narrative sync)

- Source: (none - Lean ground-truth sync after commits d83ff8b6 + 196a5a70: Halenka-Miller primary-source verification + unit-coherent `EntropicGravityDarkEnergy` §2/§6 restatement)
- Lift action: Prose-revision-bookkeeping
- Insertion point: abstract; §1 bundle-goals; §9.1 intro + aggregator paragraph; §9.2 r_d-independence; READINESS_GATES.md substantive-content item 1
- Stage-13 redo required: no
- Notes: Bayes-decisive cohort corrected 3-of-4 → 2-of-4 (Tsallis HDE, Odintsov-D'Onofrio-Paul; aggregated in `both_decisive_bayes_bounds_exceed_jeffreys_decisive`). Verlinde 2017's quantitative ledger restated as σ-significance — excluded at >5σ by Halenka-Miller PRD 102, 084007 (2020) galaxy-cluster mass densities under nominal profile assumptions only (weakens once profile systematics are included); it is a Gaussian-σ statement, not a Bayes factor, and not a CMB/Bullet test. Barrow HDE stays AIC-moderate (ΔAIC = +4.7). The 4-of-4 closure is now cited only at the mixed-threshold unit-coherent level (`all_quantitative_bounds_disfavoured`, σ / log𝓑 / ΔAIC / log𝓑); the stale §9.1 citation of the deprecated alias `all_quantitative_bounds_exceed_jeffreys_decisive` (now restricted to the 2-of-4 Bayes cohort) removed. Also fixed §1 "all eight quantitative bounds exceeding the Jeffreys-decisive threshold" (only 4 of 8 ledgers are explicitly quantitative; only 2 are Bayes-decisive) and §9.2 "three Bayes-factor decisive bounds" cohort arithmetic. pdflatex ×2 clean.

## 2026-06-10 — Prose-revision-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: Source-paper reconciliation vs last_lift 2026-05-12: 1 flagged source (paper17_dark_sector) carries one REAL commit, not mtime noise — commit 5207b72b (2026-06-10) single axiom-prose fix at paper17 line ~668 ('single axiom gapped_interface_axiom' -> 'since retired into the tracked Prop TPFConjecture'). D5's three matching sites (abstract ~l.104, section 1 ~l.158, section 13 ~l.1307) were fixed IN THE SAME COMMIT — source and bundle edited in tandem; verified aligned line-by-line. 2026-06-10 remediation themes verified present in D5 (applied directly to D5 by commits d83ff8b6/196a5a70, no paper17 counterpart exists — paper17 has zero Halenka/Verlinde/Luciano mentions): (1) Halenka-Miller PRD 102, 084007 (2020) relaxed-cluster framing (23 relaxed clusters, weak-lensing + X-ray profiles, nominal-assumptions caveat) at l.71 + l.847-858 + bibitem HalenkaMiller2020; (2) Verlinde-2017 no-go unit-coherent (sigma vs logB separated; ledger honestly 2-of-4 Bayes-decisive via both_decisive_bayes_bounds_exceed_jeffreys_decisive + 4-of-4 mixed-unit all_quantitative_bounds_disfavoured; renamed theorem verlinde_2017_no_go_via_cluster_mass_densities_halenka_miller resolves at EntropicGravityDarkEnergy.lean:248); (3) Luciano DeltaAIC=+4.7 pinned to Table II (abstract l.75-76 + l.888-905, barrow_aic_delta_below_jeffreys_decisive resolves at l.387). No content lift required. QuantumNetwork (6AP/6AQ) Lean content NOT absorbed — separate queued absorption event, out of scope here. Disclosure block (DISCLOSURE_TEXT.md Variant B, register-verified aristotle_used=no) installed in same session as a separate draft edit; pdflatex x2 clean (14pp). freshness_stale deliberately NOT cleared per reconciliation-task constraint (flag also covers the queued QuantumNetwork absorption).

## 2026-06-10 — Standard AI-disclosure block installed (draft edit, non-substantive)

- Source: (none — DISCLOSURE_TEXT.md application)
- Edit: `\section*{Methods and tools disclosure}` (Variant B — register-derived `aristotle_used=no` per `scripts/aristotle_usage_by_bundle.py` 2026-06-10 run) inserted immediately before `\begin{thebibliography}{99}` (paper_draft.tex ~l.1318). No pre-existing ad-hoc disclosure text existed; nothing normalized away.
- Substantive prose: UNCHANGED — no claims, counts, citations, or Lean references touched; stage13_redo_required remains false.
- Compile gate: pdflatex ×2 clean, zero errors (14pp / 1371023B).
- Metadata note: the Prose-revision-bookkeeping event above auto-bumped `last_lift` and cleared `freshness_stale`; both fields were deliberately restored (`last_lift=2026-05-12T13:00:00Z`, `freshness_stale=true`) per the reconciliation-task constraint — the flag also covers the separate queued Phase 6AP/6AQ QuantumNetwork absorption event, which was NOT absorbed here.
