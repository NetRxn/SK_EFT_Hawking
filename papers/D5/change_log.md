# Bundle D5 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

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
