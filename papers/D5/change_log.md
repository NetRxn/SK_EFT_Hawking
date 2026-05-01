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
