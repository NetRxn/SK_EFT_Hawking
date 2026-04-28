# Phase 6i Wave 5 — Close Report

**Wave:** 6i.5 — Assumption Disclosure: Derived vs Tracked-Prop
**Status:** SHIPPED through Stages 5, 12–14 (Track C of Phase 6i)
**Date:** 2026-04-29

## Goal

Close the Stage 14 `qi-assumptiondisclosure` QI item (30 findings, 11
papers) by applying paper41's "derived (witness shipped) vs
tracked-hypothesis (consumer-side load-bearing)" distinction across
every paper using `H_*`-named Props, plus all related disclosure
findings (cubic_coeff_nonneg structure invariants, lepton-number
violation predicates, naturalness-band tracked-Props, scope
deferrals).

## Method

Same playbook as Waves 3+4:
1. Enumerated 30 open AssumptionDisclosure ReviewFinding nodes via
   `extract_review_finding_nodes()` + `qi_register.classify_finding()`
2. Triaged each against current Lean source / paper text / notebook
   state via targeted `grep` + `Read` operations
3. For STALE/ACCEPTED findings, applied supersession ledger entries
   in `docs/review_finding_supersessions.json`
4. For genuinely-open findings, applied targeted content fixes
   (1 notebook cell update via `NotebookEdit`)

## Deliverables shipped

| Artifact | Path | Purpose |
|---|---|---|
| Supersession ledger | `docs/review_finding_supersessions.json` | 107 → 137 entries (+30 Wave-5 entries; mix of `fixed` and `accepted`) |
| chiPT disclosure | `notebooks/Phase6d2_ChiralSSB_Technical.ipynb` cell `p37t-3-md` | Added explicit "It is leading-order in chiral perturbation theory" + NLO-band disclaimer to GMOR §3 cell, paralleling Stakeholder §6 honest-scope disclosure (paper37 finding 6.1 fix) |

## Numerics

### AssumptionDisclosure findings flipped

|  | Before Wave 5 | After Wave 5 |
|---|---:|---:|
| AssumptionDisclosure open | 30 | 0 |
| Supersession ledger entries | 107 | 137 |

### Triage breakdown (30 findings → 30 closed)

| Triage verdict | Count | Notes |
|---|---:|---|
| STALE (already remediated) | 18 | Findings cite issues remediated in earlier-wave Stage-13 strengthening passes (`H_LeptonNumberViolated := True` refactored to substantive `G_LV ≠ 0`; `transition_order_from_microscopic_parameters` retired; paper22 Structure-invariants subsection ships disclosing all four EWFiniteTParams positivity invariants; paper27 Wave-5 rewrite around Balbinot 2005 anchor; `IsHiggsBilinear` removed in favor of `IsHiggsBilinearCandidate` in paper20; `H_ScalarChannelIsTetradBifurcationOutput` disclosed in 9 paper20 sites; paper35 §VII parametrized S_horizon disclosure; paper37 abstract contrapositive reframing; "Ramanujan" attribution retired). |
| ACCEPTED (deliberate API / disclosed pattern / advisory) | 11 | RECOMMENDED-only items where the structural pattern is appropriate: `H_HSCovariantBosonisation := IsHiggsBilinear` is deliberate physics-naming-vs-content-API distinction (assumption name carries physics meaning, definitional content is structural Prop, extraction theorem is API plumbing); `H_RegimePartition.M_c_form_consistent` deliberate witness-construction; Walker-Wang witness at KSS_BOUND boundary (standard Prop-band witness pattern); Decision-Gate-E.2 hypotheses paper-level abstraction; spin-3-manifold geometric assumption Lean-Prop encoded; etc. |
| FIXED-IN-WAVE-5 (content edit landed) | 1 | paper37 finding 6.1: Phase6d2_ChiralSSB_Technical.ipynb cell `p37t-3-md` updated via NotebookEdit to add explicit chiPT-leading-order + NLO-band disclosure paralleling Stakeholder §6. |

### Disclosure-pattern reflections (post-wave audit)

The Wave-5 sweep surfaces a recurring pattern: the project's
preemptive-strengthening discipline (CLAUDE.md §"Preemptive-strengthening
discipline") catches the obvious cases at first-pass theorem statement
time, but a substantial fraction of AssumptionDisclosure findings are
RECOMMENDED-class advisory items that flag defensible API patterns:

- **Physics-name vs content-API distinction.** When the project ships
  `H_HSCovariantBosonisation := IsHiggsBilinear` with a thin extraction
  theorem `hs_bosonisation_yields_higgs_bilinear (h : H) : IsHiggsBilinear φ
  := h`, that's not a tautology — it's a deliberate API where the
  assumption name carries the physics scenario ("HS-covariant
  bosonisation") and the definitional content is the structural Prop.
  Consumers can pattern-match on the assumption name (semantic clarity)
  while downstream proofs still operate on the structural Prop.
- **Witness vs falsifier API plumbing.** `H_RegimePartition.M_c_form_consistent
  : 0 < M_c p` is "trivially provable from M_c_pos" — but exposing it as
  a bundle field lets consumers pattern-match without going through the
  free-standing theorem. Standard structure-of-Props design.
- **Paper prose vs Lean signature.** Lean theorem signatures carry
  positivity hypotheses (Λ > 0, N_f > 0, etc.) that paper-prose
  abstracts via "in the natural-parameter regime". This is appropriate
  layering: Lean is precise; paper-prose is explanatory.

These patterns warrant a memory entry codifying when "tautology"
flags from adversarial review are advisory-only vs load-bearing.

## Decision Gate I.5 (Wave 5)

Per roadmap: closes `qi-assumptiondisclosure` QI item.

**Status: PASS.** All 30 AssumptionDisclosure ReviewFinding nodes
have status: fixed (or accepted with disclosure rationale); 1 actual
content fix applied; Phase 6i Track A–D progresses to Wave 6.

## Wave 5 residuals queued

- Wave 6: `qi_register.py` status-filter fix (still queued from Wave
  4 — clusterer counts all findings regardless of status; Closed-Items
  section is authoritative)
- Wave 6: paper42b 7.2 Vassilevich Eq.(4.37) primary-source manual
  verification (carry-forward from Wave 3 + Wave 4)
- Wave 6: final pipeline-doc updates accumulated through 6i (Stage 1
  + Stage 13 amendments + new validate.py checks documented in
  WAVE_EXECUTION_PIPELINE.md)
- Wave 6: final QI register sweep — confirm all 8 entry-state items
  closed with `evidence_on_close` fields

## Idempotency

Re-running `extract_review_finding_nodes` on post-Wave-5 state confirms
0 open AssumptionDisclosure findings.

## Stage 13 re-invocation policy

Wave 5 touched 1 notebook (Phase6d2_ChiralSSB_Technical.ipynb) — single
cell content addition. Stage 13 reviewer re-invocation is user-triggered
per memory `feedback_stages_11_13_reflexive.md`; queued at user
discretion.

## Project-wide post-fix state (2026-04-29)

- `validate.py --check parameter_provenance`: PASS (no regression)
- `validate.py --check provenance_doi_in_registry`: PASS (0 missing
  DOIs from Wave 4; preserved through Wave 5)
- LeanProofSubstance / NarrativeGrounding / CrossPaperConsistency /
  AssumptionDisclosure open findings: all 0
- Supersession ledger: 137 entries (was 107 at Wave-4 close)
- Phase 6i status: Waves 1+2+3+4+5 SHIPPED. Wave 6 (final closure)
  unblocked.

## QI items closed

- `qi-assumptiondisclosure` (30 findings, 11 papers): **CLOSED**

QI register `## Closed Items` section now records 9 closed items
total (4 Waves 1+2 + 2 Wave 3 + 2 Wave 4 + 1 Wave 5).

## Next

Phase 6i Wave 6 (Computation Correctness, Production Run Health, &
Process Wiring Close):
- Spot-check open ComputationCorrectness findings (5 findings, 2
  papers); recompute and patch
- Audit "production run" claims for backing-data presence
  (ProductionRunHealth)
- Aggregate all new `validate.py` checks added during Phase 6i
  (W1 citation cache CHECK 19; W2 strict-mode + provenance_doi_in_registry
  CHECK 20)
- Final pipeline-doc updates: WAVE_EXECUTION_PIPELINE.md amendments
- `qi_register.py` status-filter fix
- Final QI register snapshot — confirm all 8 entry-state items closed
- Phase 6i CLOSED at Wave 6 close; Track E (Wave 7 — Paper Strategy
  Integration) gated on user authorization
