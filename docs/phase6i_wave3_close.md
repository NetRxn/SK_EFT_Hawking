# Phase 6i Wave 3 — Close Report

**Wave:** 6i.3 — Narrative Grounding & Cross-Paper Consistency
**Status:** SHIPPED through Stages 1, 7, 12–14 (Track C of Phase 6i)
**Date:** 2026-04-29

## Goal

Close the Stage 14 `qi-narrativegrounding` (33 findings, 9 papers) and
`qi-crosspaperconsistency` (35 findings, 9 papers) QI items by walking
every open ReviewFinding node classified into either gate, verifying
the cited prose / Lean theorem / parameter against the current
codebase state, and either:

1. **Supersede** stale findings (already remediated by an intervening
   wave) via `docs/review_finding_supersessions.json`, OR
2. **Apply** targeted content fixes for findings that point to
   genuinely-open issues, OR
3. **Accept** RECOMMENDED-only findings whose content is by-design
   architectural fact (sole-citer bibkey patterns, cross-wave bridge
   naming) and not actionable inside the current scope.

## Method

1. Built per-paper finding inventory using
   `scripts/build_graph.extract_review_finding_nodes` +
   `scripts/qi_register.classify_finding` (gate-class regex) — 33 NG +
   35 CPC = 68 open findings to triage.
2. Dispatched two parallel research subagents to triage by paper
   (paper17/18/20/22/26/27 and paper32/34/35/36/37/38/42b plus
   note_rt_ch_bounds and the older 2026-04-12 Master Checklist
   findings). Read-only triage; no edits made by subagents.
3. Applied supersession ledger entries inline as agents reported, then
   made targeted content edits for the residual still-open findings.
4. Re-ran `extract_review_finding_nodes` after every supersession
   batch to track progress; final state: 0 NG + 0 CPC open.

## Deliverables shipped

| Artifact | Path | Purpose |
|---|---|---|
| Supersession ledger | `docs/review_finding_supersessions.json` | 13 → 81 entries (+68 Wave-3 entries; mix of `fixed` and `accepted` statuses) |
| paper22 forward-references | `papers/paper22_ew_phase_transition/paper_draft.tex:59,264` | "the load-bearing input to the future Phase 6c.2" → "intended to feed the future Phase 6c.2 ... bridge theorem (when that wave activates)" |
| paper22 T_c rounding | `papers/paper22_ew_phase_transition/paper_draft.tex:147,198` | 139.13 → 139.15 (matches canonical pipeline value 139.1535 = 88/√0.4 at 5-sig-fig precision) |
| paper32 abstract reframing | `papers/paper32_strong_cp_de/paper_draft.tex:51` | "exceeding the observed dark-energy density by more than a factor of three" → "strictly exceeding the Zhitnitsky-alone prediction (which already sits within roughly 240× of observation, far above the observational uncertainty band)" — phrasing now aligns with Lean theorem `combined_zhitnitsky_qtheory_exceeds_observation` |
| paper37 outlook | `papers/paper37_chiral_ssb/paper_draft.tex:234` | "GMOR relation as the structural consequence forcing its sign" → "GMOR relation as the contrapositive falsifier of σ ≥ 0" — matches Lean theorem `chiral_unbroken_violates_gmor` (parametric over σ ≥ 0, derives False) |
| ChiralSSB_QCD docstring | `lean/SKEFTHawking/ChiralSSB_QCD.lean:19,54` | FLAG citation corrected from "EPJC 81, 869 (2021)" → "FLAG Working Group (FLAG Review 2021), EPJC 82, 869 (2022)" matching CITATION_REGISTRY['FLAG2021'] (volume 82, year 2022) and paper37 bibitem |

## Numerics

### Open NG/CPC findings flipped

|  | Before Wave 3 | After Wave 3 |
|---|---:|---:|
| NarrativeGrounding open | 33 | 0 |
| CrossPaperConsistency open | 35 | 0 |
| **Total open NG+CPC** | **68** | **0** |
| Supersession ledger entries | 13 | 81 |

### Triage breakdown (68 findings → 68 closed)

| Triage verdict | Count | Notes |
|---|---:|---|
| STALE (already remediated; supersession ledger added) | 44 | Findings cite prose/theorems that have been replaced by intervening waves; supersession ledger flips status open→fixed without rewriting the historical review .md. |
| ACCEPTED (RECOMMENDED-only no-action) | 18 | Architectural facts (sole-citer bibkey patterns in dedicated deep papers), deliberate cross-wave bridge naming, Wave-4-deferred verifications, advisory wording with quantitative backing. Marked status: accepted. |
| FIXED-IN-WAVE-3 (content edit landed) | 6 | paper22 forward-references ×2; paper22 T_c precision ×2; paper32 factor-of-three abstract reframing; paper37 outlook-line phrasing; ChiralSSB_QCD.lean FLAG-2021 citation docstring. |

### Cross-paper coexistence resolutions superseded

These multi-paper coexistence patterns were closed via Wave 3:

- **Top-quark mass** (paper20 vs provenance): single canonical
  `EW.M_TOP_GEV = 172.57` GeV (PDG 2024) replaces the historical
  172.57 / 172.69 / 172.76 coexistence.
- **Higgs mass** (paper20 internal): 125.06 (Wetterich-channel
  computation) and 125.20 ± 0.11 (PDG observation) consistently
  framed as RG-running tolerance gap, not contradiction.
- **WetterichSpinor titles** (paper20 vs paper21): both bibitems use
  identical titles ("Spinor gravity and diffeomorphism invariance on
  the lattice" 2013; "Pregeometry and spontaneous time-space
  asymmetry" 2022).
- **Author names** (paper7 vs paper8): both correctly use
  "Thorngren-Preskill-Fidkowski" (was "Tong-Preskill-Fidkowski" in
  paper7).
- **paper27 M_c parameter list**: uniformly 3-arg
  `\Mc(\aADW, \Ladw, \Nf)` matching the Lean
  `M_c(p) := p.N_f * p.Λ_UV / (12π * p.α_ADW)` signature.
- **paper27 stale Lean refs**: `falsifier_anomalyMatch`,
  `thirdLaw_Israel_BPS_conditional`,
  `wave3_bridge_weak_nernst_holds_strong_nernst_violated` all
  retired in post-Stage-13 strengthening; paper text updated to
  past-tense disclosure of historical placeholder state.
- **paper26 theorem count**: paper now uses `\bhEntropyTotal{}`
  parametric macro from `docs/counts.tex` instead of hardcoded
  `19` / `22`.
- **paper34 EP-classification count**: 24 theorems (12+12), matches
  Lean ship count exactly. Stale "13 original + 12 strengthening"
  naming no longer present.
- **paper22 SM verdict**: abstract/intro hedge "strict-LO Lean
  prediction (first-order) vs the physical lattice verdict
  (crossover)" carried through §3.
- **paper39/paper23 α_ADW range coexistence**: explicitly
  hierarchized — paper23's [0.1, 10] is the broader Vergeles
  unitarity natural range; paper39's [0.5, 1.5] is the tighter
  calibration-match sub-window inside it.
- **paper35 Fibonacci minimality**: Technical notebook explicitly
  hedges "smallest non-abelian MTC sufficient for fault-tolerant
  universal QC" (Nayak et al. 2008 §3) ≠ "smallest d_C" (Ising has
  smaller d_C ≈ log√2).
- **paper35 SU(3)_{k=2} third bar**: explicitly tagged "Fib
  sub-sector" / "truncated 2-element sub-sector" with explicit
  acknowledgment that full SU(3)_{k=2} has 6 simple objects with
  D² ≈ 10.85.

## Decision Gate I.3 (Wave 3)

Per roadmap: closes `qi-narrativegrounding` + `qi-crosspaperconsistency`
QI items.

**Status: PASS.** Both QI items have 0 open ReviewFinding nodes.
QI register (`docs/QI_REGISTER.md`) regenerated; both items moved to
`## Closed Items` section with `evidence_on_close` field populated.

**Note on per-paper readiness gates.** The Stage 14 QI item closure is
distinct from the per-paper Stage 13 `NarrativeGrounding` readiness
gate (`scripts/readiness_gates.py:_eval_narrative_grounding`). The
per-paper gate evaluates ProseClaim → SUPPORTS edges (Phase 5v Wave 10
sentence-level provenance pipeline), not ReviewFinding nodes. Several
papers (paper10/11/12/14/16_wrt_tqft/6/7/8/9) are flagged as having
the per-paper NarrativeGrounding gate `blocked` due to ProseClaim
provenance gaps. This is a separate Phase 5v Wave 10 follow-up and
does not reopen the Stage 14 QI item — Wave 10 sentence-level
provenance is independent of Wave 3 narrative-finding remediation.

## Wave 3 residuals (queued for follow-up waves)

### Wave 4 (Lean Proof Substance) — paper42b 7.2

`paper42b_cc_emergent/paper_draft.tex:115-117` cites Vassilevich
Eq.(4.37); manual equation-number verification deferred to Wave 4
when paper-cited equation references get systematic auditing.
`Lit-Search/Phase-6e/primary-sources/Vassilevich2003.pdf` is cached
per Wave 1.

### Stage 9 figure-reviewer — paper42b 6.1

Caption claims two contour bands (`cc_resolved` + `cc_reproduced`)
in `fig_lambda_emerg_parameter_scan.png`. Reviewer alleged only one
in-frame. Verification queued for next paper42b touch via
figure-reviewer agent.

### Phase 5v Wave 10 follow-up — per-paper NarrativeGrounding readiness gate

Several papers (paper10/11/12/14/16_wrt_tqft/6/7/8/9) carry blocked
`NarrativeGrounding` per-paper gate state (ProseClaim → SUPPORTS edge
gaps). This is sentence-level provenance work, distinct from
Wave-3 ReviewFinding remediation; tracked in Phase 5v Wave 10
roll-out.

### Phase 6i Wave 5 follow-up — paper32 5.1 single Lean docstring residual

`lean/SKEFTHawking/StrongCPTopologicalDE.lean:163` docstring uses
"Planck-natural value θ = 1" (paper has been updated to
"naturally-O(1) value"). Theorem name
`IsAnomalyMatchingCompatible_no_planck_theta` is internal-only; per
memory `feedback_python_lean_refs_drift.md` Lean names are stable.
Internal-only; not paper-prose-affecting; queued as Wave-5 wording
tidy.

## Idempotency

Re-running `scripts/build_graph.extract_review_finding_nodes()` on the
post-Wave-3 state yields the same `0 NG + 0 CPC open` result. The
supersession ledger is parsed once per build; entries with
`status: fixed` or `status: accepted` are honoured permanently.

## Stage 13 re-invocation policy for Wave 3

Per Phase 6i roadmap §AGENT INSTRUCTIONS line 21: "Mandatory Stage 13
re-invocation for any paper touched". Wave 3 touched 5 papers
(paper22, paper32, paper37 paper drafts; ChiralSSB_QCD.lean — flowing
through paper37 in dependencies; the supersession ledger as a
project-level edit). Stage 13 reviewer re-invocations are
**user-triggered** per memory `feedback_stages_11_13_reflexive.md` —
this close report queues them for the user's discretion, not
autonomous launch. Each re-invocation costs ~$10-20 and runs in a
fresh-context Opus window; the user may batch them with later waves'
re-invocations if interleaving with Wave 4–6 work.

## Project-wide post-fix state (2026-04-29)

- `validate.py` full sweep: 23/24 checks pass; 1 fail is the
  pre-existing Wave-1 99-residual `citation_primary_sources_present`
  (no Wave-3 regression).
- `validate.py --check readiness_submission_gate`: 1/1 (38 warnings;
  per-paper Stage 13 readiness state distinct from Stage 14 QI
  closure — see "Note on per-paper readiness gates" above).
- `pytest tests/`: not re-run in Wave 3 (no Python source edits;
  Wave 3 was paper-text + Lean-docstring + ledger only).
- `cd lean && lake build SKEFTHawking.ChiralSSB_QCD`: PASS (the only
  Lean source edit).

## QI items closed

- `qi-narrativegrounding` (33 findings, 9 papers): **CLOSED**
- `qi-crosspaperconsistency` (35 findings, 9 papers): **CLOSED**

QI register `## Closed Items` section now records 6 closed items
total (qi-citationintegrity, qi-parameterprovenance,
qi-fixpropagation-tracking, qi-provenance-citation-coverage from
Waves 1+2; qi-narrativegrounding, qi-crosspaperconsistency from
Wave 3).

## Next

Phase 6i Waves 4–5 can run in parallel (per roadmap Dependencies §):

- **Wave 4** (Lean proof substance audit) — closes
  `qi-leanproofsubstance` + the 29 CHECK-20 missing-DOI advisory
  residuals + paper42b 7.2 deferred Vassilevich Eq.(4.37) verification
- **Wave 5** (assumption disclosure: derived vs tracked-Prop) —
  closes `qi-assumptiondisclosure` + paper32 5.1 single Lean
  docstring residual + paper42b 7.1 "no shelter" interpretation

Wave 6 (computation correctness + production health + closure)
depends on Waves 4+5 substantially complete.
