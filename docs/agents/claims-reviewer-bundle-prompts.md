# Per-Bundle Stage-13 Review Anchor List

**Purpose:** The Phase 6i Wave 7 bundle architecture requires the
`physics-qa:claims-reviewer` and `physics-qa:figure-reviewer` agents to
operate at the bundle level rather than the per-paper level. Each
bundle has a different review profile (depth, scope, breadth, anchor
list). This document is the canonical per-bundle anchor list — the
specific load-bearing claims and citations the bundle's Stage-13 review
must verify.

**Companion to:** `docs/PAPER_STRATEGY.md` (canonical bundle
architecture) and `docs/PAPER_DRAFT_MAPPING.md` (per-draft → per-bundle
table).

**Created:** 2026-04-29 (Phase 6i Wave 7.2).

---

## How agents consume this document

The reviewer agents accept a `bundle_target` argument (one of the 13
bundle codes: `F`, `D1`–`D5`, `L1`–`L3`, `I1`, `I2`, `E1`, `E2`). Given
a bundle target, the agent:

1. Resolves the bundle's lifted source material via
   `scripts/bundle_clusters.py` and `docs/PAPER_DRAFT_MAPPING.md` §2
   ("Per-bundle source map").
2. Loads the bundle's per-section anchor list from this document.
3. Executes the bundle-appropriate review depth:
   - **Tier 2 (PRL splash):** stand-alone, single-paper depth.
   - **Tier 1 (deep):** intra-bundle consistency + cross-bundle
     consistency for cross-bridge claims.
   - **Tier 0 (flagship):** review-paper style, against published Tier 1
     bundles.
   - **Tier 3 (infrastructure):** software/methodology paper style,
     reproducibility-anchored.
   - **Tier 4 (experimental):** lightweight + device-parameter audit.
4. Produces a `papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md`
   review document.

The driver `scripts/review_runner.py --bundle <target>` orchestrates
this; see `scripts/review_runner.py --help`.

---

## Tier 0 — Flagship

### F. Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey

**Review profile:** review-paper style. Reviewer pulls published-version
DOIs / arXiv IDs from the citation cache (Phase 6i Wave 1 infrastructure)
and verifies each cited claim resolves correctly to the published Tier 1
bundle.

**Anchors (load-bearing, must verify):**
- Every published L1/L2/L3 Tier 2 bundle's central claim cited
  character-for-character.
- Every D1–D5 Tier 1 bundle's main result statement cited
  character-for-character.
- `RESEARCH_STATUS_OVERVIEW.md` proven-chains list current at the
  flagship-submission date.
- `ARCHITECTURE_SCOPE.md` §2 + §10 lifted verbatim and consistent with
  current state.
- Theorem / module / paper counts current per `docs/counts.tex`
  macros (no inline literals).

**Stage-13 BLOCKERs:**
- Any cited L*/D*/I*/E* claim drifts from its published form.
- Any inline numerical literal (per `validate.py --check
  numerical_literals` + `count_literals`).
- Any flagship section that cites a bundle still in preparation
  (`inprep: True` consistency must hold per the bundle's submission
  state).

---

## Tier 1 — Deep papers

### D1. Analog Hawking across three platforms

**Sources:** paper1, paper2, paper4, paper12 (BEC + polariton),
paper16_graphene_sk_eft.

**Anchors (load-bearing):**
- BEC analog Hawking dissipative correction `δ_diss = (1 + ξ²)⁻¹` at the
  fiducial parameters from `EXPERIMENTS['BEC_KIM_2014']`.
- Exact-WKB connection formula with the three non-perturbative effects
  (greybody factor, dispersive cut-off, sub-leading corrections).
- Polariton platform shot-count feasibility result from
  `feasibility.py:polariton_shot_count`.
- Graphene Dirac-fluid 92% Lean-theorem-reuse claim (verified against
  the Phase 5w cross-platform reuse counter).

**Stage-13 anchors specific to D1:**
- Cross-section consistency: the same dimensional analysis (linear
  density, [m⁻¹]) used across BEC, polariton, and graphene sections.
- The exact-WKB connection formula in §4 must match the Lean theorem in
  `WKBConnection.lean` (verified via `audit_paper_lean_refs.py`).

### D2. Anomaly constraints on SM particle content

**Sources:** paper7, paper8, paper9 (anomaly portion), paper10 (full
derivation as primary section).

**Anchors:**
- Z16 anomaly chain `dai_freed_spin_z4 ↔ Ω_5^{Spin×Z_4} ≅ Z_16` (pre-
  acknowledged Mathlib-bordism scope deferral; should be disclosed).
- Three-pillar synthesis: GS (Green-Schwarz) evasion, TPF (topological
  pivoting frame), modular generation `N_f ≡ 0 mod 3`.
- Drinfeld center cross-bridge to D4 §4 (the two D2 §3 + D4 §4
  occurrences must say the same thing).
- Quaternionic-spinor structure framing as motivation, not as a proven
  causal lemma.

**Stage-13 anchors specific to D2:**
- The `24 | c₋` chain claim (load-bearing for L2) must match between
  D2 §2 and L2 (see L2 below).
- "First quantum group / first rank-2 quantum group / first SU(3)
  fusion category in Lean 4" first-claim verifications via
  `qi-firstclaimverification` spot-check.

### D3. Emergent gravity through BH thermodynamics

**Sources:** paper3, paper5, paper6 (conditional), paper20–paper27 (gravity
chain), paper35 (cross-bridge), paper36–paper38 (QCD), paper39–paper43
(higher-curvature + nonlinear EFE + EC torsion).

**Anchors:**
- ADW gap equation + tetrad gap + bifurcation results.
- Emergent G_N: G_N^Sak = 12π/(N_f Λ_UV²) per Vassilevich Eq. (4.37)
  (already explicated in Wave 6 paper42b §3 expansion).
- Decision-Gate-E.2/E.3/E.4 biconditionals.
- Sakharov-Adler induced Newton constant ↔ heat-kernel a_2 coefficient.
- Stelle (α, β, γ) basis change at order a_4.
- Multi-channel PPN ratios (deflection α / precession (2α+1)/3 /
  ringdown α).
- Einstein-Cartan torsion |T_EC| ≃ 2.05×10⁻⁷⁷ GeV vs Kostelecky-
  Russell-Tasson 10⁻³¹ GeV bound — **not** the older `1.3×10⁻¹¹⁴ GeV`
  (Wave-6-fixed docstring drift).
- BCH four laws by regime (cross-bridge to L3 splash; same content).
- BH entropy from MTC counting + Kaul-Majumdar SU(2)_k -3/2 closed form.

**Stage-13 anchors specific to D3:**
- Cross-bridge to L1 (GW170817 / vestigial graviton) — D3 §6 + L1
  must report the same numerical Δc/c constraint.
- Cross-bridge to L3 (BCH four laws) — D3 §8 + L3 must agree.
- Cross-bridge to D4 §7 (QEC-Holography) — D3 §9 cross-bridge claim
  must match D4's framing.

### D4. Topological quantum computation foundations

**Sources:** paper9 (Drinfeld center), paper11 (primary kernel), paper14,
paper16_wrt_tqft, paper18, paper35 (QEC), note_rt_ch_bounds.

**Anchors:**
- First quantum-group formalization (`U_q(sl_2)`, `U_q(sl_3)`).
- Ising MTC complete + trefoil = −1 + figure-eight knot invariants.
- WRT TQFT partition functions + WRT surgery formula.
- Doublon SWAP gate + Berry-phase + first symmetry-protected gate.
- Hayden-Preskill structural QEC on horizon-MTC substrate.
- RT / Casini-Huerta knife-edge biconditional + tracked Props.

**Stage-13 anchors specific to D4:**
- Cross-bridge to D2 §3 (Drinfeld center) — D2 + D4 must say the same
  thing about the Drinfeld center construction.
- D4 §8 (RT/CH) must reference the W3 `H_HorizonBoundaryCondition`
  tracked Prop honestly.

### D5. Dark sector under substrate constraints

**Sources:** paper17, paper29, paper32, paper34, paper42b (CC-channel
secondary).

**Anchors:**
- Six Phase-5x DM mechanism classification.
- BBN classification (paper29) — N_eff bounds and BBN-conformant vs
  -violator partition.
- Zhitnitsky topological-DE absorption: ρ ~ Λ_QCD⁶/M_P² ≈ 6.71×10⁻⁹
  eV⁴.
- EP-violation matrix; vestigial-only verdict.
- CC-channel constraint: heat-kernel a_0 does not produce Λ_obs
  naturally.

**Stage-13 anchors specific to D5:**
- Cross-bridge to D3 §21 (paper42b CC reproduction) — D3 + D5 §7 must
  use the same heat-kernel a_0 coefficient.
- Cross-bridge to D2 (anomaly classification of DM candidates).

---

## Tier 2 — PRL splashes

### L1. GW170817 / vestigial-graviton

**Source:** paper25.

**Anchors:**
- LIGO Δc/c bound from Abbott 2017 GW170817 detection paper.
- Vestigial-graviton dispersion forecast at the project's natural χ_vest
  range.
- GW170817 falsification factor ~7×10¹⁴ in the natural range.

**Stage-13 BLOCKERs:**
- The numerical Δc/c bound must match D3 §6 character-for-character
  (cross-bundle consistency check via Wave 7.3).
- Abbott 2017 detection paper bibitem must be cached and `doi_verified:
  True` (Wave 1+2 infrastructure).

### L2. Three generations from modular invariance

**Source:** paper10.

**Anchors:**
- Modular generation constraint `N_f ≡ 0 mod 3` derived from the
  generation-anomaly discriminant.
- The `24 | c₋` chain claim load-bearing in the discriminant
  computation.
- Ext computation over Steenrod subalgebra A(1) (first-formalization
  claim must be spot-checked against Agda/Coq registries).

**Stage-13 BLOCKERs:**
- L2 + D2 §2 must use the same Ext-computation chain.
- "First Ext computation over Steenrod subalgebra A(1)" first-claim
  verification per `qi-firstclaimverification`.

### L3. BCH four laws by regime

**Source:** paper27 (already submission-ready as of 2026-04-27).

**Anchors:**
- BCH four laws by regime partition (`H_RegimePartition` Prop bundle
  with M_c_form_consistent witness).
- Balbinot 2005 BEC-acoustic primary anchor (NOT the older
  3He-A heating analogy — `feedback_deep_research_analog_conflation.md`
  applies).
- Hawking 1975 Schwarzschild contrast as the secondary anchor.

**Stage-13 BLOCKERs:**
- L3 + D3 §8 must agree on the regime-partition definition.
- Balbinot 2005 must be cached and primary; not 3He-A heating.

---

## Tier 3 — Infrastructure

### I1. Verification methodology with worked cases

**Source:** paper15 (substantially expanded) + worked-case curated set.

**Anchors:**
- FirstOrderKMS Aristotle counterexample case (Phase 1).
- Gap-solution-bounded counterexample case (Phase 5d).
- Chirality-wall axiom decomposition case (Phase 5h).
- The 14-stage Wave Execution Pipeline.
- The supersession ledger pattern + Pipeline Invariant #13 (Wave 6).

**Stage-13 profile:** software/methodology paper style; each worked
case must trace to a reproducible Aristotle run ID OR commit-pinned
counterexample.

### I2. Verified statistical estimators + lean-tensor-categories

**Sources:** Phase 5c VerifiedJackknife; Phase 5o Wave 4
lean-tensor-categories.

**Anchors:**
- VerifiedJackknife test suite cross-references.
- lean-tensor-categories Mathlib upstream cycle (when a PR is in
  review).

**Stage-13 profile:** software paper style; each function must trace
to a passing test.

### I3. Verified Stochastic Calculus for Mathlib4

**Sources:** Phase 6o.ζ Lean module synthesis (no per-paper substrate;
analogous to I2's lean-tensor-categories framing). See
`temporary/working-docs/phase6n/i3_bundle_scoping.md` for the bundle
scoping document.

**Anchors:**

1. **First-of-its-kind formalization claims.** Each "first
   formalization in any proof assistant" claim (stochastic integral,
   quadratic variation, Itô's lemma, Novikov, Cramér, Sanov, Varadhan)
   must be supported by a literature search showing no prior
   Lean/Coq/Isabelle/HOL Light/Mizar formalization exists.
2. **Mathlib substrate consumed.** Claims about consuming Brownian
   motion (Degenne–Ledvinka–Marion–Pfaffelhuber, "Formalization of
   Brownian motion in Lean", arXiv:2511.20118, 2025), Doob martingales
   (Ying-Degenne 2022), Markov kernels (Degenne, "Markov kernels in
   Mathlib's probability library", arXiv:2510.04070, 2025;
   primary-source verified Phase 7 absorption Session 5
   2026-05-08 — supersedes carry-forward "Marion 2025"
   misattribution), sub-Gaussian variables, must trace to the named
   upstream Mathlib commits.
3. **Reproducibility.** Each Lean module must build (no sorry, except
   documented stubs registered in `SORRY_GAPS`); the Mathlib upstream
   coordination memo's PR list must be live and cite-able.
4. **`LDPCompatibleSKEFT` typeclass cross-bridge.** Claims about D3 /
   D5 / E1 downstream consumers must trace to specific Lean theorems
   in those modules that explicitly invoke the typeclass.
5. **Mathlib upstream coordination integrity.** Claims about
   coordination with Degenne et al. (Brownian motion authors:
   Degenne, Ledvinka, Marion, Pfaffelhuber) or any Mathlib maintainer
   must trace to actual Zulip / GitHub coordination artifacts (not
   unilateral assertions).

**Stage-13 profile:** software/methodology paper style (Tier 3 — same
profile as I1 / I2). Each first-of-its-kind claim must trace to a
reproducible Aristotle run ID OR commit-pinned counterexample where
applicable.

---

## Tier 4 — Experimental letters

### E1. Paris-LKB polariton letter

**Source:** paper12 (companion content) + Phase 5u Wave 21 cover letter.

**Anchors:**
- Polariton platform shot-count feasibility.
- LKB-specific device parameters (per the experimental team's published
  device specs).

**Stage-13 profile:** lightweight letter review + device-parameter
audit pass.

### E2. Dean-Kim-Lucas graphene letter

**Source:** paper16_graphene_sk_eft (companion content).

**Anchors:**
- Graphene Dirac-fluid SK-EFT prediction.
- Dean-Kim-Lucas device parameters.

**Stage-13 profile:** lightweight letter review + device-parameter
audit pass.

---

## Cross-bundle anchor summary table

| Cross-bridge | From | To | Anchor |
|---|---|---|---|
| GW170817 Δc/c | L1 | D3 §6 | Same numerical bound |
| BCH four laws | L3 | D3 §8 | Same regime partition |
| Modular generation | L2 | D2 §2 | Same Ext + 24 \| c₋ chain |
| Drinfeld center | D2 §3 | D4 §4 | Same construction |
| QEC ↔ horizon-MTC | D3 §9 | D4 §7 | Same cross-bridge |
| CC channel | D3 §21 | D5 §7 | Same heat-kernel a_0 |
| Polariton companion | D1 §6 | E1 | Same LKB device specs |
| Graphene companion | D1 §7 | E2 | Same Dean-Kim-Lucas specs |

The Wave 7.3 `validate.py --check bundle_consistency` walks each
cluster in `cluster_bundle_index.json` (built by Wave 7.1
`bundle_clusters.py`) and flags any `cross_bundle: true` cluster whose
member sentences disagree on the cross-bridge's numerical content.

---

*Document created 2026-04-29 (Phase 6i Wave 7.2). Companion to
`PAPER_STRATEGY.md` and `PAPER_DRAFT_MAPPING.md`. Loaded by
`physics-qa:claims-reviewer` and `physics-qa:figure-reviewer` when
invoked with `bundle_target=<target>`.*
