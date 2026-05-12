# Bundle I1 — Change Log

_Initial bookkeeping created 2026-05-01T13:09:42Z by `scripts/bundle_source_manifest.py`._

## 2026-05-01 — Phase 7a sub-wave 7a.2 initial draft (synthesis-driven)

Authored I1 paper_draft.tex as a synthesis-driven new composition,
not a stitched lift. Sources synthesized (per Phase 7a sub-wave 7a.2
step 3 outline):

- `paper15_methodology` (verification methodology backbone)
- `paper44_riemannian_connection` (sidebar §12)
- Phase 6f Wave 1-6 algebraic-GR substrate rosters (sidebar §11)
- Phase 6g Wave 5 structural-Prop scoping pattern (sidebar §13)
- `WAVE_EXECUTION_PIPELINE.md` (current 14-stage version + invariants)
- `CLAUDE.md` (preemptive-strengthening discipline + 6 anti-patterns)
- Phase 7a robustness infrastructure (`BUNDLE_LIFT_PROCEDURE.md` +
  `LATE_PHASE6_ABSORPTION_PROTOCOL.md` + bundle architecture)

Section structure:

- §1 Introduction (substantive — fully drafted)
- §2 Three-layer verification architecture (substantive — fully drafted)
- §3 Worked case 1: FirstOrderKMS Aristotle counterexample (stub w/ outline)
- §4 Worked case 2: gap-solution-bounded conjecture disproof (stub w/ outline)
- §5 Worked case 3: chirality-wall axiom decomposition (stub w/ outline)
- §6 Fourteen-stage wave execution pipeline (substantive — fully drafted)
- §7 Preemptive-strengthening discipline (substantive — fully drafted)
- §8 Sentence-level provenance + cross-paper consistency clusters (stub)
- §9 Aristotle automated theorem prover integration (stub)
- §10 Fresh-context adversarial-reviewer pattern (stub)
- §11 Algebraic-general-relativity substrate first-formalizations (stub)
- §12 Riemannian connection sidebar (stub)
- §13 Structural-Prop scoping under Mathlib-dependency fallback (stub)
- §14 Lessons and future work (substantive — fully drafted)

Key extensions over paper15_methodology baseline:
- Pipeline expanded from 12 → 14 stages (Stage 3a interactive Lean,
  Stage 13 adversarial-review, Stage 14 meta-process QI)
- Invariants expanded from 10 → 14 (placeholder non-load-bearing,
  no heartbeat overrides, primary-source citation cache,
  provenance-DOI-in-registry, QI register auto-regen,
  bundle-assignment-mandatory)
- Six anti-pattern preemptive checklist (P2-P7)
- Bundle architecture as Invariant 14
- §11/§12/§13 sidebars on Phase 6f/6g substrate work

Stage-13 redo required: yes. Reviewer triple (Stage 9/10/13) to be
invoked once §3-§5 + §8-§13 are filled in.

## 2026-05-01 — Smoke-test reset (superseded)

Earlier today (2026-05-01T12:22Z) `scripts/bundle_append.py` smoke
test ran paper15+paper44 → I1 §1+§12 to validate the script
end-to-end. The test left a placeholder paper_draft.tex which
conflicted with synthesis framing; reset before authoring real I1.

## 2026-05-01T15:30Z — Phase 7a sub-wave 7a.2 stub completion

All 9 previously-stubbed sections authored substantively. Total
1338 lines / 14 sections / 0 stub markers. Substrate sourced via
two parallel explore agents:

- §3 FirstOrderKMS Aristotle counterexample — substantive prose
  using `lean/SKEFTHawking/SKDoubling.lean` lines 351-439, Aristotle
  run 270e77a0, full algebraic FDR (7 component-level identities,
  not 4) and the noise-floor consequence ($i_3 = 0$).
- §4 Gap-solution-bounded conjecture disproof — substantive prose
  using `lean/SKEFTHawking/TetradGapEquation.lean` lines 304-340,
  Aristotle run 79e07d55, explicit counterexample
  $G = 1/(c_4/2 \cdot (1 - \log 2))$ with $\Delta = 1 = \Lambda$
  fixed-point saturation. Original false claim preserved as
  commented-out stub at lines 316-325.
- §5 Chirality-wall axiom decomposition — substantive prose using
  `lean/SKEFTHawking/EWBaryogenesisChiralityWall.lean`,
  AXIOM_METADATA `chirality_wall_three_pillars` (3 hard tier),
  9-fold structural decomposition (3 pillars × 3 sub-lemmas each
  for Z₁₆ + crossover obstructions), all 9 sub-lemmas closed in
  single Aristotle priority batch. Surfaced hidden
  sphaleron-suppression dependency.
- §8 Sentence-level provenance + bundle architecture — sentence ID
  schema, content-hash IDs that survive prose edits, claim-cluster
  registry with `cross_bundle: true` flag, validate.py CHECK 21
  bundle_consistency, 13-bundle 5-tier publication architecture
  (F + D1-D5 + L1-L3 + I1-I2 + E1-E2), append-only mapping table,
  bundle_metadata.json schema, BUNDLE_LIFT_PROCEDURE.md (14 steps),
  LATE_PHASE6_ABSORPTION_PROTOCOL.md (stages A-G), Pipeline
  Invariant 14.
- §9 Aristotle integration — historical shift from primary-tool to
  fallback-for-residual after Stage 3a (lean-lsp-mcp) introduced
  ~1000× speedup. Three retained Aristotle indications: large
  tactic search spaces, post-decomposition batch closure, and
  diagnostic counterexample production. Run-record summary:
  78dcc5f4 (25-thm single-batch record), 79e07d55 (gap-equation
  batch with the counterexample of §4).
- §10 Fresh-context adversarial-reviewer pattern — April 2026
  external-review 13-dimension seed event; fresh-context property
  as load-bearing design constraint; 8 finding classes against 11
  readiness gates; ReviewFinding graph nodes + supersession ledger
  + readiness_submission_gate; bundle-level extension via
  scripts/review_runner.py --bundle <X> --prep-brief.
- §11 Phase 6f W1-W6 substrate first-formalizations sidebar —
  Curvature.lean (16 thms — algebraic Riemann + first Bianchi +
  pair symmetry), EinsteinTensor.lean (9 thms — dim-4 trace +
  vacuum biconditional + Λ-vacuum cross-bridge), EnergyConditions
  (8 thms — NEC/WEC/SEC/DEC), ExactSolutions (16 thms — Mink/dS/
  AdS/Schwarzschild Kerr-Schild), ADMFormalism (10 thms —
  Hamiltonian + momentum constraint), TetradFormalism (5 thms).
  64 thms / 0 sorry / 0 new axioms / exhaustive prior-art audit
  on file at Lit-Search/Phase-6f/audit.
- §12 Riemannian connection sidebar — IsLorentzianMetric typeclass
  (no prior art in any proof assistant); Wave 7
  (LorentzianMetric + RiemannianConnection, 13 thms — Christoffel-
  quadratic Riemann antisymmetry + Koszul Levi-Civita closed form);
  Wave 8 (RiemannCoordinate + RiemannDifferentialBianchi +
  BundleRiemannAux + BundleRiemann + LeviCivita, 44 thms — full
  coordinate Riemann + algebraic + differential Bianchi + bundle-
  level via Bonn IsCovariantDerivativeOn + cyclic Jacobi for
  manifold Lie bracket + bundle-level Levi-Civita uniqueness via
  Koszul-bilinear-form). 2 Mathlib upstream PRs in preparation.
- §13 Structural-Prop scoping discipline — Mathlib-PDE-fallback
  pattern. Phase 6g W5 (CauchyProblem.lean for Einstein vacuum
  Cauchy problem); W9 (Riccati / Mazur / curve-Penrose / area, 20
  thms post-audit); W10 (WaveEquation1D distillation: 6 thms —
  IsClassicalWaveSolution + 2 explicit witnesses + linearity
  corollary + IsLocallyWellPosed cross-bridge). Pattern was
  encoded after ~2 months of recoverable cost from in-project PDE
  reinvention.

Bookkeeping updated: `append_log.json` event added with
agent_run_id `phase7a-7a.2-stubs-2026-05-01T15:30:00Z` and 22
referenced Lean modules. `bundle_metadata.json` `last_lift` →
2026-05-01T15:30:00Z; status notes updated.

Stage-13 redo required: yes. Reviewer triple (Stage 9/10/13) to
be invoked next; per user directive 2026-05-01 they run as
background processes against the bundle target I1.

## 2026-05-06 — Lift-section from `_phase6n_W2b_lean_only` (§8)

- Source title: Quantum Crooks no-go (Perarnau-Llobet)
- Lift action: Lift-section
- Insertion point: §8
- Stage-13 redo required: yes
- Notes: D.2 sidebar: Phase 6n W2b methodology case — typeclass-connections cross-bridge pattern; QuantumCrooks/SKEFTConnection IsReservoirCoupled non-vacuity strengthening

## 2026-05-06 — Lift-section from `_phase6o_W2a_lean_only` (§11)

- Source title: APS-η for analog horizons
- Lift action: Lift-section
- Insertion point: §11
- Stage-13 redo required: yes
- Notes: D.2 sidebar: Phase 6o W2a methodology case — substrate-discovery pattern (predicate-level operationalization at Wave 2a.2 + per-substrate concrete computation at Wave 2a.3-5; ³He-A unique non-degenerate cell)

## 2026-05-06 — Lift-section from `_phase6o_W3a_lean_only` (§7)

- Source title: G10 ETH-α productive-value refutation tableau: `ETH/Predicates.lean` (5 candi...
- Lift action: Lift-section
- Insertion point: §7
- Stage-13 redo required: yes
- Notes: D.2 sidebar: Phase 6o W3a methodology case — parallel-axiomatization productive-value Aristotle-driven tableau pattern (5 candidate ETH axiomatizations + 3 concrete refutation theorems)

## 2026-05-06 — REVISION required by Phase 6n.γ (D.3 GATE 1, user-auth granted)

I1 §3 (Worked Case 1: FirstOrderKMS Aristotle Counterexample) **substantively reframed** from "project-original axiom replaced by stronger one" to "first-order projection of the published Glorioso-Liu axiomatic skeleton."

**Substantive content changes:**

- New opening framing paragraph cites the published axiomatic anchor:
  Crossley-Glorioso-Liu (CGL) JHEP 09 (2017) 095 (closed-time-path
  action with hermiticity, reflection positivity Im S ≥ 0, local KMS
  Z₂); Glorioso-Crossley-Liu II JHEP 09 (2017) 096 (dynamical-KMS Z₂
  in any local-equilibrium state); Glorioso-Liu (arXiv:1612.07705)
  local second-law derivation ∂_μ J^μ_S ≥ 0; Liu-Glorioso TASI
  PoS TASI2017 (2018) 008 pedagogical version; Jain-Kovtun JHEP
  01 (2024) 162 UV-realization ambiguity in dynamical-KMS.

- Renamed transport coefficients (κ, ν) → (γ_1, γ_2) to match the
  Lean code's DissipativeCoeffs structure (`SKDoubling.lean` lines
  244-280). The Lean naming is "γ_1: isotropic phonon damping
  (related to bulk viscosity); γ_2: anisotropic damping along the
  superfluid flow." The original (κ, ν) labeling did not match the
  code; the rename is a hygiene correction available with or without
  6n.γ, rolled into this batch.

- Reclassified the original `KMSSymmetry` axiom as a **preliminary
  transform-level constraint** (the field-level transform ψ_a → ψ_a
  + iβ ∂_t ψ_r acts only on 4 of 9 components). Aristotle's
  counterexample c = (0,0,0,0,0,0,0,1,0) is now framed as flagging
  the gap between the transform-level and algebraic-level forms.

- Reclassified the strengthened `FirstOrderKMS` axiom as the
  **first-order projection of the published dynamical-KMS axiom**.
  The 4-of-9 / 5-of-9 partition Aristotle exposed is, in the new
  reading, a *theorem* of first-order projection: the four components
  whose KMS partners fit within the first-order budget vs the five
  whose partners exceed it and surface at second order in the
  Glorioso-Liu loop expansion (formalized in the program's
  GloriosoLiu/SecondOrderProjection module).

- Figure 4 caption upgraded to identify which constraint each panel
  corresponds to (transform-component vs algebraic-FDR-projection of
  dynamical-KMS).

- Closing punchline preserved verbatim ("Aristotle's failure to prove
  a wrong statement is the substantive content of this case") plus
  added explanatory clause naming the substantive *why* (the original
  axiom omitted the second-order content the published dynamical-KMS
  axiom carries).

**Citations added to thebibliography (5 new bibitems):**

- `CrossleyGloriosoLiu2017` — JHEP 09 (2017) 095, arXiv:1511.03646.
- `GloriosoCrossleyLiu2017` — JHEP 09 (2017) 096, arXiv:1701.07817.
- `GloriosoLiu2018` — arXiv:1612.07705 (already in CITATION_REGISTRY).
- `GloriosoLiu2018TASI` — PoS TASI2017 (2018) 008, arXiv:1805.09331
  (NEW; added to CITATION_REGISTRY 2026-05-06; primary-source cache
  fetch deferred).
- `JainKovtun2024` — JHEP 01 (2024) 162, arXiv:2309.00511 (NEW;
  added to CITATION_REGISTRY 2026-05-06; primary-source cache fetch
  deferred).

**Source verification (per user direction):** All five references
verified via WebFetch + arXiv abstract reads + JHEP DOI confirmation
2026-05-06. Pre-draft framing of "six axioms + one load-bearing
theorem" preserved as program-level synthesis reading; specific
attributions in the new prose hew to what each cited paper actually
says (CGL: CTP + Im S ≥ 0 + local KMS; CGL II: dynamical KMS Z₂ +
local equilibrium; GL: ∂_μ J^μ_S ≥ 0 from Z₂ + classical-limit
unitarity remnant + local equilibrium; JK: UV-realization ambiguity).

**LaTeX compile gate (per BUNDLE_LIFT_PROCEDURE.md §7):** `pdflatex
paper_draft.tex` clean. 21 pages, 925 KB. Only LaTeX Font Warning
advisories (project-wide pre-existing pattern; no Errors).

**Stage 9/10/13 redo required:** yes. Per protocol §F, the I1
reviewer triple must re-clear before bundle close.

**D.3 cross-bundle propagation (cross-ref-only, no prose change):**
D3 §8 (entropy-current second-law content) and L3 (BCH four laws
second-law statement) absorb a cross-reference upgrade pointing at
the formalized `Glorioso_Liu_local_second_law` theorem. This is
already registered via the `_phase6n_W2a_lean_only` D.2 absorption
event for L3 + the D.3 GATE 2 work (Phase 6n.ζ Sakharov ↔
horizon-Crooks, separately tracked). No prose change needed in D3
or L3 from GATE 1 alone.

**Pre-draft consumed:** `temporary/working-docs/phase6n/6n_gamma_I1_reframing_predraft.md`.

Pre-existing GREEN reviewer-triple state (Stage 9 yellow / Stage 10
green / Stage 13 green from 2026-05-01) reset to pending pending
re-review.

## 2026-05-11 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event for Stage-13-sweep freshness cleanup)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-11 Stage-13-sweep freshness cleanup: paper15_methodology/tables/table1_stages.tex + table2_checks.tex regenerated at 12:56. I1 bundle paper_draft.tex does NOT \input source paper tables; bundle compile path unaffected. No bundle content change required; last_lift bumped.

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper44_riemannian_connection signature-falsifier wording softened; I1 bundle own draft 'this paper is the first bundle to be drafted under the architecture' -> 'this paper is drafted under that architecture'. I1's §lessons-learned reference at line 1141 (citing a historical 'first machine-checked' claim that had unrecognized Coq prior art) is PRESERVED INTACT - it documents the failure mode that motivated Stage-13 and is load-bearing pedagogical content.
