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
