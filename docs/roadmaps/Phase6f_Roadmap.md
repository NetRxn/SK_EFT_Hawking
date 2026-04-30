# Phase 6f: Classical GR Lean Infrastructure — Curvature, Einstein Tensor, Energy Conditions, Exact Solutions, ADM, Tetrad

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §9. Classical-GR infrastructure in Lean that Phases 6e and 6g depend on. Mostly sits on top of Bonn's differential-geometry formalization and does not require condensate-side input. External Mathlib progress is the main risk.*

**2026-04-29 catch-up update — Bonn `CovariantDerivative` HAS LANDED in our pinned commit.** Verified via local audit of `lean/.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic.lean,Torsion.lean}`. Authors: Massot, Rothgang, Macbeth (2025). Files dated 2026-04-13 in `.lake`. The branch shipped: `IsCovariantDerivativeOn`, `CovariantDerivative` (bundled), `ContMDiffCovariantDerivative` typeclass, `addOneForm`/`difference`/`affine_combination`, plus `Torsion` with `torsion_self = 0`, `torsion_antisymm`, `torsion_eq_zero_iff` (`∇_X Y - ∇_Y X = [X, Y]`). The branch did NOT include `LeviCivita` as such, nor curvature objects — those remain SK-EFT-owned per audit §4.

What this changes:
- Phase 6f docstrings claiming "Bonn in flight, awaiting review since mid-2025" are now stale and have been corrected (EinsteinTensor.lean, Curvature.lean, ExactSolutions.lean, ADMFormalism.lean, TetradFormalism.lean).
- The "second Bianchi `∇^μG_{μν} = 0` is a one-line consequence once Bonn lands" claim in EinsteinTensor.lean was over-optimistic — Mathlib still lacks Riemann/Ricci/scalar curvature on a connection. Project-local Riemann-from-connection lands together with the Lorentzian metric in Phase 6g.1.
- Phase 6f waves remain SHIPPED at the algebraic / point-wise level. The connection-based companion layer is queued for 6g.1 alongside Lorentzian metric and causal structure.

**2026-04-26 update: Phase 6f deep-research audit landed.** See [`Lit-Search/Phase-6f/Phase 6f audit — Classical GR Lean infrastructure.md`](../../../Lit-Search/Phase-6f/Phase%206f%20audit%20%E2%80%94%20Classical%20GR%20Lean%20infrastructure.md). Confirmed verbatim findings:

- **Mathlib4 master @ 8850ed93 (April 2026) has zero curvature objects and zero GR content.** Reaches up to smooth manifolds, tangent/vector bundles, Lie groups, integral curves, and a brand-new positive-definite Riemannian-metric typeclass (`IsRiemannianManifold`, 2025) with `Bundle.RiemannianMetric` on vector bundles. **No** connection, Christoffel, Riemann/Ricci/scalar/sectional/Weyl/Einstein, Bianchi, exponential map, parallel transport, manifold-side differential forms, Lorentzian signature, energy conditions, ADM, or named GR solutions.
- **Bonn coordination (Massot/Rothgang) — actionable:** ~6,000-line Mathlib branch on **connections / Levi-Civita / Ehresmann / torsion / geodesic flow / exponential map**, in review since mid-2025, landing progressively through 2026. Curvature tensors / Lorentzian metrics / GR are NOT on Bonn's roadmap (HALF ERC is harmonic-analysis-funded). **SK_EFT_Hawking must coordinate on connections/Levi-Civita and own everything from Riemann tensor downward.**
- **Cross-system landscape:** No proof assistant (Coq, Isabelle/AFP, HOL Light, HOL4, Mizar, Agda) has Riemann tensor, Bianchi, Schwarzschild/Kerr/FLRW as Einstein-equation solutions, ADM, energy conditions, positive-mass theorem, or singularity theorems. Special relativity is formalized in three independent systems (Isabelle `Schutz_Spacetime`, AFP `GyrovectorSpaces`, PhysLean `Relativity/Special`) but never bridged to curvature.
- **Per-wave one-line recommendations (per audit Section 4):**
  - **6f.1 Curvature** → Build downstream of Bonn's Levi-Civita branch; PR-track to Mathlib.
  - **6f.2 EinsteinTensor** → Build; small focused PR candidates after 6f.1.
  - **6f.3 EnergyConditions** → Build in PhysLean (project-local); physics-flavored predicates out of Mathlib scope.
  - **6f.4 ExactSolutions** → Build in PhysLean; Lorentzian metric must precede.
  - **6f.5 ADM** → Build in PhysLean; depends on submanifolds (Rothgang in-flight) + Lorentzian.
  - **6f.6 Tetrad/Einstein-Cartan** → Build in PhysLean; depends on principal bundles (Steinitz, in-flight) + spin/Clifford bundle (PhysLean TODO).

No direction change vs the original roadmap; the audit confirms the build-vs-import-vs-PR strategy at the wave level. `IsRiemannianManifold` (positive-definite, post-2025) is a usable foundation; Lorentzian extension is a project-local task on top of it.

**2026-04-27 update — Wave 6f.3 Lean module shipped (`EnergyConditions.lean`, 8 substantive theorems + 1 marker / 0 sorry / 0 new axioms).** Predicates on an abstract bilinear form (`StressEnergyTensor : Vec4 → Vec4 → ℝ`) over `Vec4 = Fin 4 → ℝ`: `IsNull`, `IsTimelike`, `IsFutureDirectedTimelike` (signature `−+++` with explicit time-direction parameter), `NEC`, `WEC`, `DEC`, `SEC`. Three chain implications: `DEC_implies_WEC` (direct), `WEC_implies_NEC_under_continuity` (continuity hypothesis explicit, load-bearing), `DEC_implies_NEC_under_continuity` (composition). Five counterexample witnesses: `cosmologicalLambda_WEC` (Λ ≥ 0 satisfies WEC), `cosmologicalLambda_NEC` (Λ at any value satisfies NEC vacuously), `cosmologicalLambda_violates_SEC` (Λ > 0 with explicit witness `t = v = (1,0,0,0)`), `ghostScalar_violates_NEC` (explicit non-zero gradient + null-vector witness), `stiff_fluid_violates_DEC` (perfect fluid `ρ = 1, p = 2` with explicit witness pair `v = (1, 9/10, 0, 0)`, `w = (1, -9/10, 0, 0)`). Per the audit §3E: this is the **first formalization** of these four predicates with chain implications and explicit counterexample witnesses across all proof assistants (Lean / Coq / Isabelle/AFP / HOL Light / HOL4 / Mizar / Agda). The full Lorentzian-manifold version (stress-energy field on a globally hyperbolic spacetime) is deferred to Wave 6f.4 once the Lorentzian-metric infrastructure lands; the abstract-bilinear-form version captures all the algebraic content needed for Phase 6a Wave 6 (Witten's positive-mass theorem at point-wise DEC).

**2026-04-29 update — Wave 6f.6 SHIPPED — Phase 6f FULLY CLOSED.** `TetradFormalism.lean` ships **6 substantive theorems + 1 marker / 0 sorry / 0 new axioms** (verified `propext, Classical.choice, Quot.sound` only). Tetrad (vierbein) formulation of GR at the algebraic / point-wise level. **§2 Tetrad-metric equivalence:** `tetradInducedMetric` def + `tetradInducedMetric_symm` (substantive symmetry from η-symmetry). **§3 Minkowski tetrad:** `minkowskiTetrad` def + `minkowskiTetrad_induces_minkowski_metric` (named-API consistency: `e^a_μ = δ^a_μ` ⇒ `g = η`). **§4 Tetrad determinant:** `diagonalTetradDet` def + `minkowskiTetrad_det_eq_one`. **§5 Torsion structure:** `torsionResidual` def (the `torsionResidual_zero_iff` Iff.rfl-on-identity-def biconditional was originally shipped but CUT in the post-closure strengthening pass — see closure block below). **§6 Cross-bridge to Phase 6e.6 EinsteinCartanExtension:** `tetrad_metric_equivalence_at_alpha_one` (consumes `ecResidual_at_alpha_one`) + `tetrad_levi_civita_iff_alpha_unity` (specializes `ecResidual_eq_zero_iff_alpha_unity`). The full Cartan structure equations (T^a = de^a + ω^a_b ∧ e^b, R^{ab} = dω^{ab} + ω^a_c ∧ ω^{cb}) are deferred until differential-form machinery lands; the substantive content shipped is the algebraic foundation + 6e.6 cross-bridge. **First formalization in any proof assistant** (per audit §3E + 6f.1-6f.5 first-formalization context) of the tetrad formalism with metric-equivalence biconditional + torsion-vanishing characterization + Einstein-Cartan torsion-amplitude cross-bridge. **Cross-layer Python pipeline:** 4 helpers in `formulas.py` (`tetrad_induced_metric`, `minkowski_tetrad`, `diagonal_tetrad_det`, `torsion_residual`); `tests/test_tetrad_formalism.py` (12 pytest cases / 5 test classes — TestTetradInducedMetric / TestDiagonalTetradDet / TestTorsionResidual / TestPhase6eCrossBridge consuming 6e.6 `ec_residual_at_point` / TestAntiPatternAudit, all PASS in 0.05s); figure `fig_tetrad_metric_equivalence` (2-panel: tetrad-induced metric heatmap for Minkowski tetrad with diagonal blue/red/zero off-diagonals + |EC residual| vs α_EC on log-y showing Levi-Civita reduction at α_EC = 1). **Strengthening (first-pass): 0 retroactive cuts** (back to 6f.2/6f.3/6e.5/6b.2 best — applied 6f.5 lessons aggressively); +1 post-closure cut applied later (`torsionResidual_zero_iff` Iff.rfl-on-identity-def — see closure block below). The named-quantity discipline + 6f.5 lesson-mitigation (avoid simp-trivial-on-constant-zero spatial-contraction theorems; substantive `tetradInducedMetric_symm` proved via η-diagonal substitution rather than pure simp) prevented all P3 patterns at first-pass. Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5, 6f.2=0, 6f.3=0, 6f.4=1, 6f.5=4, **6f.6=0** (back to best — 6f.5 lessons applied). Stages 10/11/13 deferred per user policy.

**🎉 PHASE 6f FULLY CLOSED 2026-04-29.** All 6 waves shipped end-to-end with cross-layer Python pipeline + first-formalization claim per proof-assistant audit §3E. Post-closure strengthening pass (2026-04-29) cut 3 additional rfl-rename / Iff.rfl-on-identity-def theorems (one per 6f.4/6f.5/6f.6) for net Phase 6f total **64 substantive theorems**:
- 6f.1 Curvature.lean (Riemann/Ricci/scalar algebraic + first-formalization) — **16 substantive**
- 6f.2 EinsteinTensor.lean (G_μν algebraic + Λ-vacuum biconditional) — **9 substantive**
- 6f.3 EnergyConditions.lean (NEC/WEC/DEC/SEC predicates + 5 counterexample witnesses) — **8 substantive**
- 6f.4 ExactSolutions.lean (Minkowski/dS/AdS/Schwarzschild catalog + BH thermodynamics) — **16 substantive** (post-closure cut: `deSitter_Ricci_eq` rfl-rename to 6f.1's `constantSectional_minkowski_Ricci_eq`)
- 6f.5 ADMFormalism.lean (3+1 decomposition + Hamiltonian/momentum constraints + Yamabe-form biconditional) — **10 substantive** (post-closure cut: `schwarzschild_adm_mass_pos_iff` Iff.rfl on identity-function def)
- 6f.6 TetradFormalism.lean (vierbein + 6e.6 EC cross-bridge) — **5 substantive** (post-closure cut: `torsionResidual_zero_iff` Iff.rfl on identity-function def)

Total Phase 6f: **64 substantive theorems / 0 sorry / 0 new axioms / 6 modules / 6 figures / 176 cross-layer pytest cases**. Post-closure strengthening: **3 additional cuts** (1 in each of 6f.4, 6f.5, 6f.6) — all P5 structural-tautology / rfl-rename patterns. Total Phase 6f cuts: **13** (5 in 6f.1 + 0 in 6f.2 + 0 in 6f.3 + 1 in 6f.4 first-pass + 1 in 6f.4 post-closure + 4 in 6f.5 first-pass + 1 in 6f.5 post-closure + 0 in 6f.6 first-pass + 1 in 6f.6 post-closure).

**2026-04-29 update — Wave 6f.5 SHIPPED (`ADMFormalism.lean`, 11 substantive theorems + 1 marker / 0 sorry / 0 new axioms).** ADM (Arnowitt-Deser-Misner) 3+1 decomposition at the algebraic / point-wise level. **§2 ADM 4-metric block decomposition:** `admFourMetric_00` / `_0i` defs + Minkowski specializations (`minkowski_admFourMetric_00`, `minkowski_admFourMetric_0i`). **§3 Spatial-tensor utilities:** `extrinsicCurvatureTrace` / `_Squared` defs (no separate K=0 specialization theorems — P3-trivial cuts). **§4 Hamiltonian constraint:** `hamiltonianConstraint` def + `hamiltonianConstraint_vacuum_iff` biconditional + `hamiltonianConstraint_moment_of_time_symmetry` (K=0 specialization) + `hamiltonianConstraint_moment_of_time_symmetry_iff` (Yamabe-form biconditional `^(3)R = 16πGρ`). **§5 Momentum constraint:** `momentumConstraint_i` def + `momentumConstraint_vacuum_iff` biconditional. **§6 Specific spacetime ADM data:** Minkowski (`minkowski_satisfies_hamiltonianConstraint` / `_satisfies_momentumConstraint`); de Sitter flat slicing (`deSitter_flat_slicing_hamiltonian_iff` Λ=3H² ADM-level cross-bridge to 6f.4 `deSitter_lambda_eq_three_H_squared`); Schwarzschild (`schwarzschild_adm_mass_eq_half_horizon_radius` substantive cross-bridge to 6f.4's `schwarzschildHorizonRadius` / `schwarzschild_adm_mass_pos_iff` positive-energy specialization). 2 named noncomputable defs (`hamiltonianConstraint`, `momentumConstraint_i` — both Real.pi-dependent), plus `schwarzschildADMMass` and `deSitterADMMass` value defs. **First formalization in any proof assistant** (per audit §3E + 6f.1+6f.2+6f.3+6f.4 first-formalization context) of the ADM 3+1 decomposition with Hamiltonian + momentum constraint biconditionals + cross-bridges to canonical exact-solutions catalog. **Cross-layer Python pipeline:** 8 helpers in `formulas.py` (`adm_four_metric_g00`, `adm_four_metric_g0i`, `extrinsic_curvature_trace`, `extrinsic_curvature_squared`, `hamiltonian_constraint`, `momentum_constraint`, `schwarzschild_adm_mass`, `desitter_adm_mass`); `tests/test_adm_formalism.py` (32 pytest cases / 9 test classes — TestADMFourMetric / TestSpatialContractions / TestHamiltonianConstraint / TestMomentumConstraint / TestMinkowskiADM / TestDeSitterADM / TestSchwarzschildADM / TestStrengtheningQuantitative / TestPhase6fCrossBridge / TestAntiPatternAudit, all PASS in 0.05s); figure `fig_adm_constraint_surface` (2-panel: Yamabe-form Hamiltonian constraint contours in (³R, ρ) plane with Minkowski + Schwarzschild markers + Yamabe locus dashed line + dS flat-slicing Λ=3H² parabola with anchor markers). **Strengthening discipline: 4 retroactive cuts** (`schwarzschild_adm_K_zero` rfl on constant-zero P3 plumbing + `extrinsicCurvatureTrace_zero_at_K_zero` + `extrinsicCurvatureSquared_zero_at_K_zero` simp-trivial unconsumed + `schwarzschild_adm_mass_eq_M` rfl rename replaced by substantive `_eq_half_horizon_radius` cross-bridge + `deSitter_adm_mass_eq_zero` rfl rename — closed forms encoded at the def level). Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5, 6f.2=0, 6f.3=0, 6f.4=1, **6f.5=4** (regression — multiple rfl-rename + simp-trivial patterns slipped past first-pass; preemptive checklist did not catch named-def-makes-rename-redundant pattern at the spatial-contraction level. Pattern logged: spatial-tensor-trace + sum-of-zero-summands theorems are P3 trivial when K (or any input) is the constant-zero function — caught by ruthless audit). **Phase 6f wave 6 unblocked** (TetradFormalism). Stages 10/11/13 deferred per user policy.

**2026-04-29 update — Wave 6f.4 SHIPPED (`ExactSolutions.lean`, 17 substantive theorems + 1 marker / 0 sorry / 0 new axioms).** Catalogue of canonical exact solutions of the Einstein field equations as named consumers of the Phase 6f.1 + 6f.2 + 6f.3 algebraic infrastructure plus BH thermodynamics cross-bridges to Phase 6a Wave 5. **Minkowski (K=0, Λ=0):** `minkowski_lambda_zero_iff_K_zero` (uniqueness biconditional — Minkowski is the unique Λ=0 vacuum among constant-K solutions). **de Sitter (K>0):** `deSitter_Ricci_eq` / `deSitter_scalar_eq` / `deSitter_einsteinTensor_eq` / `deSitter_lambda_vacuum_iff` / `deSitter_lambda_eq_three_H_squared` / `deSitter_T_H_eq_kappa_over_2pi` (6 thms; the last uses Gibbons-Hawking 1977 dS Hawking-Unruh `T_H = κ/(2π)` and consumes named defs `deSitterHubbleRadius` / `deSitterKappa` / `deSitterHawkingTemp`). **Anti-de Sitter (K<0):** `ads_lambda_eq_neg_three_over_ell_sq` (1 thm; AdS-radius anchor `Λ_AdS = -3/ℓ²`). **Schwarzschild (Kerr-Schild form):** `schwarzschild_horizon_iff` (biconditional `φ=1 ↔ r=2M` strengthening KerrSchild.lean's existing forward direction) / `schwarzschild_g_tt_outside_horizon_neg` / `_at_horizon_zero` / `_inside_horizon_pos` (3 signature theorems characterizing the t-direction character flip across the horizon) / `schwarzschild_kappa_times_4M` / `schwarzschild_T_H_times_M` / `schwarzschild_T_H_eq_kappa_over_2pi` / `schwarzschild_area_eq_16pi_M_sq` / `schwarzschild_S_BH_eq_4pi_M_sq` (5 BH-thermo cross-bridges to 6a.5 BHThermodynamicsFourLaws consuming the named defs `schwarzschildHorizonRadius` / `schwarzschildKappa` / `schwarzschildHawkingTemp` / `schwarzschildArea` / `schwarzschildBHEntropy`). The vacuum-Ricci verification `Ric(g_Schw) = 0` outside r = 2M is **deferred** — requires coordinate ∂_μ machinery not yet in the project. Vacuous tracked Prop pattern explicitly REJECTED at first-pass per 6f.2 strengthening lesson. **Cross-layer Python pipeline:** 14 helpers in `formulas.py` (deSitter_lambda_from_K + 6 dS / 1 AdS / 6 Schwarzschild + g_tt evaluator); `tests/test_exact_solutions.py` (45 pytest cases / 8 test classes — TestMinkowski / TestDeSitter / TestDeSitterThermodynamics / TestAntiDeSitter / TestSchwarzschildSignature / TestSchwarzschildThermodynamics / TestStrengtheningQuantitative / TestPhase6fCrossBridge / TestAntiPatternAudit — all PASS in 0.06s); figure `fig_exact_solutions_catalog` (3-panel: Schwarzschild g_tt(r) signature flip + Λ-K linear branch with dS/Mink/AdS markers + Schwarzschild thermodynamics scaling laws on log-log). **Strengthening discipline: 1 retroactive cut** (`schwarzschild_kappa_eq` rfl rename — substantive content lives in the `schwarzschildKappa` def + `schwarzschild_kappa_times_4M` consumer). Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5, 6f.2=0, 6f.3=0, **6f.4=1**. The named-quantity definition pattern (Schwarzschild's 5 noncomputable defs) made most P3-trivial content substantive named-API rather than rename theorems; the rfl `schwarzschild_kappa_eq` was the one slipped pattern caught by ruthless post-wave audit. **Phase 6f waves 5+6 unblocked** (6f.5 ADM, 6f.6 Tetrad). Stages 10/11/13 deferred per user policy (Mathlib-PR-style infrastructure).

**2026-04-29 update — Wave 6f.3 BACKFILL CLOSED (cross-layer Python pipeline shipped).** A 2026-04-29 audit (post-6f.2 ship) caught that 6f.3's original "SHIPPED (Stage 1-2)" tag was misleading — Lean module was complete and clean (Stage 3 done) but Stages 2 (formulas), 6 (tests), and 8 (figure) had been skipped, breaking the cross-layer precedent set by 6f.1 + 6f.2. Backfill closes the gap: **11 formulas helpers** in `src/core/formulas.py` (`apply_bilinear` + 3 predicate helpers `is_null_vec`/`is_timelike`/`is_future_directed_timelike` + 4 condition checks `nec_check`/`wec_check`/`dec_check`/`sec_check` + 3 named tensor witnesses `cosmological_lambda_stress_energy`/`ghost_scalar_stress_energy`/`perfect_fluid_stress_energy` + 1 trace helper `perfect_fluid_trace_minkowski`), each with `Lean: SKEFTHawking.EnergyConditions.<thm>` cross-references. **`tests/test_energy_conditions.py`** (38 pytest cases / 7 test classes — TestPredicateBasics / TestCosmologicalLambdaWitness / TestGhostScalarWitness / TestStiffFluidWitness / TestChainImplications / TestPerfectFluidEnergyConditionRegions / TestAntiPatternAudit / TestPhase6f1CrossBridge — all PASS in 0.07s). **Figure `fig_energy_conditions_perfect_fluid_regions`** (4-panel (ρ, p) heatmap; ★ cos-Λ at (1, -1) sits in NEC/WEC/DEC blue + SEC orange regions; ◆ stiff-fluid at (1, 2) sits in NEC/WEC/SEC blue + DEC orange regions — visually verifies all 5 named Lean counterexample-witness theorems). Lean module summary docstring corrected from stale "7 substantive theorems" to actual "8 + 1 marker" + Wave-3 backfill cross-reference appended. **LIFT bridge from `StressEnergyTensor : Vec4 → Vec4 → ℝ` to 6f.1/6f.2's `Fin 4 → Fin 4 → ℝ` matrix carrier remains DEFERRED** (judgment call: defer until 6f.4 actually needs it). Project totals after backfill: **4528 substantive theorems / 198 modules / 91 test files (+1 from 90) / 139 figures (+1 from 138) / 1 axiom / 0 sorry**. Wave 6f.3 is now FULLY SHIPPED end-to-end (per the user's "build-locally" + cross-layer-default policy).

**2026-04-27 update — Wave 6f.1 STAGE 1 SCOPING.** Architecture-decision doc + Bonn outreach script template at `temporary/working-docs/phase6f1_curvature_architecture_decision.md`. Implementation deferred behind the Massot↔Rothgang Mathlib branch landing (`CovariantDerivative` / `Torsion` / `LeviCivita` API). Per audit §4 outreach recommendation, three-question outreach email to Rothgang + Massot is staged in the architecture doc (questions: ∇-on-tensor-sections, Levi-Civita uniqueness signature-agnosticism, willingness to accept a downstream curvature PR). Default expectation per audit: yes/yes/yes-welcome. Wave 6f.1 itself is signature-agnostic (Riemann tensor only requires a linear connection, not a metric); the Lorentzian-vs-Riemannian fork becomes load-bearing for 6f.4-6f.6, NOT for 6f.1.

**2026-04-29 update — Wave 6f.1 SHIPPED (Stages 1-9, 12 + strengthening pass).** `Curvature.lean` shipped under the user's "build-locally" policy: rather than wait on Bonn's Levi-Civita branch landing, we built the algebraic content in our repo following Mathlib conventions for eventual upstream port. **16 substantive theorems / 0 sorry / 0 new axioms** (verified `propext, Classical.choice, Quot.sound` only; was 21 first-pass — strengthening pass cut 5 retroactive theorems: 4 `zeroRiemann_*` trivial-witness theorems (`AntisymLastTwo`/`FirstBianchi`/`lower_zero`/`ricci_zero` — all P3-trivial-discharge plumbing) + 1 unused helper `sumFin4_kron_eq`). Coordinate-based `Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ` carrier matching the Phase 6f.3 EnergyConditions precedent for our project; index-free Mathlib-PR-shaped formulation deferred until Bonn's `CovariantDerivative` API lands (then this module's algebraic content ports directly). Wave headline: `pair_symmetry_lowered` derives `R_{ρσμν} = R_{μνρσ}` from the three algebraic predicates `AntisymPair12 + AntisymPair34 + FirstBianchiCycle` via the standard Wald §3.2 four-Bianchi-sum derivation. Quantitative bounds: `constantSectional_Ricci_eq` ships `Ric = 3K · g` with the dimension-3 factor explicit in 4D; `constantSectional_diag_trace_eq` ships `R_trace = 12K` with the n(n−1) = 12 factor. Cross-bridge: `linearizedEFE_η_metricSymmetric` calls `LinearizedEFE.η_symm` directly (audit P6 pattern). Falsifier: `nonBianchiTensor_violates_FirstBianchi` confirms FirstBianchi is non-vacuous. **First formalization in any proof assistant** of these algebraic Riemann predicates with chain implications + explicit constant-K witness + cross-module bridge (per audit §3E). **Discipline metric: 5 retroactive theorems** (regression vs 6e.5/6b.2 = 0 — pattern the preemptive checklist missed: zero-witness-as-trivial-plumbing on the negative-class side; failure-mode logged for future waves). Stages 10 (paper) + 13 (adversarial reviewer) **deferred per user policy** — wave is Mathlib-PR infrastructure, no in-project paper deliverable in PAPER_STRATEGY.md; Stage 11 notebook also deferred per same policy. Tests: 23 pytest cases all PASS (test names unchanged after strengthening cuts — Python tests use the constant-K formula, not the cut zeroRiemann_* Lean witnesses). validate.py 25/25 PASS. Project totals: 4519 substantive theorems (+14 net), 197 modules (+1), 89 test files (+1), 137 figures (+1). **Waves 6f.2-6f.6 unblocked** by 6f.1 algebraic foundation. Wave 6f.2 (`EinsteinTensor.lean`) is the natural next step.

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. Classical-GR-relevant anchors: `KerrSchild.lean` (7, gravitational solutions scaffolding), existing tetrad infrastructure in `ADWMechanism.lean` and `TetradGapEquation.lean`. Mathlib: differential-geometry machinery as of 2026 — **audit complete** (see above) — `IsRiemannianManifold` + `IsManifold I n M` + `mfderiv` + `VectorBundle.{Tangent, Riemannian, CovariantDerivative}` available as foundation; everything from Riemann tensor downward must be built.

**Thesis.** Six waves of classical-GR infrastructure formalized in Lean: Riemann / Ricci curvature, Einstein tensor + Bianchi, energy conditions, exact solutions catalog, ADM 3+1 decomposition, tetrad (vierbein) formalism. Nearly all waves are Mathlib-PR candidates. This phase is the prerequisite backbone for Phases 6a.6 (positive mass theorem), 6e (nonlinear effective action), and 6g (global / nonperturbative GR). External Mathlib progress is the main schedule risk.

**Correctness-push framing.** 6f.3 (`EnergyConditions.lean`) is the correctness-push anchor: Phase 6e.4's `T_μν^emerg` must be checkable against these predicates, and NEC violation in ADW has direct cosmological consequences (supports DE without exotic matter; tension with standard BH theorems).

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §9 (6f), §4 (6a — context for 6a.6), §8 (6e — context for 6e.1/6e.4), §10 (6g — downstream dependency)
> 4. Wave-specific pre-reads (all waves): Mathlib current `Mathlib.Geometry.Manifold.*` namespace audit — identify existing differential-geometry / Riemannian-geometry infrastructure. Drop deep-research prompt `Lit-Search/Tasks/Phase6f_mathlib_gr_infrastructure_audit.md` before Wave 1 Stage 1 if unclear.
> 5. Bonn differential-geometry formalization (strategy doc §16 Open Q) — contact / coordinate? If not yet contacted, proceed independently with Mathlib-first approach; if contacted, align scope upstream.
> 6. Mathlib-PR strategy: every wave is a candidate Mathlib PR. Follow the Mathlib-categorical-PR guide in `Lit-Search/Phase-5h/Contributing categorical infrastructure to Mathlib4.md` adapted for differential-geometry contributions.
> 7. 6f waves are foundation-building; the correctness-push value comes via downstream consumers (6a.6, 6e, 6g). Do not demand correctness-push anchors inside 6f itself — it is infrastructure.
> 8. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to published constants); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check (no `rfl`/`decide`/`not_lt.mpr h_disagree` tautologies); (5) defining-the-conclusion check (vacuous when `f := <obvious target>`). The end-of-wave strengthening pass should produce **0 retroactive theorems** — if it produces 5+, log the failure mode and tighten the next wave's discipline.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6f:**
- Riemann `R^ρ_{σμν}`, Ricci `R_μν`, scalar `R` as typed Lean objects with standard identities
- Einstein tensor `G_μν = R_μν − ½ R g_μν` + second Bianchi `∇^μ G_μν = 0`
- Energy conditions: WEC, NEC, DEC, SEC as predicates on stress-energy
- Exact solutions catalog: Schwarzschild, Kerr, de Sitter, FLRW
- ADM 3+1 decomposition: lapse, shift, induced metric, extrinsic curvature, constraint equations
- Tetrad (vierbein) formalism on manifolds: frame-bundle section, spin connection, torsion, Einstein-Cartan action

**OUT OF SCOPE for 6f:**
- Full numerical-relativity machinery — simulation, not formalization (backlog)
- Covariant perturbation theory at nonlinear order — 6e territory
- Supersymmetric / higher-dimensional curvature — OOS by program framing
- Specific astrophysical solutions beyond the catalog (Kerr-Newman, charged solutions) — add as 6f.4 extensions if specifically needed

**External dependency:** If Bonn diff-geom team's formalization becomes available upstream, switch to import-based structure rather than in-house definitions. Decision per wave at Stage 1.

---

## Track A: Curvature Stack (6f.1, 6f.2)

### Wave 1 — `Curvature.lean` (6f.1) [Pipeline: Stages 1–9, 11-12 SHIPPED 2026-04-29; Stage 10 paper + Stage 13 adversarial review deferred per user policy — Mathlib-PR infrastructure]

**Goal:** Riemann `R^ρ_{σμν}`, Ricci `R_μν`, scalar `R` as typed Lean objects with standard algebraic identities (antisymmetry, first Bianchi, Ricci symmetry).

**Prerequisites:** Mathlib current differential-geometry audit. If Bonn work is available, use it; otherwise build on Mathlib base.

**Module structure:**
- `lean/SKEFTHawking/Curvature.lean`
  - Riemann tensor `R^ρ_{σμν}(∇) : TensorField` from Levi-Civita connection ∇
  - Ricci tensor `R_{μν} = R^ρ_{μρν}`
  - Scalar curvature `R = g^{μν} R_{μν}`
  - Antisymmetry: `R_{ρσμν} = −R_{σρμν} = −R_{ρσνμ}`, symmetry: `R_{ρσμν} = R_{μνρσ}`
  - First Bianchi: `R^ρ_{[σμν]} = 0`
  - Ricci symmetry: `R_{μν} = R_{νμ}`
- Target ~12–16 theorems.

**Python side:** Minimal (Lean-side heavy).
- `src/classical_gr/curvature_numerical.py` — numerical curvature on test metrics (Minkowski, Schwarzschild) — validation against Lean

**Bridges:**
- Feeds 6f.2, 6f.3, 6f.4, 6f.5, 6f.6 (all downstream 6f waves)
- Feeds 6a.6 (positive mass theorem), 6e (nonlinear effective action), 6g (global GR)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_curvature.py`
- **Mathlib PR:** Curvature objects + core identities — coordinated with Mathlib maintainers
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Dependent on Mathlib differential-geometry maturity. If Mathlib already has Riemann/Ricci, this becomes an import + specialization wave (~1 PM).

### Wave 2 — `EinsteinTensor.lean` (6f.2) [Pipeline: Stages 1-9, 12 SHIPPED 2026-04-29; Stages 10/11/13 deferred per user policy — Mathlib-PR infrastructure, no PAPER_STRATEGY.md target]

**Status:** SHIPPED 2026-04-29. **9 substantive theorems / 0 sorry / 0 new axioms / 26 tests / 1 figure / 0 retroactive cuts.** Coordinate-based algebraic Einstein tensor `G_{μν} := Ric_{μν} − (1/2) R g_{μν}` (`EinsteinTensorType : Fin 4 → Fin 4 → ℝ` carrier). Wave headline `constantSectional_einsteinTensor_eq` ships `G_{μν} = -3K · g_{μν}` for the constant-K Riemann witness in 4D. Quantitative dimension-4 trace identity `einsteinTensor_trace_eq_neg_scalar` (`G^μ_μ = -R` via `n − 2 = 2` cancellation under `(g_inv : g) = 4` hypothesis). Vacuum characterization biconditional `einsteinTensor_zero_iff_ricci_zero` (`G = 0 ↔ Ric = 0` in 4D, with `R = scalarOf Ric g_inv`). De Sitter Λ-vacuum cross-bridge `constantSectional_lambda_vacuum_iff` (`G + Λg = 0 ↔ Λ = 3K` under non-degenerate `g`; algebraic-level cross-bridge to Phase 6c W1 Zhitnitsky-DE program). Minkowski self-inverse contraction `minkowski_dim_contraction = 4` (concrete 4D dimension witness on `LinearizedEFE.η`). **Second Bianchi `∇^μ G_{μν} = 0` deferred** to a future wave once Bonn's `CovariantDerivative` API lands (option (a) tracked-Prop with trivial discharge REJECTED per 6f.1's strengthening lesson). **Strengthening pass: 0 retroactive cuts** (best yet — back to 6e.5/6b.2 baseline). The 6f.1 carry-forward question prevented zero-witness-trivial-plumbing in the first place. **First formalization in any proof assistant** (per audit §3E + 6f.1 first-formalization context) of the algebraic Einstein tensor with quantitative trace identity + constant-K specialization + de Sitter-Λ algebraic cross-bridge.

**Goal:** `G_μν = R_μν − ½ R g_μν`; second Bianchi `∇^μ G_μν = 0` as theorem (or as tracked Prop pending `CovariantDerivative` API — see design note below).

**Prerequisites:** Wave 1 (`Curvature.lean`) — SHIPPED. Direct consumers: `ricciOf`, `scalarOf`, `lowerFirstIndex`, `constantSectionalRiemann`, `constantSectional_Ricci_eq`, `constantSectional_diag_trace_eq`.

**Module structure:**
- `lean/SKEFTHawking/EinsteinTensor.lean`
  - `G_μν` definition (matrix-form `Fin 4 → Fin 4 → ℝ`)
  - Symmetry: `G_{μν} = G_{νμ}` from Ricci + metric symmetry
  - Trace identity: `G^μ_μ = −R` in 4D — quantitative dimension-factor theorem (mirror of 6f.1's `12K` pattern)
  - Constant-K specialization: `G_{μν} = −3K g_{μν}` (consumes 6f.1 witnesses)
  - Vacuum characterization: `G_{μν} = 0 ↔ Ric_{μν} = 0` in 4D
  - Cosmological-constant bridge: `G_{μν} + Λ g_{μν} = 0` iff `Λ = 3K` for de Sitter
  - Second Bianchi `∇^μ G_{μν} = 0`: see design note
- Target ~6-8 substantive theorems.

**Design note — second (differential) Bianchi.** The classical `∇^μ G_{μν} = 0` requires a covariant divergence operator. We don't model the connection in 6f.1 (algebraic-only formulation). Three options at Stage 1:
- **(a) Tracked Prop, recommended:** state as `H_SecondBianchi` algebraic predicate; ship constant-K witness (curvature gradient is zero ⇒ second Bianchi trivially holds) and concrete falsifier. Matches 6f.1's pattern of treating connection-properties as algebraic Props.
- **(b) Defer:** push second Bianchi to a future wave once Bonn's `CovariantDerivative` API lands.
- **(c) Coordinate `∂_α` placeholder:** define finite-difference divergence; heavy bookkeeping, not recommended for Mathlib PR target.

**Strengthening lesson carried from 6f.1:** add the question *"is the witness-existence statement informative beyond the predicate definition?"* to the preemptive checklist. 6f.1 hit 5 retroactive cuts on zero-witness-as-trivial-plumbing.

**Python side:** Minimal — small `formulas.py` helpers (`einstein_tensor_from_ricci`, `einstein_tensor_trace`, etc.) mirroring 6f.1's pattern.

**Bridges:**
- Depends on Wave 1 (consumes `ricciOf`, `scalarOf`, `constantSectionalRiemann` witnesses)
- Feeds 6f.4 (exact solutions check), 6e.4 (nonlinear EFE — already shipped, possible cross-bridge upgrade), 6g (global GR)
- Optional concrete cross-bridge to Phase 6c W1 (Zhitnitsky DE Λ value) at the algebraic level

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_einstein_tensor.py`
- (Optional) `fig_einstein_tensor_trace_identity` showing `G^μ_μ vs −R` linearity or de Sitter `G_{μν} = −3K g_{μν}` over K
- **Mathlib PR (deferred):** Einstein tensor + Bianchi as Mathlib-PR-shaped formulation when Bonn's API lands
- Inventory update: +6-8 theorems, +1 Lean module

**Estimated LOE:** 2-4 person-months (likely shorter under build-locally policy following 6f.1's algebraic pattern; ~1 session expected).
**Risk:** Low. Algebraic content; main design choice is (a)/(b)/(c) above.

---

## Track B: Energy Conditions (6f.3)

### Wave 3 — `EnergyConditions.lean` (6f.3) [Pipeline: Stages 1–8]

**Goal:** Formal statements of weak, null, dominant, strong energy conditions as predicates on stress-energy. This is 6f's correctness-push anchor — enables NEC check on Phase 6e.4's `T_μν^emerg`.

**Prerequisites:** Waves 1, 2 complete.

**Module structure:**
- `lean/SKEFTHawking/EnergyConditions.lean`
  - Stress-energy tensor abstract type
  - WEC predicate: `∀ timelike u^μ, T_μν u^μ u^ν ≥ 0`
  - NEC predicate: `∀ null k^μ, T_μν k^μ k^ν ≥ 0`
  - DEC predicate: `∀ timelike u^μ, −T^μ_ν u^ν is future-pointing causal`
  - SEC predicate: `∀ timelike u^μ, (T_μν − ½ T g_μν) u^μ u^ν ≥ 0`
  - Implication theorems: `DEC ⇒ WEC`, `WEC ⇒ NEC`, etc.
  - **Correctness-push theorem (external to 6f, activated by 6e.4):** `ADW_T_emerg_satisfies_NEC` — open / activated when 6e.4 ships `T_μν^emerg` explicit form. If NEC is violated on ADW's emergent stress-energy, that regime becomes a targeted study (6g.2 Penrose singularity may not apply; DE support without exotic matter is permitted).
- Target ~8–10 theorems.

**Python side:**
- `src/classical_gr/energy_conditions.py` — numerical energy-condition checker on representative stress-energy tensors

**Bridges:**
- Depends on Waves 1, 2
- Feeds 6a.6 (positive mass under DEC), 6g.2 (Penrose singularity under NEC), 6g.4 (classical area theorem under NEC), 6e.4 (`T_μν^emerg` classification)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_energy_conditions.py`
- **Mathlib PR:** Energy conditions as predicates (possibly combined with 6f.1/6f.2 PR)
- Inventory update: +8–10 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 2–3 person-months
**Risk:** Low. Pure predicate definitions + implication theorems.

**Correctness-push anchor (activated downstream).** NEC on `T_μν^emerg` is the single most load-bearing check in the post-SK-EFT gravity program.

---

## Track C: Exact Solutions (6f.4)

### Wave 4 — `ExactSolutions.lean` (6f.4) [Pipeline: Stages 1–8]

**Goal:** Schwarzschild, Kerr, de Sitter, FLRW as explicit metrics satisfying vacuum / appropriate-source Einstein equations.

**Prerequisites:** Waves 1, 2 complete. `KerrSchild.lean` (existing) for Kerr-family scaffolding.

**Module structure:**
- `lean/SKEFTHawking/ExactSolutions.lean`
  - Schwarzschild metric + vacuum-EFE verification
  - Kerr metric (extending existing `KerrSchild.lean`) + vacuum-EFE verification
  - de Sitter metric + `Λ`-sourced EFE verification
  - FLRW metric (already referenced in 6a.4 `FLRWDynamics.lean`) — cross-reference or absorb
  - Horizon structure: Schwarzschild event horizon, Kerr inner/outer + ergosphere, de Sitter cosmological horizon
  - Killing vector fields
- Target ~14–18 theorems.

**Python side:**
- `src/classical_gr/exact_solutions.py` — numerical evaluators + Einstein-tensor verification on each solution

**Bridges:**
- Depends on Waves 1, 2
- Extends `KerrSchild.lean`
- Feeds 6g.6 (no-hair theorem), 6a.5 (BH thermodynamics on specific solutions)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_exact_solutions.py`
- **Mathlib PR:** Exact solutions catalog (possibly)
- Inventory update: +14–18 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Kerr metric + horizon structure is the most technical subcomponent.

---

## Track D: ADM and Tetrad (6f.5, 6f.6)

### Wave 5 — `ADMFormalism.lean` (6f.5) [Pipeline: Stages 1–8]

**Goal:** Lapse, shift, induced metric, extrinsic curvature, Hamiltonian and momentum constraint equations. Required for 6g.5 (Cauchy problem).

**Prerequisites:** Waves 1, 2 complete. LeanMillenniumPrizeProblems PDE framework (external) as coordinated dependency — if unavailable, build inline.

**Module structure:**
- `lean/SKEFTHawking/ADMFormalism.lean`
  - Foliation of spacetime by spacelike hypersurfaces `Σ_t`
  - Lapse function `N`, shift vector `N^i`
  - Induced metric `γ_{ij}` on `Σ_t`
  - Extrinsic curvature `K_{ij}`
  - Hamiltonian constraint: `^(3)R + K² − K_{ij} K^{ij} = 16π G ρ`
  - Momentum constraint: `∇_j (K^{ij} − γ^{ij} K) = 8π G j^i`
  - Gauss-Codazzi relations
- Target ~12–16 theorems.

**Python side:**
- `src/classical_gr/adm_formalism.py` — ADM split of representative metrics (Schwarzschild in ADM form)

**Bridges:**
- Depends on Waves 1, 2
- Feeds 6g.5 (Cauchy problem) — critical
- Cross-references LeanMillenniumPrizeProblems PDE weak-solution framework

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_adm_formalism.py`
- **Mathlib PR:** ADM formalism (possibly — coordinated with LMPP)
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 4–6 person-months
**Risk:** Medium–high. Heavy bookkeeping; interacts with LMPP PDE framework.

### Wave 6 — `TetradFormalism.lean` (6f.6) [Pipeline: Stages 1–8]

**Goal:** Tetrad as frame-bundle section; spin connection; torsion tensor; Einstein-Cartan action. Bridges classical-GR side to ADW's tetrad-native formalism.

**Prerequisites:** Waves 1, 2 complete. Existing tetrad work in `ADWMechanism.lean`, `TetradGapEquation.lean` — align conventions.

**Module structure:**
- `lean/SKEFTHawking/TetradFormalism.lean`
  - Tetrad / vierbein `e^a_μ` as frame-bundle section
  - Inverse vierbein `E_a^μ`, orthonormality `g_μν e^a_μ e^b_ν = η_{ab}`
  - Spin connection `ω^{ab}_μ`
  - Torsion tensor `T^a_{μν}` (aligns with 6e.6 Einstein-Cartan extension)
  - Curvature 2-form `R^{ab}_{μν}`
  - Einstein-Cartan action as tetrad/spin-connection functional
  - Bridge theorem: `tetrad_formalism_EFE = metric_formalism_EFE` (equivalence when torsion = 0)
- Target ~12–16 theorems.

**Python side:**
- `src/classical_gr/tetrad_formalism.py` — tetrad split of representative metrics

**Bridges:**
- Depends on Waves 1, 2
- Aligns conventions with `ADWMechanism.lean`, `TetradGapEquation.lean`
- Feeds 6e.6 (Einstein-Cartan extension)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_tetrad_formalism.py`
- **Mathlib PR:** Tetrad formalism (possibly)
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium.

---

## Decision Gates

**Gate F.1 — before Wave 1 begins:** Mathlib differential-geometry audit complete? Bonn team coordination decided? Gate determines whether Wave 1 is build-from-Mathlib-base (3–5 PM) or import-Bonn+specialize (1 PM).

**Gate F.2 — after Wave 3 (`EnergyConditions`) ships:** Is 6e.4 `T_μν^emerg` sufficiently formed to test against NEC? If YES → immediate NEC check as follow-up. If NO → NEC check activates later when 6e.4 ships.

**Gate F.3 — before Wave 5 (`ADMFormalism`) begins:** LeanMillenniumPrizeProblems PDE framework available? If YES → import-based structure. If NO → inline PDE-lite for ADM; document as follow-up dependency.

**Gate F.4 — Mathlib PR strategy:** Coordinate which 6f waves become Mathlib PRs vs in-project modules. Default: all 6f waves are Mathlib-PR candidates; decision per wave at Stage 12.

---

## Dependencies

```
6f.1 (Curvature) — foundational; depends on Mathlib DG audit
  ↓
6f.2 (EinsteinTensor) — depends on 6f.1
  ↓
6f.3 (EnergyConditions) — depends on 6f.1, 6f.2
6f.4 (ExactSolutions) — depends on 6f.1, 6f.2
6f.5 (ADMFormalism) — depends on 6f.1, 6f.2; LMPP optional
6f.6 (TetradFormalism) — depends on 6f.1, 6f.2

Parallelism:
  6f.1 then 6f.2 (serial)
  6f.3, 6f.4, 6f.5, 6f.6 all parallel after 6f.2
```

---

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6f.1 | `Curvature.lean` + Mathlib PR | 3–5 | Mathlib DG audit | **TIER 0 — foundational** |
| 6f.2 | `EinsteinTensor.lean` + Mathlib PR | 2–4 | 6f.1 | **TIER 0** |
| 6f.3 | `EnergyConditions.lean` + Mathlib PR | 2–3 | 6f.1, 6f.2 | **TIER 1 (correctness-push downstream)** |
| 6f.4 | `ExactSolutions.lean` + Mathlib PR | 3–5 | 6f.1, 6f.2 | **TIER 1** |
| 6f.5 | `ADMFormalism.lean` + Mathlib PR (possibly) | 4–6 | 6f.1, 6f.2, LMPP opt | **TIER 1** |
| 6f.6 | `TetradFormalism.lean` + Mathlib PR | 3–5 | 6f.1, 6f.2 | **TIER 1** |

**Total Phase 6f LOE:** 17–28 person-months. 6f.1 + 6f.2 serial (5–9 PM), then 6f.3 + 6f.4 + 6f.5 + 6f.6 parallel: wall-clock 9–15 months minimum.

**Deliverables cumulative:**
- 6 new Lean modules
- 6 small Python scripts (validation only; 6f is Lean-heavy)
- 0 papers in-project; all output is Mathlib PRs
- ~64–84 new theorems; zero sorry target; zero new axioms target

---

## Open Questions

**O.1 — LOAD-BEARING.** Mathlib differential-geometry audit: what's already present? What needs fresh formalization? Drop deep-research prompt before Wave 1.

**O.2** — Bonn diff-geom coordination: does the user have a contact? Strategy doc §16 Open Q item 4 flags this explicitly.

**O.3** — LeanMillenniumPrizeProblems PDE framework: usable directly, or needs Einstein-specific additions? Affects Wave 5.

**O.4** — Mathlib PR acceptance timeline: PRs may take months to land. Parallel track: in-project module + PR submission; accept if PR lands.

---

## What Success Looks Like

**Per wave:**
- 6f.1: Riemann + Ricci + scalar curvature typed + identities; Mathlib PR submitted/landed
- 6f.2: Einstein tensor + Bianchi identity; Mathlib PR submitted/landed
- 6f.3: WEC/NEC/DEC/SEC predicates; enables `T_μν^emerg` NEC check (correctness-push downstream)
- 6f.4: Schwarzschild + Kerr + dS + FLRW catalog; EFE-verification theorems
- 6f.5: ADM formalism + Hamiltonian/momentum constraints; Cauchy-problem prerequisite
- 6f.6: Tetrad + spin connection + torsion; Einstein-Cartan action; convention-alignment with ADW

**Cumulative:**
- 6 new Lean modules, Mathlib PRs (0–6 depending on acceptance)
- ~64–84 new theorems, zero sorry target
- **Program-level value:** backbone for 6a.6, 6e, 6g; contributes to Mathlib community

---

## Cross-References

**Prior phases this extends:**
- Phase 3/5d (existing tetrad work) — `ADWMechanism.lean`, `TetradGapEquation.lean` conventions
- Phase 5 (Paper 5 KerrSchild) — `KerrSchild.lean` extension

**Feeds downstream phases:**
- Phase 6a.6 (positive mass theorem) — 6f.1, 6f.3
- Phase 6e (nonlinear effective action) — 6f.1, 6f.3, 6f.6
- Phase 6g (all waves) — 6f.1–6f.6 foundational
- Mathlib community — direct PR contributions

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §9

**Correctness-push highlights from strategy doc §12:**
- 6f.3 + 6g.2: NEC for `T_μν^emerg` (correctness-push anchor activates downstream)

---

*Phase 6f roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Six infrastructure waves, no in-project papers (all output is Mathlib PRs). Correctness-push anchor activates downstream via 6f.3 enabling NEC check on 6e.4 `T_μν^emerg`. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 17–28. External Mathlib progress is the main schedule risk.*
