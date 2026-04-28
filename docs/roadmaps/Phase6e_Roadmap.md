# Phase 6e: Nonlinear Effective Action from ADW — Heat-Kernel Expansion to Full Einstein Equations

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §8. The central missing calculation for "GR from condensate." Derives the full Einstein-Hilbert action (all orders in curvature) from the ADW 8-fermion microscopic theory via heat-kernel / derivative expansion of the fermion determinant.*

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. Primary anchors: `TetradGapEquation.lean` (24 after 5y W6, MF machinery), `FermionBag4D.lean` (16), `ADWMechanism.lean` (21), `Uqsl2Hopf.lean` (66, Dirac-operator infrastructure), Phase 6a.1 `LinearizedEFE.lean` (prerequisite — linearized calibration).

**Thesis.** Derive the full nonlinear effective action (Einstein-Hilbert, higher-curvature corrections, Einstein-Cartan with torsion) from the ADW 8-fermion microscopic theory. Six waves, five correctness-push highlights. This is the heaviest-compute, highest-leverage, most physics-dense track in the entire post-SK-EFT program. If it succeeds, "GR from condensate" is a derived theorem, not an aspirational claim.

**Correctness-push framing.** Every wave is highly falsifiable. 6e.1 (`a_2` coefficient vs 6a.1 linearized calibration) defines the mean-field validity boundary. 6e.3 (nonlinear diff invariance) is the central structural check. 6e.5 (cosmological constant in emergent form) either resolves or reproduces the CC problem.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §8 (6e) and §12 (correctness-push highlights)
> 4. Wave-specific pre-reads:
>    - 6e.1 — `TetradGapEquation.lean`, `FermionBag4D.lean`, `ADWMechanism.lean`, `Uqsl2Hopf.lean`; Seeley-DeWitt heat-kernel literature (Gilkey); Volovik vol 2 fermion-determinant chapters. Phase 6a.1 must be substantially complete.
>    - 6e.2 — 6e.1, Weyl-tensor / Gauss-Bonnet identity literature
>    - 6e.3 — 6e.1, 6e.2, Wald's variational techniques + diff-invariance literature
>    - 6e.4 — 6e.1–6e.3; Phase 6f.1 `Curvature.lean` (if available) or inline
>    - 6e.5 — 6e.1–6e.4, 6a.1 for calibration, Weinberg CC problem literature
>    - 6e.6 — 6e.1–6e.5, `VestigialGravity.lean`, Einstein-Cartan literature (Hehl+)
> 5. Deep research prompts (likely needed): heat-kernel expansion coefficients for 8-fermion effective actions; nonlinear diff-invariance check strategies (path-b direct vs path-a symmetry-enhancement); CC problem in emergent-gravity contexts. Drop into `Lit-Search/Tasks/Phase6e_*` folders as needed.
> 6. 6e is the heaviest phase. User must explicitly authorize each wave start. Do not speculate on 6e scope without user sign-off.
> 7. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to published constants); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check (no `rfl`/`decide`/`not_lt.mpr h_disagree` tautologies); (5) defining-the-conclusion check (vacuous when `f := <obvious target>`). The end-of-wave strengthening pass should produce **0 retroactive theorems** — if it produces 5+, log the failure mode and tighten the next wave's discipline.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6e:**
- Heat-kernel / Seeley-DeWitt expansion of `det(γ^a Ê^a_μ D^μ)`
- `a_0, a_2, a_4` coefficients → `Λ^4, R, R² + Ricci² + Riemann²`
- Higher-curvature basis: Gauss-Bonnet topological in 4D, 2 physical combinations
- Nonlinear diff-invariance check (path-b direct variation; path-a symmetry-enhancement deferred to backlog)
- Full Einstein equations as EOM from effective action variation
- Microscopic-to-macroscopic coefficient match: `G_N^emerg`, `Λ^emerg`, higher-curvature couplings
- Einstein-Cartan with torsion sourced by fermion spin current

**OUT OF SCOPE for 6e (per strategy doc §15 and §14):**
- Quantum-corrected effective action beyond mean field (two-loop + higher fermion-determinant corrections) — backlog
- Path-a symmetry-enhancement emergence theorem for 6e.3 — backlog; revisit if 6e.3 path-(b) succeeds
- Asymptotic-freedom / RG-flow corrections — backlog, HepLean adjacent
- Full numerical relativity / collapse simulations — OOS by framing
- Non-Abelian fracton hydrodynamics corrections — existing Tier 3, backlog

**OUT OF SCOPE for 6e (lands in 6g):**
- Singularity theorems
- BH uniqueness
- Cauchy problem

**Python-side note:** 6e is unusually Python-heavy relative to other phases — the heat-kernel expansion has a genuine CAS / numerical side that Python must cross-validate. Strategy doc lists +12–18 PM "derivation-side" PM on top of the Lean cost.

---

## Track A: Heat-Kernel Expansion (6e.1)

### Wave 1 — `HeatKernelExpansion.lean` (6e.1) [Pipeline: Stages 1–10] — **SHIPPED 2026-04-27** (Stage 11 notebooks user-triggered)

**Status:** Wave 1 closed end-to-end through Stage 10 (paper). Stages 11 (notebooks) and 13 (adversarial review) deferred per pipeline policy (user-triggered).
- `HeatKernelExpansion.lean`: **19 substantive theorems** / 0 sorry / 0 new axioms (verified `propext, Classical.choice, Quot.sound` only).
- `src/heat_kernel/`: 3 modules (`__init__.py`, `seeley_dewitt.py`, `a2_computation.py`, `a4_computation.py` — 4 files; subpackage shape matches Phase 6c standard) + 36 pytest cases (36/36 PASS in 0.04s).
- `papers/paper39_heat_kernel_expansion/paper_draft.tex`: long-form formalization paper, 4 pages, 368 KB, compiles clean, 9 bibitems (Sakharov 1968, Adler 1982, Diakonov 2011, Vladimirov-Diakonov 2012, Vergeles 2025, Gilkey 1995, Vassilevich 2003, Christensen-Duff 1979 + LinearizedEFE in-prep).
- `fig_a2_vs_linearized_G_N`: 2-panel calibration figure (rel-err vs α_ADW + G_N(Λ_UV) log-log), registered in `review_figures.py`.
- Closed-form Christensen-Duff Dirac coefficients `a_0(N_f) = 4 N_f / (4π)²`, `a_2(N_f, R) = -(N_f/12)·R / (4π)²`, `a_4` triple at rational `(-5, +7, -12) / (12·180)` per Vassilevich Eq. (4.37–4.42).
- Tracked-hypothesis structure `DiracHeatKernelAsymptotic` encodes the PDE-level asymptotic existence (Vassilevich Theorem 4.1, requires Mathlib spin-bundle infrastructure not yet available); structure invariants `a0_value` + `a2_R_value` force consumers to commit to the textbook coefficient table.
- **Decision Gate E.2 anchor**: load-bearing cross-bridge `G_N_from_a2_eq_G_N_sakharov` invokes `LinearizedEFE.G_N_sakharov` by name in proof body — drift-protection for the heat-kernel ↔ 6a.1 cross-module reference.
- **Correctness-push biconditional `a2_matches_GNemerg_iff_alpha_ADW_unity`**: heat-kernel `G_N(Λ, N_f)` matches linearized `G_N_emerg(Λ, N_f, α)` iff `α = 1` (Sakharov-Adler baseline). Forward direction uses `mul_right_cancel₀` against `G_N_sakharov_pos`; reverse invokes `LinearizedEFE.G_N_emerg_at_alpha_one`.
- Quantitative anchors: `G_N_from_a2_at_GUT_inverse` (closed-form `15·10³²/(12π)`); `G_N_from_a2_inverse_at_GUT_below_planck_squared` (norm_num via `Real.pi_gt_three`, showing GUT-cutoff gives `1/G_N < M_Pl²`).
- Gauss-Bonnet local-algebra identity `a4_gauss_bonnet_combination`: `c_R² − 4 c_Ricci² + c_Riem² = -N_f/(48 (4π)²)` via `ring`. Topological vanishing at the integral level deferred to Phase 6f.1.
- Discipline metric: **2 retroactive theorems** (post-wave audit caught: `fourPiSq_mul_inv` unused identity wrapper deleted; `dirac_heat_kernel_yields_G_N_sakharov` defining-the-conclusion P5 strengthened to `DiracHeatKernelAsymptotic.a2_eq_closed_form` consuming `a2_R_value`; `G_N_from_a2_at_GUT_anchor` rfl-tautology replaced with substantive `G_N_from_a2_at_GUT_inverse` exposing `one_div_div`). Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, **6e.1=2**.

### ~~Wave 1 specification (preserved for reference)~~

**Goal:** Systematic Seeley-DeWitt heat-kernel expansion of `det(γ^a Ê^a_μ D^μ)` organized by mass dimension. Produces coefficients `a_0, a_2, a_4, …` entering the effective action.

**Prerequisites:** Phase 6a.1 (`LinearizedEFE.lean`) substantially complete — provides the calibration point for `a_2`. User authorization before Stage 1.

**Module structure:**
- `lean/SKEFTHawking/HeatKernelExpansion.lean`
  - Fermion determinant structural form: `log det(D̸) = −∫ dτ/τ · Tr(e^{−τD̸²})`
  - Heat-kernel coefficients `a_0, a_2, a_4` as tensor objects on the manifold
  - `a_0 → Λ^4` (cosmological constant contribution)
  - `a_2 → R` (Einstein-Hilbert coefficient = `G_N^emerg`)
  - `a_4 → R² + Ricci² + Riemann²` (higher curvature)
  - **Correctness-push theorem:** `a_2_coefficient_matches_6a1_linearized_iff_mean_field_valid` — consistency between `a_2` nonlinear coefficient and `G_N^emerg` from 6a.1 linearized derivation defines the mean-field validity boundary; mismatch = concrete limit on ADW validity
- Target ~16–22 theorems.

**Python side (heavy):**
- `src/heat_kernel/` new subpackage — derivation-heavy
  - `seeley_dewitt.py` — Seeley-DeWitt coefficient evaluator
  - `a2_computation.py` — analytical `a_2` with cross-reference to 6a.1 `G_N^emerg`
  - `a4_computation.py` — `a_4` and higher-curvature basis decomposition
  - `heat_kernel_cas.py` — CAS-backed coefficient derivation (symbolic)
- Formula additions: `seeley_dewitt_a0`, `seeley_dewitt_a2`, `seeley_dewitt_a4`, each with Lean cross-ref

**Bridges:**
- Depends on 6a.1 (linearized calibration)
- Integrates `TetradGapEquation`, `FermionBag4D`, `ADWMechanism`, `Uqsl2Hopf`
- Feeds ALL downstream 6e waves (6e.2–6e.6)

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_heat_kernel.py`
- Physics derivation paper `papers/paper39_heat_kernel_expansion/paper_draft.tex` — long-form derivation, possibly Annals
- Figure: `fig_a2_vs_linearized_G_N` — consistency between 6e.1 `a_2` and 6a.1 `G_N^emerg` over parameter grid
- Inventory update: +16–22 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 6–10 person-months Lean + 6–12 derivation-side PM
**Risk:** High. Seeley-DeWitt machinery is mathematically deep; Mathlib coverage is uncertain. Budget for two separate deep-research rounds: (1) coefficient formalism in Lean; (2) CAS-backed symbolic derivation for cross-check.

**Correctness-push highlight.** `a_2` coefficient vs 6a.1 linearized `G_N^emerg` = mean-field validity boundary. Either outcome is substantive.

---

## Track B: Higher-Curvature Structure (6e.2)

### Wave 2 — `HigherCurvatureStructure.lean` (6e.2) [SHIPPED 2026-04-30 — Stages 1–12 closed]

**Status:** SHIPPED (Stages 1–12 closed; Stages 11 notebooks + 13 adversarial review deferred per pipeline policy). Phase 6 mid-program: 6e Wave 2 ships in parallel with reviewer-fix pass on Wave 1's `fig_a2_vs_linearized_G_N` (figure-reviewer 4 polish items resolved; claims-reviewer 6 WARNs deferred to a hygiene wave).

**Final state:**
- Lean module `lean/SKEFTHawking/HigherCurvatureStructure.lean`: **11 substantive theorems** / 0 sorry / 0 new axioms (verified `propext, Classical.choice, Quot.sound` only on the main basis-change identity, correctness-push, and tracked-Prop witness).
- Python: `src/higher_curvature/{__init__, curvature_basis, gauss_bonnet_check, observational_bound_check}.py` + 6 new functions in `formulas.py` (`higher_curvature_R_sq_coefficient`, `higher_curvature_Ricci_sq_coefficient`, `higher_curvature_Riemann_sq_coefficient`, `gauss_bonnet_4D_identity`, `weyl_squared_4D`, `higher_curvature_predicted_in_observational_band`).
- Tests: `tests/test_higher_curvature.py` — 40/40 PASS in 0.06 s.
- Figure: `fig_higher_curvature_obs_bounds` (2-panel: predictions across N_f bars + ceiling-comparison log scale).
- Paper: `papers/paper40_higher_curvature/paper_draft.tex` (3 pages, 446 KB, 7 bibitems).
- Inventory: +11 thms / +1 module / +40 tests / +1 figure / +1 paper.

**Discipline metric:** **1 retroactive theorem** (post-wave audit cut `gaussBonnet4D_vacuum_eq_riemann_sq` — trivial-after-unfold P3 with no downstream consumer). Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, **6e.2=1** (best yet).

**Highlights:**
- Closed-form Stelle-basis coefficients `(α, β, γ) = (-N_f/324, -41 N_f/4320, +17 N_f/4320) / (4π)²` solved from a 3×3 linear system over the Wave 1 Christensen-Duff rationals.
- **Sign-definite for N_f > 0**: α < 0, β < 0, **γ > 0** (the topological coefficient carries the chiral-anomaly-positive sign).
- **Main basis-change identity `a4_density_eq_a4_density_in_RC2GB_basis`**: substantive cross-bridge to Wave 1; proof body unfolds Wave 1 coefs by name (P6 drift-protection per `feedback_python_lean_refs_drift.md`); closes by `ring`.
- **Conformal-flatness biconditional `weylSquared4D_eq_zero_iff_conformally_flat`** + algebraic identity `gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination`: 𝒢 − C² = (2/3) R² − 2 R_μν².
- **Correctness-push `higher_curvature_below_pulsar_bound`**: at 0 < N_f ≤ 100, all 3 a_4 coefficients sit strictly below `hc_bound_pulsar = 10⁵⁹` (Hulse-Taylor binary pulsar, tightest ceiling). Proof structure: `1 < (4π)²` from `Real.pi_gt_three` → `fourPiSqInv < 1` → numerical estimate `100 · 12/2160 · 1 < 1` → `1 < 10⁵⁹` (norm_num).
- **Falsifier `higher_curvature_predictions_strictly_positive`**: predictions strictly non-zero — rules out the trivial reading "all bounds passed because all predictions are zero."
- **Tracked Prop predicate `H_HigherCurvatureWithinObservationalBounds B`** parameterised by upper bound; pulsar-bound witness theorem follows from correctness-push.

---

### Wave 2 specification (preserved for reference) — `HigherCurvatureStructure.lean` (6e.2) [Pipeline: Stages 1–8]

**Goal:** `R², Ricci², Riemann²` coefficients at `a_4` order assembled into basis (Gauss-Bonnet `𝒢` topological in 4D; 2 remaining combinations physical). Coefficients predicted from microscopic parameters.

**Prerequisites:** Wave 1 (`HeatKernelExpansion.lean`) substantially complete.

**Module structure:**
- `lean/SKEFTHawking/HigherCurvatureStructure.lean`
  - Curvature basis: `R², R_μν R^μν, R_μνρσ R^μνρσ` as 3 scalars
  - Gauss-Bonnet identity: `𝒢 = R² − 4 R_μν R^μν + R_μνρσ R^μνρσ` topological in 4D
  - Physical basis (2 combinations): define conventions
  - `a_4 → c_R R² + c_W W² + 𝒢 topological` decomposition theorem
  - **Correctness-push theorem:** `higher_curvature_coefficients_bounded_by_LIGO_pulsar_SRG` — microscopic predictions compared to observational bounds from LIGO, pulsar timing, short-range-gravity experiments
- Target ~10–14 theorems.

**Python side:**
- `src/higher_curvature/` new subpackage
  - `curvature_basis.py` — 3-scalar basis evaluator
  - `gauss_bonnet_check.py` — topological check in 4D
  - `observational_bound_check.py` — LIGO + pulsar + SRG bound comparison

**Bridges:**
- Depends on Wave 1
- Feeds 6e.3, 6e.4, 6e.5, 6e.6

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_higher_curvature.py`
- Paper `papers/paper40_higher_curvature/paper_draft.tex`
- Figure: `fig_higher_curvature_obs_bounds` — microscopic predictions over parameter grid vs LIGO/pulsar/SRG bounds
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Gauss-Bonnet topological identity in 4D is standard but Lean bookkeeping requires care.

---

## Track C: Diff-Invariance Check (6e.3)

### Wave 3 — `NonlinearDiffInvariance.lean` (6e.3) [Pipeline: Stages 1–12]

**Goal:** At each order in expansion, effective action must be diff-invariant. Path-(b) direct check: compute variation under infinitesimal coordinate change, verify it vanishes. Path-(a) symmetry-enhancement emergence theorem deferred to backlog.

**Prerequisites:** Waves 1, 2 substantially complete. User authorization before Stage 1 — 6e.3 is the structural correctness-push anchor.

**Module structure:**
- `lean/SKEFTHawking/NonlinearDiffInvariance.lean`
  - Diff-invariance predicate: `DiffInvariant (L : EffectiveLagrangian) : Prop`
  - Variation under infinitesimal coordinate change (path-b direct)
  - Order-by-order check: `a_0, a_2, a_4, …` each preserve diff invariance
  - **Correctness-push theorem:** `nonlinear_diff_invariance_holds_iff_higher_curvature_structure_matches_admissible_class` — critical structural check. If higher-order terms are NOT automatically diff-invariant, ADW emergent-gravity claim is falsified at nonlinear level.
- Target ~8–12 theorems.

**Python side:**
- `src/diff_invariance/` new subpackage
  - `variational_check.py` — diff-invariance numerical check at each order
  - `anomaly_hunt.py` — automated search for diff-anomaly in `a_4`+

**Bridges:**
- Depends on Waves 1, 2
- Feeds 6e.4 (full EFE) — diff invariance is prerequisite for well-posed variational EOM

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_diff_invariance.py`
- Paper `papers/paper41_diff_invariance/paper_draft.tex`
- Figure: `fig_diff_invariance_order_check` — order-by-order diff-invariance status
- Inventory update: +8–12 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** High if path-(b) fails. Fallback: document failure + move path-a to near-term priority (promoted from backlog).

**Correctness-push highlight.** If higher-order terms are NOT automatically diff-invariant → ADW emergent-gravity falsified at nonlinear level. Clean falsifiable result.

---

## Track D: Full EFE + Coefficient Match (6e.4, 6e.5)

### Wave 4 — `NonlinearEFE.lean` (6e.4) [Pipeline: Stages 1–8]

**Goal:** Variation of effective action w.r.t. `e^a_μ` produces `G_μν + α · R_μνρσ R^μνρσ g_μν + … = 8π G^emerg_N T_μν^emerg`, with computed higher-curvature coefficients.

**Prerequisites:** Waves 1, 2, 3 complete (path-b diff invariance confirmed or path-a promoted).

**Module structure:**
- `lean/SKEFTHawking/NonlinearEFE.lean`
  - Variational derivation: δS/δe^a_μ = 0 as tensor equation
  - Emergent stress-energy `T_μν^emerg` — ADW-substrate-sourced; explicit form
  - Full EFE: `G_μν + α · (higher-curvature) = 8π G^emerg_N T_μν^emerg`
  - **Correctness-push theorem:** `T_emerg_differs_from_matter_sector_in_observable_ways` — `T_μν^emerg` is not the same as bare matter-sector `T_μν`; difference in observable ways = testable prediction (modified gravity-like signatures)
- Target ~10–14 theorems.

**Python side:**
- `src/nonlinear_efe/` new subpackage
  - `efe_solver.py` — nonlinear EFE numerical solver at representative backgrounds
  - `T_emerg_vs_matter.py` — explicit comparison `T_μν^emerg` vs matter `T_μν`
  - `observable_prediction.py` — observable signatures (deflection / precession / ringing) from `T_emerg` corrections

**Bridges:**
- Depends on Waves 1, 2, 3
- Feeds 6e.5, 6e.6
- Cross-references Phase 6f.3 (`EnergyConditions.lean` when available) for `T_μν^emerg` DEC/NEC/WEC check

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_nonlinear_efe.py`
- PRD paper `papers/paper42_nonlinear_efe/paper_draft.tex`
- Figure: `fig_T_emerg_vs_matter` — observable deviation predictions
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Variational bookkeeping on nonlinear effective action is heavy.

### Wave 5 — Microscopic-to-Macroscopic Coefficient Match (6e.5) [Pipeline: Stages 1–8]

**Goal:** Express `G_N^emerg, Λ^emerg`, higher-curvature couplings in microscopic parameters `(Λ_UV, N_f, G_c)`. Test against experimental bounds.

**Prerequisites:** Waves 1–4 substantially complete. Phase 6a.1 for linearized calibration context.

**Module structure:** (No new standalone module; extends previous modules with `MicroscopicCoefficientMatch` sections — OR creates `MicroscopicCoefficientMatch.lean` standalone — decision at Stage 1.)
- Section: `HeatKernelExpansion.microscopic_a0 = fn(Λ_UV, N_f, G_c)` — `Λ^emerg` closed form
- Section: `HeatKernelExpansion.microscopic_a2 = fn(…)` — `G_N^emerg` closed form (cross-check 6a.1)
- Section: `HigherCurvatureStructure.microscopic_a4 = fn(…)` — higher-curvature closed form
- **Correctness-push theorem:** `Λ_emerg_resolves_or_reproduces_CC_problem` — under natural microscopic parameters, `Λ^emerg ≈ (2.3 meV)^4` would resolve CC problem; natural parameters giving `Λ^emerg ≈ M_Pl^4` reproduces it in emergent form (either is publishable; either supports Phase 5y's structural finding)
- Target ~8–12 theorems (extension-only wave, or +12–16 if standalone module).

**Python side:**
- `src/micro_macro_match/` new subpackage
  - `G_N_emerg_from_micro.py` — `G_N^emerg(Λ_UV, N_f, G_c)` evaluator
  - `Λ_emerg_from_micro.py` — `Λ^emerg(Λ_UV, N_f, G_c)` evaluator
  - `cc_problem_assessment.py` — natural-parameter scan: resolves or reproduces CC problem?

**Bridges:**
- Depends on Waves 1–4
- Cross-references 6a.1 for linearized calibration + Phase 5y closure DE landscape
- Feeds 6b.2 cosmological perturbations (if `Λ^emerg` small, background differs from de Sitter)

**Deliverables:**
- Module extension OR standalone module, zero-sorry
- `tests/test_micro_macro_match.py`
- Paper / section extending 6e.4 — `papers/paper42_nonlinear_efe/` § "Cosmological constant in emergent form" OR standalone short paper `papers/paper42b_cc_emergent/`
- Figure: `fig_Λ_emerg_parameter_scan` — `Λ^emerg` over microscopic parameters, observed value contour + natural-parameter region
- Inventory update: +8–12 theorems, +1 Python subpackage, +0/+1 paper

**Estimated LOE:** 2–4 person-months
**Risk:** Medium. CC problem in emergent form is the central test. Either outcome is substantive.

**Correctness-push highlight.** `Λ^emerg` CC-problem resolution OR reproduction. Clean publishable result either direction.

---

## Track E: Einstein-Cartan Extension (6e.6)

### Wave 6 — `EinsteinCartanExtension.lean` (6e.6) [Pipeline: Stages 1–8]

**Goal:** Full Einstein-Cartan with torsion sourced by fermion spin current. Natural since ADW uses tetrads.

**Prerequisites:** Waves 1–5 substantially complete. `VestigialGravity.lean` (24 after 5y W6) provides torsion-related machinery.

**Module structure:**
- `lean/SKEFTHawking/EinsteinCartanExtension.lean`
  - Torsion tensor `T^a_{μν} = e^a_μ;ν − e^a_ν;μ` as typed object
  - Fermion spin current as torsion source
  - Einstein-Cartan equations: `G_μν + ST terms = 8π G^emerg_N T_μν + spin torque terms`
  - **Correctness-push theorem:** `torsion_effects_small_but_nonzero_bounds_matched_by_ADW` — torsion observationally small but nonzero; microscopic prediction matches or over/under-shoots observational bounds
- Target ~10–14 theorems.

**Python side:**
- `src/einstein_cartan/` new subpackage
  - `torsion_tensor.py` — torsion-tensor numerical
  - `spin_current_source.py` — fermion spin current from ADW substrate
  - `torsion_obs_bound_check.py` — observational-bound comparison

**Bridges:**
- Depends on Waves 1–5
- Integrates `VestigialGravity.lean`
- Cross-references Phase 6c.3 (`EquivalencePrinciple.lean`) — torsion-induced EP violations flagged in 6c.3's mechanism matrix

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_einstein_cartan.py`
- Paper `papers/paper43_einstein_cartan/paper_draft.tex`
- Figure: `fig_torsion_obs_bound` — torsion microscopic prediction vs observational bounds
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium.

---

## Decision Gates

**Gate E.1 — before Wave 1 begins:** User explicit authorization. 6e is the heaviest phase.

**Gate E.2 — after Wave 1 (`HeatKernelExpansion`) ships:** Does `a_2` microscopic coefficient match 6a.1 `G_N^emerg` within stated tolerance? If YES → all subsequent 6e waves proceed. If NO → document mean-field validity boundary as the 6e.1 published result; reassess Waves 2–6 scope (still proceed, but with explicit "mean-field-valid" scope caveat).

**Gate E.3 — after Wave 3 (`NonlinearDiffInvariance`) ships:** Does path-(b) diff invariance hold order-by-order? If YES → Waves 4–6 proceed at full scope. If NO → document failure as the 6e.3 published result (itself the correctness-push output); promote path-(a) symmetry-enhancement to near-term priority (from backlog) as Wave 3b recovery attempt.

**Gate E.4 — after Wave 5 ships:** Does `Λ^emerg` resolve or reproduce CC problem under natural parameters? Document result; either way is substantive.

---

## Dependencies

```
6e.1 (HeatKernelExpansion) — depends on 6a.1; user gate
  ↓
6e.2 (HigherCurvatureStructure) — depends on 6e.1
  ↓
6e.3 (NonlinearDiffInvariance) — depends on 6e.1, 6e.2; user gate
  ↓
6e.4 (NonlinearEFE) — depends on 6e.1, 6e.2, 6e.3
  ↓
6e.5 (MicroscopicCoefficientMatch) — depends on 6e.1–6e.4
  ↓
6e.6 (EinsteinCartanExtension) — depends on 6e.1–6e.5

Parallelism:
  Mostly serial. Limited: 6e.4 can partially overlap with 6e.5 scoping.
```

---

## Timeline

| Wave | Scope | PM Lean | PM Derivation | Dependencies | Priority |
|------|-------|---------|---------------|--------------|----------|
| 6e.1 | `HeatKernelExpansion.lean` + long derivation paper | 6–10 | 6–12 | 6a.1 + user gate | **TIER 0 — central** |
| 6e.2 | `HigherCurvatureStructure.lean` + paper | 3–5 | (incl above) | 6e.1 | **TIER 1** |
| 6e.3 | `NonlinearDiffInvariance.lean` + paper | 3–5 | (incl above) | 6e.1, 6e.2 + user gate | **TIER 1** |
| 6e.4 | `NonlinearEFE.lean` + PRD paper | 3–5 | (incl above) | 6e.1–6e.3 | **TIER 1** |
| 6e.5 | Microscopic coefficient match (extension or standalone) | 2–4 | (incl above) | 6e.1–6e.4 | **TIER 1** |
| 6e.6 | `EinsteinCartanExtension.lean` + paper | 3–5 | (incl above) | 6e.1–6e.5 | **TIER 2** |

**Total Phase 6e LOE:** 20–34 person-months Lean + 12–18 derivation-side PM. Serial execution: wall-clock 18–36 months minimum. The largest single-phase budget in the post-SK-EFT program (alongside 6g).

**Deliverables cumulative:**
- 6 new Lean modules (`HeatKernelExpansion`, `HigherCurvatureStructure`, `NonlinearDiffInvariance`, `NonlinearEFE`, optional `MicroscopicCoefficientMatch`, `EinsteinCartanExtension`)
- 6 new Python subpackages
- 5+ papers (Papers 39–43 reserved; 42b if standalone)
- ~62–88 new theorems; zero sorry target; zero new axioms target

---

## Open Questions

**O.1 — LOAD-BEARING.** Is the Seeley-DeWitt heat-kernel machinery represented in Mathlib? Likely NO (would need deep research + potential Mathlib PRs). Drop prompt `Lit-Search/Tasks/Phase6e_mathlib_heat_kernel_audit.md` before Stage 1.

**O.2** — 6e.5 standalone module vs extension: decision affects paper-count. Default: extension + section in 6e.4 paper.

**O.3** — 6e.3 path-(a) vs path-(b): default path-(b); path-(a) in backlog. If path-(b) fails, promote path-(a).

**O.4** — CAS dependency in Python side: is the user willing to add SymPy / Mathematica as pipeline dependency for heat-kernel derivation? Most elements can be done analytically, but some `a_4` coefficients require CAS.

**O.5** — Paper strategy: long Annals paper for 6e.1 (derivation) vs bundle Waves 1–2 into one paper vs multiple short papers? User decision at Stage 10.

---

## What Success Looks Like

**Per wave:**
- 6e.1: Heat-kernel coefficients `a_0, a_2, a_4` explicitly derived; `a_2` consistency with 6a.1 `G_N^emerg` documented (consistent = mean-field valid; mismatch = validity boundary)
- 6e.2: Higher-curvature basis established; microscopic coefficients bounded by LIGO/pulsar/SRG
- 6e.3: Diff invariance confirmed order-by-order (or falsified, which is itself a correctness-push result)
- 6e.4: Full nonlinear EFE with `T_μν^emerg` explicitly formed; observable deviations predicted
- 6e.5: `G_N^emerg`, `Λ^emerg`, higher-curvature couplings in microscopic form; CC problem outcome documented
- 6e.6: Einstein-Cartan with torsion; observational bound comparison

**Cumulative:**
- 6 new Lean modules, 6 Python subpackages, 5+ papers
- Correctness-push anchors: `a_2` vs 6a.1 (6e.1), diff-invariance order-by-order (6e.3), `Λ^emerg` CC problem (6e.5), torsion observational bounds (6e.6)
- **Program-level value:** "GR from condensate" becomes a derived theorem with explicit microscopic coefficients, not an aspirational claim

---

## Cross-References

**Prior phases this extends:**
- Phase 3 (ADW mean-field) — `ADWMechanism.lean`, `TetradGapEquation.lean`
- Phase 5c/5i (quantum groups for Dirac-operator context) — `Uqsl2Hopf.lean`, related
- Phase 5d (Tetrad gap, fermion bag) — `FermionBag4D.lean`
- Phase 5y closure (vestigial extensions) — `VestigialGravity.lean`
- Phase 6a.1 (linearized EFE) — calibration point for 6e.1

**Feeds downstream phases:**
- Phase 6f.3 (`EnergyConditions.lean`) — `T_μν^emerg` tested against DEC/NEC/WEC
- Phase 6g.2 (Penrose singularity) — NEC check on `T_μν^emerg` is critical input

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §8

**Correctness-push highlights from strategy doc §12:**
- 6e.1: `a_2` vs 6a.1 linearized
- 6e.3: Nonlinear diff invariance order-by-order
- 6e.5: `Λ^emerg` from microscopic (CC problem)

---

*Phase 6e roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Six waves, central nonlinear-GR calculation, heaviest single-phase budget. Three correctness-push anchors (6e.1, 6e.3, 6e.5). All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 20–34 Lean + 12–18 derivation. Multi-year program on its own. User authorization required before Wave 1 and Wave 3 start.*
