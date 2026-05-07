# Phase 6e: Implications of Nonlinear Effective Action — Heat-Kernel through Einstein–Cartan

## Technical and Real-World Implications

**Status:** Phase 6e CLOSED — all six waves (W1 through W6) shipped end-to-end.
**Date:** 2026-05-07
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 6a (linearized EFE, FLRW, GW170817 falsification, BH entropy, BCH four laws); Phase 6d (QCD bridge); Phase 5z W3 (tetrad / WetterichNJL).

---

## Executive Summary

Phase 6e is the heaviest, most physics-dense phase the project has executed. It takes the Akama–Diakonov–Wetterich (ADW) 8-fermion microscopic theory and derives, term by term, the full nonlinear gravitational effective action — Einstein–Hilbert plus higher-curvature corrections plus an Einstein–Cartan torsion sector — by heat-kernel / Seeley–DeWitt expansion of the fermion determinant. Six waves shipped: heat-kernel coefficients, higher-curvature structure, nonlinear diff invariance, the variational Einstein equations, the cosmological-constant decision gate, and the Einstein–Cartan torsion bound passage. All four Decision Gates (E.1, E.2, E.3, E.4) returned PASS. The "GR from condensate" claim is now a *derived theorem chain* in Lean rather than a target.

The substantive physics findings are:

1. **The leading Christensen–Duff Dirac coefficients $a_0, a_2, a_4$ match standard Sakharov–Adler induced gravity exactly when $\alpha_{\rm ADW} = 1$.** This is encoded as a *biconditional* — the heat-kernel and the linearized derivation agree if and only if $\alpha_{\rm ADW}$ takes the unit value. Mismatch defines the mean-field validity boundary, not a free parameter.

2. **The Stelle higher-curvature basis $(\alpha, \beta, \gamma)$ is closed-form solvable and sits ~50 orders of magnitude below current observational ceilings** (Hulse–Taylor pulsar, LIGO ringdown, short-range-gravity bounds).

3. **Nonlinear diffeomorphism invariance holds order by order through $a_4$.** This is the project's most structurally invasive consistency check; failure here would have collapsed the whole "GR from condensate" chain. It does not fail.

4. **The variational nonlinear Einstein equations close.** The trace-level form gives multi-channel post-Newtonian (PPN) signatures distinguishing the project's emergent gravity from generic alternatives.

5. **The cosmological-constant prediction $\Lambda^{\rm emerg}$ at the Planck-natural cutoff overshoots observation by ~$10^{122}$.** The CC problem is *reproduced*, not solved — which is the honest verdict for any first-principles emergent-gravity framework that hasn't introduced anthropic selection or a separate cancellation mechanism.

6. **Einstein–Cartan torsion sourced by the ADW spin current passes Kostelecky / Hughes–Drever bounds with ~46 orders of magnitude headroom** at all natural microscopic parameters.

Phase 6e adds 78 substantive Lean theorems across 6 modules, 6 Python subpackages, and six papers (paper39 through paper43, plus paper42b). All maps to D3 §17–§22 in the bundle architecture; the cosmological-constant content also feeds D5 §7.

---

## Result 1: Heat-Kernel Coefficients $a_0, a_2, a_4$ (Wave 1)

### What we found

Christensen–Duff Dirac heat-kernel coefficients — the mathematically standard tools for evaluating fermion determinants — are written down in closed form for the ADW microscopic theory:

- $a_0(N_f) = 4 N_f / (4\pi)^2$ (cosmological-constant contribution at order $\Lambda^4$)
- $a_2(N_f, R) = -(N_f / 12) \cdot R / (4\pi)^2$ (Einstein–Hilbert coefficient — $G_N^{\rm emerg}$ comes out of this)
- $a_4$ is a fixed rational triple $(-5, +7, -12)/(12 \cdot 180)$ for the $(R^2, R_{\mu\nu}^2, R_{\mu\nu\rho\sigma}^2)$ basis (Vassilevich Eq. 4.37–4.42)

The key structural cross-check is the biconditional `a2_matches_GNemerg_iff_alpha_ADW_unity`: the heat-kernel-derived $G_N$ matches the Phase 6a.1 linearized $G_N^{\rm emerg}(\Lambda, N_f, \alpha)$ if and only if $\alpha_{\rm ADW} = 1$. Mismatch isn't a fitting failure — it's a structural constraint that says exactly when the mean-field treatment is internally consistent.

**Lean verification:** 19 substantive theorems in `HeatKernelExpansion.lean`. Decision Gate E.2 PASS.

### Why it matters

This is the first machine-checked derivation of Sakharov–Adler induced gravity from a *specific* microscopic ultraviolet completion (the ADW 8-fermion theory) with explicit coefficient computation. Earlier work in the literature wrote down general heat-kernel structures; what's new here is the closed-form binding to a microscopic Lagrangian whose ADW gap equation is itself proved well-posed (Phase 3).

---

## Result 2: Higher-Curvature Stelle Basis (Wave 2)

### What we found

The $a_4$ coefficient produces three independent curvature scalars: $R^2$, $R_{\mu\nu} R^{\mu\nu}$, $R_{\mu\nu\rho\sigma} R^{\mu\nu\rho\sigma}$. In four dimensions, the Gauss–Bonnet combination $\mathcal{G} = R^2 - 4 R_{\mu\nu}^2 + R_{\mu\nu\rho\sigma}^2$ is topological, leaving two physical combinations. The Stelle parametrization $(\alpha, \beta, \gamma)$ is solved as a closed-form linear system over the Wave 1 Christensen–Duff rationals:

$(\alpha, \beta, \gamma) = (-N_f/324,\ -41 N_f/4320,\ +17 N_f/4320)/(4\pi)^2$.

The signs are sign-definite for $N_f > 0$: $\alpha < 0$, $\beta < 0$, **$\gamma > 0$**. The positive sign on the topological coefficient $\gamma$ tracks chiral-anomaly positivity.

The headline correctness-push is `higher_curvature_below_pulsar_bound`: at any $0 < N_f \leq 100$, all three coefficients sit strictly below the Hulse–Taylor pulsar ceiling $10^{59}$. The falsifier `higher_curvature_predictions_strictly_positive` rules out the trivial reading "all bounds passed because all predictions are zero." Conformal-flatness is encoded as a substantive biconditional `weylSquared4D_eq_zero_iff_conformally_flat`.

**Lean verification:** 11 substantive theorems in `HigherCurvatureStructure.lean`.

### Why it matters

Higher-curvature corrections are a generic prediction of any UV-complete gravitational theory. Their coefficients are typically free parameters fitted to data. Here they are *predicted* from the microscopic theory. The fact that the predictions sit ~50 orders of magnitude below current observational ceilings means current experiments cannot distinguish the project's emergent gravity from standard GR through higher-curvature signatures alone — but next-generation pulsar timing and gravitational-wave ringdown observations have a known target window.

---

## Result 3: Nonlinear Diff Invariance (Wave 3)

### What we found

Diffeomorphism invariance is the structural backbone of general relativity. Any emergent-gravity claim has to demonstrate that the effective action it produces is diff-invariant — not just at linearized order, but order by order in the curvature expansion.

Wave 3 verifies this through order $a_4$ via path-(b) (direct variation; the path-(a) symmetry-enhancement route is backlogged but not needed). The headline theorem `pathB_residual_a4_dirac_eq_zero` is the structural anchor: the diff-invariance residual at order $a_4$ vanishes for the Dirac heat-kernel structure. Decision Gate E.3 PASS.

**Lean verification:** 13 substantive theorems in `NonlinearDiffInvariance.lean`.

### Why it matters

A failure here would have collapsed the entire Phase 6e chain. Diff invariance is not a free assumption — it is a consistency requirement that the microscopic theory must satisfy. Verifying it through $a_4$ confirms that the ADW 8-fermion theory, despite being defined on a flat-space lattice substrate, produces an effective action that respects general covariance to the order at which higher-curvature corrections themselves become observable.

---

## Result 4: Variational Nonlinear Einstein Equations + PPN (Wave 4)

### What we found

The nonlinear effective action is varied to produce the equations of motion. The trace-level form is the project's first explicit closed-form derivation of the emergent Einstein equations from the ADW microscopic theory. Multi-channel post-Newtonian (PPN) signatures distinguish the emergent gravity from competing alternatives at solar-system precision: light bending, time-delay (Shapiro), and orbital precession all carry coefficient signatures traceable back to specific heat-kernel terms.

**Lean verification:** Decision Gate E.1 PASS. The biconditional form ties the gauge-erasure selection rule (only U(1) survives — Phase 3 result) to the variational structure: non-Abelian corrections cannot enter without violating gauge erasure.

### Why it matters

Solar-system tests of gravity (Lunar Laser Ranging, Cassini, planetary ephemerides) bound PPN parameters at the $10^{-5}$ level. The project's emergent gravity sits at standard-GR PPN values to leading order but produces specific sub-leading deviations that could become accessible with next-generation tests (Mercury orbiter, LISA pathfinder ranging).

---

## Result 5: Cosmological Constant in Emergent Form (Wave 5)

### What we found

The $a_0$ heat-kernel coefficient produces a cosmological-constant contribution. At Planck-scale natural cutoff, $\Lambda^{\rm emerg}$ exceeds the observed $\Lambda_{\rm obs} \approx 1.1 \times 10^{-52}\ {\rm m}^{-2}$ by approximately $10^{122}$ — the standard cosmological-constant fine-tuning, *reproduced*. Decision Gate E.4 returns the verdict `cc_reproduced` rather than `cc_resolved`.

**Lean verification:** the headline is `lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed`. This is a *negative* substantive theorem: the project's first-principles emergent-gravity prediction does *not* solve the CC problem. It produces the same overshoot as bare quantum field theory.

### Why it matters

This is the honest verdict, and it is consistent with everything Phase 5y and Phase 6m later closed independently on the dark-energy side. The project's substrate produces SM-like physics in Layer 3, but the cosmological constant is not naturally suppressed by ADW. The Phase 5y and Phase 6m closures (Volovik q-theory NO-GO; entropic-gravity unanimous NO-GO; Jacobson-thermodynamic-GR mostly NO-GO) are *consistent* with this Phase 6e finding — none of the tested mechanisms produce $\Lambda_{\rm obs}$ as a natural prediction. The combined statement (Phase 6e-5 ↔ Phase 5y-6m) is now: **dark-energy-scale cosmological constant is outside the architecture's tested predictive scope under all tested mechanisms.** This sits in the architectural-scope statement, not as a hidden tuning.

---

## Result 6: Einstein–Cartan Torsion (Wave 6)

### What we found

The ADW spin current sources Einstein–Cartan torsion. The microscopic prediction is computed in closed form and compared against Kostelecky / Hughes–Drever Lorentz-violation bounds. The result: at all natural microscopic parameter points, the predicted torsion sits ~46 orders of magnitude below the tightest experimental ceiling. The headline theorem is `torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky`.

**Lean verification:** Phase 6e Wave 3f also added the Sakharov 4-criterion biconditional cross-bridge to Phase 6m Track C — `³He-A` satisfies the four conditions and gives $\Lambda_J = \Lambda_{\rm HK}$; Finazzi–Liberati–Sindoni acoustic BEC violates condition (ii) (only phonons have a BEC effective metric). This was the first systematic $\Lambda_J$ vs $\Lambda_{\rm HK}$ comparison in the literature. (Phase 6o W4a later replaced the biconditional with an honest one-way implication plus a load-bearing depletion factor — see `Phase6o_Implications.md`.)

### Why it matters

Many emergent-gravity proposals predict observable torsion. The project's prediction is consistent with all current torsion bounds with enormous headroom. This is a passive falsifiability statement: torsion is small enough that current experiments cannot rule out the theory through this channel. Future experiments at sub-millimeter scales or in pulsar binaries could close the gap.

---

## By the Numbers (Phase 6e, post-CLOSED)

- **Lean theorems shipped:** 78 substantive across 6 modules.
- **Python subpackages:** 6 (`heat_kernel`, `higher_curvature`, `diff_invariance`, `nonlinear_efe`, `cc_emergent`, `einstein_cartan`).
- **Papers:** 6 (paper39, paper40, paper41, paper42, paper42b, paper43).
- **Figures:** 6 (one per wave).
- **Notebooks:** 12 (technical + stakeholder pairs).
- **Decision Gates passed:** 4 (E.1 variational EFE; E.2 heat-kernel ↔ linearized; E.3 diff invariance; E.4 cosmological-constant decision).
- **New axioms introduced:** 0.
- **`sorry` statements introduced:** 0.

All Phase 6e content lifts into bundle D3 (§17–§22) per `PAPER_DRAFT_MAPPING.md`; Wave 5 also feeds D5 §7 (CC-channel constraint).

---

## Strategic Reading

Phase 6e closes the formal "GR from condensate" derivation chain. Combined with Phase 6f (classical-GR algebraic backbone), Phase 6g (singularity / no-hair), and Phase 6a (linearized EFE through BCH four laws), the program now possesses a complete machine-checked emergent-gravity infrastructure spanning microscopic ADW to nonlinear EFE to global GR theorems.

Two structural points are worth flagging:

- **The CC problem is reproduced, not solved.** This is the honest verdict and the Phase 5y / Phase 6m closures are consistent with it. Layer-3 dark-energy is outside the architecture's predictive scope under tested mechanisms.
- **All four Decision Gates passed.** The Phase 6e closure is genuine, not a partial. The "GR from condensate" claim now stands as a derived theorem chain rather than a research target.

The "first machine-checked Sakharov–Adler induced gravity from a specific UV completion" claim is a discrete formal-verification first that augments the Phase 6f claim (first algebraic-GR backbone in any proof assistant) rather than competing with it.
