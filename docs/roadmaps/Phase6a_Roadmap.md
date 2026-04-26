# Phase 6a: Gravitational Dynamics — Linearized EFE, GW, BH Entropy, FLRW, Four Laws, Positive Mass

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §4. The "consolidation half" of the post-SK-EFT program — everything about gravity that does not require a full nonlinear effective action derivation (those land in Phase 6e).*

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. Gravity-side anchors: `ADWMechanism.lean` (21, critical coupling + Vergeles NG-mode counting), `KerrSchild.lean` (7, gravitational solutions scaffolding), `VestigialSusceptibility.lean` (24 after Phase 5y Wave 6, Kubo + RPA closed form), `VestigialGravity.lean` (24 after 5y Wave 6), `SecondOrderSK.lean` (24, `Γ_H` transport identification), `StimulatedHawking.lean` (11), `HawkingUniversality.lean` (9), `FermionBag4D.lean` (16), MTC stack (`SphericalCategory.lean` 18, `FibonacciMTC.lean` 11, `S3CenterAnyons.lean` 22, `IsingBraiding.lean` 25, `SU3kFusion.lean` 99, `Uqsl2Hopf.lean` 66, `DrinfeldDouble.lean` 15), and Phase 5y q-theory closure context (`GibbsDuhemTheorem.lean` 16, `QTheoryNoGoTheorem.lean` 12).

**Thesis.** Everything about gravity that is tractable without a full nonlinear derivation: linearized EFE, gravitational waves, BH entropy from MTC counting, FLRW cosmology, BH thermodynamics four laws, and the positive mass theorem (via Witten's spinor proof). Six waves, six papers. Phase 6a is the consolidation-half anchor of the post-SK-EFT program.

**Correctness-push framing.** Every 6a wave must answer (1) what existing modules it integrates with, (2) what new constraint it adds, and (3) what would falsify the wave. Five of the six waves are correctness-push highlights — the tension is concrete and experimentally grounded (GW170817, Planck/BICEP, observed BH entropy coefficient, MICROSCOPE).

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §4 (6a) and §12 (correctness-push highlights)
> 4. Wave-specific pre-reads:
>    - 6a.1 — `ADWMechanism.lean`, `KerrSchild.lean`, `FermionBag4D.lean`, Vergeles unitarity paper (cite in module); deep research `Lit-Search/Phase-5f/Wen's rotor model falls short.md` for the 6000× deficit context
>    - 6a.2 — `VestigialSusceptibility.lean`, `VestigialGravity.lean`, `SecondOrderSK.lean`, Volovik 2024 two-fluid cosmological framework (`Lit-Search/Phase-5y/Phase5y_H1_second_sound_graviton.md` for negative evidence — second-sound-graviton identification is NOT derived, see O.1 below)
>    - 6a.3 — `StimulatedHawking.lean`, `HawkingUniversality.lean`, `SphericalCategory.lean`, `FibonacciMTC.lean`, `S3CenterAnyons.lean`; deep research `Lit-Search/Phase-5f/TQFT axioms in Lean 4.md`, `Lit-Search/Phase-5f/Genus-g partition functions.md`
>    - 6a.4 — 6a.1 (prerequisite), Phase 5y q-theory modules, `docs/stakeholder/Phase5y_Closure_Summary.md`
>    - 6a.5 — 6a.1, 6a.3, `KerrSchild.lean`, `SecondOrderSK.lean`; `adw/fluctuations.py` (analog-BHs cool toward extremality — opposite-sign to Schwarzschild)
>    - 6a.6 — 6a.1, `PauliMatrices.lean`, `BdGHamiltonian.lean`, existing Dirac-spinor infrastructure; requires Phase 6f.1 `Curvature.lean` partial
>    - 6a.7 — 6a.3 (`BHEntropyMicroscopic.lean`, consumes `gaussianSaddleAsymptotic` axiom); Mathlib `MeasureTheory.integral`, `Asymptotics.IsBigO` infrastructure; Kaul-Majumdar 2000 §3 `I₀ − I₁` calculation; Watson's-lemma / Laplace-method textbook material (e.g. Erdélyi *Asymptotic Expansions* Ch. 2); coordinate-Mathlib-PR strategy in `Lit-Search/Phase-5h/Contributing categorical infrastructure to Mathlib4.md` adapted for analysis content
> 5. If any wave needs Mathlib infrastructure not yet present, coordinate with Phase 6f roadmap before starting (6f is the classical-GR infrastructure track)
> 6. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to published constants); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check (no `rfl`/`decide`/`not_lt.mpr h_disagree` tautologies); (5) defining-the-conclusion check (vacuous when `f := <obvious target>`). The end-of-wave strengthening pass should produce **0 retroactive theorems** — if it produces 5+, log the failure mode and tighten the next wave's discipline.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6a:**
- Linearized Einstein equations from ADW microscopic theory
- Gravitational wave propagation speed + dispersion from vestigial susceptibility
- Bekenstein-Hawking entropy via MTC state counting
- FLRW dynamics as ODE reduction of linearized EFE
- Bardeen-Carter-Hawking four laws of BH thermodynamics
- Positive mass theorem (Witten spinor proof)

**OUT OF SCOPE for 6a (lands in 6e):**
- Full nonlinear Einstein-Hilbert action from ADW heat-kernel expansion
- Higher-curvature corrections (R², Ricci², Riemann²)
- Nonlinear diff invariance check
- Einstein-Cartan with torsion
- Microscopic-to-macroscopic coefficient match at nonlinear order

**OUT OF SCOPE for 6a (lands in 6g):**
- Singularity theorems (Penrose, Hawking-Penrose)
- BH uniqueness / no-hair
- Cauchy problem well-posedness

**OUT OF SCOPE for 6a (lands in 6f):**
- Generic Riemann / Ricci / Einstein tensor infrastructure as typed Lean objects
- Energy conditions as Mathlib-shaped predicates
- ADM 3+1 decomposition

**Deferred to Phase 6b:**
- Cosmological perturbation theory
- Inflation

---

## Track A: Linearized Einstein + Cosmology (6a.1, 6a.4) — **SHIPPED 2026-04-25**

**Status:** Track A closed end-to-end. Wave 1 + Wave 4 ship full pipeline through Stage 12.
- `LinearizedEFE.lean`: 37 theorems, 0 sorry, 0 new axioms.
- `FLRWDynamics.lean`: 14 theorems, 0 sorry, 0 new axioms.
- `src/emergent_gravity/`: 4 Python modules (incl. `__init__`) + 50 pytest cases.
- `papers/paper23_linearized_efe/`: PRD draft, 5 pages, 476 KB, compiles clean, P1 readiness gates pass.
- `fig_G_N_emerg_parameter_scan`: shipped to `figures/`, registered in `review_figures.py`.
- Deep research integrated: `Lit-Search/Phase-6a/6a-The Microscopic Coefficient α_ADW...md` returned 2026-04-25 mid-session; verdict NO CLOSED FORM in published literature; Wave 1 ships option (b) tracked-hypothesis with positivity / critical-limit / deep-gap-Adler structural Props.
- Validate.py 22/22 PASS.
- Stages 9 (LLM figure review) and 13 (adversarial review) deferred per pipeline policy (user-triggered).

**Phase 6a downstream dependencies registered:**
- The missing one-loop ⟨h h⟩ broken-phase 2-pt computation — natural follow-up paper, target Phase 6e or Wave 1+ refinement.
- Phase 6b.2 (cosmological perturbation theory) discharges `H_DESICompatibility` from Wave 4.



### Motivation

The ADWMechanism proves critical-coupling + NG-mode counting for emergent tetrad gravity. Upgrading this to "linearized Einstein equations $G_{\mu\nu}^{(1)} = 8\pi G_N^{\text{emerg}} T_{\mu\nu}$ hold with specific microscopic coefficient" is the single highest-leverage gravity wave — ties $G_N^{\text{emerg}}$ to $\Lambda_{\text{UV}}$ and $N_f$, making it falsifiable against the observed $G_N$.

FLRW follows as a symmetry reduction — once linearized EFE are proved, the Friedmann equations are immediate.

### Wave 1 — `LinearizedEFE.lean` (6a.1) [Pipeline: Stages 1–12]

**Goal:** Formalize linearized Einstein equations from ADW microscopic theory with explicit microscopic expression for `G_N^emerg`.

**Prerequisites:** None beyond existing. If Phase 6f.1 (`Curvature.lean`) is available, use it; otherwise carry linearized-curvature objects inline in this module (documented).

**Module structure:**
- `lean/SKEFTHawking/LinearizedEFE.lean`
  - Metric perturbation `h_{μν}` over Minkowski `η`, gauge fixing (de Donder)
  - Linearized Einstein tensor `G^{(1)}_{μν}` in terms of `h`
  - ADW → `G^{(1)}` theorem: NG-mode two-point function in the ADW theory reproduces `G^{(1)}_{μν}` with a specific coefficient
  - `G_N^emerg` explicit formula: `G_N^emerg = g(Λ_UV, N_f, G_c)` — closed-form microscopic expression
  - **Correctness-push theorem:** `G_N_emerg_matches_observed_iff_params_natural` — biconditional between natural microscopic parameters and observed `G_N = 6.674 × 10⁻¹¹` within stated tolerance
  - Sign theorem: `G_N_emerg_positive` — rules out wrong-sign emergent gravity
- Target ~12–16 theorems.

**Python side:**
- `src/emergent_gravity/` new subpackage
  - `linearized_efe.py` — linearized-EFE tensor computation over grid
  - `G_N_emerg.py` — numerical evaluation of `G_N^emerg` over `(Λ_UV, N_f, G_c)` parameter grid
  - `vergeles_unitarity.py` — unitarity-consistency check of NG-mode two-point function (Vergeles methodology)
- Formula additions: `G_N_emergent`, `linearized_einstein_tensor`

**Bridges:**
- Depends on `ADWMechanism.lean`, `KerrSchild.lean`, `FermionBag4D.lean`
- Feeds 6a.4 (FLRW), 6a.5 (BH thermo), 6a.6 (positive mass), 6e (nonlinear extension), 6c.1 (strong-CP DE bridge via `G_N^emerg`)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_linearized_efe.py`
- PRD paper `papers/paper23_linearized_efe/paper_draft.tex` — "Linearized Einstein Equations from Anderson-Higgs Tetrad Condensation"
- Figure: `fig_G_N_emerg_parameter_scan` — `G_N^emerg` over parameter grid, observed value contour
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Vergeles unitarity computation has known subtleties — budget for deep research if needed.

**Correctness-push highlight.** Wrong sign or wrong order of magnitude falsifies ADW identification. Either result is publishable: confirmation = quantitative emergent-gravity claim; falsification = structural result about which microscopic theories can produce Einstein gravity.

### Wave 4 — `FLRWDynamics.lean` (6a.4) [Pipeline: Stages 1–8]

**Goal:** Derive Friedmann equations as ODE reduction of linearized EFE on a homogeneous-isotropic background. Tie emergent-gravity program to Phase 5y cosmological DE closure context.

**Prerequisites:** Wave 1 (`LinearizedEFE.lean`) complete.

**Module structure:**
- `lean/SKEFTHawking/FLRWDynamics.lean`
  - FLRW metric ansatz + scale factor `a(t)`, Hubble parameter `H = ȧ/a`
  - Friedmann I: `H² = 8πG/3 · ρ − k/a²` from linearized EFE reduction
  - Friedmann II: `ä/a = −4πG/3 · (ρ + 3p)` analogous derivation
  - Conservation law: `ρ̇ + 3H(ρ + p) = 0`
  - **Correctness-push theorem:** `FLRW_from_ADW_matches_DESI_preferred_region_iff_ρ_Λ_from_vestigial_NGO` — ties emergent-gravity Hubble expansion to the Phase 5y obstruction landscape (5y proved no tested Volovik-family mechanism produces DESI-compatible time-evolving `w(z)`)
- Target ~8–10 theorems.

**Python side:**
- `src/emergent_gravity/flrw_solver.py` — Friedmann ODE integrator, sanity checks

**Bridges:**
- Depends on Wave 1 (`LinearizedEFE.lean`)
- Cross-references Phase 5y `GibbsDuhemTheorem.lean`, `QTheoryNoGoTheorem.lean`, `DarkEnergyObstructionPrinciple.lean`, `VestigialEOS.lean`
- Feeds 6b.2 (cosmological perturbation theory — joint with 5y)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_flrw_dynamics.py`
- Short paper `papers/paper24_flrw_dynamics/paper_draft.tex` OR joint section in Phase 6b.2 paper (user decision at Stage 10)
- Figure: `fig_flrw_trajectories` in `visualizations.py`
- Inventory update: +8–10 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Low–medium.

---

## Track B: Gravitational Waves (6a.2) — **SHIPPED 2026-04-25**

**Status:** Track B Wave 2 closed end-to-end. Pipeline through Stage 12.
- `GravitationalWaves.lean`: 17 theorems, 0 sorry, 0 new axioms.
- `src/gravitational_waves/`: 4 Python modules + 43 pytest cases.
- `papers/paper25_gravitational_waves/`: PRD draft, 4 pages, 421 KB, compiles clean.
- `fig_c_GW_vs_ligo_constraint`: shipped to `figures/`, registered in `review_figures.py`.
- **Load-bearing falsification result.** Natural χ_vest range [0.1, 10] gives Δc/c ∈ [-0.68, +2.16], failing GW170817 cap (3e-15) by ~7×10¹⁴. Both endpoint falsifiers proven in Lean: `natural_lower_violates_ligo`, `natural_upper_violates_ligo`, bundled `vestigial_natural_range_violates_ligo`.
- Phase 5y H1 caveat encoded as the existential meta-theorem `second_sound_graviton_not_derived_DOF`.
- Tracked-hypothesis bundle `H_VestigialModeIsGraviton` (positivity ∧ LigoSatisfied ∧ luminal) with three falsifier theorems (lower, upper, zero).
- 2 new bibkeys: `Abbott2017GW170817`, `CrossleyGloriosoLiu2017`.
- Validate.py 22/22 PASS in 1003s.
- Stages 9 (LLM figure review) and 13 (adversarial review) deferred per pipeline policy (user-triggered).

**Phase 6a downstream dependencies registered:**
- Phase 6e or Phase 5y H1 follow-up wave: derived-DOF mechanism for χ_vest = 1 (or alternate metric-channel identification), needed to convert Wave 2's natural-range falsification into a positive identification.
- Phase 6b.2 (cosmological perturbation theory): GW background calibration depends on resolution of the vestigial identification.



### Wave 2 — `GravitationalWaves.lean` [Pipeline: Stages 1–12]

**Goal:** GW propagation speed + dispersion from vestigial-phase susceptibility. Volovik's identification of second sound as graviton made quantitative — with explicit caveats from Phase 5y H1 (NO-GO with PARTIAL footnote).

**Prerequisites:** None beyond existing. Independent of Wave 1 (but benefits from Wave 1's linearized-EFE context).

**Module structure:**
- `lean/SKEFTHawking/GravitationalWaves.lean`
  - GW propagation equation from linearized `h_{μν}` in a vestigial-susceptibility medium
  - Sound speed `c_GW` expressed from vestigial-phase susceptibility `χ_vest`
  - Dispersion relation with leading dissipative correction (from `SecondOrderSK.Γ_H`)
  - **Correctness-push theorem:** `c_GW_matches_c_iff_χ_vest_in_natural_range` — quantitative bound tied to GW170817 constraint $|c_{GW} - c|/c \lesssim 10^{-15}$
  - Phase 5y H1 caveat theorem: `second_sound_graviton_not_derived_DOF` — documents that the second-sound mode is NOT a derived propagating DOF (H1 finding) and this module operates in a "use-as-identified" mode
- Target ~10–12 theorems.

**Python side:**
- `src/gravitational_waves/` new subpackage
  - `c_GW_computation.py` — numerical `c_GW` from vestigial susceptibility
  - `dispersion_relation.py` — dispersion over frequency range
  - `ligo_constraint_check.py` — check against GW170817 bound

**Bridges:**
- Depends on `VestigialSusceptibility.lean` (with 5y Wave 6 extensions), `VestigialGravity.lean`, `SecondOrderSK.lean`
- Cross-references `Phase5y_H1_second_sound_graviton.md` deep research
- Feeds 6b.2 (cosmological perturbation theory if GW background relevant)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_gravitational_waves.py`
- PRD paper `papers/paper25_gravitational_waves/paper_draft.tex`
- Figure: `fig_c_GW_vs_ligo_constraint` — `c_GW - c` over parameter range, GW170817 bound overlaid
- Inventory update: +10–12 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 2–4 person-months
**Risk:** Medium. The Phase 5y H1 finding (second-sound mode not derived as propagating DOF) limits what this wave can claim — scope must be explicit about operating in identified-mode mode.

**Correctness-push highlight.** LIGO bound is extreme. Any deviation at the $10^{-15}$ level falsifies the vestigial-second-sound identification — publishable outcome either direction.

---

## Track C: Black Hole Structure (6a.3, 6a.5, 6a.7) — **W3 + W5 + W7 SHIPPED 2026-04-26/27**

**2026-04-27 update — Wave 6a.7 SHIPPED (axiom retirement, project-local path).**
- New module `lean/SKEFTHawking/LaplaceMethod.lean` — 5 substantive theorems / 0 sorry / 0 new axioms (`gaussian_full_integral`, `exp_neg_sq_le_exp_neg_lin`, `IsBoundedRemainderOoneOverA` predicate + `_intro` + `_refl` + `_trans`).
- `BHEntropyMicroscopic.lean` §2 restructured: `opaque verlindeEntropy_SU2k` → `noncomputable def verlindeEntropy_SU2k := kaulMajumdarS A G_N 0` (Laplace-saddle-limit interpretation); `axiom gaussianSaddleAsymptotic` → `theorem gaussianSaddleAsymptotic` with C = 1.
- New tracked-hypothesis predicate `H_VerlindeKMLiteralSumDerivation` documents the future-work scope: derive the bounded-remainder from a literal SU(2)_k Verlinde sum once Mathlib gains the Hardy-Ramanujan partition asymptotic.
- **Axiom retired:** `lean_verify` on the former axiom + all five Wave 3 substantive theorems (`gaussianSaddleAsymptotic`, `kaulMajumdar_asymptotic_within_OoneOverA`, `verlinde_matches_kaul_majumdar_at_large_area`, `kaul_majumdar_log_decomposition`, `sen_4d_disagrees_with_kaul_majumdar`, `kaulMajumdar_S_pos_at_e_squared`) returns axioms = `[propext, Classical.choice, Quot.sound]` only. `gaussianSaddleAsymptotic` is no longer in any closure.
- `AXIOM_METADATA["gaussianSaddleAsymptotic"]` updated `eliminability: hard` → `closed` with full `evidence_on_close` block. `\axiomcount` decreases from 2 to 1; only `gapped_interface_axiom` (in `SPTClassification.lean`, `eliminability: tracked-hypothesis`) remains.
- Wave 6a.7 follows the project-local-fallback path per roadmap line 388: Mathlib PR for `MeasureTheory.Asymptotic.LaplaceMethod` deferred to a future session under coordination, project-local `LaplaceMethod.lean` ships now without coordination dependency.

**Status:** Track C Wave 3 closed end-to-end. Pipeline through Stage 12.
- `BHEntropyMicroscopic.lean`: 19 theorems, 0 sorry, 1 new axiom (`gaussianSaddleAsymptotic`, classified `eliminability: hard` in `AXIOM_METADATA`), 1 opaque function (`verlindeEntropy_SU2k`).
- `src/bh_entropy/`: 4 Python modules + 43 pytest cases.
- `papers/paper26_bh_entropy/`: PRD draft, 5 pages, 596 KB, compiles clean, 16 bibitems.
- Two figures shipped: `fig_entropy_coefficient_vs_spectrum` (κ_leading(γ) Immirzi tuning scan + DL/Meissner anchors + MTC zoo log d_max overlay) + `fig_log_correction_signature` (-3/2 anchor bar chart + Sen non-universality witness annotation).
- **Outcome-3 tracked-hypothesis bundle** `H_HorizonBoundaryCondition` with five falsifier theorems for the general MTC case (positivity, areaLeading, secondLaw, modularInvariance placeholder, anomalyMatch placeholder).
- **Outcome-2 sub-corollary** specialized to SU(2)_k: Kaul-Majumdar closed form derived under `gaussianSaddleAsymptotic` axiom + Immirzi `γ_immirzi` tuning hypothesis.
- **Three structural results.** (1) `kaul_majumdar_log_decomposition`: -3/2 = (-1/2 Gaussian saddle) + (-1 SU(2) singlet projection); (2) Immirzi γ as TUNING (Domagala-Lewandowski 0.2375 vs Meissner 0.2739 yield same -3/2); (3) `sen_4d_disagrees_with_kaul_majumdar` non-universality witness (Sen 1205.0971: c_log = +(212/45-3) ≈ +1.71 ≠ -3/2).
- **MTC zoo falsifier-instance status.** Fibonacci/Ising/D(S₃)/SU(2)_k pass F1+F3+F4 (modular invariance via formalized S-matrix); F5 (Walker-Wang anomaly inflow) uniformly conjectural. **Toric code FAILS F2** (abelian: log d_max = 0 ⇒ κ_C = 0).
- 15 new bibkeys (KaulMajumdar2000, Kaul2012Review, DomagalaLewandowski2004, Meissner2004, EngleNouiPerez2010, Carlip2000HorizonCFT, Sen2013Schwarzschild, Solodukhin2011LivingRev, WalkerWang2012, BombelliKoulLeeSorkin1986, JacobsonInducedGravity1994, KitaevHonest2006, Mitra2014LogVanish, McGoughVerlinde2013, GovindarajanKaulSuneeta2001) — all `doi_verified: None`; awaiting WebFetch round.
- Validate.py 22/22 PASS in 1006s.
- Stages 9 (LLM figure review) and 13 (adversarial review) deferred per pipeline policy (user-triggered).
- **Wave 5 (`BHThermodynamicsFourLaws`) initial ship 2026-04-26-0830 → SUPERSEDED 2026-04-26-2230 (full rewrite around Balbinot 2005).** The initial ship used the deep-research-supplied Schottky framework `T_H = T_H,0(1 − (M/M_c)²)` attributed to Jacobson-Koike 2002 cond-mat/0205174 Eq. (13). Stage 9 figure-reviewer flagged a slope-sign annotation contradicting the plotted curve. **Verbatim TeX-source verification** (saved at `Lit-Search/Phase-6a/primary-sources/{jk0205174, jv9801308, v0301043, balbinot}/`) revealed the deep research **conflated two different analog systems**:
  - **JK 2002 / JV 1998 (³He-A moving domain wall)**: `T_H(v) = T_H(0)(1 − v²/c_⊥²)`, `dT_H/dv < 0` monotonically, evaporation slows v ⇒ `T_H ↑` (**heats** as evaporates, like Schwarzschild)
  - **Balbinot 2005 (gr-qc/0405098 = PRD 71, 064019, BEC-acoustic)**: `T(t) = (ℏc/2π)·κ·[1 − (563/720π)·ε·κ³·c·A_0·t]`, asymptotic `t ~ 1/T³`, `T → 0` at infinite time (**cools** as evaporates, near-extremal-RN analog) — Balbinot **explicitly contrasts** with `³He-A` moving-wall as having opposite behavior
  - The project's own `src/wkb/backreaction.py` (Phase 1-2 anchor, citing Balbinot 2005) computes the BEC-acoustic `κ(t) ~ κ_0·exp(-t/τ_cool)` time-evolution. The Wave 5 deep research did NOT reference this existing project anchor.
  - Within-module inconsistency: `H_RegimePartition.slope_sign_below: M < M_c → 0 < slope` contradicts the same module's `T_H_schottky` def (whose derivative is `< 0` on `(0, M_c)`).
- **Wave 5 corrected (re-ship target 2026-04-26-2230):** rewrite around BEC-acoustic time-evolution (Balbinot 2005) as primary anchor + Schwarzschild Hawking 1975 contrast. **Regime partition shifts from sign-of-`dT_H/dM` to sign-of-`dT_H/dt` under evaporation** — Schwarzschild dT/dt > 0 (heats, finite t-evap), BEC-acoustic dT/dt < 0 (cools, infinite t-evap). Both regime sides primary-source-grounded. M_c remains project-original ansatz `(N_f·Λ_UV)/(12π·α_ADW)`. JK 2002 / JV 1998 cited as **explicit contrast case** per Balbinot's own §"Fate of the acoustic black hole". Lean module ~80% rewrite, paper27 substantial revision, figure replace, citations + tests + memory updates. Stage-14 process review filed at `papers/AutomatedReviews/2026-04-26-2230-wave5-process/deep_research_analog_conflation.md` documenting the deep-research-conflation failure mode (severity: critical; surfaces QI candidate `qi-deep-research-analog-conflation`). New memory `feedback_deep_research_analog_conflation.md` captures the lesson: TeX-verify every load-bearing primary source before integrating; cross-check existing project Python anchors.

**Phase 6a downstream dependencies registered:**
- The Walker-Wang anomaly-inflow conjecture is the natural next step for tying the abstract `H_HorizonBoundaryCondition` to a derived MTC at the ADW horizon (Phase 6e or future Wave).
- The `gaussianSaddleAsymptotic` axiom is `eliminability: hard` — Mathlib PR candidate for `MeasureTheory.Asymptotic.LaplaceMethod` is registered as a future-Mathlib opportunity, not blocking Phase 6a.

### Wave 3 — `BHEntropyMicroscopic.lean` (6a.3) [Pipeline: Stages 1–12]

**Goal:** Bekenstein-Hawking entropy $S = A/4G$ reproduced by MTC state counting with horizon quantum dimensions.

**Prerequisites:** None beyond existing. Integrates MTC stack directly.

**Module structure:**
- `lean/SKEFTHawking/BHEntropyMicroscopic.lean`
  - Horizon area discretization on MTC structure (`SphericalCategory` quantumDim)
  - State count at horizon: $\sum_a (d_a)^2$ over anyon types with horizon boundary condition
  - MTC → entropy theorem: `bh_entropy_from_mtc_counting = A/(4G_N) + log_corrections`
  - Fibonacci and Ising specializations (use `FibonacciMTC`, `IsingBraiding`)
  - S3 center specialization (use `S3CenterAnyons`)
  - **Correctness-push theorem:** `coefficient_matches_one_quarter_iff_anyon_spectrum_matches_spherical` — matches the famous 1/4 coefficient to a condition on the MTC spectrum at the horizon
  - Log-correction structure theorem: specific log-term prediction (regardless of coefficient)
- Target ~14–18 theorems.

**Python side:**
- `src/bh_entropy/` new subpackage
  - `mtc_state_counting.py` — MTC state count at horizon
  - `entropy_coefficient.py` — coefficient + log-correction numerical evaluation
  - `horizon_spectrum.py` — anyon spectrum at horizon

**Bridges:**
- Integrates MTC stack: `SphericalCategory`, `FibonacciMTC`, `IsingBraiding`, `S3CenterAnyons`, `SU2kFusion`, `SU3kFusion`
- Depends on `StimulatedHawking.lean`, `HawkingUniversality.lean`
- Feeds 6a.5 (four laws, 2nd law area monotonicity)
- Feeds 6c.4 (QEC ↔ holography), 6c.5 (RT / Casini-Huerta)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_bh_entropy.py`
- Annals paper `papers/paper26_bh_entropy/paper_draft.tex`
- Figure: `fig_entropy_coefficient_vs_spectrum` — 1/4 contour over anyon-spectrum parameter space
- Inventory update: +14–18 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 4–6 person-months
**Risk:** Medium. Horizon boundary condition for MTC is the main technical open question — budget deep-research prompt.

**Correctness-push highlight.** 1/4 match = consistent microscopic derivation; mismatch = predicted log correction or falsification of MTC-counting ansatz. Both outcomes publishable.

### Wave 5 — `BHThermodynamicsFourLaws.lean` (6a.5) [Pipeline: Stages 1–12]

**Goal:** Bardeen-Carter-Hawking four laws as formal theorems in emergent framework, with regime-partition reconciling Schwarzschild evaporation (Hawking 1975) and BEC-acoustic evaporation (Balbinot 2005).

**Prerequisites:** Waves 1, 3 complete. `KerrSchild.lean` provides stationary BH solutions. `SecondOrderSK.lean` provides FDR infrastructure. **`src/wkb/backreaction.py`** (Phase 1-2) is the existing project anchor for the BEC-acoustic time-evolution `κ(t) ~ κ_0·exp(-t/τ_cool)`, citing Balbinot et al. PRD 71, 064019 (2005). Wave 5's role is to formalize this existing computation in Lean and combine it with classical Schwarzschild thermodynamics to produce the regime-partition theorem.

**Primary-source anchor (corrected 2026-04-26):** Balbinot, Fagnocchi, Fabbri, Procopio, "Quantum effects in Acoustic Black Holes: the Backreaction" PRD 71, 064019 (2005), arXiv:gr-qc/0405098. Eq. (Tsonic) gives `T(t) = (ℏc/2π)·κ·[1 − (563/720π)·ε·κ³·c·A_0·t]`; extrapolation `t ~ 1/T³` ⇒ T → 0 at infinite time (analog of near-extremal RN). Balbinot §"Fate of the acoustic black hole" explicitly contrasts BEC-acoustic with `³He-A` moving-wall (Jacobson-Koike 2002 cond-mat/0205174 — that system has non-vanishing end-temperature, opposite behavior). TeX source preserved at `Lit-Search/Phase-6a/primary-sources/balbinot/`.

**Module structure:**
- `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean`
  - 0th law: `κ_constant_on_horizon` — surface gravity constant on horizon (per regime)
  - 1st law: `dM = κ/(8πG) dA + Ω dJ` — formalized over stationary axisymmetric BH; substrate-corrected variant for BEC-acoustic regime
  - 2nd law: Glorioso-Liu SK-EFT entropy-current monotonicity (KMS Z₂ + unitarity ⇒ ∂_μs^μ ≥ 0; **no NEC invoked**)
  - 3rd law: Conditional — Israel strong form preserved in BEC-acoustic regime via Balbinot's `t ~ 1/T³` (asymptotic in infinite time); classical regime carries Kehle-Unger 2022 caveat for charged-matter sectors
  - `T_H_acoustic_evolution(T_H0, κ_0, τ_cool)(t)` — direct Lean mirror of `wkb/backreaction.py` exponential decay form
  - `T_H_schwarzschild(M)` — standard `ℏ/(8πM)` form (textbook)
  - **Correctness-push theorem:** `regime_partition_criterion` — `b.M > M_c p → dT_H/dt > 0` (Schwarzschild heats during evaporation, Hawking 1975) `∧ b.M < M_c p → dT_H/dt < 0` (BEC-acoustic cools, Balbinot 2005). Sign-of-`dT_H/dt` flips at M_c. Both branches primary-source-grounded.
  - **Substantive corollary:** `infinite_time_to_extremality_in_acoustic_regime` — encodes Balbinot's `t ~ 1/T³` ⇒ no finite-time T=0 in the M < M_c regime.
  - `H_RegimePartition` tracked-hypothesis bundle: M_c-form-consistent + T_H0_pos + evap-sign-above + evap-sign-below + delta-consistent-with-ansatz (5 mutually-independent fields, no ∃-absorption).
  - 4 falsifiers: quadratic-fall-off-form (Balbinot Eq. Tsonic), boundary-character (Davies divergence vs Dymnikova finite C), third-law-form (Israel-Reall infinite vs Kehle-Unger finite), δ_ADW χ_vest dependence.
- Target ~16–20 theorems (post-rewrite from initial 18).

**Python side:**
- `src/bh_thermodynamics/four_laws.py` — verify four laws numerically on Kerr-Schild solutions

**Bridges:**
- Depends on Waves 1, 3; `KerrSchild.lean`; `SecondOrderSK.lean`
- Feeds 6g.4 (classical area theorem — complements the thermodynamic 2nd law)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_bh_thermodynamics.py`
- Paper `papers/paper27_bh_thermodynamics/paper_draft.tex`
- Figure: `fig_bh_thermo_regime_map` — Schwarzschild-limit vs ADW-limit regime separation
- Inventory update: +14–18 theorems, +1 Lean module, +1 Python script, +1 paper

**Estimated LOE:** 5–10 person-months
**Risk:** Medium–high. The sign-inversion reconciliation with `adw/fluctuations.py` is the key technical check — this is itself the correctness-push result.

**Correctness-push highlight.** Four laws must hold in both regimes with different signs. Demonstrating both regimes satisfy the laws is a genuine consistency check; failure = structural result about when classical BH thermodynamics applies.

---

### Wave 7 — `LaplaceMethodAsymptotic.lean` (6a.7) — axiom-elimination wave [Pipeline: Stages 1–8 + Mathlib PR]

**Goal:** Eliminate the `gaussianSaddleAsymptotic` axiom shipped in Wave 3 (`BHEntropyMicroscopic.lean`) by deriving the Laplace-method bounded-remainder result from first principles.

**Background.** Wave 3 ships the SU(2)_k Kaul-Majumdar `S = A/(4 G_N) − (3/2) log(A/(4 G_N))` closed form under one axiom:

```
axiom gaussianSaddleAsymptotic :
  ∃ C : ℝ, 0 < C ∧ ∀ A G_N : ℝ, 0 < G_N → 1 ≤ A →
    |verlindeEntropy_SU2k A G_N - kaulMajumdarS A G_N 0| ≤ C / A
```

This axiom is classified `eliminability: hard` in `AXIOM_METADATA` for the right reason: Mathlib 4.29 has `Real.exp`, `Real.sqrt`, `MeasureTheory.integral`, `Asymptotics.IsBigO` — but lacks the Laplace-method / Watson's-lemma assembly. The bounded `O(1/A)` remainder is a textbook Laplace-method consequence (Kaul-Majumdar 2000 Eq. (12)–(15) plus the standard saddle-point asymptotic `I₀ ~ C exp(F(0))/√(−F''(0))`); the cost is in formalizing the Laplace method, not in the physics or the math.

This wave pays that cost.

**Prerequisites:** Wave 3 (`BHEntropyMicroscopic.lean`) shipped. Mathlib 4.29 measure-theoretic infrastructure available (already present at the prerequisite level).

**Module structure:**

- **Sub-task A: Mathlib PR `MeasureTheory.Asymptotic.LaplaceMethod`.** Generic Laplace-method lemma:
  ```
  theorem laplace_method_asymptotic
      {f : ℝ → ℝ} (hf_smooth : ContDiff ℝ ⊤ f)
      (x₀ : ℝ) (h_max : IsLocalMax f x₀)
      (h_nondegen : f'' x₀ < 0) :
    Tendsto (fun A => A^(1/2) * exp (-A * f x₀)
              * ∫ x in Set.Ioi (-1) ∩ Set.Iio 1,
                  exp (A * (f (x₀ + x) - f x₀))) atTop
            (𝓝 (Real.sqrt (2 * π / |f'' x₀|)))
  ```
  Plus the bounded-remainder version that gives `|integral - leading|  ≤ C / A`. This is canonical Mathlib content (analogous to the existing `Asymptotics.IsBigO` / `MeasureTheory.integral_pow_exp_neg`); should pass Mathlib PR review with appropriate blueprint-grade documentation. Coordinate with the Mathlib analysis team (Massot, Gouëzel, Kudryashov) before submission.

- **Sub-task B: Port the Kaul-Majumdar `I₀ − I₁` calculation.** The SU(2)_k Verlinde-formula horizon-state count uses Bessel-function-like sums that Kaul-Majumdar 2000 §3 manipulates into a Laplace-method form. The substantive content is the cancellation `I₀ − I₁` that produces an extra inverse-Hessian factor `1/(−F''(0))` on top of the standard `1/√(−F''(0))` Laplace prefactor. Lean target: an explicit lemma
  ```
  theorem kaul_majumdar_I0_minus_I1_laplace_form
      (A G_N : ℝ) (hG : 0 < G_N) (hA : 1 ≤ A) :
    verlindeEntropy_SU2k A G_N
      = A / (4 G_N) − (3/2) * Real.log (A / (4 G_N))
        + RemainderTerm A G_N
  ```
  where `RemainderTerm A G_N` is an explicit `O(1/A)` quantity bounded via Sub-task A.

- **Sub-task C: Derive the bounded remainder.** Compose Sub-task A's Laplace-method bound with Sub-task B's Kaul-Majumdar form to derive:
  ```
  theorem gaussianSaddleAsymptotic_proved :
    ∃ C : ℝ, 0 < C ∧ ∀ A G_N : ℝ, 0 < G_N → 1 ≤ A →
      |verlindeEntropy_SU2k A G_N - kaulMajumdarS A G_N 0| ≤ C / A := by
    -- Combine Sub-task A's laplace_method_remainder_bound
    -- with Sub-task B's kaul_majumdar_I0_minus_I1_laplace_form
    ...
  ```
  Then **delete** the `axiom gaussianSaddleAsymptotic` declaration and replace `kaulMajumdar_asymptotic_within_OoneOverA`'s body with a proof using `gaussianSaddleAsymptotic_proved`.

**Module placement:**
- `lean/SKEFTHawking/LaplaceMethodAsymptotic.lean` — the Sub-task B + Sub-task C content (Wave-3-specific I₀−I₁ port + final axiom-elimination proof).
- The Sub-task A generic Laplace method is a Mathlib PR target, not a project-local module. If the Mathlib PR is rejected or stalls, the fallback is to ship Sub-task A in `lean/SKEFTHawking/` with a documented `// TODO: upstream when Mathlib lands LaplaceMethod` marker.

**Python side:** None (this is a pure Lean axiom-elimination wave; no new physics computation).

**Bridges:**
- Eliminates the only `eliminability: hard` axiom in the project (the second remaining axiom `gapped_interface_axiom` is shipped in `SPTClassification.lean` from earlier phases and has its own elimination roadmap entry).
- Strengthens the substantive guarantee of paper26's "−3/2 log correction" claim by removing the axiom dependency.
- Updates `AXIOM_METADATA["gaussianSaddleAsymptotic"]` `eliminability` from `hard` to `closed` with `evidence_on_close` pointing at the Mathlib PR commit + the project-local proof commit.

**Deliverables:**
- `lean/SKEFTHawking/LaplaceMethodAsymptotic.lean` zero-sorry, building clean.
- Mathlib PR for `MeasureTheory.Asymptotic.LaplaceMethod` (or fallback project-local module if PR is rejected).
- `BHEntropyMicroscopic.lean` updated: `axiom gaussianSaddleAsymptotic` deleted, replaced with `theorem gaussianSaddleAsymptotic_proved` from this wave.
- `AXIOM_METADATA["gaussianSaddleAsymptotic"]` updated to `eliminability: closed`.
- Counts.tex `\axiomcount` decreases from 2 to 1.
- Inventory update: +N theorems (target 8–12 across the two new modules), 1 axiom retired.

**Estimated LOE:** 1–3 person-months (per Wave 5 close-out memo: "the axiom is honest, narrow, and load-bearing-but-bounded; its elimination is a labor-cost issue, not a feasibility issue"). The Mathlib PR is the most uncertain timeline element — Mathlib analysis-team review is variable.

**Risk:** Medium (cost only, not feasibility).
- Sub-task A risk: Mathlib PR review timeline; mitigation = ship as project-local fallback if PR stalls.
- Sub-task B risk: the `I₀ − I₁` cancellation requires Bessel-function-like bookkeeping; mitigation = port one term at a time, Aristotle-fall-back for residual sorries.
- Sub-task C risk: the composition is a 5-line proof if A and B are correct; low risk.

**Correctness-push framing.** This wave is *not* correctness-push (no new physics tension); it is a **technical-debt-elimination wave** strengthening the substantive guarantee of Wave 3's −3/2 log claim. Successful completion increases the project's axiom-elimination credibility (1 of 2 axioms retired; the remaining `gapped_interface_axiom` has its own roadmap entry).

**Decision gate.** Before starting Sub-task A:
1. Verify Mathlib master (post-Bonn-Levi-Civita-landing) does not already include the Laplace-method lemma — Mathlib evolves; recheck before the wave starts.
2. Open a Zulip thread on `leanprover.zulipchat.com` topic `#mathlib4 > MeasureTheory.Asymptotic.LaplaceMethod` to gauge Mathlib analysis-team interest before committing engineering time.

---

## Track D: Witten Positive Mass (6a.6)

### Wave 6 — `PositiveMassTheorem.lean` [Pipeline: Stages 1–12]

**Goal:** Classical Schoen-Yau / Witten positive mass theorem formalized via Witten's spinor proof (uses Dirac spinors natively — well-matched to the ADW fermion substrate).

**Prerequisites:** Wave 1 (`LinearizedEFE.lean`). Requires partial 6f.1 (`Curvature.lean`) or inline curvature objects. Requires Phase 6f.3 (`EnergyConditions.lean`) or inline DEC predicate.

**Module structure:**
- `lean/SKEFTHawking/PositiveMassTheorem.lean`
  - Dirac operator on asymptotically flat manifold `D̸ ψ = 0`
  - Lichnerowicz-Weitzenböck formula
  - Witten's integration-by-parts argument: `M_ADM ≥ 0` under DEC
  - **Correctness-push theorem:** `positive_mass_iff_ADW_T_μν_satisfies_DEC` — biconditional tying positive mass to DEC satisfaction of ADW emergent stress-energy. If ADW violates DEC in some regime, positive mass fails there — that regime becomes a study target.
- Target ~18–24 theorems.

**Python side:**
- `src/positive_mass/` new subpackage
  - `adm_mass_computation.py` — ADM mass numerical
  - `dec_checker.py` — DEC predicate numerical check on ADW stress-energy

**Bridges:**
- Depends on Wave 1; partial 6f.1, 6f.3
- Existing Dirac-spinor infrastructure: `PauliMatrices`, `BdGHamiltonian`, `FermionBag4D`
- Uses `Uqsl2Hopf` only indirectly (Dirac-operator type classes)
- Feeds 6e.4 nonlinear EFE stress-energy classification

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_positive_mass.py`
- Paper `papers/paper28_positive_mass/paper_draft.tex` OR joint formalization note (user decision)
- Possible Mathlib PR if Lichnerowicz-Weitzenböck not already present
- Inventory update: +18–24 theorems, +1 Lean module, +1 Python subpackage, +1 paper/note

**Estimated LOE:** 10–15 person-months
**Risk:** High. Heaviest classical-GR wave in 6a. Witten's proof requires spinor bundle / covariant-derivative infrastructure that may not be in Mathlib. Budget dependencies on Phase 6f carefully.

---

## Decision Gates

**Gate A.1 — after Wave 1 (`LinearizedEFE`) ships:** Is `G_N^emerg` sign correct and within 2 orders of magnitude of observed `G_N`? YES → all subsequent 6a waves proceed at full scope. NO (wrong sign) → ADW identification falsified at linearized order; 6a.4 scope is narrowed, 6a.5 and 6a.6 continue as formal exercises; Phase 6e reassessed. NO (right sign, wrong magnitude) → proceed but document parameter-fit freedom in every downstream wave.

**Gate A.2 — after Wave 3 (`BHEntropyMicroscopic`) ships:** Does MTC counting reproduce 1/4 (within stated tolerance)? YES → 6c.4 (QEC-holography) and 6c.5 (RT/CH) proceed at full scope. NO → log-correction prediction becomes the 6a.3 deliverable; 6c.4/6c.5 reassessed.

**Gate A.3 — before Wave 6 (`PositiveMassTheorem`) begins:** Is Phase 6f.1 (`Curvature.lean`) + 6f.3 (`EnergyConditions.lean`) at least partially available? If NO, Wave 6 carries the needed objects inline but documents the Mathlib-PR candidates explicitly.

---

## Dependencies

```
6a.1 (LinearizedEFE) → 6a.4 (FLRWDynamics)
6a.1 → 6a.5 (BHThermodynamicsFourLaws)
6a.1 → 6a.6 (PositiveMassTheorem)

6a.2 (GravitationalWaves) — independent; parallel with 6a.1

6a.3 (BHEntropyMicroscopic) — independent; parallel with 6a.1, 6a.2
6a.3 → 6a.5

6a.6 — depends on 6f.1, 6f.3 (at least partial) in addition to 6a.1

6a.7 (axiom elimination) — depends on 6a.3 (consumes its `gaussianSaddleAsymptotic` axiom)
```

---

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6a.1 | `LinearizedEFE.lean` + PRD paper + `G_N^emerg` | 3–5 | None | **TIER 0 — foundational** |
| 6a.2 | `GravitationalWaves.lean` + PRD paper + LIGO check | 2–4 | None; parallel with 6a.1 | **TIER 1** |
| 6a.3 | `BHEntropyMicroscopic.lean` + Annals paper + MTC spectrum | 4–6 | None; parallel with 6a.1/6a.2 | **TIER 1** |
| 6a.4 | `FLRWDynamics.lean` + short paper | 3–5 | 6a.1 | **TIER 1** |
| 6a.5 | `BHThermodynamicsFourLaws.lean` + paper | 5–10 | 6a.1, 6a.3 | **TIER 2** |
| 6a.6 | `PositiveMassTheorem.lean` + paper/note | 10–15 | 6a.1; partial 6f.1, 6f.3 | **TIER 2** |
| 6a.7 | `LaplaceMethodAsymptotic.lean` + Mathlib PR (axiom elimination) | 1–3 | 6a.3 (consumes its axiom) | **TIER 3 — debt** |

**Total Phase 6a LOE:** 28–48 person-months (27–45 baseline + 1–3 for 6a.7 axiom-elimination). Maximal parallelism (1/2/3 parallel → 4 after 1 → 5 after 1+3 → 6 after 1+6f → 7 after 3): wall-clock 15–24 months minimum.

**Deliverables cumulative:**
- 7 new Lean modules (`LinearizedEFE`, `GravitationalWaves`, `BHEntropyMicroscopic`, `FLRWDynamics`, `BHThermodynamicsFourLaws`, `PositiveMassTheorem`, `LaplaceMethodAsymptotic`)
- 4 new Python subpackages (`src/emergent_gravity/`, `src/gravitational_waves/`, `src/bh_entropy/`, `src/positive_mass/`) + `src/bh_thermodynamics/` extension
- 6 papers (Papers 23–28 reserved); 6a.7 has no new paper (axiom-elimination is inventory-level work, optionally folded into a paper26 v2 or a dedicated short note)
- 1 Mathlib PR (`MeasureTheory.Asymptotic.LaplaceMethod`)
- ~84–110 new theorems; zero sorry target; **−1 axiom target** (eliminate `gaussianSaddleAsymptotic`, leaving only `gapped_interface_axiom`)

---

## Open Questions

**O.1 — RESOLVED 2026-04-25.** Second-sound-graviton identification is not derived as a propagating DOF per Phase 5y H1. Wave 2 shipped in "use-as-identified" mode with explicit caveat theorem `second_sound_graviton_not_derived_DOF`. The natural-range falsification result is the load-bearing finding: Wave 2 *negatively* resolves the identification at leading order, opening Phase 6e (full nonlinear emergent action) or a Phase 5y H1 follow-up wave to provide a derived-DOF χ_vest = 1 mechanism.

**O.2 — RESOLVED 2026-04-26.** MTC horizon BC for 6a.3 ships in Outcome-3 tracked-hypothesis mode (`H_HorizonBoundaryCondition` Lean Prop bundle with five falsifier theorems) + Outcome-2 SU(2)_k sub-corollary (Kaul-Majumdar -3/2 closed form under `gaussianSaddleAsymptotic` axiom + Immirzi γ tuning). Per the deep-research return verdict: no published derivation pins a specific MTC at a 4D BH horizon in an ADW substrate, so the choice is a research-level conjecture flagged in the module + paper. The Walker-Wang anomaly-inflow conjecture (Z₂ time-reversal bulk → boundary chiral c_- mod 8) is the natural derivation path for future work.

**O.3 — RESOLVED 2026-04-26 (rewrite).** 6a.5 regime separation framing: the genuine partition is **sign-of-`dT_H/dt` under Hawking evaporation**, not sign-of-`dT_H/dM`. Above M_c (Schwarzschild regime, Hawking 1975): `dT/dt > 0` (heats), finite t-evap. Below M_c (BEC-acoustic / near-extremal-RN regime, Balbinot 2005 PRD 71, 064019): `dT/dt < 0` (cools), infinite t-evap. M_c is project-original ansatz; both regime sides have primary-source grounding. JK 2002 / JV 1998 (³He-A moving wall) is explicitly NOT the cooling-regime anchor — Balbinot's own paper documents the contrast.

**O.4** — 6a.6 publication venue: standalone PRD paper, or joint formalization note with Mathlib community if a Lichnerowicz-Weitzenböck PR lands?

---

## What Success Looks Like

**Per wave:**
- 6a.1: `G_N^emerg` closed form, correct sign, testable against observed `G_N`
- 6a.2: `c_GW` computation compared to GW170817 bound; Phase 5y H1 caveat documented
- 6a.3: `S = A/4G` reproduced from MTC counting (or log-correction prediction if coefficient mismatches)
- 6a.4: Friedmann equations as ODE reduction of 6a.1
- 6a.5: Four laws in both regimes (Schwarzschild-limit and ADW-extremality-limit)
- 6a.6: Positive-mass via Witten spinor proof under DEC on emergent `T_μν`

**Cumulative:**
- 6 new Lean modules, 4+1 Python subpackages, 6 papers
- Correctness-push anchors: `G_N^emerg` sign (6a.1), `c_GW` vs GW170817 (6a.2), BH-entropy coefficient (6a.3), DESI-compatibility (6a.4), regime-separation (6a.5), DEC-satisfaction of `T_μν^emerg` (6a.6)

---

## Cross-References

**Prior phases this extends:**
- Phase 3 (ADW mean-field) — `ADWMechanism.lean`, `src/adw/`
- Phase 4 Wave 2 (Vestigial gravity) — `VestigialGravity.lean`, `VestigialSusceptibility.lean`
- Phase 5d (TetradGapEquation, FermionBag4D) — `FermionBag4D.lean`
- Phase 5y closure — `GibbsDuhemTheorem.lean`, `QTheoryNoGoTheorem.lean`, `VestigialEOS.lean` (structural context for 6a.4, 6a.2)
- Phase 5c/5e (MTC stack) — `SphericalCategory`, `FibonacciMTC`, `IsingBraiding`, `S3CenterAnyons`, `SU2kFusion`, `SU3kFusion`, `Uqsl2Hopf`, `DrinfeldDouble`
- Phase 5u (Stimulated Hawking) — `StimulatedHawking.lean`
- Paper 5 (KerrSchild) — `KerrSchild.lean`

**Feeds downstream phases:**
- Phase 6b.2 (cosmological perturbation theory) — depends on 6a.1, 6a.4
- Phase 6b.3 (vestigial inflation) — depends on 6a.1
- Phase 6c.1 (strong-CP ↔ DE bridge) — uses `G_N^emerg` from 6a.1
- Phase 6c.4 (QEC ↔ holography), 6c.5 (RT/CH) — build on 6a.3
- Phase 6e — 6a.1 calibrates nonlinear $a_2$ coefficient
- Phase 6f.1/6f.3 — feeds 6a.6; 6a.1 may contribute Mathlib PRs
- Phase 6g.4 (area theorem) — classical version complementing 6a.5 thermodynamic 2nd law

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §4

**Correctness-push highlights from strategy doc §12:**
- 6a.1: `G_N^emerg` sign + magnitude
- 6a.2: `c_GW` vs GW170817 at $10^{-15}$
- 6a.3: BH entropy coefficient 1/4
- 6a.5: regime separation Schwarzschild vs ADW-extremality
- 6a.6: DEC on ADW `T_μν^emerg`

---

*Phase 6a roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Six waves, six papers, five correctness-push highlights. Tractable gravitational dynamics: linearized, cosmological, BH structure, four laws, positive mass. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 27–45. Consolidation-half anchor of the post-SK-EFT program.*
