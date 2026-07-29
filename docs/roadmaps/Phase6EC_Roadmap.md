# Phase 6EC — Kernel-Verified Electrothermal Detector Physics: Bias Stability, Loop Gain, and Bolometric Noise Floors

**Status: COMPLETE — all three waves SHIPPED (authorized 2026-07-27; Waves 2 + 3 landed and phase closed 2026-07-29).** Third phase of the `6E*` series (*verified device-physics metrology*). Consumes 6EB (NEP/ENBW layer, **COMPLETE 2026-07-29**); consumed by 6EE (composite ceilings). See `Phase6EA_Roadmap.md` for the series framing.

> **Status correction 2026-07-29.** This header read `PLANNED` and Wave 1's AC boxes were unchecked, but Wave 1 had in fact shipped — verified against the tree, not the checkboxes: `lean/SKEFTHawking/Electrothermal/ETFModel.lean`, **52 declarations**, zero sorry / zero axiom / zero `native_decide` / zero `maxHeartbeats`, root-imported in `SKEFTHawking.lean`. (The only textual matches for the banned constructs are in the header docstring *asserting their absence* — the grep-false-positive class; purity was re-checked with `#print axioms`.) The AC list below is annotated with the shipped names. **Only Waves 2–3 remain.**
>
> Wave 1 shipped **more** than its AC asked: `solution_unique` (integrating-factor uniqueness of the heat-balance solution, not merely one explicit solution), the marginal case `etf_marginal_of_loopGain_eq_neg_one`, the Irwin–Hilton convention bridge `loopGain_eq_irwinHilton` as a *theorem* rather than a comment, and three **refutations** of magnitude-only stability criteria (`magnitudeOnly_criterion_unsound`, `absLoopGain_criterion_unsound`, `effectiveTimeConstant_neg_of_unstable`) — Guardrail 2 enforced by kernel, not prose.

**Thesis.** Thermal detectors (bolometers, calorimeters, TES-class sensors) are governed by a small linearized electrothermal model — heat balance `C·dT/dt = P_bias(T) + P_signal − G·ΔT`, electrothermal feedback (ETF) loop gain `ℒ = P_J·α/(G·T)` (equivalently `V²(dR/dT)/(R²G)` under voltage bias), stability iff `ℒ > −1`, effective time constant `τ_eff = τ/(1+ℒ)`, and the phonon/Johnson noise floors — that the instrument literature (Irwin–Hilton and its citation graph) treats as settled algebra. None of it is kernel-checked anywhere (repo sweep 2026-07-27: zero electrothermal/bolometry content in any prover-adjacent corpus we track). This phase formalizes the linearized model exactly: the ODE facts, the stability dichotomy, the responsivity closed forms with their ETF corrections, and the noise-floor composition through the 6EB layer.

Clean whitespace: no kernel-checked ETF stability criterion, loop-gain-corrected responsivity, or bolometric NEP-floor family exists in any prover.

> **⚠️ GUARDRAIL — the linearized model is the object; say so everywhere.** Every theorem is about the *stated linear model* (small-signal expansion at a bias point). Physical devices realize it only within a validity neighborhood; that identification is the consumer's declared hypothesis. No theorem may read as a claim about a physical device, and large-signal/nonlinear behavior is out of scope (a candidate later phase, not this one).

> **⚠️ GUARDRAIL — signs are physics; keep them signed.** `dR/dT` sign conventions carry the entire stability physics (positive-α under voltage bias = stabilizing negative feedback; negative-α = destabilizing). No magnitude-only shortcuts: every statement uses signed quantities, and the stability dichotomy must be an iff, not a sufficient condition.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop.)*
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` → `SK_EFT_Hawking_Inventory_Index.md` → `Phase6EA_Roadmap.md` (series head) → `Phase6EB_Roadmap.md` (consumed layer).
> 2. **Read this roadmap end-to-end**; Bricks are exact (verified 2026-07-27).
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`), per the 6EA instructions.
> 4. **Pipeline disciplines (hard gates):** (a) **bundle target D12** (authorized 2026-07-27; Invariant #14 applies — bundle-aware content from inception; scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`); (b) preemptive-strengthening + post-wave audit; (c) kernel-purity, zero sorry, no new axioms without sign-off (#15); (d) no `maxHeartbeats` (#10).
> 5. **This phase:** the ODE layer follows the `OpenSystems/DampedTwoLevel.lean` pattern (explicit solution + `deriv`-level verification, no ODE-existence machinery); numeric floors follow `NumericalBounds` rational enclosures.

**Standing invariants:** kernel-pure; no new axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening; never push. **Two-layer honesty** per the guardrail: linearized-model mathematics Lean-verified; device identifications live with consumers. Wave sizing ≈ one `/goal`.

**Substrate (verified 2026-07-27).**
- **Reuse:** `SKEFTHawking.OpenSystems.DampedTwoLevel` (`dampedTwoLevel_population_solves_rate`, `_decay_envelope`) — the explicit-ODE-solution formalization pattern this phase's thermal ODE copies; `SKEFTHawking.QuantumNetwork.FDTNoiseFloor`/`QuantumFDTFloor` (Johnson–Nyquist + quantum floors to compose); 6EB `nep_quadrature_add`, `sigma_eq_responsivity_nep_sqrt_enbw`, `enbw_mul_window_ge_half`; `NumericalBounds.expNeg_enclosure`.
- **Absent → build:** everything electrothermal (sweep found zero: no heat-balance model, no ETF, no responsivity, no phonon-NEP).
- **Mathlib:** `deriv`/`HasDerivAt` calculus; nothing exotic required.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology* (**authorized 2026-07-27**; `PAPER_STRATEGY.md` §2.2). Scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`.

---

## Wave 1 — Linearized electrothermal model & the stability dichotomy

**Goal.** The bias-point linearization as a definition set; loop gain; the stability iff; time-constant modification. Verdict: reachable — first-order linear ODE with explicit solutions, `DampedTwoLevel`-pattern.

**Why.** The stability dichotomy is the phase's keystone screen (an operating point with `ℒ ≤ −1` is unphysical-as-modeled) and every later formula carries `(1+ℒ)` factors.

**Bricks.** `DampedTwoLevel.lean` (pattern); Mathlib `HasDerivAt`.

**Done (AC / `/goal` condition).** ✅ **SHIPPED** — verified against the tree 2026-07-29 (52 declarations, 0 sorry / 0 axiom / 0 `native_decide` / 0 `maxHeartbeats`, root-imported).
- [x] `lean/SKEFTHawking/Electrothermal/ETFModel.lean` builds 0-sorry, kernel-pure, with:
- [x] **shipped as `structure ETFModel` + `loopGain` / `effectiveConductance` / `timeConstant` / `effectiveTimeConstant` / `joulePower` / `alphaTCR` defs.** Positivity is deliberately *not* a structure field — `0 < C/G/R` sit in each theorem's binder list, which keeps hypotheses minimal *and* makes the degenerate branches statable, so non-droppability is witnessed (`loopGain_R_hypothesis_load_bearing`, `stability_G_hypothesis_load_bearing`) rather than asserted. Degenerate branches disclosed: `loopGain_of_R_eq_zero`, `loopGain_of_G_eq_zero` `etfModel` structure … + `loopGain_def` and `effectiveConductance_def`;
- [x] **shipped as `biasPower_hasDerivAt` (the `HasDerivAt` form) + `biasPower_linearization` (the `deriv` form), over an *arbitrary* differentiable `R`-vs-`T` curve rather than a chosen functional form**, plus `linearizedSlope_eq_neg_effectiveConductance`, which *calls* it — so `ℒ`'s grouping is justified by computation, not by naming `biasPower_linearization : d(V²/R(T))/dT = −V²·dRdT/R²`;
- [x] **shipped as `perturbation` + `perturbation_eq_exp_neg_div_effectiveTimeConstant` + `etf_perturbation_solves` / `etf_perturbation_solves_linearized`, and strengthened with `solution_unique`** (integrating-factor uniqueness — no Picard–Lindelöf) `etf_perturbation_solves`;
- [x] `etf_stable_iff` — the dichotomy as an iff, with `PerturbationsDecay` quantifying over *every* trajectory solving the ODE (a `Tendsto … (𝓝 0)` limit) rather than aliasing `G_eff > 0`; both directions shipped (`tendsto_perturbation_of_pos`, `not_perturbationsDecay_of_effectiveConductance_nonpos`), plus `etf_diverges_of_loopGain_lt_neg_one` and the marginal case `etf_marginal_of_loopGain_eq_neg_one`;
- [x] `etf_timeConstant_speedup` + `etf_timeConstant_slowdown` (+ `effectiveTimeConstant_eq_div`, `effectiveTimeConstant_neg_of_unstable`, `unstable_imp_dRdT_neg`);
- [x] `norm_num` witnesses on both sides of the boundary — `stableWitness` / `marginalWitness` / `unstableWitness` / `speedupWitness` with their loop gains, decay/non-decay verdicts, `marginalWitness_frozen`, and `stableWitness_decay_enclosure`;
- [x] preemptive-strengthening + post-wave audit — residue: three **refutations** of magnitude-only stability criteria (`magnitudeOnly_criterion_unsound`, `absLoopGain_criterion_unsound`, `effectiveTimeConstant_neg_of_unstable`), i.e. Guardrail 2 enforced by kernel rather than prose.

## Wave 2 — Responsivity with ETF correction

**Goal.** Small-signal power-to-current responsivity closed forms, with and without the `(1+ℒ)` correction, and the correction-factor theorem relating them. Verdict: reachable — algebra over Wave 1.

**Why.** The uncorrected responsivity overstates response by exactly `(1+ℒ)` for `ℒ > 0` — a factor that silently corrupts NEP budgets; the correction theorem is the citable repair.

**Bricks.** Wave 1; 6EB `nep_def` + `sigma_eq_responsivity_nep_sqrt_enbw`.

**Done (AC / `/goal` condition).** ✅ **SHIPPED 2026-07-29** — 26 declarations, 0 sorry / 0 axiom / 0 `native_decide` / 0 `maxHeartbeats`, kernel-pure (13 headline theorems checked individually with `#print axioms`), root-imported.
- [x] `lean/SKEFTHawking/Electrothermal/ETFResponsivity.lean` builds 0-sorry, kernel-pure, with:
- [x] **shipped as the signed defs `currentTempSlope` / `responsivityBare` / `responsivityETF`, each *derived* rather than posited** — `hasDerivAt_current` gets `dI/dT = −V·(dR/dT)/R²` from `HasDerivAt.div` over an arbitrary differentiable `R`-vs-`T` curve (minus sign derived, mirroring Wave 1's `biasPower_hasDerivAt`), and `hasDerivAt_responsivityETF` / `hasDerivAt_responsivityBare` obtain both responsivities as genuine **chain-rule** derivatives of current-vs-absorbed-power (`HasDerivAt.comp`), differing only in which temperature-per-power map is composed. Magnitude corollaries are separate (`abs_responsivityETF_lt_abs_responsivityBare`) `dc_responsivity_bare` and `dc_responsivity_etf`;
- [x] `responsivity_etf_correction : R_bare = (1+ℒ)·R_etf` — **and the audit found the unrestricted form FALSE.** At the marginal point `ℒ = −1` we have `G_eff = 0`, so `R_etf` collapses to Lean's junk `0` and the RHS is `0` while the LHS is not; the shipped statement carries `1 + ℒ ≠ 0` and `marginalWitness_correction_fails` witnesses the failure at Wave 1's published `marginalWitness` (LHS `1/2`, RHS `0`). Also shipped: `responsivity_opposite_sign_of_unstable` (on the unstable branch `ℒ < −1` the two responsivities have **opposite signs**, not merely different magnitudes);
- [x] `responsivity_frequency_rolloff` — the single-pole `1/√(1+(ωτ_eff)²)` factor, **built rather than deferred** (see UNKNOWN-1). Route as prescribed: explicit sinusoidal steady state `thermalResponse`, verified by `thermalResponse_solves` (`HasDerivAt`, no Fourier machinery), amplitude `thermalResponseAmplitude` with the single-pole closed form `thermalResponseAmplitude_eq_singlePole` (in `τ_eff`, **not** `τ` — feedback moves the pole), the DC normalization `thermalResponseAmplitude_zero`, and `thermalResponseAmplitude_strictAnti` so the factor provably *bites* rather than being compatible with a flat response;
- [x] input-referred NEP transfer via 6EB — `nep_bare_understates_by_one_plus_loopGain` **calls** `Detection.nepOfOutput`, so the seam is a computation; the direction is the dangerous one (an overstated responsivity *understates* NEP, making a detector look better than it is). Rational witness at Wave 1's already-published `speedupWitness` (`ℒ = 3`): `speedupWitness_bare_overstates_fourfold` and `speedupWitness_nep_quarter` — the bare form reports a noise floor **4× too low**, a 300 % sensitivity overclaim, with no floating point anywhere;
- [x] preemptive-strengthening + post-wave audit — residue: the false-without-`1+ℒ≠0` correction identity (above, caught by Lean not by review), a dead `0 ≤ P₀` binder dropped from `responsivity_frequency_rolloff`, and `responsivity_magnitudeOnly_loses_stability_information` — the Wave-2 analogue of Wave 1's `magnitudeOnly_criterion_unsound`: two bias points satisfy the *identical* magnitude relation `|R_bare| = |1+ℒ|·|R_etf|` while sitting on opposite sides of the stability dichotomy, so a magnitude-corrected budget silently accepts a divergent operating point.

## Wave 3 — Bolometric noise floors

**Goal.** Phonon (thermal-fluctuation) NEP floor `NEP_ph² = 4·k_B·T²·G`-shape and Johnson-noise NEP through the responsivity chain; the composed bolometer noise floor. Verdict: reachable — composition algebra citing existing FDT floors; the phonon-NEP statement's honesty (equilibrium hypothesis explicit) is the care point.

**Why.** Completes the layer 6EE composes into detector-side ceilings: with Wave 2 + 6EB, "no thermal detector of this linearized class beats this NEP floor at a stated bias point" becomes a theorem.

**Bricks.** `FDTNoiseFloor` (Johnson–Nyquist), `QuantumFDTFloor` (quantum floor seam); Waves 1–2; 6EB `nep_quadrature_add`.

**Done (AC / `/goal` condition).** ✅ **SHIPPED 2026-07-29** — 19 extracted declarations, 0 sorry / 0 axiom / 0 `native_decide` / 0 `maxHeartbeats`, kernel-pure (8 headline theorems checked individually), root-imported.
- [x] `lean/SKEFTHawking/Electrothermal/BolometricFloors.lean` builds 0-sorry, kernel-pure, with:
- [x] **shipped as `phononPSD` / `phononNEP` (via 6EB's `nepOfPSD`, not a fresh √) + `phononNEP_sq` (the spectral round trip, which needs non-negativity — not a definitional unfolding) + `IsThermalFluctuationLimited`** (the equilibrium/white hypothesis as a `Prop` parameter in the 6EB-Wave-1 style, never absorbed) `phonon_nep_sq_def` + `phonon_nep_floor`. The `4·k_B·T²·G` prefactor is **cited, not asserted**: `phonon_psd_eq_johnsonNyquist_scaled` proves it equals `GrapheneNoiseFormula.johnsonNyquistPSD (k_B·T) G · T`, i.e. the repo-canonical FDT PSD at the *thermal* conductance. Plus `phononPSD_pos` and `phononPSD_strictMono_conductance` (better isolation is strictly quieter — a falsifiable screen);
- [x] **shipped as `johnsonCurrentPSD` + `johnsonNEP` (referred through the ETF-corrected responsivity, never the bare one) + `johnsonNEP_bare_understates_by_one_plus_loopGain`** `johnson_nep_via_responsivity`. The last is the substantive form: because NEP *divides* by responsivity, Wave 2's `(1+ℒ)` overclaim reappears as an **understatement of a noise channel** by `|1+ℒ|` — a factor of 4 at the published `ℒ = 3` bias point, in a *noise* budget. It consumes `responsivity_etf_correction`, so the cross-wave link is a computation;
- [x] `bolometer_nep_floor` — **quadrature is 6EB's `nep_quadrature_two`, consumed with `IsUncorrelatedAt` intact and not restated**; what this wave adds is the *physical* entry point (the phonon channel enters as `IsThermalFluctuationLimited`, and the whiteness precondition 6EB needs is discharged internally by `isWhite_of_thermalFluctuationLimited`), so a consumer states physics rather than spectral algebra. **The roadmap's literal "monotone consequences" were declined** — `x² ≤ x² + y²` is true of any reals and carries no bolometric content; shipped instead is `phononLimited_iff_psd_lt`, the phonon-limited regime as an **iff** (a decision procedure on a budget, the analogue of 6EB's `shotLimited_iff_psd_lt`);
- [x] `bolometer_error_floor` — the capstone: 6EC's composed PSD → 6EB's `error_floor_from_budget` → 6EA's `avgError_ge_gaussianQ_sharp`. Positivity of the composed noise scale is **discharged from the physical hypotheses** (`0 < kB`, `0 < T`, `0 < G`) via `bolometer_psd_pos` rather than taken as an abstract binder, so the capstone composes this wave's physics instead of forwarding;
- [x] root-module import + Inventory/counts refresh;
- [x] preemptive-strengthening + post-wave audit — residue: two pure forwarders caught and given content (see the two bullets above), the two trivial orderings replaced by the `iff` screen, and a dead `responsivityETF ≠ 0` binder dropped from `phononLimited_iff_psd_lt` (both sides collapse identically at `R_etf = 0`).

---

## Sequencing & parallelism

Wave 1 → Wave 2 → Wave 3 on the critical path. Wave 1 depends only on the `DampedTwoLevel` pattern — **it can run in parallel with all of 6EB** (its 6EB consumption starts at Wave 2). The `Electrothermal/` directory is new; no cross-phase contention except the root-module import (Wave 3, single-writer).

## Phase Definition of Done

- [x] `lake build` + ExtractDeps clean; zero sorry; kernel-pure; no new axioms. *(2026-07-29 — `Build completed successfully (10788 jobs)`; project-wide axioms 0, sorry 0.)*
- [x] `validate.py` green; Inventory + Index refreshed.
- [x] Adversarial statement audit logged. **Both special attentions discharged:** (a) *no theorem silently assumes `ℒ > 0`* — `responsivity_etf_correction` needs only `1 + ℒ ≠ 0` and holds on the unstable branch, where `responsivity_opposite_sign_of_unstable` shows the two responsivities *invert*; the `ℒ > 0` case appears only where it is the claim (`abs_responsivityETF_lt_abs_responsivityBare`). (b) *no magnitude-only statement hides a sign inversion* — `responsivity_magnitudeOnly_loses_stability_information` proves two bias points satisfy the identical magnitude relation `|R_bare| = |1+ℒ|·|R_etf|` on **opposite sides** of the dichotomy, the Wave-2 analogue of Wave 1's `magnitudeOnly_criterion_unsound`. Wave-3 residue: two pure forwarders caught and given content; two vacuous orderings replaced by an `iff` screen.
- [x] Roadmap status updated with dated shipped-declarations list. *(Below, 2026-07-29.)*

## Shipped declarations (dated)

| wave | module | decls | date |
|---|---|---|---|
| W1 | `lean/SKEFTHawking/Electrothermal/ETFModel.lean` | 52 | pre-existing, status corrected 2026-07-29 |
| W2 | `lean/SKEFTHawking/Electrothermal/ETFResponsivity.lean` | 27 | 2026-07-29 |
| W3 | `lean/SKEFTHawking/Electrothermal/BolometricFloors.lean` | 19 | 2026-07-29 |

Counts are extracted-declaration counts from `lean_deps.json` (the same convention as the 6EB table).

## Open UNKNOWNs

- **UNKNOWN-1 — RESOLVED 2026-07-29 (Wave-2 Stage 2), and resolved *past* the Pareto floor.** The prescribed test was "decide by whether 6EE consumes it". **Evidence: it does not.** `Phase6EE_Roadmap.md` Wave 3's Bricks list is entirely DC/static (`avgAssignmentError_rational_floor`, `readoutDecayProb_enclosure`, `thermalExcitedPop`, 6EA `poisson_avgError_floor` + Gaussian floors, 6EB `error_floor_from_budget`, 6EC `bolometer_error_floor`, `GeneralizedAmpDamp`, `CoherenceFidelity`), and the whole 6EE roadmap contains **zero** occurrences of frequency / ω / rolloff / bandwidth. So the Pareto branch *permits* deferral. Deferral was nonetheless **declined**: permission is not a requirement, and the rolloff is tractable by the prescribed route (sinusoidal steady state verified by `HasDerivAt`, no Fourier machinery). Wave 2 therefore builds the DC core first — the part 6EE actually consumes, so delivery of the consumed content is never at risk — and ships the rolloff on top. Rationale: correctness/completeness over expediency; a deferred single-pole factor would have to be rebuilt by any later consumer that *does* work in the frequency domain.
- **UNKNOWN-2:** phonon-NEP prefactor generality (the `4k_BT²G` white form vs. the `γ`-factor gradient correction) — ship the white form with the hypothesis explicit; note the correction as a tagged extension, don't block on it.
- **UNKNOWN-3:** whether the bias circuit generalization (current bias / Thévenin) is worth a wave-4 — default no (voltage bias covers the stated class; generalize on demand).
