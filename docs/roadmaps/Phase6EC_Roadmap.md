# Phase 6EC — Kernel-Verified Electrothermal Detector Physics: Bias Stability, Loop Gain, and Bolometric Noise Floors

**Status: PLANNED (authorized 2026-07-27).** Third phase of the `6E*` series (*verified device-physics metrology*). Consumes 6EB (NEP/ENBW layer); consumed by 6EE (composite ceilings). See `Phase6EA_Roadmap.md` for the series framing.

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

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Electrothermal/ETFModel.lean` builds 0-sorry, kernel-pure, with:
- [ ] `etfModel` structure (C, G, bias-point R, V, signed `dRdT`, all positivity/sign hypotheses explicit and minimal) + `loopGain_def : ℒ = V^2 · dRdT / (R^2 · G)` and `effectiveConductance_def : G_eff = G·(1+ℒ)`;
- [ ] `biasPower_linearization : d(V²/R(T))/dT = −V²·dRdT/R²` (the sign-carrying step, from `deriv`);
- [ ] `etf_perturbation_solves : δT(t) = δT₀ · exp (−t/τ_eff)` solves the linearized heat balance, with `τ_eff = C/G_eff` (`HasDerivAt` verification, explicit solution);
- [ ] `etf_stable_iff : (perturbations decay) ↔ ℒ > −1` — the dichotomy as an iff (decay ↔ `G_eff > 0`), including the divergence direction for `ℒ < −1`;
- [ ] `etf_timeConstant_speedup : ℒ > 0 → τ_eff < τ` and the slowdown dual;
- [ ] `norm_num` witnesses on both sides of the dichotomy boundary;
- [ ] preemptive-strengthening + post-wave audit.

## Wave 2 — Responsivity with ETF correction

**Goal.** Small-signal power-to-current responsivity closed forms, with and without the `(1+ℒ)` correction, and the correction-factor theorem relating them. Verdict: reachable — algebra over Wave 1.

**Why.** The uncorrected responsivity overstates response by exactly `(1+ℒ)` for `ℒ > 0` — a factor that silently corrupts NEP budgets; the correction theorem is the citable repair.

**Bricks.** Wave 1; 6EB `nep_def` + `sigma_eq_responsivity_nep_sqrt_enbw`.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Electrothermal/ETFResponsivity.lean` builds 0-sorry, kernel-pure, with:
- [ ] `dc_responsivity_bare : |dI/dP| = V·|dRdT|/(R²·G)` (no-feedback form) and `dc_responsivity_etf : ... /(R²·G·(1+ℒ))` (ETF-consistent form), both signed at the definition level with the magnitude corollaries separate;
- [ ] `responsivity_etf_correction : R_bare = (1+ℒ) · R_etf` (the correction-factor identity) + monotonicity corollaries;
- [ ] `responsivity_frequency_rolloff` — the single-pole `1/√(1+(ωτ_eff)²)` magnitude factor (algebraic, no Fourier machinery: stated for the sinusoidal steady-state solution verified by `HasDerivAt`, UNKNOWN-1);
- [ ] input-referred NEP transfer through both responsivity forms via 6EB algebra, with a `norm_num` witness quantifying the budget error from using the bare form at a stated `ℒ`;
- [ ] preemptive-strengthening + post-wave audit.

## Wave 3 — Bolometric noise floors

**Goal.** Phonon (thermal-fluctuation) NEP floor `NEP_ph² = 4·k_B·T²·G`-shape and Johnson-noise NEP through the responsivity chain; the composed bolometer noise floor. Verdict: reachable — composition algebra citing existing FDT floors; the phonon-NEP statement's honesty (equilibrium hypothesis explicit) is the care point.

**Why.** Completes the layer 6EE composes into detector-side ceilings: with Wave 2 + 6EB, "no thermal detector of this linearized class beats this NEP floor at a stated bias point" becomes a theorem.

**Bricks.** `FDTNoiseFloor` (Johnson–Nyquist), `QuantumFDTFloor` (quantum floor seam); Waves 1–2; 6EB `nep_quadrature_add`.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Electrothermal/BolometricFloors.lean` builds 0-sorry, kernel-pure, with:
- [ ] `phonon_nep_sq_def` + `phonon_nep_floor` — thermal-fluctuation NEP with the equilibrium/white-approximation hypotheses as explicit `Prop` parameters (never absorbed);
- [ ] `johnson_nep_via_responsivity` — Johnson current noise referred to input power through the ETF-corrected responsivity (citing `FDTNoiseFloor`, not re-deriving it);
- [ ] `bolometer_nep_floor : NEP_total² ≥ NEP_ph² + NEP_J²` (quadrature composition, with independence hypothesis explicit) and its monotone consequences;
- [ ] `bolometer_error_floor` — the capstone seam: composed NEP + 6EB matched-filter budget + 6EA Gaussian floor ⇒ a concrete average-error floor shape for any threshold readout of this detector class;
- [ ] root-module import + Inventory/counts refresh;
- [ ] preemptive-strengthening + post-wave audit.

---

## Sequencing & parallelism

Wave 1 → Wave 2 → Wave 3 on the critical path. Wave 1 depends only on the `DampedTwoLevel` pattern — **it can run in parallel with all of 6EB** (its 6EB consumption starts at Wave 2). The `Electrothermal/` directory is new; no cross-phase contention except the root-module import (Wave 3, single-writer).

## Phase Definition of Done

- [ ] `lake build` + ExtractDeps clean; zero sorry; kernel-pure; no new axioms.
- [ ] `validate.py` green; Inventory + Index refreshed.
- [ ] Adversarial statement audit logged (special attention: no theorem silently assumes `ℒ > 0`, and no magnitude-only statement hides a sign inversion).
- [ ] Roadmap status updated with dated shipped-declarations list.

## Open UNKNOWNs

- **UNKNOWN-1:** the frequency-rolloff statement form — sinusoidal steady-state via explicit particular solution (`HasDerivAt`, no Fourier) vs. deferring rolloff entirely to a later phase; decide at Stage 2 by whether 6EE consumes it (if 6EE only needs DC forms, defer — Pareto).
- **UNKNOWN-2:** phonon-NEP prefactor generality (the `4k_BT²G` white form vs. the `γ`-factor gradient correction) — ship the white form with the hypothesis explicit; note the correction as a tagged extension, don't block on it.
- **UNKNOWN-3:** whether the bias circuit generalization (current bias / Thévenin) is worth a wave-4 — default no (voltage bias covers the stated class; generalize on demand).
