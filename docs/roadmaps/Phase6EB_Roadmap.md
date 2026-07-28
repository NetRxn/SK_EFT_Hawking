# Phase 6EB — Kernel-Verified Filtered-Readout Noise Floors: ENBW, NEP, and Matched-Filter Limits

**Status: PLANNED (authorized 2026-07-27).** Second phase of the `6E*` series (*verified device-physics metrology*). Consumes Phase 6EA (Poisson/Gaussian floors); consumed by 6EC (electrothermal detectors) and 6EE (composite readout ceilings). See `Phase6EA_Roadmap.md` for the series framing.

**Thesis.** Between the statistics of Phase 6EA and any physical detector sits the *signal-processing layer*: a filter of equivalent noise bandwidth (ENBW) integrating for a window `T`, a noise-equivalent-power (NEP) budget referred to a declared plane, and a responsivity chain converting power to the classified variable. This layer has its own exact floors — the matched-boxcar realizability bound `ENBW·T ≥ 1/2` (Cauchy–Schwarz), matched-filter optimality, and the `σ = R·NEP·√ENBW` composition algebra — which are ubiquitously *assumed* in detector literature and never kernel-checked. The public repo's signal layer is nearly empty (verified 2026-07-27: PSD/SNR formulas exist in `GrapheneNoiseFormula`; no filter theory, no NEP algebra, no matched filter). This phase builds it once, exactly.

Clean whitespace: no prover has a kernel-checked ENBW/NEP/matched-filter floor family; the `ENBW·T ≥ 1/2` single-shot realizability bound in particular appears in instrument papers as folklore with no primary formal source.

> **⚠️ GUARDRAIL — conventions are load-bearing; declare once, thread everywhere.** One-sided vs two-sided PSDs and incident- vs absorbed-plane referencing silently change every constant by factors of 2 and η. This phase fixes ONE convention set (one-sided PSD, matching `GrapheneNoiseFormula`; plane transfer via 6EA's thinning algebra) as *definitions*, and every theorem carries its convention through the statement. A theorem that is convention-ambiguous is a defect, not a simplification.

> **⚠️ GUARDRAIL — floors, not filter designs.** Optimality statements (matched filter) are bounds over admissible filter classes with the class stated explicitly. No claim about any physical instrument's implementation.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop.)*
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` → `SK_EFT_Hawking_Inventory_Index.md` → `docs/roadmaps/Phase6EA_Roadmap.md` (series head).
> 2. **Read this roadmap end-to-end** before claiming a wave; Bricks name exact declarations (verified 2026-07-27).
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`), per the 6EA instructions.
> 4. **Pipeline disciplines (hard gates):** (a) **bundle target D12** (authorized 2026-07-27; Invariant #14 applies — bundle-aware content from inception; scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`); (b) preemptive-strengthening before every theorem + post-wave audit; (c) kernel-purity, zero sorry, no new axioms without sign-off (#15); (d) no `maxHeartbeats` (#10).
> 5. **This phase:** integral inequalities live over `MeasureTheory.integral` with explicit integrability hypotheses — prefer interval-supported L² statements (the physical filter class) over maximal generality; the Cauchy–Schwarz brick is Mathlib's `inner_mul_le_norm_mul_norm`/`MeasureTheory.integral_mul_le_Lp` family (resolve exact citation at Stage 2, UNKNOWN-1).

**Standing invariants:** kernel-pure; no new axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening; never push. **Two-layer honesty:** mathematics Lean-verified; the identification of a physical instrument's filter with an admissible `h ∈ L²[0,T]` is the consumer's declared hypothesis. Wave sizing ≈ one `/goal`.

**Substrate (verified 2026-07-27).**
- **Reuse:** `SKEFTHawking.GrapheneNoiseFormula.johnsonNyquistPSD_pos` + `hawkingNoisePSD_pos` + `snr_independent_of_sigma_Q` (the PSD/SNR convention anchor); `SKEFTHawking.QuantumNetwork.FDTNoiseFloor` + `QuantumFDTFloor` (thermal/quantum noise floors to compose against); Phase 6EA Waves 1–3 outputs (`shotPSD_*`, `poisson_thinning`, Gaussian threshold algebra).
- **Absent → build (confirmed by sweep 2026-07-27):** ENBW as a defined functional of a filter; the `ENBW·T ≥ 1/2` floor; matched-filter optimality; NEP definitions + plane-transfer algebra; responsivity chains; `σ = R·NEP·√ENBW` composition.
- **Mathlib:** L² Cauchy–Schwarz / Hölder on finite-measure intervals; `intervalIntegral` machinery.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology* (**authorized 2026-07-27**; `PAPER_STRATEGY.md` §2.2). Scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`.

---

## Wave 1 — ENBW and the matched-boxcar realizability floor

**Goal.** Define ENBW for an interval-supported filter and prove the single-shot floor. Verdict: reachable — the floor is one Cauchy–Schwarz application once the definitions are right; the work is in honest convention-carrying definitions.

**Why.** The floor is the cheapest, most-cited deliverable of the phase: any claimed noise bandwidth below `1/(2T)` in a single-shot window is unphysical — a hand-checkable screen consumed by 6EC and 6EE and citable on its own.

**Bricks.** Mathlib interval-integral Cauchy–Schwarz (exact decl per UNKNOWN-1); `GrapheneNoiseFormula` PSD conventions.

**Done (AC / `/goal` condition).**
- [x] `lean/SKEFTHawking/Detection/FilterFloors.lean` builds 0-sorry, kernel-pure, with:
- [x] **shipped as the `enbw` def + convention-carrying statements (no `rfl` restatement)** `enbw_def` — one-sided ENBW of `h ∈ L²[0,T]`, `ENBW h = (∫ h²) / (2·(∫ h)²)` in the normalized DC-gain convention, with the convention documented in-statement (not only in the docstring);
- [x] **+ `enbw_mul_window_isLeast` (sharpness) and a load-bearing-hypothesis witness** `enbw_mul_window_ge_half : (∫ h ≠ 0) → ENBW h · T ≥ 1/2` — Cauchy–Schwarz, equality characterization included (`enbw_eq_half_iff_boxcar`, a.e.-constant filter);
- [x] `enbw_boxcar : ENBW (boxcar T) = 1/(2T)` — the saturating witness;
- [x] **UNKNOWN-2 → Prop-parameter form `IsWhiteFilteredVariance`** `variance_eq_psd_mul_enbw`-shape bridge: for white noise of one-sided PSD `S₀` through filter `h`, output variance `= S₀ · ENBW h` (the definitional *raison d'être*, stated with the white-noise hypothesis explicit);
- [x] preemptive-strengthening + post-wave audit.

## Wave 2 — NEP algebra and responsivity chains

**Goal.** NEP as input-referred noise density; plane-transfer and responsivity-chain algebra; the `σ = R·NEP·√ENBW` composition. Verdict: reachable — pure algebra over Wave-1 and 6EA-Wave-3 objects.

**Why.** This is the vocabulary every detector budget is written in; formalizing it kills the factor-of-2/η ambiguity class of errors and gives 6EC/6EE their composition bricks.

**Bricks.** Wave 1 (`enbw_def`, `variance_eq_psd_mul_enbw`); 6EA `shotPSD_plane_transfer` + `poisson_thinning`; `GrapheneNoiseFormula.snr_independent_of_sigma_Q` (SNR shape).

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Detection/NEPAlgebra.lean` builds 0-sorry, kernel-pure, with:
- [ ] `nep_def` (input-referred, one-sided, W/√Hz semantics as a declared unit convention) + `nep_incident_absorbed_transfer : NEP_inc = NEP_abs / η` (with `R_inc = η·R_abs` dual);
- [ ] `sigma_eq_responsivity_nep_sqrt_enbw` — the classified-variable noise composition, with hypotheses (whiteness, linearity of the chain) explicit;
- [ ] `nep_quadrature_add` — independent noise sources add in quadrature at a common plane (finite family, stated over variances);
- [ ] `shot_nep_formula : NEP_shot,abs = √(2·E_ph·P_abs)`-shape identity tied to 6EA's shot PSD (one-sided convention);
- [ ] `snr_composition`-shape theorem: end-to-end SNR through the chain, monotone in each budget term — the screen consumed by composite ceilings;
- [ ] preemptive-strengthening + post-wave audit.

## Wave 3 — Matched-filter optimality

**Goal.** Over the admissible class (interval-supported L², linear, single-shot), the matched filter maximizes SNR; corollaries give the optimal-σ floor used to convert budgets into error floors via 6EA Wave 2. Verdict: reachable — Cauchy–Schwarz again, on the signal-template inner product; the statement discipline (class explicitness) is the real work.

**Why.** Closes the layer: with matched-filter optimality, every downstream floor is stated against the *best possible* linear readout, which is what makes a ceiling a ceiling.

**Bricks.** Wave 1 + Wave 2; 6EA `avg_error_ge_of_z_le`.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Detection/MatchedFilter.lean` builds 0-sorry, kernel-pure, with:
- [ ] `matched_filter_snr_optimal : ∀ h ∈ class, SNR h ≤ SNR (matched template)` (Cauchy–Schwarz with equality characterization);
- [ ] `optimal_z_budget : z ≤ √(∫ s²/S₀)`-shape corollary (separation budget bound independent of filter choice);
- [ ] `error_floor_from_budget` — composition with 6EA Wave-2: any threshold classifier on any admissible filter has average error `≥ Q(√(∫ s²/S₀))`-shape floor;
- [ ] a `norm_num` non-vacuity witness at a concrete budget point;
- [ ] root-module import + Inventory/counts refresh for the phase;
- [ ] preemptive-strengthening + post-wave audit.

---

## Sequencing & parallelism

Strictly Wave 1 → Wave 2 → Wave 3 on the critical path (each consumes the previous), but Wave 1 and 6EA's waves are independent — **6EB Wave 1 may start as soon as a worktree slot frees, before 6EA closes**, provided 6EA Wave 3's PSD conventions are frozen first (coordinate the one-sided convention early; it is a Stage-2 decision, not a build dependency). Files are new; no contention with other phases except the root-module import (single-writer; land in Wave 3).

## Phase Definition of Done

- [ ] `lake build` + ExtractDeps clean; zero sorry; kernel-pure; no new axioms.
- [ ] `validate.py` green; Inventory + Index refreshed.
- [ ] Adversarial statement audit (vacuity/tautology hunt) logged.
- [ ] Roadmap status updated with dated shipped-declarations list.

## Open UNKNOWNs

- **UNKNOWN-1:** exact Mathlib citation for interval-L² Cauchy–Schwarz in the form needed (`inner_mul_le_norm_mul_norm` on `L²(volume.restrict (Set.Icc 0 T))` vs `MeasureTheory.integral_mul_le_Lp_mul_Lq`); resolve before freezing `enbw_mul_window_ge_half`.
- **UNKNOWN-2:** whether `variance_eq_psd_mul_enbw` is best stated via an abstract white-noise second-moment functional (no stochastic processes in the repo) or as a definitional bridge with the whiteness hypothesis as a `Prop` parameter — prefer the latter unless Mathlib's `ProbabilityTheory` gives the former cheaply.
- **UNKNOWN-3:** unit-semantics convention for NEP (dimensioned reals are not modeled repo-wide) — follow the existing `GrapheneNoiseFormula` precedent (dimensionless reals + documented unit contract + a dimensional-analysis falsifier where a wrong prefactor would be dimensionally detectable).
