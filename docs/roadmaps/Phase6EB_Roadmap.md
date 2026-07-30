# Phase 6EB — Kernel-Verified Filtered-Readout Noise Floors: ENBW, NEP, and Matched-Filter Limits

**Status: COMPLETE — all three waves SHIPPED (authorized 2026-07-27; closed 2026-07-29).** Second phase of the `6E*` series (*verified device-physics metrology*). Consumes Phase 6EA (Poisson/Gaussian floors); consumed by 6EC (electrothermal detectors) and 6EE (composite readout ceilings). See `Phase6EA_Roadmap.md` for the series framing.

> **Status correction 2026-07-29.** This header read `PLANNED` and Wave 2's AC boxes were unchecked, but both waves had in fact shipped (verified against the tree, not the checkboxes):
> `Detection/FilterFloors.lean` — 23 declarations, and `Detection/NEPAlgebra.lean` — 41 declarations; **both zero sorry, zero axiom, zero `native_decide`, zero `maxHeartbeats`**, both imported in `SKEFTHawking.lean`.
> Wave 2 shipped under names that differ from the AC text: `nep_def` landed as the pair `nepOfPSD` / `nepOfOutput` plus the bridge `nep_def_operational_eq_spectral`, and `snr_composition` as the `snrChain` definition with its composition lemmas. The AC list below is annotated accordingly — the deliverables are present, the AC wording was not updated when they landed.
> **Only Wave 3 (`Detection/MatchedFilter.lean`) and the Phase Definition of Done remain.**

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

**Done (AC / `/goal` condition).** ✅ **SHIPPED** — verified against the tree 2026-07-29 (41 declarations, 0 sorry / 0 axiom / 0 `native_decide` / 0 `maxHeartbeats`, root-imported).
- [x] `lean/SKEFTHawking/Detection/NEPAlgebra.lean` builds 0-sorry, kernel-pure, with:
- [x] **shipped as `nepOfPSD` + `nepOfOutput` (defs) + `nep_def_operational_eq_spectral` (the bridge)** `nep_def` (input-referred, one-sided, W/√Hz semantics as a declared unit convention) + `nep_incident_absorbed_transfer : NEP_inc = NEP_abs / η` (with `R_inc = η·R_abs` dual, shipped as `responsivity_incident_eq`);
- [x] `sigma_eq_responsivity_nep_sqrt_enbw` — the classified-variable noise composition, with hypotheses (whiteness, linearity of the chain) explicit — shipped via `IsResponsivityChain`;
- [x] `nep_quadrature_add` — independent noise sources add in quadrature at a common plane (finite family, stated over variances) — plus `nep_total_eq_sqrt_sum_sq`, `nep_quadrature_two`, and the load-bearing-hypothesis witness `quadrature_uncorrelated_hypothesis_load_bearing`;
- [x] `shot_nep_formula : NEP_shot,abs = √(2·E_ph·P_abs)`-shape identity tied to 6EA's shot PSD (one-sided convention) — plus `nep_thermal_johnsonNyquist`, `shotLimited_iff_psd_lt`, `shotLimited_witness`;
- [x] **shipped as the `snrChain` definition + its composition lemmas** `snr_composition`-shape theorem: end-to-end SNR through the chain, monotone in each budget term — the screen consumed by composite ceilings;
- [x] preemptive-strengthening + post-wave audit — the convention-mix family (`enbwTwoSided_eq_two_mul_enbw`, `sigma_conventionPair_consistent_invariant`, `sigma_conventionMix_eq_sqrt_two_mul`, `sigma_conventionMix_ne`) is the audit's falsifiable residue: it proves the one-sided/two-sided mix-up changes the answer by exactly √2 rather than merely asserting the convention matters.

## Wave 3 — Matched-filter optimality

**Goal.** Over the admissible class (interval-supported L², linear, single-shot), the matched filter maximizes SNR; corollaries give the optimal-σ floor used to convert budgets into error floors via 6EA Wave 2. Verdict: reachable — Cauchy–Schwarz again, on the signal-template inner product; the statement discipline (class explicitness) is the real work.

**Why.** Closes the layer: with matched-filter optimality, every downstream floor is stated against the *best possible* linear readout, which is what makes a ceiling a ceiling.

**Bricks.** Wave 1 + Wave 2; 6EA `avgError_ge_gaussianQ_sharp` (and the distribution-free
`avgError_ge_affinity_sq`). *(Record correction 2026-07-30: this line previously named
`avg_error_ge_of_z_le`, which resolves to nothing — the AC-text name was never reconciled against
what 6EA actually shipped.)*

**Done (AC / `/goal` condition).** ✅ **SHIPPED 2026-07-29** — 33 extracted declarations (`lean_deps.json`, the same convention under which W1 = 23 and W2 = 41), 0 sorry / 0 axiom / 0 `native_decide` / 0 `maxHeartbeats`, kernel-pure `{propext, Classical.choice, Quot.sound}`, root-imported.
- [x] `lean/SKEFTHawking/Detection/MatchedFilter.lean` builds 0-sorry, kernel-pure, with:
- [x] **shipped strictly stronger** as `filteredSNR_le_matchedBudget` (bound by the *filter-free* budget `√(2·∫s²/S₀)`, not by `SNR(matched)`) + `filteredSNR_matched_eq_budget` (attainment) + `matchedFilter_isGreatest` (the two as an `IsGreatest`) `matched_filter_snr_optimal : ∀ h ∈ class, SNR h ≤ SNR (matched template)` (Cauchy–Schwarz with equality characterization — shipped as the full biconditional `filteredSNR_eq_budget_iff`, saturation **iff** `h` is a.e. a *positive* multiple of the template, with `filteredSNR_neg_matched_eq_neg_budget` witnessing that the positivity is not removable). The AC's literal (weaker) form is deliberately **not** shipped — identity-wrapper rule, same call as 6EA's `avgError_ge_gaussianQ_sharp`;
- [x] **shipped as `optimal_z_budget` + `matchedBudget_half_eq`** (the closed form `matchedBudget/2 = √(∫s²/(2·S₀))`, one-sided constant explicit) `optimal_z_budget : z ≤ √(∫ s²/S₀)`-shape corollary;
- [x] `error_floor_from_budget` — composition with 6EA Wave-2's `avgError_ge_gaussianQ_sharp`: `gaussianQ (matchedBudget/2) ≤ avgAssignmentError …` for any admissible filter and any threshold, with the deflection/noise identification carried as explicit binders (`hμ`, `hσV`);
- [x] a `norm_num` non-vacuity witness at a concrete budget point — `matchedBudget_twoBoxcar` (`matchedBudget 1 2 (2·𝟙[0,2]) = 4`, so `z = 2`) feeding `error_floor_twoBoxcar_witness` (`1/125 ≤ avgAssignmentError`, via 6EA's rational enclosure `gaussianQ_two_ge_rational` — no floating-point `exp` anywhere);
- [x] root-module import + Inventory/counts refresh for the phase;
- [x] preemptive-strengthening + post-wave audit — residue: the audit dropped a redundant `hss` binder from `matchedFilter_isGreatest` and the dead `0 ≤ ∫s²` binder from `matchedBudget_half_eq`, and added `filteredSNR_ramp_lt_budget` (the ramp against the unit boxcar sits strictly below the budget at `√3/2 < 1`) so the ceiling is shown to *discriminate* rather than being saturated by everything — the exact analogue of Wave 1's `enbw_ramp_gt_half`.
- [x] **Post-6EC-review addendum, 2026-07-29 (slot wt1).** Two minors raised while remediating 6EC, both closed here: (a) `matchedBudget_half_eq` was *also* carrying a dead `0 < S₀` binder while its docstring boasted about having dropped the `0 ≤ ∫s²` one — the minimality standard now applies to both, and the statement is unconditional; (b) `optimal_z_budget`'s docstring now states why it is exempt from the identity-wrapper rule the same file's AC-deviations section invokes against shipping the AC's literal optimality form (it crosses the `z = SNR/2` convention boundary that `matchedBudget_half_ne_matchedBudget` proves detectable). **New declaration:** `matchedBudget_antitone_psd` — the budget is antitone in the one-sided noise PSD, with `0 < S₁` the only (and genuinely load-bearing) hypothesis. This is what 6EC's `phonon_only_error_floor` needs to state a floor for a *single irreducible channel* rather than for a composed budget, and it belongs here because it is a fact about `matchedBudget`.

**Supporting bricks shipped alongside:** `IsAdmissibleFilter` (the class, stated as a structure with both conditions in the statement), `filteredSNR`, `matchedBudget`, `admissibleSNRs`; `integral_sub_smul_sq` + `sq_integral_mul_le` (the two-function interval Cauchy–Schwarz — the settled variance route, not Hölder/`MemLp`); `matched_ratio_eq_sqrt`, `filteredSNR_smul_eq_budget`; `intervalIntegrable_twoBoxcar_sq`, `integral_twoBoxcar_sq`; `filteredSNR_of_variance_eq_zero` (degenerate branch disclosed).

---

## Sequencing & parallelism

Strictly Wave 1 → Wave 2 → Wave 3 on the critical path (each consumes the previous), but Wave 1 and 6EA's waves are independent — **6EB Wave 1 may start as soon as a worktree slot frees, before 6EA closes**, provided 6EA Wave 3's PSD conventions are frozen first (coordinate the one-sided convention early; it is a Stage-2 decision, not a build dependency). Files are new; no contention with other phases except the root-module import (single-writer; land in Wave 3).

## Phase Definition of Done

- [x] `lake build` + ExtractDeps clean; zero sorry; kernel-pure; no new axioms. *(2026-07-29 — `Build completed successfully (10786 jobs)`; project-wide axioms 0, sorry 0.)*
- [x] `validate.py` green; Inventory + Index refreshed. *(2026-07-29 — `update_counts.py` + `update_inventory_index.py` re-run against the fresh `ExtractDeps`.)*
- [x] Adversarial statement audit (vacuity/tautology hunt) logged. *(Per-wave audits in the notebook; the Wave-3 residue is recorded inline in the Wave-3 AC above.)*
- [x] Roadmap status updated with dated shipped-declarations list. *(This document, 2026-07-29.)*

## Shipped declarations (dated)

| wave | module | decls | merged |
|---|---|---|---|
| W1 | `lean/SKEFTHawking/Detection/FilterFloors.lean` | 23 | `4378cc01` (2026-07-28) |
| W2 | `lean/SKEFTHawking/Detection/NEPAlgebra.lean` | 41 | `193437a1` (2026-07-28) |
| W3 | `lean/SKEFTHawking/Detection/MatchedFilter.lean` | 33 | 2026-07-29 |

Post-merge corrections folded in: `25307cf6` (PSD duplication reconciled — canonical is `Detection.shotPSD`), `a9c257da` (W2 docstring re-pointed at shipped names).

## Open UNKNOWNs — all resolved

- **UNKNOWN-1 — RESOLVED (W1, 2026-07-28).** The roadmap posed a false binary. Neither Mathlib route was used: the interval Cauchy–Schwarz is proved from non-negativity of the variance integral `0 ≤ ∫₀ᵀ (h − c)²` (`sq_integral_le`), with no Hölder, no `rpow`, no `MemLp`. W3's two-function form `sq_integral_mul_le` uses the same route at `0 ≤ ∫₀ᵀ (h − c·s)²` — which additionally hands the equality case over for free, where a Hölder route would have had to reconstruct it separately.
- **UNKNOWN-2 — RESOLVED (W1, 2026-07-28)** in favour of the roadmap's preferred option: `IsWhiteFilteredVariance` is a `Prop` parameter (`∀ h, V h = S₀/2 · ∫₀ᵀ h²`). Mathlib carries no Wiener–Khinchin / spectral measure for a second-order process at the pin, and the repo models no stochastic processes; whiteness is a modelling assumption about the *source*, so it belongs in the binder list, not smuggled into a definition. W3 consumes it directly.
- **UNKNOWN-3 — RESOLVED (W2, 2026-07-28):** dimensionless reals + a declared unit-contract table, per the `GrapheneNoiseFormula` precedent. Falsifiability is carried by `σ = R·NEP·√ENBW` closing dimensionally, and by the convention-**mix** family (`sigma_conventionMix_ne` et al.) — a one-sided/two-sided *mix-up* is detectable at exactly √2, whereas a uniformly-wrong convention is not detectable from a variance at all (`S₀·ENBW` is convention-invariant; see `SETTLED_FORKS.md` → `6eb-enbw-convention-falsifier-shape`).
