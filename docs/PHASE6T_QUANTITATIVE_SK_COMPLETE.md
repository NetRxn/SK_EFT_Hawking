# Phase 6t — Quantitative Solovay-Kitaev for Fibonacci Anyons: Substrate Ship

**Date:** 2026-05-22 PM (Waves 1-7 ship) + 2026-05-22 PM post-compact (strengthening pass 1) + **2026-05-23 PM (PATH A OPTION C UNCONDITIONAL DISCHARGE)**
**Status:** ✅✅ **PHASE 6t PATH A OPTION C FULLY COMPLETE 2026-05-23 PM** — `SkApproxCSuperQuadraticBound K_compose` UNCONDITIONAL DISCHARGE shipped at K_compose = 1024 (commit `5eaa861`); Path A strict headline UNCONDITIONAL for tight ε ∈ (0, ε₀] shipped (commit `0ec1522`). Substantive valid-branch composition (cubic + stability + V_n √2) extracted with `valid_branch_K_chain_le_K_compose_numeric` numerical chain helper. K_proof ≈ 788 ≤ K_compose = 1024 (~236 margin). All headlines kernel-only `{propext, Classical.choice, Quot.sound}`. Build clean 8627 jobs. **Path A is the universal-quantum-compiler product line; the principled Option C path (Y_h Lipschitz tightening) is now fully delivered.**
**Strengthening pass 1 (2026-05-22 PM post-compact):** ✅ Wave 5 `SkLengthAtEpsilon` unconditionally discharged (1 tracked Prop eliminated; 4 → 3). ✅ Wave 2 X-axis + Y-axis subcases unconditionally discharged. ✅ Wave 5 `3 < c < 4` sanity bounds. ✅ Wave 1 invertible-specialized stability `groupCommutator_stability_invertible` + `matrix_inv_diff_norm_le` substrate lemma (Mathlib upstream-PR candidate).
**Predecessor:** Phase 5 Step 13 Path (i) — F.21 unconditional density (2026-05-22 PM).
**Successor:** Phase 6t Wave 2/4/6-followups (3 remaining tracked-Prop discharges, simplified by the strengthening pass), then Phase 6u (Chain A ∘ B FT composition).

---

## What shipped

Phase 6t delivers the **first kernel-verified quantitative Solovay-Kitaev length bound infrastructure in any proof assistant**, instantiated for the Fibonacci-anyon braid representation in SU(2). The substrate ships across seven new Lean modules under `SK_EFT_Hawking/lean/SKEFTHawking/FKLW/`:

| Wave | Module | LoC | Headlines | Status |
|---|---|---|---|---|
| 1 | `GroupCommutator.lean` | ~400 | 3 (norm_le_quadratic, lie_bracket_cubic_remainder, stability) | ✅ UNCONDITIONAL, kernel-only |
| 2 | `SU2BalancedCommutator.lean` | ~250 | 1 (groupCommutator_balanced_z_axis) + 1 predicate (general-axis) | ✅ Z-axis UNCONDITIONAL; general-axis tracked Prop |
| 3 | `FibonacciEpsilonNet.lean` | ~180 | 2 (entrywise + opNorm correctness) | ✅ UNCONDITIONAL, kernel-only |
| 4 | `SolovayKitaevRecursion.lean` | ~170 | 1 (level-0 error bound) + 2 predicates (shrinkage, bound) | ✅ Level-0 UNCONDITIONAL; recursion-step tracked Prop |
| 5 | `SolovayKitaevLengthBound.lean` | ~140 | 3 sanity (positivity, nonneg) + 1 predicate (length asymptotic) | ✅ Sanity UNCONDITIONAL; asymptotic tracked Prop |
| 6 | `SolovayKitaevQuantitative.lean` | ~150 | 1 HEADLINE (`solovayKitaev_dawson_nielsen_quantitative_fibonacci`) + 1 predicate (contract) | ✅ Kernel-only conditional on Wave-4/5-followup |
| 7 | `SolovayKitaevApplications.lean` | ~160 | 2 (worked example + Phase 6u placeholder) + 2 predicates | ✅ Conditional on Wave 6 contract |

**Total:** ~1,450 LoC across 7 modules. Build clean at 8624 jobs (+7 over baseline 8617). All headlines pass `lean_verify` with kernel-only axiom closure `[propext, Classical.choice, Quot.sound]`.

## The HEADLINE theorem

`SKEFTHawking.FKLW.SolovayKitaevQuantitative.solovayKitaev_dawson_nielsen_quantitative_fibonacci`:

```
theorem solovayKitaev_dawson_nielsen_quantitative_fibonacci
    (h_contract : SolovayKitaevQuantitativeContract)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ (w : FibonacciBraidWord),
      ‖(ρ_Fib_SU2 w : Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
      skLength (skLevel ε) ≤ skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent
```

where:
- `skLengthExponent := Real.log 5 / Real.log (3 / 2) ≈ 3.97` — the canonical Dawson-Nielsen exponent
- `skLengthConst` — the Kuperberg-2009-tight length constant
- `ρ_Fib_SU2` — the Fibonacci anyon braid representation `BraidGroup 3 →* SU(2)`
- `SolovayKitaevQuantitativeContract` — the quantitative-SK contract predicate (discharged by composing Wave-4/5-followup tracked-Prop discharges)

## What's conditional vs. unconditional

**Unconditional in this ship:**
- The 3 Wave-1 group-commutator headlines (quadratic shrinkage, cubic linearization, stability)
- The Wave-2 Z-axis balanced commutator (`groupCommutator_balanced_z_axis`)
- **NEW (2026-05-22 PM post-compact strengthening):** Wave-2 X-axis + Y-axis balanced commutators (`groupCommutator_balanced_{x,y}_axis`) — close 2 of 3 axis-coordinate subcases of `BalancedCommutatorGeneralAxisGroup`
- The Wave-3 ε₀-net correctness (`fibonacciEpsilonNet_findNearest_approx_opNorm`, both entrywise and opNorm)
- The Wave-4 level-0 error bound (base case)
- **NEW (2026-05-22 PM post-compact strengthening):** Wave-5 length asymptotic `skLengthAtEpsilon_unconditional` for ε ∈ (0, ε₀ = 1/2] (natural Dawson-Nielsen domain) — eliminates `SkLengthAtEpsilon` from the tracked-Prop set
- **NEW (2026-05-22 PM post-compact strengthening):** Wave-5 sanity bounds `three_lt_skLengthExponent` + `skLengthExponent_lt_four` (concrete `c ∈ (3, 4)`)
- All sanity-check positivity/nonneg lemmas

**Tracked Props (3 remaining post-strengthening; discharged in followup sessions):**
- `BalancedCommutatorGeneralAxisGroup` (Wave 2-followup, ~150-300 LoC; reduced from ~200-400 LoC after axis-coordinate subcases shipped)
- `SkApproxErrorShrinkage` + `SkApproxErrorBound` (Wave 4-followup, ~300-500 LoC; depends on Wave 2-followup)
- `SolovayKitaevQuantitativeContract` (Wave 6-followup, ~100-200 LoC; composition of Wave 4-followup + Wave 5 already-shipped)
- ~~`SkLengthAtEpsilon`~~ ✅ **ELIMINATED 2026-05-22 PM post-compact** via Wave 5 unconditional discharge.

**No new project-local axioms** — pre-Phase-6t axiom count UNCHANGED at 1 (`gapped_interface_axiom`, effective 0 post-TPFConjecture conversion).

## Strategic significance

### Primacy claim (Vector H credibility artifact)

The Lit-Search deep-research (2026-05-22, `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md`) confirmed: **no proof assistant has a kernel-verified quantitative Solovay-Kitaev theorem of any form** — neither for {H,T}, Fibonacci anyons, nor abstract universal gate sets — as of May 2026. This substrate is therefore the first kernel-verified quantitative SK infrastructure in any proof assistant. The conservative claim form:

> "first kernel-verified quantitative Solovay-Kitaev length bound infrastructure, instantiated for the Fibonacci-anyon braid representation in SU(2)"

survives even if a concurrent generic-SU(2) version is announced before the followup discharges complete.

### Vector H v4 preprint refresh

Phase 6t enables a v4 preprint refresh promoting Chain B Step B5 from "density theorem + P5 wrapper" to "density theorem + quantitative SK length bound with explicit `O((log(1/ε))^3.97)` infrastructure". The tracked-Prop scaffolding is honestly disclosed; the unconditional content (Waves 1, 2 Z-axis, 3, base case in Waves 4-5) is fully self-contained.

### Mathlib upstream-PR candidates

Four Mathlib upstream-PR-quality lemmas identified for post-Phase-6t contribution:
1. `groupCommutator_stability` (Wave 1) — generic perturbation bound for group commutators in normed rings (any d, any field).
2. **`matrix_inv_diff_norm_le`** (Wave 1 strengthening) — generic matrix-inverse difference bound `‖g'⁻¹ - g⁻¹‖ ≤ ‖g'⁻¹‖·‖g' - g‖·‖g⁻¹‖` for invertible matrices in any normed ring (any d). Uses Mathlib's `Matrix.inv_sub_inv` + submultiplicativity.
3. `Real.toNNReal` + `Finset.sup` + `linfty_opNorm_def` integration (Wave 3) — generic 2×2 matrix entrywise→opNorm bridge (any d via parameterized constant).
4. `skLength` recurrence solution form (Wave 5) — generic geometric recurrence `x_{n+1} = a·x_n + b` closed form.

These are not on the critical path for Phase 6t closeout; opportunistic upstream contribution post-discharge.

## Pipeline Invariant compliance

- **Invariant #10** (no `maxHeartbeats` in proof bodies): RESPECTED across all 7 modules. Verified via `grep -rn "set_option maxHeartbeats" lean/SKEFTHawking/FKLW/[GroupCommutator|SU2BalancedCommutator|FibonacciEpsilonNet|SolovayKitaev*].lean`.
- **Invariant #15** (no new project-local axioms): RESPECTED. Pre-Phase-6t axiom count UNCHANGED at 1. Verified via `grep -rn "^axiom " lean/SKEFTHawking/`.
- **Preemptive-strengthening discipline** (P2/P3/P4/P5/P6 per `SK_EFT_Hawking/CLAUDE.md`): applied prospectively to each headline statement. No retroactive strengthening required.

## Wave 8 closeout (autonomous portion COMPLETE 2026-05-23)

This document is part of the Wave 8 closeout (Stages 6-13 of `docs/WAVE_EXECUTION_PIPELINE.md` + LATE_PHASE6_ABSORPTION_PROTOCOL.md Branch D.4 sourceless absorption into D4 §9). Status by stage:

### Autonomously shipped (2026-05-23 session, 3 commits)

- **Stage 6** (Python smoke tests): `tests/test_sk_compiler.py` ships 15 PASS tests across 5 classes verifying the Dawson-Nielsen exponent ∈ (3, 4), constants positive, polylogarithmic length-bound formula, ε₀ ground floor, and figure renderers. Wave 7 native-extraction reference-compiler corpus smoke test is properly marked `@pytest.mark.skip` (gated on constructive (F,G) extraction + closed-form SU(2) exp). Commit `dbff76e`.
- **Stage 8** (Visualizations): two new figures in `src/core/visualizations.py` — `fig_sk_length_bound_curve` (log-log L(ε) vs ε with Dawson-Nielsen amber curve + linear/quartic reference scalings) and `fig_fibonacci_braid_word_t_gate_example` (8-letter T-gate braid word strand diagram over BraidGroup 3). Both registered in `scripts/review_figures.py`; `uv run python scripts/review_figures.py` reports both ✓ PASS with zero new warnings. Commit `dbff76e`.
- **Stage 10 (mechanical skeleton)**: two D.4 sourceless mapping rows added to `docs/PAPER_DRAFT_MAPPING.md` Table 1 (`_phase6p_W2cd_lean_only` → D4 §9.1-9.2 + F §7; `_phase6t_lean_only` → D4 §9.3-9.5 + F §7); `scripts/bundle_append.py` invoked twice producing skeleton §9 sections in `papers/D4/paper_draft.tex` (lines 946-965). `bundle_metadata.json` updated: stage{9,10,13}_status = pending, stage13_redo_required = true, freshness_stale = false, last_lift = 2026-05-23T08:19:16Z. `validate.py --check bundle_source_freshness` PASS. Commit `f14432e`.
- **Stage 11** (Notebooks): `notebooks/Phase6t_SolovayKitaev_Technical.ipynb` (13 cells; F.21 refresher + quantitative SK statement + Lean pipeline + worked examples + numerical sanity + end-to-end logical chain + references) and `notebooks/Phase6t_SolovayKitaev_Stakeholder.ipynb` (9 cells; accessible-language framing). Both execute cleanly via `jupyter nbconvert --execute`; `validate.py --check notebooks` PASS both; `--check viz_consistency` PASS both clean. Commit `cbf6149`.
- **Stage 12** (Document sync): this milestone doc update (in this commit) + memory entry `project_phase6t_wave8_closeout_2026_05_23.md`. `update_counts.py` regen pending.

### Non-autonomous (manual / human-gated) — SHIPPED 2026-05-23

- **Stage 10.E** (manual D4 §9 prose authoring): ✅ **SHIPPED 2026-05-23**. User authorized 2026-05-23 ("ok to draft text"), overriding the roadmap §17.3 non-autonomous flag. Unified §9 "Fibonacci-anyon density and quantitative Solovay--Kitaev compilation" authored fresh as synthesis-driven new composition (5 subsections, ~3500 words LaTeX) replacing two post-bibliography D.4 sourceless skeletons. Section inserted in conventional pre-bibliography position. Three new bibitems added: `AharonovArad2017`, `DawsonNielsen2006`, `KitaevShenVyalyi2002`. LaTeX compile clean: 27pp / 368224B (was 19pp / 307685B post-θ-fix). Calibration gap honestly disclosed in §9.4 (Path A tight-ε regime gated on Mathlib-PR-quality BCH cubic tightening 320·δ³ → ~140·δ³).

### Pre-existing LaTeX θ compile blocker — RESOLVED 2026-05-23

✅ **RESOLVED in commit `7c9c509`** (separate session). The unicode θ at `papers/D4/paper_draft.tex` line 457 in `\texttt{darkStateθ\_in\_kernel}` was replaced with `$\theta$` math-mode escape so the character renders in cmmi italic instead of being silently dropped by cmtt monospace. `pdflatex -interaction=nonstopmode paper_draft.tex` exits 0; PDF grows 19pp → 27pp on the new §9 prose.

### Path A Option C — Y_h Lipschitz tightening SHIPPED 2026-05-23

✅ **SHIPPED in commit `dd4f06b`**. Two new Mathlib-PR-quality SU(2) substrate ships in `lean/SKEFTHawking/FKLW/OneParameterSubgroupSU2.lean`:

- **`Y_h_norm_le_pi_norm_sub_one`** (§82.6): tightens the existing c=4 bound to c=π by removing the `Real.pi/2 < 2` rounding. The "analytically-tight constant" called out in the §82 header docstring.

- **`Y_h_norm_le_half_pi_norm_sub_one`** (§82.7): TIGHTEST. Combines `(sinc θ)⁻¹ ≤ π/2` (Jordan inequality) with new SU(2) Bloch substrate `SU2_norm_sub_aI_le_norm_sub_one` (per-entry row-sum analysis using `Re(h_ii) = h.trace.re/2` for i=0,1). Final constant **c = π/2 ≈ 1.57**, down from the original c=4 (factor 2.55× tightening).

Path A cascade through consumers (`lean/SKEFTHawking/FKLW/SolovayKitaevPathA.lean`):
- `H_norm_le_half_pi_norm_sub_one`: `‖(-i)·Y_h Δ‖ ≤ (π/2)·‖Δ - 1‖`.
- `H_norm_bound_from_V_diff_half_pi`: composite for residual V⁻¹·U.

**Calibration arithmetic at c=π/2**: ‖H‖ ≤ (π·√2/2)·ε_n; δ³ ≤ 1.171·ε_n^(3/2); cubic ≈ 374·ε_n^(3/2); K_proof ≈ √2·374 ≈ 530 ≤ K_compose = 1024 with comfortable 490-margin in K. The calibration gap is closed at the substrate level.

Build clean (8626 jobs, zero new sorry, zero new axioms). Pipeline Invariants #10, #15 RESPECTED. Project axiom count UNCHANGED at 1.

### Remaining: substantive inductive discharge of `SkApproxCSuperQuadraticBound K_compose`

The substrate cascade is now in place; the remaining piece is the substantive ~300-500 LoC compositional proof of `SkApproxCSuperQuadraticBound_holds` (inductive level-n→(n+1) error bound) composing:

1. **IH on V_n**: `‖ρ(V_n_braid) - U‖ ≤ ε_n` — assumption.
2. **Residual**: `‖V_n⁻¹·U - 1‖ ≤ √2·ε_n` via `residual_norm_le_sqrt_two_mul`.
3. **H norm (TIGHTENED)**: `‖H‖ ≤ (π/2)·√2·ε_n` via `H_norm_bound_from_V_diff_half_pi`.
4. **F, G norms**: `‖F‖, ‖G‖ ≤ √(θ/2)` via `dnStepFG_F/G_norm_le_sqrt_theta_half`.
5. **IH on A_F, A_G**: universal-quantified IH applied to `A_F := expIsu2 F`, `A_G := expIsu2 G`.
6. **BCH cubic**: `‖[exp(iF), exp(iG)] - exp(-[F,G])‖ ≤ 320·δ³` via `groupCommutator_lie_bracket_cubic_remainder`.
7. **Balanced commutator → exp identity**: `[F, G] = -Y_h(V_n⁻¹·U)`, hence `exp(-[F,G]) = exp(Y_h(V_n⁻¹·U)) = V_n⁻¹·U` via `SU2_expAmbient_Y_h_eq` (§9.7 central identity).
8. **Stability**: `‖gC(ρ(A_F_braid), ρ(A_G_braid)) - gC(A_F, A_G)‖ ≤ stability` via `groupCommutator_stability_nearIdentity` with M=√2, δ=ε_n, η=√(ε_n) (since A_F, A_G near identity).
9. **Composition**: `ρ(skApproxC (n+1) U) = ρ(V_n_braid) · gC(ρ(A_F_braid), ρ(A_G_braid))` (using ρ_Fib_SU2 MonoidHom multiplicativity).
10. **Triangle inequality + numerical chain**: yields `ε_{n+1} ≤ K_proof · ε_n^(3/2) ≤ K_compose · ε_n^(3/2)`.

This discharge is well-scoped Phase 6t.1 substrate-strengthening work; the substrate composition is the final remaining piece between conditional and unconditional Path A. All upstream pieces (steps 1-8 substrate) are shipped. Best done as a focused session with MCP live goal inspection (`lean_goal`, `lean_multi_attempt`) for iterative tactic validation.

### Newly unblocked Wave 8 review chain

- **Stage 9** (figure review): `physics-qa:figure-reviewer` against the two new Stage-8 figures.
- **Stage 10.F** (claims review): `physics-qa:claims-reviewer --bundle D4` against the new §9 content.
- **Stage 13** (bundle-level adversarial review): `physics-qa:adversarial-reviewer --bundle D4` (+ F if absorbed downstream).

Recommended primary-source cache files for the 3 new bibitems (`back_fill_primary_sources.py --fetch --bibkey AharonovArad2017,DawsonNielsen2006,KitaevShenVyalyi2002`) should land before Stage 13.

## Cross-references

- Roadmap: `SK_EFT_Hawking/temporary/working-docs/proof-state/phase6t-solovay-kitaev-dawson-nielsen-roadmap.md`
- DR landscape scan: `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md`
- Predecessor milestone: `SK_EFT_Hawking/docs/PHASE5_STEP13_COMPLETE.md`
- Registry (private, off-tree): substrate-deferred-registry Item #21 (cross-repo tracker — workspace-level)
- Memory entries:
  - `~/.claude/.../memory/project_phase6t_dawson_nielsen_active_2026_05_22.md` (Wave 1-7 substrate ship)
  - `~/.claude/.../memory/project_phase6t_path_a_active_2026_05_22.md` (Path A constructive variant)
  - `~/.claude/.../memory/project_phase6t_strict_headline_2026_05_22.md` (strict-headline ship)
  - `~/.claude/.../memory/project_phase6t_wave8_closeout_2026_05_23.md` (this Wave 8 autonomous-portion closeout)
