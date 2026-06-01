# Phase 6t — Quantitative Solovay-Kitaev for Fibonacci Anyons: Substrate Ship

**Date:** 2026-05-22 PM (Waves 1-7 ship) + 2026-05-22 PM post-compact (strengthening pass 1) + **2026-05-23 PM (PATH A OPTION C UNCONDITIONAL DISCHARGE)**
**Status:** ✅✅ **PHASE 6t PATH A OPTION C FULLY COMPLETE 2026-05-23 PM** — `SkApproxCSuperQuadraticBound K_compose` UNCONDITIONAL DISCHARGE shipped at K_compose = 1024 (commit `5eaa861`); Path A strict headline UNCONDITIONAL for tight ε ∈ (0, ε₀] shipped (commit `0ec1522`). Substantive valid-branch composition (cubic + stability + V_n √2) extracted with `valid_branch_K_chain_le_K_compose_numeric` numerical chain helper. K_proof ≈ 788 ≤ K_compose = 1024 (~236 margin). All headlines kernel-only `{propext, Classical.choice, Quot.sound}`. Build clean 8627 jobs. **Path A is the universal-quantum-compiler product line; the principled Option C path (Y_h Lipschitz tightening) is now fully delivered.**
**Strengthening pass 1 (2026-05-22 PM post-compact):** ✅ Wave 5 `SkLengthAtEpsilon` unconditionally discharged (1 tracked Prop eliminated; 4 → 3). ✅ Wave 2 X-axis + Y-axis subcases unconditionally discharged. ✅ Wave 5 `3 < c < 4` sanity bounds. ✅ Wave 1 invertible-specialized stability `groupCommutator_stability_invertible` + `matrix_inv_diff_norm_le` substrate lemma (Mathlib upstream-PR candidate).
**Predecessor:** Phase 5 Step 13 Path (i) — F.21 unconditional density (2026-05-22 PM).
**Successor:** Phase 6t Wave 2/4/6-followups (3 remaining tracked-Prop discharges, simplified by the strengthening pass), then Phase 6u (Chain A ∘ B FT composition).

---

## What shipped

Phase 6t delivers the **first kernel-verified quantitative Solovay-Kitaev length bound infrastructure in any proof assistant**, instantiated for the Fibonacci-anyon braid representation in SU(2). The substrate ships across seven new Lean modules under `SK_EFT_Hawking/lean/SKEFTHawking/FKLW/`:

| Wave | Module | LoC | Headlines | Status (post-2026-05-23 PM) |
|---|---|---|---|---|
| 1 | `GroupCommutator.lean` | ~400 | 3 (norm_le_quadratic, lie_bracket_cubic_remainder, stability) | ✅ UNCONDITIONAL, kernel-only |
| 1+ | `GroupCommutatorNearIdentity.lean` | ~440 | 1 (`groupCommutator_stability_nearIdentity`) — near-identity-sharpened stability | ✅ UNCONDITIONAL, kernel-only (Iteration 2 substrate) |
| 2 | `SU2BalancedCommutator.lean` | ~250 | 1 (groupCommutator_balanced_z_axis) + Wave 2-followup (X, Y axes + general-axis discharge) | ✅ ALL UNCONDITIONAL post-followup |
| 3 | `FibonacciEpsilonNet.lean` | ~180 | 2 (entrywise + opNorm correctness) | ✅ UNCONDITIONAL, kernel-only |
| 4 | `SolovayKitaevRecursion.lean` | ~170 | 1 (level-0 error bound) + Wave 4-followup discharges (shrinkage, bound) | ✅ ALL UNCONDITIONAL post-followup |
| 5 | `SolovayKitaevLengthBound.lean` | ~140 | 3 sanity + Wave 5 unconditional `skLengthAtEpsilon_unconditional` | ✅ ALL UNCONDITIONAL |
| 6 | `SolovayKitaevQuantitative.lean` | ~150 | 1 HEADLINE (`solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict`) | ✅ UNCONDITIONAL post-Wave-6-followup |
| 7 | `SolovayKitaevApplications.lean` | ~160 | 2 worked examples | ✅ UNCONDITIONAL post-Wave-6 |
| Option C | `SolovayKitaevPathA.lean` | **~2500** | **3 HEADLINES**: `SkApproxCSuperQuadraticBound_holds` (commit `5eaa861`); `valid_branch_K_chain_le_K_compose_numeric` (numerical chain helper); `_strict_constructive_tight` (commit `0ec1522`) | ✅ **UNCONDITIONAL kernel-only as of 2026-05-23 PM** |

**Total:** ~4,000 LoC across 9 modules post Path-A Option C. Build clean at 8627 jobs. All headlines pass `lean_verify` with kernel-only axiom closure `[propext, Classical.choice, Quot.sound]`. **Project axiom count UNCHANGED at 1 (`gapped_interface_axiom`) — zero new project-local axioms across all Phase 6t work.**

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

**ALL Phase 6t tracked Props have been discharged unconditionally as of 2026-05-23 PM.** The final remaining piece — `SkApproxCSuperQuadraticBound K_compose` — shipped at K_compose = 1024 in commit `5eaa861`, kernel-only `{propext, Classical.choice, Quot.sound}`. Project axiom count UNCHANGED at 1.

**Unconditional in this ship (chronological):**
- The 3 Wave-1 group-commutator headlines (quadratic shrinkage, cubic linearization, stability)
- The Wave-2 Z-axis balanced commutator (`groupCommutator_balanced_z_axis`)
- Wave-2 X-axis + Y-axis balanced commutators (`groupCommutator_balanced_{x,y}_axis`) — 2026-05-22 PM post-compact
- **Wave 2-followup**: `BalancedCommutatorGeneralAxisGroup` discharged unconditionally via SU(2) Bloch (task #34) — 2026-05-22 PM
- The Wave-3 ε₀-net correctness (`fibonacciEpsilonNet_findNearest_approx_opNorm`, both entrywise and opNorm)
- The Wave-4 level-0 error bound (base case)
- **Wave 4-followup**: `SkApproxErrorShrinkage` + `SkApproxErrorBound` discharged (task #35) — 2026-05-22 PM
- Wave-5 length asymptotic `skLengthAtEpsilon_unconditional` for ε ∈ (0, ε₀] (2026-05-22 PM)
- Wave-5 sanity bounds `three_lt_skLengthExponent` + `skLengthExponent_lt_four` (2026-05-22 PM)
- **Wave 6-followup**: `SolovayKitaevQuantitativeContract` discharged (task #36) — 2026-05-22 PM
- **Iteration 1+2 (2026-05-22)**: ε₀ refinement, matrix log residual bound, ε_seq + skApprox_exists
- **Path A Steps 1-5 (2026-05-22)**: `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive` conditional headline + loose-ε / structural-K_huge unconditional variants
- **Path A Option C (2026-05-23 PM, 19 commits)** — the FINAL discharge:
  - Y_h Lipschitz tightening 4 → π/2 (`Y_h_norm_le_half_pi_norm_sub_one`)
  - ρ_Fib_SU2 matrix-level helpers (`ρ_Fib_SU2_groupCommutator_val` etc.)
  - Load-bearing identities `[F, G] = -Y_h Δ` + `exp(-[F,G]) = Δ`
  - Near-identity bounds + regime checks + Y_h injectivity in regime
  - DN cubic composition `dnStepFG_gC_minus_Delta_norm_le_cubic`
  - Invalid-branch helpers (`dnStepFG_invalid_F_zero`, `expIsu2_zero_val`)
  - **HEADLINE 1**: `SkApproxCSuperQuadraticBound_holds` (commit `5eaa861`) — UNCONDITIONAL discharge at K_compose = 1024
  - **HEADLINE 2**: `valid_branch_K_chain_le_K_compose_numeric` — pure numerical chain helper (Mathlib-PR-quality)
  - **HEADLINE 3**: `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` (commit `0ec1522`) — UNCONDITIONAL strict headline for tight ε ∈ (0, ε₀] bundling BOTH error AND length at the same algorithmic level

**Tracked Props remaining**: ✅ NONE. All Phase 6t predicates are discharged unconditionally.

**No new project-local axioms** — pre-Phase-6t axiom count UNCHANGED at 1 (`gapped_interface_axiom`, effective 0 post-TPFConjecture conversion).

## Strategic significance

### Primacy claim (Vector H credibility artifact)

The Lit-Search deep-research (2026-05-22, `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md`) confirmed: **no proof assistant has a kernel-verified quantitative Solovay-Kitaev theorem of any form** — neither for {H,T}, Fibonacci anyons, nor abstract universal gate sets — as of May 2026. This substrate is therefore the first kernel-verified quantitative SK infrastructure in any proof assistant. The conservative claim form:

> "first kernel-verified quantitative Solovay-Kitaev length bound infrastructure, instantiated for the Fibonacci-anyon braid representation in SU(2)"

survives even if a concurrent generic-SU(2) version is announced before the followup discharges complete.

### Vector H v4 preprint refresh

Phase 6t enables a v4 preprint refresh promoting Chain B Step B5 from "density theorem + P5 wrapper" to "density theorem + quantitative SK length bound with explicit `O((log(1/ε))^3.97)` infrastructure". The tracked-Prop scaffolding is honestly disclosed; the unconditional content (Waves 1, 2 Z-axis, 3, base case in Waves 4-5) is fully self-contained.

### Mathlib upstream-PR candidates

Eight Mathlib upstream-PR-quality lemmas identified across Phase 6t — opportunistic post-discharge contribution targets:

**Generic group-commutator + matrix lemmas:**
1. `groupCommutator_stability` (Wave 1) — generic perturbation bound for group commutators in normed rings (any d, any field).
2. `matrix_inv_diff_norm_le` (Wave 1 strengthening) — generic matrix-inverse difference bound `‖g'⁻¹ - g⁻¹‖ ≤ ‖g'⁻¹‖·‖g' - g‖·‖g⁻¹‖` for invertible matrices in any normed ring.
3. `Real.toNNReal` + `Finset.sup` + `linfty_opNorm_def` integration (Wave 3) — generic 2×2 matrix entrywise→opNorm bridge.
4. `skLength` recurrence solution form (Wave 5) — generic geometric recurrence `x_{n+1} = a·x_n + b` closed form.
5. **`groupCommutator_stability_nearIdentity`** (Iteration 2 substrate) — near-identity-sharpened group commutator stability `‖[g',h'] - [g,h]‖ ≤ 2(M²+M⁴)·δ·η + (M⁴+M⁶)·δ²` with leading term linear in the near-identity radius η (vs the generic linear-in-δ bound). Substantially tighter for Dawson-Nielsen-style recursions where the operands are near-identity.

**SU(2) matrix-log substrate (Option C, 2026-05-23):**
6. **`SU2_norm_sub_aI_le_norm_sub_one`** — SU(2) row-sum identity `‖h - a·I‖ ≤ ‖h - 1‖` for a = trace(h)/2. Exploits `Re(h_ii) = h.trace.re/2` for i = 0, 1 to bound diagonal entries entry-wise.
7. **`Y_h_norm_le_half_pi_norm_sub_one`** — Tightest matrix-log Lipschitz bound `‖Y_h(h)‖ ≤ (π/2)·‖h - 1‖` combining `(sinc θ)⁻¹ ≤ π/2` (Jordan) with SU(2) Bloch row-sum.
8. **`SU2_subtype_inv_val_eq_matrix_inv`** — Bridge identity `(A⁻¹ : SU(2)).val = (A.val)⁻¹` (subtype group inverse equals matrix nonsing inverse).

**Numerical chain helper (Option C, 2026-05-23):**
9. **`valid_branch_K_chain_le_K_compose_numeric`** — pure real-valued numerical chain establishing the calibration arithmetic for Solovay-Kitaev recursions. Generalizable template for SK constant calibration at arbitrary K.

These are not on the critical path for Phase 6t closeout (now COMPLETE); opportunistic upstream contribution.

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

### ✅ SHIPPED 2026-05-23 PM: substantive inductive discharge of `SkApproxCSuperQuadraticBound K_compose`

The substantive compositional proof (`SkApproxCSuperQuadraticBound_holds`, commit `5eaa861`, ~981 LoC) discharges the predicate unconditionally at K_compose = 1024. Proof structure:

1. **IH on V_n**: `‖ρ(V_n_braid) - U‖ ≤ ε_n` via `ih U` (induction hypothesis).
2. **Residual**: `‖V_n⁻¹·U - 1‖ ≤ √2·ε_n` via `residual_norm_le_sqrt_two_mul`.
3. **H norm (TIGHTENED)**: `‖H‖ ≤ (π/2)·√2·ε_n` via `H_norm_bound_from_V_diff_half_pi`.
4. **Case split** on dnStepFG validity (`0 < ‖H‖ ∧ ‖H‖ ≤ 1`):
   - **VALID branch** (substantive):
     - `δ_lie := √(θ/2)`, with `δ_lie² ≤ (π/4)·√2·ε_n` (regime)
     - F, G norms: `‖F‖, ‖G‖ ≤ δ_lie` via `dnStepFG_F/G_norm_le_sqrt_theta_half`
     - IH on A_F, A_G: `‖ρ A_F_braid - A_F.val‖ ≤ ε_n` and similarly for A_G
     - DN cubic: `‖gC(A_F.val, A_G.val) - Δ.val‖ ≤ 320·δ_lie³` via `dnStepFG_gC_minus_Delta_norm_le_cubic` (composing Wave 1 `groupCommutator_lie_bracket_cubic_remainder` + Wave 2 `balanced_commutator_general_axis_lie_traceless` + §9.7 `SU2_expAmbient_Y_h_eq`)
     - Stability: `‖gC(ρ A_F_braid, ρ A_G_braid) - gC(A_F.val, A_G.val)‖ ≤ stab_bound` via `groupCommutator_stability_nearIdentity` with M = √2, η = √2·δ_lie·exp(δ_lie), δ = ε_n
     - Composition: `ρ(skApproxC (n+1) U) = V_n · gC(ρ A_F_braid, ρ A_G_braid)` (ρ_Fib_SU2 MonoidHom + matrix gC identity `ρ_Fib_SU2_groupCommutator_val`)
     - Triangle inequality decomposing into `√2·stab_bound + √2·320·δ_lie³`
     - Numerical chain via `valid_branch_K_chain_le_K_compose_numeric`: bounds K_proof ≤ 788 ≤ K_compose = 1024 (margin ~236)
   - **INVALID branch** (`‖H‖ = 0`, the only failure mode in regime since `‖H‖ ≤ 1` always):
     - `Y_h(Δ.val) = 0` (from H = -i·Y_h(Δ.val) = 0)
     - `Δ.val = 1` via `Y_h_eq_zero_in_regime_implies_eq_one`
     - Hence `V_n.val = U.val` (since Δ_SU2 = V_n_SU2⁻¹ * U = 1)
     - F = G = 0 via `dnStepFG_invalid_F_zero`; A_F = A_G via `expIsu2_val` + F = G; braid commutator [g, g] = 1
     - So `skApproxC (m+1) U = V_n_braid` (braid equality); `ρ(skApproxC (m+1) U) = V_n_SU2 = U`
     - Error = 0 ≤ K_compose · ε_n^(3/2) ✓

The wrapper `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` (commit `0ec1522`) applies `SkApproxCSuperQuadraticBound_holds` to the conditional strict headline of §6, dropping the `h_bound` hypothesis. Path A is now UNCONDITIONAL on all three regimes.

**Architecture lessons saved for future SK discharges:**
- Pipeline Invariant #10 forbids `set_option maxHeartbeats` — required extracting the numerical chain into a top-level helper (`valid_branch_K_chain_le_K_compose_numeric`) to fit the 200,000-heartbeat per-theorem ceiling.
- `noncomm_ring` (not `ring`) for matrix distributivity rewrites `a·b - a·c = a·(b - c)`.
- Tighter (π/4)·√2 ≤ 6/5 bound (via π < 3.15 + √2 ≤ 3/2) brings K_proof ≤ 788 under K_compose = 1024; loose bounds (π ≤ 4, etc.) overshoot at ~1440.

### Newly unblocked Wave 8 review chain

- **Stage 9** (figure review): `physics-qa:figure-reviewer` against the two new Stage-8 figures.
- **Stage 10.F** (claims review): `physics-qa:claims-reviewer --bundle D4` against the new §9 content.
- **Stage 13** (bundle-level adversarial review): `physics-qa:adversarial-reviewer --bundle D4` (+ F if absorbed downstream).

Recommended primary-source cache files for the 3 new bibitems (`back_fill_primary_sources.py --fetch --bibkey AharonovArad2017,DawsonNielsen2006,KitaevShenVyalyi2002`) should land before Stage 13.

## Cross-references

- Roadmap: `SK_EFT_Hawking/temporary/working-docs/proof-state/phase6t-solovay-kitaev-dawson-nielsen-roadmap.md`
- DR landscape scan: `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md`
- Predecessor milestone: `SK_EFT_Hawking/temporary/working-docs/PHASE5_STEP13_COMPLETE.md`
- Registry (private, off-tree): substrate-deferred-registry Item #21 (cross-repo tracker — workspace-level)
- Memory entries:
  - `~/.claude/.../memory/project_phase6t_dawson_nielsen_active_2026_05_22.md` (Wave 1-7 substrate ship)
  - `~/.claude/.../memory/project_phase6t_path_a_active_2026_05_22.md` (Path A constructive variant)
  - `~/.claude/.../memory/project_phase6t_strict_headline_2026_05_22.md` (strict-headline ship)
  - `~/.claude/.../memory/project_phase6t_wave8_closeout_2026_05_23.md` (this Wave 8 autonomous-portion closeout)
