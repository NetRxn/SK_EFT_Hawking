# Phase 5u: Paper Revision from April 2026 Review Round

## Technical Roadmap — April 2026

*Prepared 2026-04-13 | Triggered by: consolidated findings of 7 automated review documents (2026-04-10 Perplexity Citation + Comprehensive + LKB-Paris + IndependentVerification-01; 2026-04-12 Paper 10 Deep + Master Systematic Checklist + Updated Paper Assessment).*

**Scope:** Remediate substantive paper issues uncovered in the April review round. Separate from:
- Phase 5s (q-Serre sorry closure + Muger + FK axiom) — Lean formalization track
- Phase 6 (vestigial MC at scale) — compute track
- Phase 6 VerifiedStatistics — pipeline upgrade track

**Why a separate wave:** The issues fall into 4 categories:
1. **Post-parameter-correction stragglers** (Paper 1 Table 1, Paper 12 polariton values) — paper didn't get regenerated when constants.py was corrected
2. **Citation content errors** (Paper 3 Adler page, Paper 10 bibliography 4 issues, arXiv resolution) — beyond what `claims-reviewer` Layer 4 checks
3. **Lean content-meaningfulness** (`sixteen_convergence_full`, `dai_freed_spin_z4`) — theorems exist but encode nothing
4. **Textbook-fact errors in prose** (Paper 3 SO(4k) center, Paper 10 ℤ₁₆ in class D, Paper 10 "16 = 8 × 2")

These are **process gaps**, not just edits. The fix is both (a) do the paper edits and (b) close the process gaps so similar issues don't land in the next round.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read `temporary/working-docs/reviews/papers/2026-04-12-Perplexity/IndependentVerification-02.md` — authoritative findings
> 3. Read agent definitions: `.claude/plugins/physics-qa/agents/claims-reviewer.md`, `.claude/plugins/physics-qa/agents/figure-reviewer.md`
> 4. Do NOT modify Paper 6 to indicate MC crashed status — roadmap tracks this, paper should reflect post-MC-completion state (see Phase 4/5 roadmaps)

---

## Track A — Paper 1 Revision (Parameter Correction Propagation)

### Wave 1 — Table 1 regeneration [Pipeline: Stages 1, 2, 3, 6, 7, 10]

**2026-04-13 — scope expanded after discovering a provenance-grounded pipeline bug.**
What was originally "rerun transonic solver, update table" turned out to involve a
dimensional bug in `compute_dissipative_correction` that has been present since the
function was first committed (`d72f197`). The bug: treats Beliaev-derived transport
coefficients γ₁, γ₂ (units [m²/s]) as if they were damping rates (units [s⁻¹]),
missing a k_H² = (κ/c_s)² conversion factor. This produces δ_diss off by a factor
of ~10⁷–10⁸ from the correct Beliaev prediction.

Four of the project's internal authorities all agree on the correct formula:
- Lean docstring `SecondOrderSK.lean:352`: δ_diss = Γ_H / κ
- `formulas.first_order_correction`: matches Lean
- `formulas.beliaev_transport_coefficients`: returns γ in [m²/s], docstring explicit
- `provenance.py:657` `PAPER_DEPENDENCIES`: *"Γ_H = (γ₁+γ₂)(κ/c_s)²"*

Only `transonic_background.compute_dissipative_correction` is wrong. **The identity
Γ_H = (γ₁+γ₂) k_H² has no Lean theorem** — that is the root cause: without a Lean
anchor, a Python-layer dimensional mistake never tripped a validation check. Tests
pass because they use hand-picked γ values and only assert `|δ_diss| < 0.1`, which
any formula satisfies for small inputs.

**Original problem (parameter propagation):**
Paper 1 Table 1 values were computed against a pre-correction parameter set. Current pipeline produces:

| Platform | Quantity | Paper | Current | Δ |
|----------|----------|-------|---------|---|
| Steinhauer | c_s (mm/s) | 0.46 | 0.5476 | 19.0% |
| Steinhauer | ξ (μm) | 1.57 | 1.3344 | 15.0% |
| Heidelberg | c_s (mm/s) | 3.37 | 3.9194 | 16.3% |
| Heidelberg | ξ (μm) | 0.48 | 0.4159 | 13.4% |
| Trento | c_s (mm/s) | 1.83 | 2.1848 | 19.4% |
| Trento | ξ (μm) | 1.51 | 1.2644 | 16.3% |

All 6 rows outside 0.5% tolerance. Also:
- Inline `a_s = 5.77 nm = 109 a₀` (old) → `5.31 nm = 100.4 a₀` (current, van Kempen 2002)
- Figures 1–4 derived from these parameters need regeneration

**Deliverables — split into 4 sub-waves:**

#### Wave 1a — Fix `compute_dissipative_correction` dimensional bug [Pipeline: Stage 2]
- [ ] Edit `src/core/transonic_background.py:compute_dissipative_correction`:
  introduce `k_H_sq = (kappa / cs)**2`; set `Gamma_H = (gamma_1 + gamma_2) * k_H_sq`;
  call `first_order_correction(Gamma_H, kappa)`.
- [ ] Replace the contradictory inline comment "γ₁, γ₂ here have units [s⁻¹]" with
  the correct "γ₁, γ₂ in [m²/s] (EFT Lagrangian units); Γ_H = (γ₁+γ₂)(κ/c_s)² gives the damping rate".
- [ ] Remove the `hbar` local variable (unused, set but never referenced in the function).

#### Wave 1a — Fix `compute_dissipative_correction` dimensional bug [Pipeline: Stage 2] — DONE 2026-04-13
- [x] Edit `src/core/transonic_background.py:compute_dissipative_correction`:
  introduced `k_H_sq = (kappa / cs)**2`, `Gamma_H = (gamma_1 + gamma_2) * k_H_sq`, call
  `first_order_correction(Gamma_H, kappa)`. Exposed `Gamma_H` and `k_H_sq` in return dict.
- [x] Rewrote docstring to be internally consistent; removed contradictory inline comment
  that claimed γ₁, γ₂ were in [s⁻¹] while docstring said [m²/s].
- [x] Removed unused `hbar` local variable.
- [x] Fixed the demo `__main__` block, which was passing `gamma_beliaev` (units [s⁻¹]) as
  `gamma_1` (units [m²/s]) — replaced with `beliaev_transport_coefficients(...)`.

#### Wave 1b — Ground the identification in Lean [Pipeline: Stage 3] — DONE 2026-04-13
- [x] Added to `lean/SKEFTHawking/SecondOrderSK.lean` (Phase 5u block near the end):
  - `noncomputable def GammaH (γ₁ γ₂ κ c_s : ℝ) : ℝ := (γ₁ + γ₂) * (κ / c_s) ^ 2`
  - `theorem gammaH_def` (rfl-provable definitional identity)
  - `theorem gammaH_via_kH` (alternative factored form via `k_H = κ/c_s`)
  - `theorem gammaH_nonneg` (positivity under γ₁, γ₂ ≥ 0)
  - `noncomputable def deltaDissFromTransport (γ₁ γ₂ κ c_s : ℝ) : ℝ := GammaH γ₁ γ₂ κ c_s / κ`
  - `theorem deltaDissFromTransport_eq` (closed form: `(γ₁+γ₂) · κ / c_s²`)
  - `theorem deltaDissFromTransport_zero_iff` (vanishes iff γ₁+γ₂ = 0)
- [x] Updated `formulas.first_order_correction` docstring to cite all new theorems as
  Lean anchors for the full chain.
- Note: NOT built via `lake build` today (parallel Lean session active on Uqsl3Hopf F01;
  Lean 4.29 upgrade produced 3 files with build errors elsewhere). All additions are
  `rfl` / `ring` / `positivity` / `field_simp` proofs — no heavy elaboration risk.
  (UPDATE 2026-04-14: Uqsl3Hopf F01 parallel session concluded — Uqsl3Hopf now 0 sorry
  with Bialgebra + HopfAlgebra typeclass instances wired; full SKEFTHawking package
  builds clean no-cache. See Phase 5s Wave 8 / Phase 5i Wave 2 for details.)

#### Wave 1c — Test coverage for the Beliaev→transport→correction chain [Pipeline: Stage 6] — DONE 2026-04-13
- [x] Added `tests/test_transonic_background.py::TestBeliaevChainConsistency` with 8 tests:
  - `test_Gamma_H_equals_Gamma_Bel[×3 platforms]` — catches the exact dimensional bug by
    verifying Γ_H from transport chain = Γ_Bel direct.
  - `test_delta_diss_equals_Gamma_Bel_over_kappa[×3 platforms]` — end-to-end Lean-formula match.
  - `test_gamma_H_formula_identity` — bare Γ_H = (γ₁+γ₂)·(κ/c_s)² identity at float precision.
  - `test_delta_diss_physical_magnitude_steinhauer` — asserts `1e-7 < δ_diss < 1e-3` for
    Beliaev regime (tightens the prior `< 0.1` bound that let the bug persist).
- [x] Fixed 2 pre-existing tests (`test_correction_small`, `test_dispersive_vs_dissipative_scaling`)
  that passed only because of the bug — they used dimensionally-wrong γ values. Updated to
  Beliaev-scale γ (~10⁻¹² m²/s).
- Result: 20/20 tests in `test_transonic_background.py` pass.

#### Wave 1d — Regenerate paper Table 1 + body + figures [Pipeline: Stages 7, 8, 10] — DONE 2026-04-13
- [x] Rerun transonic solver with bugfix. Table 1 regenerated for all 3 platforms.
- [x] Updated `papers/paper1_first_order/paper_draft.tex` Table 1: c_s (0.55, 3.92, 2.18);
  ξ (1.33, 0.42, 1.26); κ/T_H unchanged to displayed precision; δ_diss row now labeled
  "(Beliaev, T=0)" with values (2.4×10⁻⁵, 1.6×10⁻³, 1.4×10⁻⁵).
- [x] Inline `a_s = 5.31 nm (100.4 a₀)` — already current, no change needed.
- [x] Added κ profile-dependence main-text paragraph (tanh ≈ 4.8 s⁻¹ vs Steinhauer step ≈ 290 s⁻¹).
- [x] Rewrote eq:hawking_damping to show explicit $(\kappa/c_s)^2$ factor, citing the new
  Lean theorems (`GammaH`, `gammaH_def`, `deltaDissFromTransport_eq`).
- [x] Rewrote γ₁/damping-regime paragraph (§ 4 around line 290) to explicitly present
  Beliaev vs Zaremba regimes with dimensionally-consistent formulas. Post-claims-reviewer
  feedback: fixed Zaremba paragraph to use rate convention (Γ_H in [s⁻¹]) consistent with
  the Lean formula `δ_diss = Γ_H/κ`, rather than mixing rate and transport-coefficient units.
- [x] Updated spin-sonic enhancement subsection (§ 4.2) to show both regime outcomes.
- [x] Rerun `scripts/review_figures.py` (also fixed a pre-existing NameError on
  `fig_fk_spectrum` in `run_structural_checks`). 76 PNGs regenerated.
- [x] Copied regenerated fig1/fig2/fig4 to `papers/paper1_first_order/figures/`.
- [x] Re-ran `physics-qa:claims-reviewer` against Paper 1: all Table 1 values pass within
  1% (was 16–20% off pre-bugfix). Zero FAIL on numerical claims. New Lean theorems all verified present.
- [x] `physics-qa:figure-reviewer` on regenerated fig1/fig2/fig4 — run 2026-04-13.
  Verdict: **fig2 FAIL (blocks paper submission)**, fig1 PASS, fig4 WARN (passes with minor notes).
  Report: `papers/paper1_first_order/figures/figure_review_report.json`.
  Root cause found in `src/core/visualizations.py:fig_correction_hierarchy` — function
  **re-computes** δ_diss locally via `gamma_bel = sqrt(n·a³)·ω_H²/c_s` with a hardcoded
  `enhancement = 100.0` for Trento, **bypassing the canonical pipeline**. This is a
  Pipeline Invariant 1/3 violation (visualizations.py must consume canonical physics from
  formulas.py / transonic_background, not re-implement it). The dimensional bugfix in
  `compute_dissipative_correction` did not propagate to this figure because the figure
  doesn't call that function. **Tracked as Wave 1e below.**
- Additional finding from figure-reviewer: for Heidelberg, post-bugfix δ_diss = 1.6×10⁻³
  exceeds δ_disp ≈ 7.3×10⁻⁵ by ~20×, **inverting the paper's claimed "δ_disp > δ_diss"
  hierarchy** for that platform. This is a genuine Beliaev-dominance signal that Paper 1's
  body text should reflect honestly — not a figure bug. Tracked as Wave 1f below.
- Residual items surfaced by claims-reviewer (addressed inline or tracked):
  - **Addressed**: eq:hawking_damping made explicit; Zaremba paragraph dimensional
    consistency; `__main__` demo bugfix; `review_figures.py` fig_fk_spectrum import.
  - **Tracked as Wave 22**: Paper 1 `CITATION_REGISTRY` reconciliation (11 bibkeys use
    `Author:Year`; registry uses `AuthorYear`; 4 entries missing entirely).

**Estimated LOE (original):** 3–5 hours — actual time ~5 h including discovery + bugfix + Lean + claims-review cycle
**Risk:** Low — purely computational
**Depends on:** None (no Lean or MC blocker)

#### Wave 1e — Refactor `fig_correction_hierarchy` to use canonical pipeline [Pipeline: Stage 8, Invariants 1 & 3]

**Problem (discovered 2026-04-13 by figure-reviewer):** `src/core/visualizations.py:fig_correction_hierarchy`
(lines 240–258) reimplements δ_diss computation locally instead of consuming
`compute_dissipative_correction`. Specifically:
- Uses Beliaev estimate `gamma_bel = sqrt(n·a³)·ω_H²/c_s` directly
- Applies a hardcoded `enhancement = 100.0` multiplier for Trento
- Never calls `compute_dissipative_correction` — so Wave 1a's k_H² bugfix never reaches this figure

This is a Pipeline Invariant 1 + 3 violation: formulas live in `formulas.py`,
visualizations must consume them. The same class of bug as Wave 1a (locally
reimplementing a computation that diverges from the canonical chain).

**Deliverables — all DONE 2026-04-13:**
- [x] Refactored `fig_correction_hierarchy` to call `beliaev_transport_coefficients` +
  `compute_dissipative_correction` canonically.
- [x] Removed the hardcoded `enhancement = 100.0` for Trento. Spin-sonic enhancement
  stays in `fig_spin_sonic_enhancement` (fig4), where it belongs; fig2 shows the
  platform baseline.
- [x] Y-axis range now auto-sized from actual data span (covers 10⁻¹⁰ to 10⁰
  including Heidelberg's δ_diss = 1.6×10⁻³ and the sensitivity bands at 10⁻¹/10⁻²/10⁻³).
- [x] Cross-term bars render as short bars near floor; tiny positive sentinel (1e-20)
  prevents silent drop on log axes for zero values.
- [x] Sensitivity-band lines now added as named `go.Scatter` traces — appear in legend
  instead of as un-labeled annotations.
- [x] Regenerated fig2, copied to `papers/paper1_first_order/figures/`.
- [x] Re-ran `physics-qa:figure-reviewer` on fig2 — **PASS**. All three platforms match
  pipeline values exactly (Steinhauer 2.38e-5, Heidelberg 1.59e-3, Trento 1.41e-5).

**Actual LOE:** ~45 min (vs estimate 1-2 h)
**Risk:** Low — landed clean

**Follow-up / regression prevention (tracked as Wave 21 Lean-grounding audit):**
A test/check that every `src/core/visualizations.py:fig_*` function consumes
pipeline-computed physics (rather than re-implementing formulas) would prevent this class
of bug from re-entering. Same root cause as Wave 1a — local reimplementation of a
canonical computation drifts from the canonical source.

#### Wave 1f — Paper 1 hierarchy claim honesty check [Pipeline: Stage 10]

**Problem (discovered 2026-04-13 by figure-reviewer):** Post-bugfix pipeline values show:

| Platform | δ_disp | δ_diss | Hierarchy |
|----------|--------|--------|-----------|
| Steinhauer | 8.5e-5 | 2.4e-5 | δ_disp > δ_diss ✓ (paper's claim holds) |
| Heidelberg | 7.3e-5 | 1.6e-3 | **δ_diss > δ_disp ✗** (paper's claim fails) |
| Trento | 9.9e-5 | 1.4e-5 | δ_disp > δ_diss ✓ |

Heidelberg shows δ_diss ~20× larger than δ_disp — the Beliaev damping rate is unusually
large at Heidelberg's higher κ = 102 s⁻¹, because Γ_Bel ~ κ² scaling amplifies its effect.
This is genuine physics, not a bug.

Paper 1 body text claims a universal "δ_disp dominates" hierarchy (this is stated as
"dispersive effects dominate the corrections" and is a key narrative point). With
post-bugfix values, **Heidelberg is a platform where the opposite is true**.

**Deliverables — all DONE 2026-04-13:**
- [x] Abstract: rewrote platform breakdown — Steinhauer 10⁻⁵–10⁻⁴, Heidelberg 10⁻³–10⁻²
  (detection target, δ_diss > δ_disp by order of magnitude), Trento spin-sonic O(10⁻¹).
- [x] Table 1 caption: clarified δ_diss is Beliaev (T=0) regime; explained non-monotonic
  κ-dependence via Γ_Bel ∝ κ² scaling → δ_diss ∝ κ/c_s.
- [x] Fig2 caption: notes the platform-dependent hierarchy explicitly; labels Heidelberg
  as the detection target at the 10⁻³ sensitivity threshold.
- [x] "Experimental reach" paragraph in §IV: split into Steinhauer/Trento-baseline
  (below sensitivity) vs. Heidelberg (at sensitivity); explains why Heidelberg is the
  cleanest detection target (δ_diss unambiguously dominates δ_disp there).
- [x] Conclusions list items 1-3: rewrote as platform-by-platform disclosure instead of
  universal hierarchy claim; added Heidelberg as #1 detection target.

Net effect on paper thesis: **strengthens, not weakens**. The original "δ_disp dominates"
narrative discouraged experimentalists from using Heidelberg to test dissipative
corrections (since it was implicitly framed as dispersive-dominated). The corrected
narrative reveals Heidelberg is the *best* testbed because δ_diss > δ_disp there by ~20×,
making any observed correction cleanly attributable to dissipation.

**Actual LOE:** ~45 min

### Wave 2 — Paper 1 Son:2002 framing [Pipeline: Stage 10]

**Problem:** Paper 1 describes Son:2002 (hep-ph/0204199) as "Galilean-invariant / nonrelativistic", but the paper is titled *"Low-Energy Quantum Effective Action for **Relativistic** Superfluids"*.

**State:** Bibitem already extended to include Endlich et al. 2013 as co-citation (fixes partial attribution). Body text NOT yet rewritten.

**Deliverables:**
- [x] Paper 1 lines 57, 69 — rewritten to clarify Son:2002 is the *relativistic* EFT framework; non-relativistic Madelung adaptation follows Endlich \textit{et al.} (PRD 88, 105001, 2013). Line 130 "Galilean Invariance" left as-is — it refers to the axiom constraint on the non-relativistic action used in the paper, which is correctly Galilean-invariant. (2026-04-13)
- [x] Paper 2 line 448 — bibitem extended: added Son relativistic title and Endlich co-citation. (2026-04-13)

**Estimated LOE:** 30 minutes — DONE
**Risk:** Low

---

## Track B — Paper 12 Polariton Parameter Resolution

### Wave 3 — Resolve Falque κ primary-source disagreement [Pipeline: Stage 1 provenance]

**Problem — CRITICAL:** Two LLM readings of Falque PRL 135, 023401 (2025) disagree:
- `src/core/provenance.py:430–442` (LLM verified 2026-03-31): "Falque 2025 demonstrated polariton horizons with SLM **but did not report surface gravity κ**. Value 5e10 s⁻¹ is an order-of-magnitude estimate..."
- `temporary/working-docs/reviews/papers/2026-04-10-Perplexity/LKB-Paris-Polariton-Assessment.md` (2026-04-10): "The measured surface gravity values are κ = 0.07 ps⁻¹ (smooth), κ = 0.08 ps⁻¹ (smooth), and κ = 0.11 ps⁻¹ (steep)."

**Resolution path:**
- [x] Third-LLM re-read of Falque PRL 135, 023401 full text (arXiv:2311.01392v2 HTML), 2026-04-13.
- [x] Ground truth: **Falque DOES report κ.** Three measured values confirmed verbatim
  in the paper:
  - κ = 0.07 ps⁻¹ = 7×10¹⁰ s⁻¹ (smooth horizon, red trace, Fig. 2 caption / §IV.1)
  - κ = 0.08 ps⁻¹ = 8×10¹⁰ s⁻¹ (smooth horizon, purple trace, Fig. 2 caption)
  - κ = 0.11 ps⁻¹ = 1.1×10¹¹ s⁻¹ (steep horizon, §IV.2)
  Also confirmed: c_s ≈ 0.40 μm/ps (§IV.1), ξ ≈ 3.4 μm upstream / 4.0 μm downstream.
- [x] `provenance.py:Paris_long.kappa` updated 2026-04-13: detail now documents the
  three measured values, flags current 5e10 s⁻¹ as an **underestimate** (below
  Falque's measured range), advances `llm_verified_date` to 2026-04-13, and
  documents the root cause of the prior error (abstract-only reading).
- [ ] Wave 4 onward: decide whether to adopt 7e10 (smooth-horizon default) or 1.1e11
  (steep-horizon maximum) for `Paris_long.kappa` in constants.py; propagate to Paper 12
  numerics (T_H, D, G(ω)).

**Process lesson** filed as Phase 5u Wave 18 (cross-LLM provenance consistency check):
the conflict between the 2026-03-31 provenance entry and the 2026-04-10 LKB audit went
undetected for three days. A systematic cross-check would have caught it immediately.

**Actual LOE:** ~30 min (LLM re-verification + provenance update).
**Risk:** Medium → Resolved. Downstream revisions in Paper 12 now unblocked (Waves 4-6).

### Wave 4 — Adopt Falque values in constants.py + Paper 12 propagation [Pipeline: Stages 1, 2, 10] — DONE 2026-04-13

**Problem:** After Wave 3 verified Falque's measured values (c_s=0.40 μm/ps, ξ=3.4 μm, κ ∈ {0.07, 0.08, 0.11} ps⁻¹), constants.py still had the pre-verification values (c_s=5e5 m/s "representative midpoint", ξ=3e-6 m "derived", κ=5e10 "projected — assumed Falque didn't report"). Paper 12 body used those stale values plus a hardcoded "near-adiabatic D=0.3-0.5" claim.

**Decision rationale** (2026-04-13, documented here for future reference):

We had to pick one κ value as the constants.py default. Three candidates:

| Candidate | T_H | D | π D²/6 | Analysis |
|-----------|-----|---|--------|----------|
| 7×10¹⁰ (smooth, red) | 85 mK | 0.60 | 0.19 | Baseline, matches Falque's most prominently reported config |
| 8×10¹⁰ (smooth, purple) | 97 mK | 0.68 | 0.24 | Middle smooth — no physical preference |
| 1.1×10¹¹ (steep) | 134 mK | 0.93 | 0.46 | Maximum T_H but D > 0.9 → non-perturbative dispersive |

**We chose 7×10¹⁰ s⁻¹ (smooth-horizon, red trace) as the default** for four reasons:
1. **Primary-source fidelity.** The red trace is what Falque reports first and most prominently in Figure 2 and Section IV.1 of the PRL. Adopting this is the cleanest LLM-verifiable anchor.
2. **EFT perturbativity.** D=0.60 keeps the paper's leading-order SK-EFT narrative defensible (−π D²/6 = −19%). Steep horizon's D=0.93 gives a 46% correction, requiring a separate narrative rewrite acknowledging non-perturbative dispersive physics — scope creep for this session.
3. **Paper 12's existing framing.** The abstract and body emphasize the stimulated-Hawking gain spectrum as a perturbative SK-EFT result; steep-horizon as the default would force rewriting the entire theoretical motivation.
4. **Conservative detection claim.** 85 mK (smooth) vs. 134 mK (steep) — starting from the smooth baseline keeps the detection claim realistic without overstating. The steep-horizon reach is still reported in Paper 12 as the platform's upper bound.

**We explicitly REJECT the middle 8×10¹⁰ (purple trace)** because picking an average has no physical justification over picking the most prominently reported value.

**We explicitly report the full 7–11×10¹⁰ range in Paper 12** (new Table 2) so experimentalists see the platform's demonstrated reach; this also transparently acknowledges that going to steep horizon is a real experimental option.

**Orthogonal constants.py update:** `Paris_standard.tau_cav` was 3 ps (projected); Falque's actual cavity is τ ≈ 8 ps (γ ≈ 1.2e11 s⁻¹ → ℏγ ≈ 80 μeV as reported). Changed Paris_standard to match Falque actual, re-categorized Paris_long/ultralong as projected future configurations.

**Deliverables — all DONE 2026-04-13:**
- [x] `src/core/constants.py:POLARITON_PLATFORMS['Paris_long']`: `c_s`=5e5→4e5, `xi`=3e-6→3.4e-6, `kappa`=5e10→7e10.
- [x] Same updates applied to `Paris_ultralong` (same SLM profile, different cavity lifetime).
- [x] `Paris_standard`: updated to match Falque actual — `tau_cav`=3e-12→8e-12, `Gamma_pol`=3.33e11→1.25e11, plus same c_s/ξ/κ updates. Description re-labeled to "matches Falque 2025 actual".
- [x] New module-level constant `FALQUE_STEEP_HORIZON_KAPPA = 1.1e11` for the upper-bound reach; used in Paper 12 body text only, not a default in POLARITON_PLATFORMS.
- [x] Header comment documents the rationale inline (future readers see it at the point of use).
- [x] `src/core/provenance.py` entries updated for `Paris_long.c_s`, `Paris_long.xi`, `Paris_long.kappa`: all tier updated to MEASURED (from EXTRACTED/PROJECTED), `llm_verified_date` advanced to 2026-04-13, detail documents the decision history with both prior (2026-03-31/04-05) and current (2026-04-13) readings.
- [x] Paper 12 abstract rewritten: explicit Falque-measured values, smooth/steep range, dispersive-regime disclosure for steep.
- [x] Paper 12 §"System parameters" Table 2 (was Table 1): two-column smooth vs. steep; footnote noting steep is non-perturbative.
- [x] Paper 12 §"Bogoliubov scattering" D≈0.3 claim → D≈0.60 smooth / 0.93 steep with the correct −π D²/6 dispersive corrections.
- [x] Paper 12 §"Platform Comparison" table: T_H 61 mK → 85 mK across rows; added steep-horizon reach row (134 mK); corrected Paris_standard κτ for the 8 ps actual cavity.
- [x] Paper 12 §"Driven-Dissipative Considerations" noise-temperature paragraph: T_noise 1.3 K → 0.81 K (at c_s=4e5); T_H 61 mK → 85 mK.
- [x] Paper 12 §"Impact" paragraph: c_s correction from 1.0 → 0.40 μm/ps (was 1.0 → 0.5).

**Numerical consistency verification** (run 2026-04-13 after changes):
```
Paris_long: c_s=4.00e+05 xi=3.40e-06 kappa=7.00e+10
  D=0.595, T_H=85.1 mK, dispersive_corr=-pi/6*D²=-0.185
Steep-horizon reach: kappa=1.10e+11, D=0.935, T_H=133.7 mK, dispersive=-0.458
```

**Not yet done:**
- [ ] Regenerate Paper 12's figures (fig_stimulated_hawking_spectrum, etc.) to pick up new κ, c_s — dispatch `scripts/review_figures.py` and run `physics-qa:figure-reviewer` on results. Same sequencing rule: figures first, reviewer after.
- [ ] Re-run `physics-qa:claims-reviewer` against Paper 12 to catch any residual stale values in sections not touched here (e.g., detection SNR numbers, QNM frequencies).
- [ ] Phase 5u Wave 5 (programmable attribution) and Wave 6 (inside-horizon wording) were not touched in this pass; they're independent edits still open.

**Actual LOE:** ~90 min (~60 min constants/provenance, ~30 min Paper 12 propagation, documentation).
**Risk:** Low — all numerical updates verified at the Python level; Paper 12 remains a draft so the narrative adjustment landed before any external claim was published.

### Wave 5 — Paper 12 "programmable" attribution [Pipeline: Stage 10]

**Problem:** "Programmable" appears in Giacobino & Jacquet lecture notes (arXiv:2512.14194), not in Falque PRL body. Falque uses "tunable" / "all-optical control".

**Deliverables:**
- [ ] Paper 12 lines 21, 56, 295 — either change "programmable" → "all-optically tunable" (Falque's language), OR add `\cite{Giacobino2025}` (arXiv:2512.14194) alongside Falque
- [ ] If adding Giacobino2025: add bibitem
- [ ] Optional: add other LKB ecosystem citations per LKB audit (Gil de Olivera 2025, Claude 2022, Guerrero 2025) — lower priority

**Estimated LOE:** 30 min

### Wave 6 — Paper 12 "inside horizon" phrasing [Pipeline: Stage 10]

**Problem:** Paper 12 line 58–59 says "inside the horizon"; Falque uses "in the supersonic regions".

**Deliverables:**
- [ ] Paper 12 line 58 — change "inside the horizon" → "in the supersonic (post-horizon) region"

**Estimated LOE:** 5 min
**Risk:** None

---

## Track C — Textbook-Fact Errors

### Wave 7 — Paper 3 SO(4k) center [Pipeline: Stage 10]

**Problem:** Paper 3 line 114 says "Z₂ × Z₂ for SO(4k)". Correct: center of SO(4k) is Z₂. Z₂ × Z₂ is center of **Spin**(4k).

**Deliverables:**
- [x] Paper 3 line 114 — rewritten to separate SO-group centers (Z₂ for SO(2k)) from Spin-group centers (Z₂ for Spin(2k+1), Z₄ for Spin(4k+2), Z₂×Z₂ for Spin(4k)). (2026-04-13)

**Estimated LOE:** 5 min
**Risk:** None

### Wave 8 — Paper 10 "time-reversal" for ℤ₁₆ [Pipeline: Stage 10]

**Problem:** Paper 10 lines 197–198 say "topological superconductors with time-reversal symmetry have a ℤ₁₆ classification". Class D has NO time-reversal (particle-hole only). Kitaev's ℤ₁₆ (16-fold way) is specifically for 2D class D free-fermion ℤ reduced to interacting ℤ₁₆.

**Deliverables:**
- [x] Paper 10 lines 196–200 — rewritten: "2D topological superconductors in symmetry class D (particle-hole symmetry, no time-reversal) admit a free-fermion ℤ classification that reduces to ℤ₁₆ under interactions." (2026-04-13)
- [x] Added `[FidkowskiKitaev2010]` bibitem (arXiv:0904.2197, PRB 81, 134509) for the interacting ℤ₁₆ reduction. (2026-04-13)

**Estimated LOE:** 20 min — DONE
**Risk:** Low (textbook-level correction)

### Wave 9 — Paper 10 "16 = 8 × 2" numerology [Pipeline: Stage 10]

**Problem:** Paper 10 presents "16 = 8 × 2, where 8 is the Bott period and 2 is the Pfaffian factor" as the unifying physical insight. Bott period is 8 for π_n(O) (real K-theory) — correct. But "2 is the Pfaffian factor" is not a theorem; "16 = 8 × 2 connects all four 16s" is an aesthetic heuristic, not a derivation. Wang 2024 connects them via the Smith homomorphism, not via Bott × Pfaffian.

**Deliverables:**
- [x] Paper 10 "16 Convergence" section — "16 = 8 × 2" numerology removed; replaced with Wang 2024 Smith homomorphism framing: "The four appearances of 16 are connected through the algebraic topology of spin structures in four dimensions: Wang (2024) establishes the relationship between the Rokhlin bound, the ℤ₁₆ anomaly, and the SM fermion count via the string bordism ℤ₂₄ class and the associated Smith homomorphism. The relationship to the Kitaev ℤ₁₆ classification is suggestive but has not been formalized here." (2026-04-13)

**Estimated LOE:** 15 min — DONE

---

## Track D — Paper 10 Bibliography

### Wave 10 — Bibliography errors [Pipeline: Stage 10]

**Problem:** Paper 10 bibliography has multiple verifiable errors.

**Deliverables:**
- [x] ABP1967 page 256 → **271** and title `Structure of the spin cobordism ring` added to bibitem. (2026-04-13)
- [x] Stolz1993 removed entirely — option (a) chosen. ABP1967 + BeaudryCampbell cover the algebraic topology needed; the Stolz PSC work is tangential to A(1) Ext / Rokhlin and the cited coordinates (Math. Ann. 296, 685) could not be verified. BeaudryCampbell now cited at Section 6 alongside ABP1967 (was orphan bibitem before). (2026-04-13)
- [x] BeaudryCampbell page 1 → **89** (also added title and end page 136 for completeness). (2026-04-13)
- [x] Kitaev2009 end page added (22–30). (2026-04-13)
- [x] `[diFrancesco1997]` *Conformal Field Theory* added for CFT/Casimir physical interpretation; line 138 reworded to distinguish analytic (Rademacher) from physical (diFrancesco + framing anomaly) origins of the 24 in the modular phase. (2026-04-13)
- [ ] `[FreedHopkins2021]` — NOT YET ADDED. Wang 2024 cites this for framing anomaly context. Consider adding in a future revision if referee requests deeper context. Low priority since the Wang citation already covers the framing-anomaly argument we use.

**Estimated LOE:** 30 min — DONE (except FreedHopkins addition, marked as future)
**Risk:** Low

### Wave 11 — Paper 3 Adler page [Pipeline: Stage 10]

**Problem:** Paper 3 line 339 cites Adler et al. 2024, Nature 636, **87**. Correct first page per DOI 10.1038/s41586-024-08188-0 is **80** (pp. 80–85).

**Deliverables:**
- [x] Paper 3 line 339 — changed `87` → `80`. (2026-04-13)

**Estimated LOE:** 1 min — DONE

---

## Track E — Lean Content-Meaningfulness

### Wave 12 — `sixteen_convergence_full` structural tautology [Pipeline: Stages 3, 10]

**Problem:** `RokhlinBridge.lean:88` theorem conclusion has four conjuncts:
1. `(∑ f, components f) = 16` — substantive (sum over SM fermions)
2. `(16 : ZMod 16) = 0` — `decide`-trivial
3. `∀ M, (16 : ℤ) ∣ M.signature` — literal echo of hypothesis `h_rokhlin`
4. `(∑ f, components f) = (16 : ℕ)` — re-typed version of #1

Proof: `⟨total_components_with_nu_R, by decide, h_rokhlin, total_components_with_nu_R⟩`. Theorem does NOT prove connection between the four 16s — only that 16 appears in four contexts.

**Deliverables:**
- [x] Option (b) chosen: comprehensive docstring added to `sixteen_convergence_full` in `RokhlinBridge.lean` disclosing the structural tautology — three of four conjuncts are either decide-trivial, hypothesis echoes, or retypes of the first. Docstring explicitly states the theorem enumerates but does NOT unify, that the physical connection is Wang (2024) external input, and directs papers to use "formally recorded" not "formally verified convergence". (2026-04-13)
- [x] Paper 10 "16 Convergence" section rewritten — now uses "formally recorded" language and the Wang Smith-homomorphism framing. (2026-04-13)

**Estimated LOE:** 30 min — DONE via option (b)
**Risk:** None (docstring-only change, no proof mods)

### Wave 13 — `dai_freed_spin_z4` Equiv.refl placeholder [Pipeline: Stages 3, 10]

**Problem:** `Z16AnomalyComputation.lean:39` — theorem statement is `∃ (φ : ZMod 16 ≃ ZMod 16), Function.Bijective φ`. Proves nothing about Dai-Freed spin bordism groups; just that a bijection exists on a finite set (trivially true via `Equiv.refl`).

**Deliverables:**
- [x] Comprehensive docstring added to `dai_freed_spin_z4` in `Z16AnomalyComputation.lean` — labels it PLACEHOLDER, explains the statement is trivially true (Equiv.refl), states the actual Ω₅^{Spin^{ℤ₄}} ≅ ℤ₁₆ cobordism identification is external (García-Etxebarria–Montero / Dai-Freed), and instructs papers to describe it as an external hypothesis, not a Lean-verified fact. (2026-04-13)
- [x] Paper 8 line 431 reworded — "former ℤ₁₆ cobordism axiom discharged (tautological)" replaced with explicit "converted to trivially-true placeholder theorem (dai_freed_spin_z4) pending Mathlib cobordism theory; the cobordism computation is an external input, as standard in the ℤ₁₆ literature." (2026-04-13)
- [N/A] Paper 9, 10 — no claims of "Lean-verified Dai-Freed theorem" found; both papers already cite GarciaEtxebarria2019 as the source of the ℤ₁₆ bordism identification. Paper 9 §SPT Stacking formalizes the GROUP STRUCTURE of ℤ₁₆ stacking (legitimately proved by `decide`), not the cobordism identification. No updates needed there.

**Estimated LOE:** 15 min — DONE
**Risk:** None

---

## Track F — Agent Checklist Upgrades (Process Improvement)

### Wave 14 — claims-reviewer Layer 2 extensions [Pipeline: N/A — infrastructure]

**Problem:** Layer 2 currently checks theorem existence and absence of `sorry`. Does not check content meaningfulness.

**Deliverables:**
- [ ] Add **"vacuous conjunct" detector**: For each theorem cited in a paper, inspect the Lean source and check if the conclusion contains:
  - (a) `True` as a top-level term
  - (b) conjuncts that are literal echoes of hypotheses
  - (c) conjuncts that are `decide`/`rfl`-trivial AND no other non-trivial conjunct
- [ ] Add **"name / content match" detector**: For each theorem cited as "verification of X", check the Lean statement body mentions X (identifiers matching).
- [ ] Update `.claude/plugins/physics-qa/agents/claims-reviewer.md` to document these checks.

**Estimated LOE:** 2 h
**Risk:** Low

### Wave 15 — claims-reviewer Layer 4 extensions (citation integrity) [Pipeline: N/A]

**Problem:** Layer 4 only checks presence in CITATION_REGISTRY, not content correctness.

**Deliverables:**
- [ ] Layer 4a — **bibitem-registry consistency**: For each `\bibitem`, verify title / authors / journal / volume / page / year / DOI all match the registry entry verbatim.
- [ ] Layer 4b — **DOI resolution**: For each registry entry with DOI, fetch metadata via doi.org and compare against registry.
- [ ] Layer 4c — **arXiv resolution**: For each `arXiv:XXXX.XXXXX`, fetch arxiv.org metadata and compare. **This would have caught the Tier 1 catastrophic errors in one pass.**
- [ ] Update `.claude/plugins/physics-qa/agents/claims-reviewer.md`.

**Estimated LOE:** 4 h
**Risk:** Medium (depends on reliable API access)

### Wave 16 — claims-reviewer Layer 3b (prose-provenance consistency) [Pipeline: N/A]

**Deliverables:**
- [ ] For each parameter cited in a paper, compare paper's epistemic phrasing ("measured", "projected", "confirmed by N measurements") against `PARAMETER_PROVENANCE.tier` and `detail`. Flag mismatches.
- [ ] Update agent spec.

**Estimated LOE:** 2 h

### Wave 17 — claims-reviewer Layer 5 extensions (textbook facts) [Pipeline: N/A]

**Problem:** Layer 5 targets feasibility claims; misses textbook mathematical facts in prose (Paper 3 SO(4k), Paper 10 class D ℤ₁₆).

**Deliverables:**
- [ ] Add **"Referenced Textbook Facts"** sub-layer: extract mathematical factual claims that are not derived from formulas.py but presented as fact. For each, require either a `\cite{}` to authoritative source OR a Lean theorem. Missing support → WARN.

**Estimated LOE:** 3 h
**Risk:** Medium — hard to automate the extraction; may require LLM-driven classification.

### Wave 18 — NEW Layer 8: Cross-LLM provenance consistency [Pipeline: N/A]

**Problem:** `provenance.py` said Falque did not report κ; LKB audit said Falque reports κ = 0.07–0.11 ps⁻¹. No mechanism to detect this conflict.

**Deliverables:**
- [ ] For each `PARAMETER_PROVENANCE` entry with a `source` field citing an arXiv/DOI, search `Lit-Search/` and `temporary/working-docs/reviews/` for docs referencing the same source. Cross-check their claims.
- [ ] Flag conflicts as WARN with both texts quoted.

**Estimated LOE:** 2 h

### Wave 19 — NEW Layer 9: Constants-source fidelity [Pipeline: N/A]

**Deliverables:**
- [ ] For each parameter value in `constants.py`, compare against the specific values reported in its provenance `source` (when extractable).
- [ ] Flag WARN when constant value differs from primary source value without explicit tier explanation.

**Estimated LOE:** 2 h

### Wave 20 — NEW Invariant 11: constants.py change invalidates claims_review [Pipeline: Stage 12]

**Deliverables:**
- [ ] Add to Pipeline Invariants: "When `src/core/constants.py` changes, all `papers/paper*/claims_review.json` files are invalidated and claims-reviewer MUST be re-run against all papers before the next submission gate."
- [ ] Add git hook or validate.py check: compare `constants.py` mtime vs each `claims_review.json` mtime. Claims review older than constants change = FAIL.

**Estimated LOE:** 1 h

### Wave 22 — Paper 1 CITATION_REGISTRY reconciliation [Pipeline: Stage 10]

**Problem (discovered by Phase 5u Wave 1d claims-reviewer on 2026-04-13):**
Paper 1 uses bibkeys in `Author:Year` convention (e.g., `Steinhauer:2019`,
`Son:2002`, `Zaremba:1999`). `src/core/citations.py` uses `AuthorYear`
(e.g., `Steinhauer2016`). Additionally, the year values themselves differ in
some cases (`Steinhauer:2019` vs registry `Steinhauer2016` — these are DIFFERENT
papers), suggesting the paper cites later/earlier Steinhauer results not yet
registered. Four Paper 1 bibkeys have no registry entry at all under either
convention: `Jacobson:1996`, `Son:2002`, `Coutant:2014`, `Zaremba:1999`.

**Deliverables:**
- [ ] For each of Paper 1's 11 bibitems (`Berti:2025`, `Corley:1996`,
  `Coutant:2014`, `Crossley:2017`, `Hawking:1974`, `Jacobson:1996`, `Jana:2020`,
  `Son:2002`, `Steinhauer:2019`, `Unruh:1981`, `Zaremba:1999`), resolve the
  primary source and add a matching entry in `CITATION_REGISTRY` with DOI
  where available. For cases where the registry already has a *different-year*
  entry under the same author (e.g., `Steinhauer2016` vs `Steinhauer:2019`),
  add both — they are different papers.
- [ ] Decide on a project-wide bibkey convention (`Author:Year` vs `AuthorYear`).
  Paper 1 uses the colon form; Papers 7, 8, 10, 12 use the no-colon form. Pick one.
- [ ] Once convention is chosen, sweep every paper and every registry key to
  enforce it; update claims-reviewer to check conformance.

**Estimated LOE:** 2 h (for Paper 1 alone); 4-6 h project-wide sweep
**Risk:** Low — mechanical; just takes time

---

### Wave 21 — NEW Invariant 12: Lean-grounding audit for formulas.py [Pipeline: Stage 12]

**Problem discovered 2026-04-13 (during Wave 1 investigation):** The δ_diss dimensional
bug in `compute_dissipative_correction` escaped detection for the project's entire
lifetime because the **identification** Γ_H = (γ₁+γ₂)(κ/c_s)² existed only in prose
(`provenance.py:657`, docstring comments) — it had no Lean theorem. Pipeline Invariant 4
says *"Every formula has a Lean theorem"*, but the project interpreted this as "every
function name in formulas.py appears in some Lean docstring", not as "every function's
computational content has a machine-checked Lean statement that could be cross-verified
against the Python implementation".

The distinction matters: the `first_order_correction` function had its Lean anchor
(`firstOrder_correction_zero_iff`) — but that theorem only states δ_diss=0 iff Γ_H=0.
The critical identification that converts EFT transport coefficients to the horizon
damping rate was entirely unformalized. A reviewer running "check that each formula
has a Lean theorem" would mark `first_order_correction` as grounded and move on,
never seeing the unit mismatch.

**Deliverables:**
- [ ] Add to Pipeline Invariant 4: "A function F in `formulas.py` is considered Lean-grounded
  only if (i) F has a `Lean:` line in its docstring citing a specific theorem name,
  (ii) the cited theorem exists in `lean/SKEFTHawking/*.lean`, and (iii) the theorem's
  statement logically implies the Python computation (not just mentions it). Specifically
  for identities that convert between unit conventions (e.g., EFT coefficients to damping
  rates), the identity itself must be formalized — a theorem about boundary conditions
  (e.g., 'vanishes iff input zero') is not sufficient."
- [ ] Add to `scripts/validate.py` a new check `lean_grounding_audit`: for each function
  in `formulas.py`, find its `Lean:` reference, resolve it in the Lean source, verify the
  theorem's conclusion mentions the function's output structure.
- [ ] One-time audit: sweep all ~137 functions in `formulas.py`, identify which have weak
  Lean anchors (existence-only, vanishing-only) vs. strong anchors (the formula identity
  itself). Results → `docs/validation/lean_grounding_audit.md`.
- [ ] Update `.claude/plugins/physics-qa/agents/claims-reviewer.md` Layer 2 to include this
  strength-of-anchor check.

**Estimated LOE:** 3-4 h for infrastructure + audit sweep
**Risk:** Medium — may uncover more Lean-anchoring gaps similar to the δ_diss bug

**Why this is HIGH VALUE:** The δ_diss bug is a canary. If it existed 9 orders of magnitude
off for the project's entire history, there are almost certainly other weakly-anchored
formulas where smaller bugs could hide. Finding them before submission is worth significant
investigation time.

---

## Track G — Paper 11 + Paper 14 integration of Phase 5e/5p new theorems [DONE 2026-04-15]

**Trigger:** Five PRs (#10–#14) merged 2026-04-15 added substantial new content (per-generator affine S², Müger center symmetric structure, det(S)≠0 → isMugerTrivial bridge, FPdim eigenvector + φ-triple-origin, D²(Z(C))=D²(C)² formula). Paper 11 (quantum group) and Paper 14 (braided MTC) were the natural homes for these results but their drafts predated the new theorems.

### Wave 23 — Paper 11 affine Hopf section update [Pipeline: Stage 10] — DONE 2026-04-15
- [x] Replaced "(pending Aristotle)" stale label on `Uqsl2AffineHopf.lean` Bialgebra/HopfAlgebra wiring (the wiring is now complete in Tranche E + Phase 5e Waves 7-8).
- [x] Added per-generator squared-antipode subsection: explains why no global `S² = Ad(K)` exists for affine ŝl₂ (rank-deficient Cartan), with the full rank-2 contradiction proof inline. Cross-references the (different) sl₃ correction at `Uqsl3Hopf.lean:3995`.
- [x] Updated theorem counts: `Uqsl2AffineHopf.lean` 4 → 201, `CoidealEmbedding.lean` 6 (zero sorry, was "pending Aristotle"), `RepUqFusion.lean` 14 (zero sorry, was "pending Aristotle").

### Wave 24 — Paper 14 abstract + contributions + new section [Pipeline: Stage 10] — DONE 2026-04-15
- [x] Updated abstract: stale counts (2237/130) → current (3021+/133); added Müger center / FPdim eigenvector / D²(Z(C))=D²(C)² formula claims; expanded Müger center mention to include `SymmetricCategory` instance.
- [x] Updated contributions list: added 3 new items (Müger center symmetric subcategory + Direction~1 bridge; FPdim eigenvector + φ-triple-origin; non-abelian Drinfeld-center dimension formula).
- [x] Added new full section `Müger Center, FPdim, and Drinfeld-Center Dimension Formula` between `SU(3)_k Fusion Categories` and `Temperley-Lieb Algebra and Jones-Wenzl Idempotents` (~50 lines, 4 subsections supporting each abstract claim with Lean file references).

**Out of scope for this track:**
- Reproducing the full proofs of the new theorems in the paper body (paper-style sketches; readers can consult the cited Lean files for full verification).
- LLM claims-reviewer pass on the updated papers (run separately when you do a comprehensive paper-claims review).
- Other papers (paper 1, 12, 15, etc.) — Phase 5e/5p content does not affect them.

---

## Dependencies

```
Wave 1 (P1 Table 1) → Wave 2 (P1 Son:2002 framing) — independent
Wave 3 (Falque κ resolution) → Wave 4 (P12 c_s framing) → Wave 5-6 (P12 wording)
Wave 7-9 (textbook facts) — independent
Wave 10-11 (bibliography) — independent
Wave 12-13 (Lean quality) — independent
Wave 14-20 (agent upgrades) — independent, do in parallel with paper edits
```

All tracks are independent; maximum parallelism.

---

## Timeline

| Wave | Scope | LOE | Priority | Status (2026-04-13) |
|------|-------|-----|----------|---------------------|
| Wave 1a | Fix compute_dissipative_correction k_H² bug | 30 min | 🔴 A | **DONE 2026-04-13** |
| Wave 1b | Add Lean theorem `gamma_H_from_transport` family | 30 min | 🔴 A | **DONE 2026-04-13** (7 theorems + 2 defs in `SecondOrderSK.lean`) |
| Wave 1c | Test Beliaev→transport→correction chain | 30 min | 🔴 A | **DONE 2026-04-13** (8 new tests, 20/20 pass) |
| Wave 1d | Regenerate Paper 1 Table 1 + body + figures | 2-3 h | 🔴 A (blocks PRL submission) | **DONE 2026-04-13** — Table 1, body text (eq:hawking_damping, Beliaev/Zaremba regimes), fig1/2/4 regenerated, claims-reviewer rerun PASS (all numerical within 1%), figure-reviewer rerun flagged fig2 FAIL → Wave 1e |
| Wave 1e | Refactor `fig_correction_hierarchy` to use canonical pipeline | 1-2 h | 🔴 A (fig2 blocks paper) | **DONE 2026-04-13** — refactored to consume beliaev_transport_coefficients + compute_dissipative_correction; removed hardcoded 100× Trento enhancement; fixed y-axis clipping; sensitivity bands now in legend; figure-reviewer PASS |
| Wave 1f | Paper 1 Heidelberg hierarchy claim honesty check | 1.5 h | 🟡 B | **DONE 2026-04-13** — abstract, Table 1 caption, fig2 caption, Experimental reach §, Conclusions list 1-3 all updated to disclose platform-dependent hierarchy and identify Heidelberg as strongest detection target |
| Wave 2 | Paper 1 Son:2002 framing | 30 min | 🟡 B | **DONE 2026-04-13** |
| Wave 3 | Falque κ resolution (primary source read) | 1-2 h | 🔴 A (blocks Paper 12) | **DONE 2026-04-13** — LLM re-verification (arXiv:2311.01392v2 full text) confirms Falque reports κ = 0.07/0.08/0.11 ps⁻¹. Prior 2026-03-31 provenance ("did not report κ") was wrong; LKB audit (2026-04-10) was right. provenance.py updated with correction + 2026-04-13 re-verification dated entry. Unblocks Waves 4-6. |
| Wave 4 | Adopt Falque values in constants.py + Paper 12 propagation | 1 h | 🟡 B | **DONE 2026-04-13** — constants.py/provenance.py/Paper 12 updated with Falque smooth-horizon defaults (κ=7e10, c_s=4e5, ξ=3.4e-6); steep-horizon reach (κ=1.1e11) quoted in text as platform upper bound; decision rationale documented |
| Wave 5 | Paper 12 "programmable" attribution | 30 min | 🟡 B | **DONE 2026-04-13** — "programmable" → "all-optically tunable / tailored"; added `[Giacobino2025]` co-citation (arXiv:2512.14194) where the "programmable simulators" framing originates; bibitem added |
| Wave 6 | Paper 12 "inside horizon" → "supersonic region" | 5 min | 🔵 C | **DONE 2026-04-13** — matches Falque's own language (§IV.2) |
| Wave 7 | Paper 3 SO(4k) center | 5 min | 🟡 B | **DONE 2026-04-13** |
| Wave 8 | Paper 10 ℤ₁₆ class D | 20 min | 🟡 B | **DONE 2026-04-13** |
| Wave 9 | Paper 10 "16 = 8 × 2" | 15 min | 🟡 B | **DONE 2026-04-13** |
| Wave 10 | Paper 10 bibliography | 30 min | 🟡 B | **DONE 2026-04-13** (FreedHopkins deferred) |
| Wave 11 | Paper 3 Adler page | 1 min | 🟡 B | **DONE 2026-04-13** |
| Wave 12 | sixteen_convergence_full | 30 min | 🟡 B | **DONE 2026-04-13** (docstring option b) |
| Wave 13 | dai_freed_spin_z4 | 15 min | 🟡 B | **DONE 2026-04-13** |
| Wave 14 | claims-reviewer Layer 2 ext | 2 h | 🔵 C | OPEN — infrastructure |
| Wave 15 | claims-reviewer Layer 4 ext | 4 h | 🔵 C (HIGH VALUE) | OPEN — infrastructure |
| Wave 16 | claims-reviewer Layer 3b | 2 h | 🔵 C | OPEN — infrastructure |
| Wave 17 | claims-reviewer Layer 5 ext | 3 h | 🔵 C | OPEN — infrastructure |
| Wave 18 | Cross-LLM provenance | 2 h | 🔵 C (HIGH VALUE) | OPEN — infrastructure |
| Wave 19 | Constants-source fidelity | 2 h | 🔵 C | OPEN — infrastructure |
| Wave 20 | Invariant 11 + hook | 1 h | 🔵 C (HIGH VALUE) | OPEN — infrastructure |
| Wave 21 | Invariant 12: Lean-grounding audit | 3-4 h | 🔵 C (HIGH VALUE) | OPEN — uncovered by Wave 1 investigation |
| Wave 22 | Paper 1 CITATION_REGISTRY reconciliation | 2 h (P1) / 4-6 h (all) | 🟡 B | OPEN — discovered by Wave 1d claims-reviewer |

**Progress 2026-04-13 / 2026-04-14**: **ALL 17 substantive Phase 5u waves complete** (Wave 1a-1f, 2, 3, 4, 5, 6, 7-13). Paper 1 and Paper 12 body text now both consistent with the pipeline, their Lean anchors, and their cited primary sources.

**Follow-up delegations completed (2026-04-14 morning):**
- Paper 12 `physics-qa:claims-reviewer` re-run (post-Wave-4): 2 FAIL + 12 WARN + 35 PASS; both FAILs fixed inline (stale "1318 theorems" → 2237+; `Giacobino2025` added to `CITATION_REGISTRY` with full metadata). Metadata drift cleaned: `PAPER_DEPENDENCIES['paper12_polariton'].key_claims` resynced with Wave-4 values; Paris_long "Perturbative" label corrected to "Borderline" in Platform-Comparison table (aligned with `tier1_regime='borderline'` from Γ_pol/κ = 0.143).
- Paper 12 figure regen + `physics-qa:figure-reviewer` (iteration 1): caught another Pipeline-Invariant-3 violation — `visualizations.py:fig_polariton_regime_map` hardcoded `kappa=5.0e10` on line 3127 (same class of bug as Wave 1e's fig_correction_hierarchy). **Fixed**: replaced with `POLARITON_PLATFORMS['Paris_long']['kappa']`. Also regenerated fig_stimulated_hawking_spectrum which had cached pre-Wave-4 annotation values in its footer.
- Paper 12 figure-reviewer (iteration 2): **both figures PASS** post-fix. T_H=85.1 mK, κ=7e10 in spectrum footer; reference line in regime map now self-consistent; all three Paris markers render correctly.

**Remaining Phase 5u work:**
- Infrastructure/process track (Waves 14–21) and citation cleanup (Wave 22) — untouched per user directive ("substantive fixes only"). These are the process-improvement tracks that turn today's bug-fix pattern into permanent invariants.
- Minor: the Wave 22 audit might now be accelerated by including `Giacobino2025` as a worked example of how to register arXiv-only lecture-notes entries.

**Side fixes applied during Wave 1d** (not separate waves but worth noting):
- `scripts/review_figures.py` missing `fig_fk_spectrum` import in `run_structural_checks` — fixed
- `src/core/transonic_background.py:__main__` demo block was passing `gamma_beliaev` (units [s⁻¹]) as `gamma_1` (units [m²/s]) — fixed to use `beliaev_transport_coefficients()` like the rest of the pipeline
- `tests/test_transonic_background.py`: 2 pre-existing tests used dimensionally-wrong γ values that passed only because of the bug; updated to Beliaev-scale γ (~10⁻¹² m²/s)

**MC validation status** (running in background, not a Phase 5u item): L=4 Hasenbusch validation run launched 2026-04-13 18:10 (ID `b5z7xs7t9`, 4 workers, 1500 traj × 14 couplings, seed=42). ~2 h in at last check, 4 of 14 couplings partially filled (170–280 / 1500). Steady-state ~25–40 s/traj at L=4 — Hasenbusch overhead exceeds CG benefit at small κ; the 50–70× speedup only materializes at L=8+.

**Total**: ~24 hours of edit + verification work; ~17 hours of agent upgrades. Parallelizable to 1–2 working days with concurrent tracks.

---

## What Success Looks Like

- Paper 1 Table 1 matches current pipeline to <0.5%; claims-reviewer passes with zero FAIL.
- Paper 12 parameters (c_s, κ, T_H, D) are consistent between abstract / table / constants.py / provenance — and defensibly match primary sources.
- Paper 3, Paper 10 textbook-fact errors all corrected.
- Paper 10 bibliography pages / citations all verified against primary sources.
- `sixteen_convergence_full` either strengthened or honestly labeled as "record of four 16s"; `dai_freed_spin_z4` labeled as placeholder.
- `claims-reviewer` agent can now catch:
  - Catastrophic arXiv errors in one pass (Wave 15)
  - Vacuous Lean theorems (Wave 14)
  - Constants/source drift (Waves 18, 19)
  - Stale claims_review after constants.py change (Wave 20)

**After Wave 20**, the process failures that caused this review round are systemically prevented, not just patched paper-by-paper.

---

## Out of Scope

- **Counts**: Per user directive (2026-04-13), count staleness is deferred — counts will change as Lean work continues. Will be reconciled atomically at paper submission.
- **Paper 6 MC status**: Per user directive, paper is NOT modified to indicate crashed status. Phase 4/5 roadmaps already track MC not-done. The Apr 10 reviews referenced legacy `run_vestigial_production.py` runs (fermion-bag), **which was superseded on 2026-04-02 by HS+RHMC** (see Phase6_Roadmap line 30, 63: "fermion-bag hits O(V⁴) percolation wall"). The current production path is `scripts/run_rhmc_epochs.sh --l 8` using `run_rhmc_production.py` (Rust-accelerated via `sk_eft_rhmc`). L=8 state as of 2026-04-13: only 2 couplings completed (g=0.5, g=2.0 from Apr 10); needs full coupling scan to resolve vestigial phase. Any new MC production for Paper 6 must use the HS+RHMC path, not the legacy fermion-bag path.
- **Lean 4.29 build errors in 3 files (Uqsl2AffineHopf, Uqsl3Hopf, TetradGapEquation)**: Tracked in parallel Lean session (Phase 5s Wave 8, Uqsl3Hopf F01 closure). Not duplicated here. (UPDATE 2026-04-14: Uqsl3Hopf resolved — 0 sorry, Bialgebra + HopfAlgebra typeclass wired, full SKEFTHawking package builds clean no-cache. Uqsl2AffineHopf and TetradGapEquation Lean 4.29 status should be re-verified.)
- **Mathlib PR process** (Phase 5g Wave 4+): Independent track, out of scope.
- **arXiv voucher / paper submissions** (Phase 5g Wave 7+): Depends on Tier A items (Wave 1, Wave 3) completing first.

---

*Phase 5u roadmap. Created 2026-04-13. All items trace to IndependentVerification-02.md. Follows [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
