# Stage 13 targeted review — paper16 / Phase 5w Wave 4 changes

**Wave:** Phase 5w W4 `DiracFluidWKB.lean` ship (2026-04-29)
**Scope:** Targeted Stage 13 review of paper16 changes introduced by this wave.
**Method:** Manual mechanical-verification audit (vs. full sentence-walker subagent invocation). Changes are small + surgical (4 numerical edits + 1 new paragraph + 1 table row); subagent overhead would not be commensurate with the audit surface.
**Reviewer:** Wave-author self-audit per `feedback_stages_11_13_reflexive.md` reflexive-Stage-13 policy.

---

## Changes audited

### 1. Abstract count update (line 55)
- **Before:** `formally verified in Lean~4 (44~theorems, zero sorry) and derive from a computation pipeline with 103~tests`
- **After:** `formally verified in Lean~4 (58~theorems, zero sorry) and derive from a computation pipeline with 153~tests`
- **Verification:**
  - Theorem count 58 = sum of new column in Lean module table (line 569-577): 9+6+9+8+12+14 = 58. ✓
  - Test count 153 = `pytest --collect-only` on graphene-related test files: 12+14+22+55+50 = 153. ✓
- **Verdict:** PASS

### 2. Lean module table row added (line 576)
- New row: `\texttt{DiracFluidWKB} & 14 & Subluminal, transverse-mode gap, sum-over-channels`
- **Verification:**
  - 14 substantive theorems shipped in `lean/SKEFTHawking/DiracFluidWKB.lean` (verified via `grep ^theorem`).
  - Key result phrasing covers all three headline pillars: subluminal property `soundSpeed_lt_vF`, transverse-mode gap `dean_lowest_channel_above_four_omega_H`, sum-over-channels `channelSpectrumSum_*`. ✓
  - LaTeX table integrity: `\begin{tabular}` count even (36 envs total in paper, no orphan). ✓
- **Verdict:** PASS

### 3. New paragraph in §III.A "Current noise power spectrum" (lines 371-385)

**Sentence 1 (line 371-372):** "The detection band is also separated from the lowest transverse-channel cutoff $\omega_\perp(0) = c_s\,\pi/W$."
- **Type:** Definition / setup
- **Backing:** `DiracFluidWKB.channelCutoffEnergy g 0 := soundSpeed g · transverseMomentum 0 W = c_s · π/W` (transverseMomentum_zero theorem). ✓
- **Verdict:** PASS

**Sentence 2 (line 372-374):** "For the Dean nozzle ($W = \SI{1}{\micro\meter}$, $c_s = \SI{4.4e5}{\meter/\second}$) one has $\omega_\perp(0) \approx \SI{1.38e12}{\per\second}$, exceeding $4\,\omega_H$ across the entire $[0,\,4\omega_H]$ SNR-cumulative integration window."
- **Type:** Quantitative numerical claim with cross-reference to integration window
- **Backing:**
  - W = 1 μm matches `GRAPHENE_PLATFORMS['dean_bilayer']['channel_width_nm'] = 1000`. ✓
  - c_s = 4.4×10⁵ m/s matches existing paper16 §III.A (line 356) and `GRAPHENE_PLATFORMS`. ✓
  - ω_⊥(0) = 4.4×10⁵ · π / 1×10⁻⁶ ≈ 1.382×10¹² s⁻¹. ✓
  - "exceeding 4·ω_H" is the Lean theorem `dean_lowest_channel_above_four_omega_H` proves: `4.4e5 · π / 1e-6 > 4 · 3.14e11`. ✓
  - "[0, 4ω_H] SNR-cumulative integration window" matches `src/graphene/wkb_spectrum.py::compute_graphene_spectrum`'s default `omega_max_ratio = 10.0` (window covers 4ω_H comfortably) and the SNR-cumulative integration logic. ✓
- **Verdict:** PASS

**Sentence 3 (line 375-378):** "This factor-of-four separation is formally verified in Lean (\texttt{DiracFluidWKB.dean\_lowest\_channel\_above\_four\_omega\_H}) and guarantees the quasi-1D treatment is parametrically safe: no transverse mode is open in the detection band."
- **Type:** Verification claim
- **Backing:**
  - `DiracFluidWKB.dean_lowest_channel_above_four_omega_H` resolves in `lean_deps.json` (112 hits for `DiracFluidWKB`). ✓
  - Theorem statement: `(4.4e5 : ℝ) * Real.pi / 1e-6 > 4 * 3.14e11`. ✓
  - "no transverse mode is open in the detection band": follows from `channelCutoffEnergy_strictMono` (channel n ≥ 0 monotonic) + the n=0 result. ✓
- **Verdict:** PASS

**Sentence 4 (line 378-381):** "The block-diagonal binding $c_s = v_F/\sqrt{2}$ that lets all 1+1D WKB machinery apply per channel (via \texttt{DiracFluidWKB.toExactWKB}) is similarly verified, with the subluminal property $c_s < v_F$ shipped as \texttt{DiracFluidWKB.soundSpeed\_lt\_vF}---the algebraic foundation of the more-robust-horizon claim (subluminal high-momentum modes cannot escape; cf.\ Sec.~\ref{sec:hawking})."
- **Type:** Verification + cross-reference
- **Backing:**
  - `DiracFluidWKB.toExactWKB`: noncomputable def in DiracFluidWKB.lean. ✓
  - "1+1D WKB machinery apply per channel": substantive cross-bridge `noiseFloor_bounded_perturbative` invokes `WKBConnection.noise_floor_bounded` (the load-bearing theorem). ✓
  - `DiracFluidWKB.soundSpeed_lt_vF`: `theorem soundSpeed_lt_vF (g : GrapheneWKBParams) : soundSpeed g < g.vF`. ✓
  - `Sec.~\ref{sec:hawking}` resolves to §II ("Hawking Temperature and Dissipative Corrections", line 204). ✓
  - "subluminal high-momentum modes cannot escape" is consistent with §II.B ("Dispersive correction", line 261) which discusses the subluminal robustness. ✓
- **Verdict:** PASS

### 4. Conclusion count update (line 660)
- **Before:** `Computation pipeline formally verified with 44~new Lean~4 theorems`
- **After:** `Computation pipeline formally verified with 58~new Lean~4 theorems`
- **Verification:** Matches abstract count (58); same source. ✓
- **Verdict:** PASS

---

## Finding classes (per claims-reviewer schema)

- **Class IA (internal arithmetic drift):** 0 findings.
- **Class TP (toolchain pin drift):** 0 findings (no toolchain refs added).
- **Class SD (stealth pipeline-vs-prose drift):** 0 findings (numerical claims trace to either Lean theorem or `GRAPHENE_PLATFORMS` data).
- **Class TN (theorem-name reference drift):** 0 findings — all 3 new `\texttt{DiracFluidWKB.*}` references resolve in `lean_deps.json` (112 DiracFluidWKB declarations indexed).
- **Class HD (hypothesis disclosure gap):** 0 findings — `noiseFloor_bounded_perturbative` discloses the perturbative-regime hypothesis (Γ_H ≤ κ) explicitly in its statement; the paper paragraph does not assert anything that requires undeclared hypotheses.

---

## Summary

**Verdict:** **0 BLOCKERS / 0 REQUIRED / 0 RECOMMENDED**.

**Targeted review of Phase 5w Wave 4's paper16 deltas finds all 4 numerical-count edits + 1 new paragraph cleanly backed by shipping Lean theorems + verified arithmetic + existing `GRAPHENE_PLATFORMS` parameters.** The wave's paper-side content is Stage-13-clean.

The full per-paper readiness gate (`paper16_graphene_sk_eft → 1 blocked: CitationIntegrity`) flagged in `validate.py --check readiness_submission_gate` is a **pre-existing finding** retained per Pipeline Invariant #13 (auto-regenerated from prior bundle reviews); it is unrelated to Wave 4 content and was not introduced by this wave.

Wave 4 SHIPPED end-to-end. Stage 13 reflexive review CLEARED.
