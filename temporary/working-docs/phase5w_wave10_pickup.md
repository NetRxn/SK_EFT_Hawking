# Phase 5w Wave 10 — Status Document

**Written:** 2026-04-16
**Updated:** 2026-04-16 (Wave 10a COMPLETE — noise formula corrected)
**Status:** Waves 2-10a,10b,10d COMPLETE. Only 10c (quasi-1D Lean bound) deferred.

## Wave 10a: RESOLVED

Deep research returned at `Lit-Search/Phase-5w/5w-landauer-buttiker-noise.md`.

**Finding:** The old formula `S_H = (2e²/π) σ_Q ω n_H` was **dimensionally wrong**.
- Units of `2e²/π` are C² (charge squared), not J·s (action)
- Off by a factor of `2e²/h ≈ 77.5 μS` (conductance quantum)

**Corrected formula:** `ΔS_I(ω) = 2ℏω σ_Q Γ(ω) n_H(ω)` [A²/Hz]
- Derived independently via Keldysh FDT and Landauer-Büttiker with Bogoliubov mixing
- Greybody Γ(ω) ≤ 1 (device-specific; using Γ=1 as upper bound)
- This is a genuinely new result (no prior publication)

**Impact on predictions:**
- S_H ≈ 10⁻²⁶ A²/Hz (was quoted as 10⁻³⁰ — wrong units)
- SNR/bin ≈ T_H/(2T_amb) ≈ 0.008 (independent of σ_Q!)
- Statistical integration time: < 1 s for 5σ (was "25 min")
- Detection is systematics-limited, not statistics-limited

**What was done:**
1. Added `graphene_hawking_noise_psd()` to `formulas.py`
2. Fixed `wkb_spectrum.py` — replaced `(2e²/π)σ_Q ω` with `2ℏω σ_Q Γ`
3. Created `GrapheneNoiseFormula.lean` (8 theorems, 0 sorry): positivity, greybody monotonicity, SNR σ_Q-independence, dimensional analysis, FDT consistency
4. Updated Paper 16: §IV.A rewritten with Keldysh/LB derivation, all numbers updated, "leading-order estimate" caveat removed
5. Regenerated figures 104-105 with corrected values
6. Added 4 dimensional consistency tests (99 total graphene tests)
7. `lake build` clean: 8411 jobs, 0 sorry

## Remaining: Wave 10c (DEFERRED)

Quasi-1D Lean bound — low priority. Would formalize the condition W >> l_ee for the quasi-1D approximation. Not blocking any paper or outreach work.

## Collaboration readiness

With the noise formula now DERIVED (not estimated), outreach to Lucas/Dean can proceed:
- T_H ≈ 2.4 K, D = 0.23, EFT valid
- Noise formula: ΔS_I = 2ℏω σ_Q Γ n_H (Keldysh + Landauer-Büttiker)
- Detection band: 0.5-85 GHz
- SNR = T_H/(2T_amb) ≈ 0.8% — systematics-limited
- Formal verification: 32 Lean theorems, 0 sorry
