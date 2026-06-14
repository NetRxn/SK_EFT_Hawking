import SKEFTHawking.Basic
import SKEFTHawking.LaplaceMethodAsymptotic
import Mathlib

/-!
# `Real.Gamma` Stirling-with-remainder — Phase 6a Wave 7C (upstream-shaped)

Mathlib has the *factorial* Stirling (`Stirling.stirlingSeq`) and the rate of convergence
`stirlingSeq n → √π` (made quantitative in `LaplaceMethodAsymptotic`, Wave 7C brick 1), and it
has the **log-convexity** of `Γ` (`Real.convexOn_log_Gamma`, the Bohr–Mollerup tool) — but it
has **no** asymptotic expansion of `log Γ` on the reals (loogle: no `Real.Gamma` `IsBigO`).

This module supplies the missing piece:
`log Γ(x) − [(x − ½)·log x − x + ½·log(2π)] = O(1/x)` as `x → ∞` over `ℝ`.

**Architecture (Bohr–Mollerup convexity squeeze):**
1. `stirlingPart x := (x − ½)·log x − x + ½·log(2π)` — the principal part.
2. *Integer points* (`logGamma_sub_stirlingPart_nat_le`): `|log Γ(m) − stirlingPart m| ≤ C/m`.
   `log Γ(m) = log((m−1)!)`, and `log((m−1)!) = log stirlingSeq(m−1) + ½·log(2(m−1)) +
   (m−1)·log((m−1)/e)` (`Stirling.log_stirlingSeq_formula`); the `½·log π` constant comes from
   the committed rate `LaplaceMethodAsymptotic.log_stirlingSeq_sub_log_sqrt_pi_le`, and the
   `(m−½)·log((m−1)/m) + 1 = O(1/m)` residue from elementary `log` bounds.
3. *Real points* (`logGamma_sub_stirlingPart_isBigO`): for `x ∈ [n, n+1]` (`n = ⌊x⌋ ≥ 2`),
   log-convexity of `Γ` (`Real.convexOn_log_Gamma`) squeezes
   `f(n) + (x−n)·log(n−1) ≤ log Γ(x) ≤ f(n) + (x−n)·log n` (`f := log ∘ Γ`,
   slopes `f(n)−f(n−1) = log(n−1)`, `f(n+1)−f(n) = log n`), bracket width `≤ log(n/(n−1)) =
   O(1/n)`; combined with step 2 and `stirlingPart` smoothness this gives `O(1/x)`.

Kernel-pure; no new axioms (the asymptotic is PROVEN, not assumed). Mathlib-PR-shaped.
-/

namespace SKEFTHawking
namespace GammaStirling

open Real Filter Asymptotics Topology

/-- The Stirling principal part of `log Γ`: `(x − ½)·log x − x + ½·log(2π)`. -/
noncomputable def stirlingPart (x : ℝ) : ℝ :=
  (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * Real.pi)

/-- **Integer-point Stirling rate for `log Γ`.** For `m ≥ 2`,
`|log Γ(m) − stirlingPart m| ≤ 2/m`. Built from `Stirling.log_stirlingSeq_formula` and the
committed quantitative rate `LaplaceMethodAsymptotic.log_stirlingSeq_sub_log_sqrt_pi_le`.
(The natural asymptotic regime; `m = 1` would need separate numeric `log (2π)` bounds and is
not needed downstream.) -/
theorem logGamma_sub_stirlingPart_nat_le (m : ℕ) (hm : 2 ≤ m) :
    |Real.log (Real.Gamma m) - stirlingPart m| ≤ 2 / (m : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  push_cast
  -- Γ(k+1) = k!
  have hΓ : Real.log (Real.Gamma ((k : ℝ) + 1)) = Real.log (k.factorial : ℝ) := by
    rw [Real.Gamma_nat_eq_factorial k]
  rw [hΓ]
  -- Stirling formula: log(k!) = log(stirlingSeq k) + ½·log(2k) + k·log(k/e)
  have hStir : Real.log (k.factorial : ℝ)
      = Real.log (Stirling.stirlingSeq k) + 1 / 2 * Real.log (2 * (k : ℝ))
        + (k : ℝ) * Real.log ((k : ℝ) / Real.exp 1) := by
    have := Stirling.log_stirlingSeq_formula k
    linarith
  -- log expansions
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have h2k : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log (k : ℝ) :=
    Real.log_mul (by norm_num) hkne
  have hke : Real.log ((k : ℝ) / Real.exp 1) = Real.log (k : ℝ) - 1 := by
    rw [Real.log_div hkne (Real.exp_ne_zero 1), Real.log_exp]
  have hsqrtπ : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 :=
    Real.log_sqrt Real.pi_pos.le
  have h2π : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
  -- KEY IDENTITY: log(k!) - stirlingPart(k+1) = first + second
  set first := Real.log (Stirling.stirlingSeq k) - Real.log (Real.sqrt Real.pi) with hfirst_def
  set second := 1 - ((k : ℝ) + 1 / 2) * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) with hsecond_def
  have hkey : Real.log (k.factorial : ℝ) - stirlingPart ((k : ℝ) + 1) = first + second := by
    rw [hfirst_def, hsecond_def, hStir, stirlingPart, h2k, hke, hsqrtπ, h2π]
    ring
  rw [hkey]
  -- Bound |first| ≤ 1/(12k)
  have hfirst_le : first ≤ 1 / (12 * (k : ℝ)) := by
    rw [hfirst_def]
    exact SKEFTHawking.LaplaceMethodAsymptotic.log_stirlingSeq_sub_log_sqrt_pi_le k hk1
  have hfirst_nonneg : 0 ≤ first := by
    rw [hfirst_def]
    exact SKEFTHawking.LaplaceMethodAsymptotic.log_stirlingSeq_sub_log_sqrt_pi_nonneg k hk1
  have hfirst_abs : |first| ≤ 1 / (12 * (k : ℝ)) := by
    rw [abs_of_nonneg hfirst_nonneg]; exact hfirst_le
  -- L := log(k+1) - log k, with 1/(k+1) ≤ L ≤ 1/k
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set L := Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) with hL_def
  -- Upper: L ≤ 1/k
  have hLupper : L ≤ 1 / (k : ℝ) := by
    have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hkne] at h1
    have hval : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by field_simp; ring
    rw [hval] at h1
    rw [hL_def]
    exact h1
  -- Lower: 1/(k+1) ≤ L
  have hLlower : 1 / ((k : ℝ) + 1) ≤ L := by
    have h2 : Real.log ((k : ℝ) / ((k : ℝ) + 1)) ≤ (k : ℝ) / ((k : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hkne (ne_of_gt hk1pos)] at h2
    have hval : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by field_simp; ring
    rw [hval] at h2
    rw [hL_def]
    linarith [h2]
  -- Bound |second| ≤ 1/(2k)
  have hkhalf : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  have hprod_up : ((k : ℝ) + 1 / 2) * L ≤ ((k : ℝ) + 1 / 2) * (1 / (k : ℝ)) :=
    mul_le_mul_of_nonneg_left hLupper (le_of_lt hkhalf)
  have hprod_low : ((k : ℝ) + 1 / 2) * (1 / ((k : ℝ) + 1)) ≤ ((k : ℝ) + 1 / 2) * L :=
    mul_le_mul_of_nonneg_left hLlower (le_of_lt hkhalf)
  have hv1 : ((k : ℝ) + 1 / 2) * (1 / (k : ℝ)) = 1 + 1 / (2 * (k : ℝ)) := by field_simp
  have hv2 : ((k : ℝ) + 1 / 2) * (1 / ((k : ℝ) + 1)) = 1 - 1 / (2 * ((k : ℝ) + 1)) := by
    field_simp; ring
  rw [hv1] at hprod_up
  rw [hv2] at hprod_low
  have hmono : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 / (2 * (k : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
  have hsecond_abs : |second| ≤ 1 / (2 * (k : ℝ)) := by
    rw [hsecond_def, abs_le]; refine ⟨by linarith, by linarith⟩
  -- Assemble: |first + second| ≤ |first| + |second| ≤ 1/(12k) + 1/(2k) = 7/(12k) ≤ 2/(k+1)
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have htri : |first + second| ≤ |first| + |second| := abs_add_le first second
  have hcombine : (1 : ℝ) / (12 * (k : ℝ)) + 1 / (2 * (k : ℝ)) = 7 / (12 * (k : ℝ)) := by
    field_simp; ring
  have hsum : |first| + |second| ≤ 7 / (12 * (k : ℝ)) := by
    rw [← hcombine]; linarith [hfirst_abs, hsecond_abs]
  have hfinal : 7 / (12 * (k : ℝ)) ≤ 2 / ((k : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hkr]
  linarith [htri, hsum, hfinal]

/-- Log-Gamma recurrence: `log Γ(t+1) = log Γ(t) + log t` for `t > 0`. -/
private lemma logGamma_succ {t : ℝ} (ht : 0 < t) :
    Real.log (Real.Gamma (t + 1)) = Real.log (Real.Gamma t) + Real.log t := by
  rw [Real.Gamma_add_one (ne_of_gt ht),
    Real.log_mul (ne_of_gt ht) (ne_of_gt (Real.Gamma_pos_of_pos ht))]
  ring

/-- Upper convexity bracket: for `N ≥ 2`, `N < x < N+1`,
`log Γ(x) ≤ log Γ(N) + (x - N)·log N`. -/
private lemma logGamma_bracket_upper (N : ℕ) (x : ℝ) (hN : 2 ≤ N)
    (hxN : (N : ℝ) < x) (hxN1 : x < (N : ℝ) + 1) :
    Real.log (Real.Gamma x) ≤ Real.log (Real.Gamma (N : ℝ)) + (x - N) * Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hkey := Real.convexOn_log_Gamma.secant_mono_aux1 (Set.mem_Ioi.mpr hN0)
    (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < (N : ℝ) + 1)) hxN hxN1
  simp only [Function.comp_apply] at hkey
  have hrec := logGamma_succ hN0
  nlinarith [hkey, hrec]

/-- Lower convexity bracket: for `N ≥ 2`, `N < x < N+1`,
`log Γ(N) + (x - N)·log (N-1) ≤ log Γ(x)`. -/
private lemma logGamma_bracket_lower (N : ℕ) (x : ℝ) (hN : 2 ≤ N)
    (hxN : (N : ℝ) < x) (hxN1 : x < (N : ℝ) + 1) :
    Real.log (Real.Gamma (N : ℝ)) + (x - N) * Real.log ((N : ℝ) - 1)
      ≤ Real.log (Real.Gamma x) := by
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hkey := Real.convexOn_log_Gamma.secant_mono_aux1
    (Set.mem_Ioi.mpr hN1) (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < x))
    (by linarith : (N : ℝ) - 1 < (N : ℝ)) hxN
  simp only [Function.comp_apply] at hkey
  have hrec : Real.log (Real.Gamma (N : ℝ)) = Real.log (Real.Gamma ((N : ℝ) - 1)) + Real.log ((N : ℝ) - 1) := by
    have := logGamma_succ hN1
    rw [sub_add_cancel] at this
    linarith
  nlinarith [hkey, hrec, hxN, hxN1]

/-- `stirlingPart` smoothness: the increment `stirlingPart x − stirlingPart N` matches its
linearization `(x − N)·log N` to within `1/(2N)` on `[N, N+1]`. -/
private lemma stirlingPart_increment_bound (N : ℕ) (x : ℝ) (hN : 2 ≤ N)
    (hxN : (N : ℝ) ≤ x) (hxN1 : x ≤ (N : ℝ) + 1) :
    |stirlingPart x - stirlingPart (N : ℝ) - (x - N) * Real.log (N : ℝ)| ≤ 1 / (2 * (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hx0 : (0 : ℝ) < x := by linarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hxne : x ≠ 0 := ne_of_gt hx0
  -- identity: the bracketed quantity equals S(x) := (x-1/2)(log x - log N) - (x - N)
  have hident : stirlingPart x - stirlingPart (N : ℝ) - (x - N) * Real.log (N : ℝ)
      = (x - 1 / 2) * (Real.log x - Real.log (N : ℝ)) - (x - N) := by
    unfold stirlingPart; ring
  rw [hident]
  set M := Real.log x - Real.log (N : ℝ) with hM_def
  -- M = log(x/N) bounds: (x-N)/x ≤ M ≤ (x-N)/N
  have hMupper : M ≤ (x - N) / (N : ℝ) := by
    have h1 : Real.log (x / (N : ℝ)) ≤ x / (N : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hxne hNne] at h1
    have hval : x / (N : ℝ) - 1 = (x - N) / (N : ℝ) := by field_simp
    rw [hval] at h1; rw [hM_def]; exact h1
  have hMlower : (x - N) / x ≤ M := by
    have h2 : Real.log ((N : ℝ) / x) ≤ (N : ℝ) / x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hNne hxne] at h2
    have hval : (N : ℝ) / x - 1 = -((x - N) / x) := by field_simp; ring
    rw [hval] at h2; rw [hM_def]; linarith
  -- products
  have hxhalf : (0 : ℝ) < x - 1 / 2 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hpu : (x - 1 / 2) * M ≤ (x - 1 / 2) * ((x - N) / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hMupper (le_of_lt hxhalf)
  have hpl : (x - 1 / 2) * ((x - N) / x) ≤ (x - 1 / 2) * M :=
    mul_le_mul_of_nonneg_left hMlower (le_of_lt hxhalf)
  rw [abs_le]
  constructor
  · -- lower: -(1/(2N)) ≤ (x-1/2)*M - (x-N)
    have hpv : (x - 1 / 2) * ((x - (N : ℝ)) / x) = (x - (N : ℝ)) - (x - (N : ℝ)) / (2 * x) := by
      field_simp
    rw [hpv] at hpl
    have hb1 : (x - (N : ℝ)) / (2 * x) ≤ 1 / (2 * (N : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hxN, hxN1, hx0, hN0]
    nlinarith [hpl, hb1]
  · -- upper: (x-1/2)*M - (x-N) ≤ 1/(2N)
    have hpv : (x - 1 / 2) * ((x - (N : ℝ)) / (N : ℝ))
        = (x - (N : ℝ)) + (x - (N : ℝ)) * (x - (N : ℝ) - 1 / 2) / (N : ℝ) := by
      field_simp; ring
    rw [hpv] at hpu
    have hb2 : (x - (N : ℝ)) * (x - (N : ℝ) - 1 / 2) / (N : ℝ) ≤ 1 / (2 * (N : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hN0, mul_nonneg (sub_nonneg.mpr hxN) (show (0 : ℝ) ≤ (N : ℝ) + 1 - x by linarith)]
    nlinarith [hpu, hb2]

/-- Pointwise master bound: `|log Γ(x) − stirlingPart x| ≤ 9/x` for `x ≥ 2`.
This is the floor-based convexity squeeze: with `n = ⌊x⌋ ≥ 2`, combine the integer rate at `n`,
the convexity bracket for `log Γ` on `[n, n+1]`, and the `stirlingPart` increment bound. -/
private lemma logGamma_sub_stirlingPart_pointwise (x : ℝ) (hx : 2 ≤ x) :
    |Real.log (Real.Gamma x) - stirlingPart x| ≤ 9 / x := by
  set n := ⌊x⌋₊ with hn_def
  have hx0 : (0 : ℝ) < x := by linarith
  have hn_le : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlt_n1 : x < (n : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one x
  have hn2 : 2 ≤ n := by
    rw [hn_def]; exact Nat.le_floor (by exact_mod_cast hx)
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hnr2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  -- integer rate at n
  have hRn : |Real.log (Real.Gamma (n : ℝ)) - stirlingPart (n : ℝ)| ≤ 2 / (n : ℝ) :=
    logGamma_sub_stirlingPart_nat_le n hn2
  -- 1/n ≤ 2/x  (since n ≥ x - 1 ≥ x/2 for x ≥ 2)
  have hn_ge : x - 1 ≤ (n : ℝ) := by linarith
  have hinv : 1 / (n : ℝ) ≤ 2 / x := by
    rw [div_le_div_iff₀ hn0 hx0]; nlinarith [hn_ge, hx]
  -- stirlingPart increment bound at (n, x)
  have hIncr := stirlingPart_increment_bound n x hn2 hn_le hlt_n1.le
  rw [abs_le] at hIncr hRn
  -- log n - log (n-1) ≤ 1/(n-1)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hloggap : Real.log (n : ℝ) - Real.log ((n : ℝ) - 1) ≤ 1 / ((n : ℝ) - 1) := by
    have h1 : Real.log ((n : ℝ) / ((n : ℝ) - 1)) ≤ (n : ℝ) / ((n : ℝ) - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hn0) (ne_of_gt hn1pos)] at h1
    have hval : (n : ℝ) / ((n : ℝ) - 1) - 1 = 1 / ((n : ℝ) - 1) := by field_simp; ring
    rw [hval] at h1; exact h1
  -- log(n-1) ≤ log n  (monotonicity)
  have hlogmono : Real.log ((n : ℝ) - 1) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hn1pos (by linarith)
  -- 2/n ≤ 9/n and similar simple comparisons
  have h2le9 : (2 : ℝ) / (n : ℝ) ≤ 9 / (n : ℝ) := by
    rw [div_le_div_iff₀ hn0 hn0]; nlinarith [hn0]
  -- 1/(n-1) ≤ 2/n  (since n ≥ 2)
  have hn1inv : 1 / ((n : ℝ) - 1) ≤ 2 / (n : ℝ) := by
    rw [div_le_div_iff₀ hn1pos hn0]; nlinarith [hnr2]
  -- x ≤ 2n  (since x < n+1 ≤ 2n for n ≥ 1)
  have hx_le_2n : x ≤ 2 * (n : ℝ) := by linarith
  -- 9/(2n) ≤ 9/x
  have h9 : 9 / (2 * (n : ℝ)) ≤ 9 / x := by
    rw [div_le_div_iff₀ (by positivity) hx0]; nlinarith [hx_le_2n]
  -- 5/(2n) ≤ 9/x  (5/(2n) ≤ 5/x ≤ 9/x via x ≤ 2n? no: use 5/(2n) ≤ 9/(2n) ≤ 9/x)
  have h5 : 5 / (2 * (n : ℝ)) ≤ 9 / x := by
    have : 5 / (2 * (n : ℝ)) ≤ 9 / (2 * (n : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hn0]
    linarith [this, h9]
  -- Case split: x = n or n < x
  rcases eq_or_lt_of_le hn_le with hxeq | hxlt
  · -- x = n: R(x) = R(n), use integer rate
    rw [abs_le, ← hxeq]
    constructor
    · linarith [hRn.1, h2le9]
    · linarith [hRn.2, h2le9]
  · -- n < x: full convexity squeeze
    have hupper := logGamma_bracket_upper n x hn2 hxlt hlt_n1
    have hlower := logGamma_bracket_lower n x hn2 hxlt hlt_n1
    have hxn_le1 : x - (n : ℝ) ≤ 1 := by linarith
    have hxn_nonneg : (0 : ℝ) ≤ x - (n : ℝ) := by linarith
    -- (x-n)(log n - log(n-1)) ≤ 1/(n-1)
    have hbracketgap : (x - (n : ℝ)) * (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1))
        ≤ 1 / ((n : ℝ) - 1) := by
      calc (x - (n : ℝ)) * (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1))
          ≤ 1 * (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) := by
            apply mul_le_mul_of_nonneg_right hxn_le1
            linarith [hlogmono]
        _ = Real.log (n : ℝ) - Real.log ((n : ℝ) - 1) := by ring
        _ ≤ 1 / ((n : ℝ) - 1) := hloggap
    -- fraction arithmetic helpers (turn distinct division-atoms into a common one)
    have hf2 : (2 : ℝ) / (n : ℝ) = 4 / (2 * (n : ℝ)) := by
      rw [div_eq_div_iff (ne_of_gt hn0) (by positivity)]; ring
    have hf4 : 4 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)) = 5 / (2 * (n : ℝ)) := by
      field_simp; norm_num
    have hf9 : 4 / (2 * (n : ℝ)) + 4 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)) = 9 / (2 * (n : ℝ)) := by
      field_simp; norm_num
    have hn1inv' : 1 / ((n : ℝ) - 1) ≤ 4 / (2 * (n : ℝ)) := by rw [← hf2]; exact hn1inv
    -- R(x) ≤ 5/(2n)  and  R(x) ≥ -9/(2n)
    have hRx_upper : Real.log (Real.Gamma x) - stirlingPart x ≤ 5 / (2 * (n : ℝ)) := by
      have hstep : Real.log (Real.Gamma x) - stirlingPart x
          ≤ (Real.log (Real.Gamma (n : ℝ)) - stirlingPart (n : ℝ)) + 1 / (2 * (n : ℝ)) := by
        nlinarith [hupper, hIncr.1]
      rw [← hf4]
      linarith [hstep, hRn.2, hf2]
    have hRx_lower : -(9 / (2 * (n : ℝ))) ≤ Real.log (Real.Gamma x) - stirlingPart x := by
      have hstep : (Real.log (Real.Gamma (n : ℝ)) - stirlingPart (n : ℝ))
          - 1 / ((n : ℝ) - 1) - 1 / (2 * (n : ℝ))
          ≤ Real.log (Real.Gamma x) - stirlingPart x := by
        nlinarith [hlower, hIncr.2, hbracketgap]
      rw [show -(9 / (2 * (n : ℝ)))
          = -(4 / (2 * (n : ℝ))) - 4 / (2 * (n : ℝ)) - 1 / (2 * (n : ℝ)) by
        rw [← hf9]; ring]
      linarith [hstep, hRn.1, hf2, hn1inv']
    rw [abs_le]
    exact ⟨by linarith [hRx_lower, h9], by linarith [hRx_upper, h5]⟩

/-- **`Real.Gamma` Stirling-with-remainder** (the missing Mathlib lemma): `log Γ` matches its
Stirling principal part to `O(1/x)` as `x → ∞`. Proven via the Bohr–Mollerup convexity squeeze
(`Real.convexOn_log_Gamma`) bridging the integer rate `logGamma_sub_stirlingPart_nat_le` to the
reals. -/
theorem logGamma_sub_stirlingPart_isBigO :
    (fun x : ℝ => Real.log (Real.Gamma x) - stirlingPart x) =O[atTop] (fun x : ℝ => 1 / x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨9, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨2, fun x hx => ?_⟩
  have hp := logGamma_sub_stirlingPart_pointwise x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hnorm1 : ‖(1 : ℝ) / x‖ = 1 / x := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Real.norm_eq_abs, hnorm1, ← mul_div_assoc, mul_one]
  exact hp

end GammaStirling
end SKEFTHawking
