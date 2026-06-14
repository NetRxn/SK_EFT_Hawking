import SKEFTHawking.Basic
import Mathlib

/-!
# Genuine literal-Verlinde Laplace derivation — Phase 6a Wave 7B

**Decision-gate verdict (2026-06-14).** The SU(2)_k horizon singlet count needs
neither the Hardy–Ramanujan partition asymptotic nor Bessel functions (both absent
from Mathlib 4.29). The number of SU(2) singlets in `(spin-½)^⊗(2m)` is the Catalan
number `C_m = binom(2m,m)/(m+1)` — the *discrete* `I₀ − I₁`
(`binom(2m,m) − binom(2m,m+1)`). Mathlib's Stirling
(`Stirling.factorial_isEquivalent_stirling`) yields `C_m ~ 4^m / (√π · m^{3/2})`,
hence `log C_m = 2m·log 2 − (3/2)·log m + O(1)` — the Kaul–Majumdar `−3/2` from the
*literal* count, with `−3/2 = −½` (the `√(2πm)` Stirling prefactor) `− 1` (the
binomial difference / the `1/(m+1)` Catalan factor).

This replaces the Wave-6a.7 placeholder where `verlindeEntropy_SU2k` was *defined* as
its own saddle limit (`:= kaulMajumdarS A G_N 0`, making `gaussianSaddleAsymptotic`
prove `|x−x|=0`). Here the singlet count is a genuine combinatorial object and its
`−3/2` log asymptotic is derived from Stirling.

## Build status
Sub-task B (this module): literal count + Stirling asymptotic. Sub-task C (wiring
into `BHEntropyMicroscopic`, redefining `verlindeEntropy_SU2k`, discharging
`H_VerlindeKMLiteralSumDerivation`) follows once the asymptotic lands.
-/

namespace SKEFTHawking
namespace LaplaceMethodAsymptotic

open Real Filter Asymptotics Topology

/--
**Literal SU(2) singlet multiplicity** of `2m` spin-½ horizon punctures: the number
of ways to couple them to total spin 0, `= Catalan m = binom(2m,m)/(m+1)`. This is
the literal Verlinde-counted horizon state density (spin-½ / `k → ∞` sector), NOT the
Wave-6a.7 saddle-limit redefinition.
-/
def singletCount (m : ℕ) : ℕ := catalan m

/-- **Catalan ↔ central binomial.** `(m+1) · C_m = binom(2m,m)` (Mathlib:
`catalan_eq_centralBinom_div` + `Nat.succ_dvd_centralBinom`). -/
theorem succ_mul_singletCount (m : ℕ) :
    (m + 1) * singletCount m = Nat.centralBinom m := by
  unfold singletCount
  rw [catalan_eq_centralBinom_div]
  exact Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom m)

/-- The singlet count is strictly positive. -/
theorem singletCount_pos (m : ℕ) : 0 < singletCount m := by
  have h := succ_mul_singletCount m
  have hcb : 0 < Nat.centralBinom m := Nat.centralBinom_pos m
  rcases Nat.eq_zero_or_pos (singletCount m) with h0 | h0
  · rw [h0, Nat.mul_zero] at h; omega
  · exact h0

/-- Exact formula for `log (n!)` via `stirlingSeq` (rearranged
`Stirling.log_stirlingSeq_formula`). -/
theorem log_factorial_formula (n : ℕ) :
    Real.log (n.factorial : ℝ)
      = Real.log (Stirling.stirlingSeq n) + (1 / 2) * Real.log (2 * n)
        + n * Real.log (n / Real.exp 1) := by
  have h := Stirling.log_stirlingSeq_formula n
  linarith

/-- **Algebraic identity (m ≥ 1).** The target difference equals a pure `stirlingSeq`
remainder plus `log m − log(m+1)` — the Stirling expansion of
`log(catalan m) = log((2m)!) − 2·log(m!) − log(m+1)` with the `m·log m` and `m` terms
cancelling, leaving the `−3/2`. -/
theorem log_singletCount_sub_eq (m : ℕ) (hm : 1 ≤ m) :
    Real.log (singletCount m) - (2 * m * Real.log 2 - (3 / 2) * Real.log m)
      = (Real.log (Stirling.stirlingSeq (2 * m)) - 2 * Real.log (Stirling.stirlingSeq m))
        + (Real.log (m : ℝ) - Real.log ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hcat_pos : (0 : ℝ) < (catalan m : ℝ) := by
    have h := singletCount_pos m; unfold singletCount at h; exact_mod_cast h
  have hcb_pos : (0 : ℝ) < (Nat.centralBinom m : ℝ) := by exact_mod_cast Nat.centralBinom_pos m
  have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  -- (m+1)·catalan = centralBinom  (over ℝ)
  have hid1 : ((m : ℝ) + 1) * (catalan m : ℝ) = (Nat.centralBinom m : ℝ) := by
    have h := succ_mul_singletCount m; unfold singletCount at h
    have h' : (((m + 1) * catalan m : ℕ) : ℝ) = ((Nat.centralBinom m : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; linarith
  -- centralBinom·(m!)² = (2m)!  (over ℝ)
  have hid2 : (Nat.centralBinom m : ℝ) * (m.factorial : ℝ) ^ 2 = ((2 * m).factorial : ℝ) := by
    have hc := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rw [show 2 * m - m = m by omega] at hc
    have hnat : Nat.centralBinom m * (m.factorial * m.factorial) = (2 * m).factorial := by
      rw [Nat.centralBinom_eq_two_mul_choose, ← mul_assoc]; exact hc
    rw [pow_two]; exact_mod_cast hnat
  -- log(catalan) = log(centralBinom) − log(m+1)
  have hlogcat : Real.log (catalan m : ℝ)
      = Real.log (Nat.centralBinom m : ℝ) - Real.log ((m : ℝ) + 1) := by
    have hmul := Real.log_mul (ne_of_gt hm1pos) (ne_of_gt hcat_pos)
    rw [hid1] at hmul; linarith
  -- log(centralBinom) = log((2m)!) − 2·log(m!)
  have hlogcb : Real.log (Nat.centralBinom m : ℝ)
      = Real.log ((2 * m).factorial : ℝ) - 2 * Real.log (m.factorial : ℝ) := by
    have hsq : Real.log ((m.factorial : ℝ) ^ 2) = 2 * Real.log (m.factorial : ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    have hmul := Real.log_mul (ne_of_gt hcb_pos) (by positivity : (m.factorial : ℝ) ^ 2 ≠ 0)
    rw [hid2, hsq] at hmul; linarith
  -- elementary composite-log expansions
  have e4 : Real.log (2 * (2 * (m : ℝ))) = Real.log 2 + (Real.log 2 + Real.log (m : ℝ)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) hmne]
  have e2 : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log (m : ℝ) := Real.log_mul (by norm_num) hmne
  have e2e : Real.log ((2 * (m : ℝ)) / Real.exp 1) = Real.log 2 + Real.log (m : ℝ) - 1 := by
    rw [Real.log_div (by positivity) (Real.exp_ne_zero 1), Real.log_exp, e2]
  have eme : Real.log ((m : ℝ) / Real.exp 1) = Real.log (m : ℝ) - 1 := by
    rw [Real.log_div hmne (Real.exp_ne_zero 1), Real.log_exp]
  rw [show (singletCount m : ℝ) = (catalan m : ℝ) from rfl, hlogcat, hlogcb,
      log_factorial_formula (2 * m), log_factorial_formula m]
  push_cast
  rw [e4, e2, e2e, eme]
  ring

/--
**Core asymptotic (Kaul–Majumdar −3/2 from the literal count).**
`log (C_m) − (2m·log 2 − (3/2)·log m)` is bounded as `m → ∞`. Equivalently the
literal singlet count grows as `C_m ≍ 4^m · m^{-3/2}` (up to a constant), so its log
carries exactly the `−3/2` log-correction coefficient.

PROVIDED SOLUTION (Stage 3a target, MCP loop):
`Stirling.factorial_isEquivalent_stirling` gives `n! ~ √(2πn)(n/e)^n`. Then
`centralBinom m = (2m)!/(m!)^2 ~ 4^m/√(πm)` and `C_m = centralBinom m/(m+1)
~ 4^m/(√π · m^{3/2})`. Taking `log`: `2m·log 2 − (3/2)·log m − (1/2)·log π + o(1)`,
so the displayed difference → `−(1/2)·log π`, hence is `O(1)`. The `−3/2`
decomposes as `−1/2` (from `√(πm)` in `centralBinom`) `− 1` (from the `1/(m+1)`).
-/
theorem log_singletCount_sub_isBigO :
    (fun m : ℕ => Real.log (singletCount m) - (2 * m * Real.log 2 - (3 / 2) * Real.log m))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  -- log (stirlingSeq m) → log √π  (stirlingSeq → √π; log continuous at √π > 0)
  have hst : Tendsto (fun m : ℕ => Real.log (Stirling.stirlingSeq m)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    ((Real.continuousAt_log (ne_of_gt hsp)).tendsto).comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have hst2 : Tendsto (fun m : ℕ => Real.log (Stirling.stirlingSeq (2 * m))) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := hst.comp h2
  -- elementary: log m − log (m+1) → 0
  have hlog1 : Tendsto (fun m : ℕ => Real.log (m : ℝ) - Real.log ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have hone : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hdiv : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 1) := by
      have heq : (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1))
          = (fun m : ℕ => 1 - 1 / ((m : ℝ) + 1)) := by
        funext m
        have hne : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      rw [heq]
      simpa using tendsto_const_nhds.sub hone
    have hlogdiv : Tendsto (fun m : ℕ => Real.log ((m : ℝ) / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      have hc := ((Real.continuousAt_log one_ne_zero).tendsto).comp hdiv
      simpa using hc
    apply Filter.Tendsto.congr' _ hlogdiv
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    rw [Real.log_div (ne_of_gt hm0) (by positivity)]
  -- assemble the limit of the stirlingSeq remainder (→ log√π − 2 log√π + 0 = −½ log π)
  have hg : Tendsto (fun m : ℕ =>
      (Real.log (Stirling.stirlingSeq (2 * m)) - 2 * Real.log (Stirling.stirlingSeq m))
        + (Real.log (m : ℝ) - Real.log ((m : ℝ) + 1))) atTop
      (𝓝 ((Real.log (Real.sqrt Real.pi) - 2 * Real.log (Real.sqrt Real.pi)) + 0)) :=
    (hst2.sub (hst.const_mul 2)).add hlog1
  -- the target equals that remainder eventually (Lemma A) ⟹ tends to the same limit ⟹ O(1)
  have htends : Tendsto (fun m : ℕ => Real.log (singletCount m)
        - (2 * m * Real.log 2 - (3 / 2) * Real.log m)) atTop
      (𝓝 ((Real.log (Real.sqrt Real.pi) - 2 * Real.log (Real.sqrt Real.pi)) + 0)) := by
    apply Filter.Tendsto.congr' _ hg
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact (log_singletCount_sub_eq m hm).symm
  exact htends.isBigO_one ℝ

/-! ## Wave 7C — the quantitative `O(1/m)` rate

The `O(1)` result above only pins the leading + log slope. Wave 7C strengthens it to the
genuine `O(1/m)` rate, identifying the literal constant `c₀ = −½·log π` (so the full
asymptotic is `log C_m = 2m·log2 − (3/2)·log m − ½·log π + O(1/m)`). The one new ingredient
is a quantitative rate of convergence of `stirlingSeq` to `√π`, built here from Mathlib's
telescoping increment bound `Stirling.log_stirlingSeq_diff_le`. -/

/-- **Lower bound on the `stirlingSeq` log-remainder.** For `n ≥ 1`,
`log (stirlingSeq n) − log √π ≥ 0` (since `√π ≤ stirlingSeq n`, Mathlib
`Stirling.sqrt_pi_le_stirlingSeq`, and `log` is monotone). -/
theorem log_stirlingSeq_sub_log_sqrt_pi_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) := by
  have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hle : Real.sqrt Real.pi ≤ Stirling.stirlingSeq n :=
    Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have := Real.log_le_log hsp hle
  linarith

/-- **Quantitative rate of convergence of `stirlingSeq` to `√π`** (the explicit `O(1/n)`
discrete Stirling remainder — missing from Mathlib). For `n ≥ 1`,
`log (stirlingSeq n) − log √π ≤ 1/(12 n)`. The drop to the limit is the telescoping tail
`∑_{k ≥ n} (log σ k − log σ(k+1))`, each increment `≤ 1/(12 k (k+1))` (Mathlib
`Stirling.log_stirlingSeq_diff_le`), summing to `1/(12 n)`. -/
theorem log_stirlingSeq_sub_log_sqrt_pi_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) ≤ 1 / (12 * (n : ℝ)) := by
  have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hflim : Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq k)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    ((Real.continuousAt_log (ne_of_gt hsp)).tendsto).comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlim : Tendsto (fun N : ℕ =>
      Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq N)) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi))) :=
    tendsto_const_nhds.sub hflim
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  set h : ℕ → ℝ := fun k => 1 / ((n : ℝ) + (k : ℝ)) with hh
  -- telescoping identity for the log-differences
  have htel : Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq N)
      = ∑ j ∈ Finset.range (N - n),
          (Real.log (Stirling.stirlingSeq (n + j)) - Real.log (Stirling.stirlingSeq (n + j + 1))) := by
    have hts := Finset.sum_range_sub' (fun j => Real.log (Stirling.stirlingSeq (n + j))) (N - n)
    simp only [Nat.add_zero, Nat.add_sub_cancel' hN] at hts
    exact hts.symm
  rw [htel]
  -- termwise bound by (1/12)(h j - h (j+1))
  have key : ∀ j ∈ Finset.range (N - n),
      Real.log (Stirling.stirlingSeq (n + j)) - Real.log (Stirling.stirlingSeq (n + j + 1))
        ≤ (1 / 12) * (h j - h (j + 1)) := by
    intro j _
    have hd := Stirling.log_stirlingSeq_diff_le (n + j)
    have hnj : (0 : ℝ) < (n : ℝ) + (j : ℝ) := by positivity
    have hnj1 : (0 : ℝ) < (n : ℝ) + (j : ℝ) + 1 := by positivity
    have hpf : (1 / 12 : ℝ) * (h j - h (j + 1))
        = 1 / (12 * ((n : ℝ) + j) * ((n : ℝ) + j + 1)) := by
      simp only [hh]
      push_cast
      field_simp
      ring
    rw [hpf]
    calc Real.log (Stirling.stirlingSeq (n + j)) - Real.log (Stirling.stirlingSeq (n + j + 1))
        ≤ 1 / (12 * ((n + j : ℕ) : ℝ) * (((n + j : ℕ) : ℝ) + 1)) := hd
      _ = 1 / (12 * ((n : ℝ) + j) * ((n : ℝ) + j + 1)) := by push_cast; ring_nf
  calc ∑ j ∈ Finset.range (N - n),
          (Real.log (Stirling.stirlingSeq (n + j)) - Real.log (Stirling.stirlingSeq (n + j + 1)))
      ≤ ∑ j ∈ Finset.range (N - n), (1 / 12 : ℝ) * (h j - h (j + 1)) := Finset.sum_le_sum key
    _ = (1 / 12 : ℝ) * (h 0 - h (N - n)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub' h (N - n)]
    _ ≤ 1 / (12 * (n : ℝ)) := by
        have hh0 : h 0 = 1 / (n : ℝ) := by simp [hh]
        have hhNn : h (N - n) = 1 / (N : ℝ) := by
          simp only [hh]
          rw [Nat.cast_sub hN]
          congr 1
          ring
        rw [hh0, hhNn]
        have hN0 : (0 : ℝ) ≤ 1 / (12 * (N : ℝ)) := by positivity
        have hrw : (1 / 12 : ℝ) * (1 / (n : ℝ) - 1 / (N : ℝ))
            = 1 / (12 * (n : ℝ)) - 1 / (12 * (N : ℝ)) := by ring
        rw [hrw]; linarith

/-- **`stirlingSeq` log-remainder is `O(1/n)`.** Immediate from the two-sided bound
`0 ≤ log σ n − log √π ≤ 1/(12 n)`. -/
theorem log_stirlingSeq_sub_log_sqrt_pi_isBigO :
    (fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi))
      =O[atTop] (fun n : ℕ => (1 : ℝ) / n) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / 12, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hub := log_stirlingSeq_sub_log_sqrt_pi_le n hn
  have hlb := log_stirlingSeq_sub_log_sqrt_pi_nonneg n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlb,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)),
    show (1 / 12 : ℝ) * (1 / (n : ℝ)) = 1 / (12 * (n : ℝ)) by ring]
  exact hub

/--
**Wave 7C core — the Kaul–Majumdar `−3/2` at the `O(1/m)` RATE.**
`log (C_m) − (2m·log 2 − (3/2)·log m − ½·log π) = O(1/m)`. This strengthens
`log_singletCount_sub_isBigO` (which only gave `O(1)`): the literal constant is
`c₀ = −½·log π = log √π − 2·log √π`, and the remainder beyond leading+log+const is
genuinely `O(1/m)`. Decomposition (via `log_singletCount_sub_eq`): the target equals
`[log σ(2m) − log √π] − 2·[log σ m − log √π] + [log m − log(m+1)]`, three `O(1/m)` pieces. -/
theorem log_singletCount_sub_rate :
    (fun m : ℕ => Real.log (singletCount m)
        - (2 * m * Real.log 2 - (3 / 2) * Real.log m - (1 / 2) * Real.log Real.pi))
      =O[atTop] (fun m : ℕ => (1 : ℝ) / m) := by
  -- piece P2: log σ m − log √π = O(1/m)
  have hP2 := log_stirlingSeq_sub_log_sqrt_pi_isBigO
  -- piece P1: log σ(2m) − log √π = O(1/m)
  have hP1 : (fun m : ℕ => Real.log (Stirling.stirlingSeq (2 * m)) - Real.log (Real.sqrt Real.pi))
      =O[atTop] (fun m : ℕ => (1 : ℝ) / m) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have h2m : 1 ≤ 2 * m := by omega
    have hub := log_stirlingSeq_sub_log_sqrt_pi_le (2 * m) h2m
    have hlb := log_stirlingSeq_sub_log_sqrt_pi_nonneg (2 * m) h2m
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlb,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)), one_mul]
    have hcast : (1 : ℝ) / (12 * ((2 * m : ℕ) : ℝ)) ≤ 1 / (m : ℝ) := by
      have hc : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      rw [hc]
      exact one_div_le_one_div_of_le hm0 (by nlinarith [hm0])
    linarith [hub, hcast]
  -- piece P3: log m − log(m+1) = O(1/m)
  have hP3 : (fun m : ℕ => Real.log (m : ℝ) - Real.log ((m : ℝ) + 1))
      =O[atTop] (fun m : ℕ => (1 : ℝ) / m) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hquot : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)
        = Real.log (((m : ℝ) + 1) / (m : ℝ)) :=
      (Real.log_div (by positivity) hm0.ne').symm
    have hpos : 0 ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
    have hle : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ ((m : ℝ) + 1) / (m : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsub : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by field_simp; ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)), one_mul, abs_sub_comm, hquot,
      abs_of_nonneg hpos]
    linarith [hle, hsub]
  -- assemble: target = P1 − 2·P2 + P3 eventually (using ½·log π = log √π)
  have hcomb := (hP1.sub (hP2.const_mul_left 2)).add hP3
  refine hcomb.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have heq := log_singletCount_sub_eq m hm
  have hsqrtpi : Real.log (Real.sqrt Real.pi) = (1 / 2) * Real.log Real.pi := by
    rw [Real.log_sqrt Real.pi_pos.le]; ring
  rw [hsqrtpi]
  linear_combination -heq

end LaplaceMethodAsymptotic
end SKEFTHawking
