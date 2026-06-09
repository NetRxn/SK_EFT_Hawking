import SKEFTHawking.QuantumNetwork.FannesAudenaert
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Phase 6AM Wave 6 — sharp Fannes–Audenaert `log(d−1)` constant

Discharges the `hAud` hypothesis of `QuantumNetwork/MirskyUnconditional.lean`'s
`quantum_fannes_audenaert` — the **classical sharp Audenaert envelope**
`|S(ρ)−S(σ)| ≤ Real.qaryEntropy d (½‖λ↓(ρ)−λ↓(σ)‖₁) = T·log(d−1) + H₂(T)` — by proving the classical
sharp Fannes–Audenaert inequality on the eigenvalue **probability** distributions and transporting it
through the `vonNeumannEntropy = ∑ negMulLog(eigenvalues₀)` bridge.

The shipped `FannesAudenaert.fannes_entropy_bound` gives only the weaker Fannes `log d` constant
(it does not use `∑ pᵢ = 1`). The sharp `log(d−1)` improvement comes from concentrating the `+T`
mass on a single outcome so the `−T` mass spreads over `d−1` outcomes — the
maximal-coupling + Fano-grouping route (Zhang 2007 / Sason 2013), which avoids simplex optimization.

Build plan (DR `Lit-Search/Phase-6AL/Formalizing the Sharp (Audenaert)…`):
* **S1 (this file, here):** the *spreading estimate* — Jensen on the `d−1` tail.
* **S2:** finite-alphabet Fano via `Fin`-indexed conditional entropy (the crux).
* **S3:** assemble + WLOG/`abs` glue → discharge `hAud`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open scoped BigOperators

/-- **Jensen for `negMulLog` over an arbitrary nonempty `Finset`** (the `Finset` generalization of
`sum_negMulLog_le_card_mul`): `∑_{i∈s} η(δᵢ) ≤ |s|·η((∑_{i∈s}δᵢ)/|s|)`, `η = negMulLog`. Uniform
weights `1/|s|` and concavity of `negMulLog`. -/
theorem sum_negMulLog_le_card_nsmul {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (δ : α → ℝ) (hδ : ∀ i ∈ s, 0 ≤ δ i) :
    ∑ i ∈ s, Real.negMulLog (δ i) ≤ (s.card : ℝ) * Real.negMulLog ((∑ i ∈ s, δ i) / s.card) := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hw0 : ∀ i ∈ s, (0 : ℝ) ≤ (1 / s.card : ℝ) := fun i _ => by positivity
  have hw1 : ∑ _i ∈ s, (1 / s.card : ℝ) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hcard)]
  have hmem : ∀ i ∈ s, δ i ∈ Set.Ici (0 : ℝ) := fun i hi => Set.mem_Ici.mpr (hδ i hi)
  have hJ := Real.concaveOn_negMulLog.le_map_sum hw0 hw1 hmem
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have harg : (1 / s.card : ℝ) * ∑ i ∈ s, δ i = (∑ i ∈ s, δ i) / s.card := by ring
  rw [harg] at hJ
  have h2 := mul_le_mul_of_nonneg_left hJ (le_of_lt hcard)
  rwa [← mul_assoc, mul_one_div, div_self (ne_of_gt hcard), one_mul] at h2

/-- **Closed form of the uniform-tail entropy:** `(d−1)·η(S/(d−1)) = S·log(d−1) + η(S)` for `S ≥ 0`,
`d ≥ 2` (`η = negMulLog`). Spreading mass `S` uniformly over `d−1` outcomes contributes
`S·log(d−1)` plus the binary `η(S)`. -/
theorem card_mul_negMulLog_div {d : ℕ} (hd : 2 ≤ d) {S : ℝ} (hS : 0 ≤ S) :
    ((d : ℝ) - 1) * Real.negMulLog (S / ((d : ℝ) - 1))
      = S * Real.log ((d : ℝ) - 1) + Real.negMulLog S := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rcases eq_or_lt_of_le hS with hS0 | hS0
  · simp [← hS0, Real.negMulLog_zero]
  · rw [Real.negMulLog, Real.negMulLog, Real.log_div (ne_of_gt hS0) (ne_of_gt hd1)]
    field_simp
    ring

/-- **S1 — spreading estimate.** For nonnegative `p : Fin d → ℝ` and any distinguished index `i₀`,
the tail entropy `∑_{i≠i₀} η(pᵢ)` is at most `(∑_{i≠i₀}pᵢ)·log(d−1) + η(∑_{i≠i₀}pᵢ)`: the uniform
spread over the remaining `d−1` outcomes maximizes the tail entropy. This is the `log(d−1)`-bearing
step of the sharp Fannes–Audenaert bound, and the DR's go/no-go gate. -/
theorem spreading_bound {d : ℕ} (hd : 2 ≤ d) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (i₀ : Fin d) :
    ∑ i ∈ Finset.univ \ {i₀}, Real.negMulLog (p i)
      ≤ (∑ i ∈ Finset.univ \ {i₀}, p i) * Real.log ((d : ℝ) - 1)
        + Real.negMulLog (∑ i ∈ Finset.univ \ {i₀}, p i) := by
  set s : Finset (Fin d) := Finset.univ \ {i₀} with hs
  have hscard : s.card = d - 1 := by
    rw [hs, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin]
  have hsne : s.Nonempty := by rw [← Finset.card_pos, hscard]; omega
  have hScard : ((s.card : ℝ)) = (d : ℝ) - 1 := by
    rw [hscard, Nat.cast_sub (by omega), Nat.cast_one]
  have hSnn : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg (fun i _ => hp i)
  have hJ := sum_negMulLog_le_card_nsmul s hsne p (fun i _ => hp i)
  rw [hScard] at hJ
  rw [card_mul_negMulLog_div hd hSnn] at hJ
  exact hJ

end SKEFTHawking.QuantumNetwork
