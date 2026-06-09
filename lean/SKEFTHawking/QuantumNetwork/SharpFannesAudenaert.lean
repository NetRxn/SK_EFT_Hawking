import SKEFTHawking.QuantumNetwork.FannesAudenaert
import SKEFTHawking.QuantumNetwork.MirskyUnconditional
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

open Matrix
open scoped BigOperators ComplexOrder

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

/-! ## S2 — finite Fano via the maximal coupling

The conditional-entropy layer. Rather than build an abstract `Fin`-indexed conditional entropy, we
work directly with the explicit **maximal (overlap-plus-product) coupling** `J x y` of the eigenvalue
distributions `p, q` and bound `H(X|Y) = H(J) − H(q)` column-by-column: each column's tail entropy is
controlled by `spreading_bound` (the `log(d−1)` part) and its binary split by `negMulLog`-concavity (the
`binEntropy` part), assembled via the conditional-entropy Jensen step `sum_g_le_binEntropy`. No simplex
optimization, no majorization API. -/

/-- **`n`-ary subadditivity of `negMulLog`:** `η(∑ᵢ fᵢ) ≤ ∑ᵢ η(fᵢ)` for `f ≥ 0`. Iterates the two-term
`negMulLog_add_le`; the entropy-merge direction (lumping outcomes never increases entropy contribution).
Supplies `H(p) ≤ H(J)` row-by-row in the coupling argument. -/
theorem negMulLog_sum_le {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) :
    Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.negMulLog_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc Real.negMulLog (f a + ∑ i ∈ s, f i)
        ≤ Real.negMulLog (f a) + Real.negMulLog (∑ i ∈ s, f i) :=
          negMulLog_add_le (hf a) (Finset.sum_nonneg (fun i _ => hf i))
      _ ≤ Real.negMulLog (f a) + ∑ i ∈ s, Real.negMulLog (f i) := by linarith [ih]

/-- **Column half-step:** `(a+b)·η(b/(a+b)) = η(b) + b·log(a+b)` for `a+b > 0` (`η = negMulLog`); holds
even when `b = 0` (both sides `0`, no `log 0` incurred). -/
theorem mul_negMulLog_div_eq {a b : ℝ} (hb : 0 ≤ b) (hab : 0 < a + b) :
    (a + b) * Real.negMulLog (b / (a + b)) = Real.negMulLog b + b * Real.log (a + b) := by
  have hab' : a + b ≠ 0 := ne_of_gt hab
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · rw [← hb0]; simp [Real.negMulLog_zero, zero_div]
  · rw [Real.negMulLog, Real.negMulLog, Real.log_div (ne_of_gt hbpos) hab']
    field_simp
    ring

/-- **Conditional-entropy column term as a binary entropy:** `η(a) + η(b) − η(a+b) = (a+b)·H₂(b/(a+b))`
for `a, b ≥ 0` (`η = negMulLog`, `H₂ = binEntropy`); both sides `0` when `a+b = 0`. Rewrites each column
contribution `g(a,b)` of the maximal coupling as `q_y · H₂(error rate)`, readying the Jensen step. -/
theorem negMulLog_add_sub_eq_mul_binEntropy {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog a + Real.negMulLog b - Real.negMulLog (a + b)
      = (a + b) * Real.binEntropy (b / (a + b)) := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h0 | hpos
  · have ha0 : a = 0 := le_antisymm (by linarith) ha
    have hb0 : b = 0 := le_antisymm (by linarith) hb
    simp [ha0, hb0, Real.negMulLog_zero]
  · have hba : 0 < b + a := by linarith
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have h1 : (1 : ℝ) - b / (a + b) = a / (a + b) := by field_simp; ring
    rw [h1, mul_add]
    have e1 : (a + b) * Real.negMulLog (b / (a + b)) = Real.negMulLog b + b * Real.log (a + b) :=
      mul_negMulLog_div_eq hb hpos
    have e2 : (a + b) * Real.negMulLog (a / (a + b)) = Real.negMulLog a + a * Real.log (a + b) := by
      have h := mul_negMulLog_div_eq (a := b) (b := a) ha hba
      rwa [add_comm b a] at h
    rw [e1, e2]
    simp only [Real.negMulLog_def]
    ring

/-- **Conditional-entropy Jensen step.** For weights `Q ≥ 0` summing to `1` with `0 ≤ Mᵢ ≤ Qᵢ`, the sum
of the coupling's column contributions is bounded by the binary entropy of the total off-diagonal mass:
`∑ᵢ (η(Qᵢ−Mᵢ) + η(Mᵢ) − η(Qᵢ)) ≤ H₂(∑ᵢ Mᵢ)`. Each term is `Qᵢ·H₂(Mᵢ/Qᵢ)`
(`negMulLog_add_sub_eq_mul_binEntropy`); concavity of `binEntropy` (`ConcaveOn.le_map_sum`) caps the
`Q`-weighted average of conditional binary entropies by the binary entropy at the mean error `∑ Mᵢ`. -/
theorem sum_g_le_binEntropy {α : Type*} (s : Finset α) (Q M : α → ℝ)
    (hQ : ∀ i ∈ s, 0 ≤ Q i) (hsum : ∑ i ∈ s, Q i = 1)
    (hM0 : ∀ i ∈ s, 0 ≤ M i) (hMQ : ∀ i ∈ s, M i ≤ Q i) :
    ∑ i ∈ s, (Real.negMulLog (Q i - M i) + Real.negMulLog (M i) - Real.negMulLog (Q i))
      ≤ Real.binEntropy (∑ i ∈ s, M i) := by
  have hterm : ∀ i ∈ s, Real.negMulLog (Q i - M i) + Real.negMulLog (M i) - Real.negMulLog (Q i)
      = Q i * Real.binEntropy (M i / Q i) := by
    intro i hi
    have h := negMulLog_add_sub_eq_mul_binEntropy (sub_nonneg.mpr (hMQ i hi)) (hM0 i hi)
    rwa [sub_add_cancel] at h
  rw [Finset.sum_congr rfl hterm]
  have hconc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) Real.binEntropy := Real.strictConcave_binEntropy.concaveOn
  have hmem : ∀ i ∈ s, M i / Q i ∈ Set.Icc (0:ℝ) 1 := by
    intro i hi
    rcases eq_or_lt_of_le (hQ i hi) with hQ0 | hQpos
    · rw [← hQ0, div_zero]; exact ⟨le_refl _, zero_le_one⟩
    · exact ⟨div_nonneg (hM0 i hi) (le_of_lt hQpos), (div_le_one hQpos).mpr (hMQ i hi)⟩
  have hJ := hconc.le_map_sum hQ hsum hmem
  simp only [smul_eq_mul] at hJ
  have hreduce : ∑ i ∈ s, Q i * (M i / Q i) = ∑ i ∈ s, M i := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases eq_or_lt_of_le (hQ i hi) with hQ0 | hQpos
    · have hMi0 : M i = 0 := le_antisymm (by have := hMQ i hi; rwa [← hQ0] at this) (hM0 i hi)
      rw [← hQ0, hMi0]; simp
    · field_simp
  rwa [hreduce] at hJ

/-! ## S3 — assemble: the classical sharp Fannes–Audenaert inequality -/

/-- **One direction of the classical sharp Fannes–Audenaert bound.** For probability distributions
`p, q : Fin d → ℝ` (`d ≥ 2`) with total-variation `T = ½∑|pᵢ−qᵢ| ≤ 1 − 1/d`, the Shannon-entropy
difference obeys `H(p) − H(q) ≤ qaryEntropy d T = T·log(d−1) + H₂(T)`. Proof by the **maximal coupling**:
the explicit overlap-plus-product joint `J x y = min(pₓ,qₓ)·[x=y] + (pₓ−qₓ)₊(qᵧ−pᵧ)₊/T` has marginals
`p, q`; subadditivity gives `H(p) ≤ H(J)`; and `H(J) − H(q) ≤ qaryEntropy d T'` (`T' = ∑ off-diagonal
column mass ≤ T`) by per-column `spreading_bound` (the `log(d−1)` part) and `sum_g_le_binEntropy` (the
binary part); `qaryEntropy` monotonicity transports `T' ↦ T`. -/
theorem sharp_fannes_oneway {d : ℕ} (hd : 2 ≤ d) (p q : Fin d → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (hTle : (∑ i, |p i - q i|) / 2 ≤ 1 - 1 / (d : ℝ)) :
    (∑ i, Real.negMulLog (p i)) - (∑ i, Real.negMulLog (q i))
      ≤ Real.qaryEntropy d ((∑ i, |p i - q i|) / 2) := by
  classical
  set T := (∑ i, |p i - q i|) / 2 with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hT1 : T ≤ 1 := by have h1d : (0:ℝ) ≤ 1 / (d:ℝ) := by positivity
                         linarith [hTle]
  set pm : Fin d → ℝ := fun i => max (p i - q i) 0 with hpmdef
  set qm : Fin d → ℝ := fun i => max (q i - p i) 0 with hqmdef
  have hpm0 : ∀ i, 0 ≤ pm i := fun i => le_max_right _ _
  have hqm0 : ∀ i, 0 ≤ qm i := fun i => le_max_right _ _
  have habs : ∀ i, |p i - q i| = pm i + qm i := by
    intro i; simp only [hpmdef, hqmdef]
    rcases le_total (p i) (q i) with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hdiffpm : ∀ i, p i - q i = pm i - qm i := by
    intro i; simp only [hpmdef, hqmdef]
    rcases le_total (p i) (q i) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hsumabs : ∑ i, |p i - q i| = (∑ i, pm i) + ∑ i, qm i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => habs i)
  have hsumdiff : (∑ i, pm i) - ∑ i, qm i = 0 := by
    have he : ∑ i, (pm i - qm i) = ∑ i, (p i - q i) :=
      Finset.sum_congr rfl (fun i _ => (hdiffpm i).symm)
    rw [← Finset.sum_sub_distrib, he, Finset.sum_sub_distrib, hp1, hq1]; ring
  have h2T : (∑ i, pm i) + ∑ i, qm i = 2 * T := by rw [← hsumabs, hTdef]; ring
  have hsum_pm : ∑ i, pm i = T := by linarith [h2T, hsumdiff]
  have hsum_qm : ∑ i, qm i = T := by linarith [h2T, hsumdiff]
  rcases eq_or_lt_of_le hT0 with hTeq | hTpos
  · -- T = 0 ⟹ p = q, so the LHS is 0 and the RHS is the nonnegative qaryEntropy
    have hzero : (∑ i, Real.negMulLog (p i)) - ∑ i, Real.negMulLog (q i) = 0 := by
      have hpq : ∀ i, p i = q i := by
        intro i
        have hsa0 : ∑ j, |p j - q j| = 0 := by rw [hTdef] at hTeq; linarith
        have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (p j - q j))).mp hsa0
        have hi := hall i (Finset.mem_univ i)
        have : p i - q i = 0 := abs_eq_zero.mp hi
        linarith
      rw [Finset.sum_congr rfl (fun i _ => by rw [hpq i])]; ring
    rw [hzero]
    exact Real.qaryEntropy_nonneg hT0 hT1
  · -- T > 0
    have hTne : T ≠ 0 := ne_of_gt hTpos
    set J : Fin d → Fin d → ℝ :=
      fun x y => (if x = y then min (p x) (q x) else 0) + pm x * qm y / T with hJdef
    have hJ0 : ∀ x y, 0 ≤ J x y := by
      intro x y
      simp only [hJdef]
      have h1 : 0 ≤ (if x = y then min (p x) (q x) else 0) := by
        split
        · exact le_min (hp0 x) (hq0 x)
        · exact le_refl 0
      have h2 : 0 ≤ pm x * qm y / T := div_nonneg (mul_nonneg (hpm0 x) (hqm0 y)) hTpos.le
      linarith
    have hJyy : ∀ y, J y y = min (p y) (q y) + pm y * qm y / T := by
      intro y; simp only [hJdef, if_true]
    have hrow : ∀ x, ∑ y, J x y = p x := by
      intro x
      have hmin : min (p x) (q x) + pm x = p x := by
        simp only [hpmdef]
        rcases le_total (p x) (q x) with h | h
        · rw [min_eq_left h, max_eq_right (by linarith)]; ring
        · rw [min_eq_right h, max_eq_left (by linarith)]; ring
      have hprod : ∑ y, pm x * qm y / T = pm x := by
        have e : ∑ y, pm x * qm y / T = pm x / T * ∑ y, qm y := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by ring)
        rw [e, hsum_qm]; field_simp
      simp only [hJdef]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ x (fun _ => min (p x) (q x)),
        if_pos (Finset.mem_univ x), hprod, hmin]
    have hcol : ∀ y, ∑ x, J x y = q y := by
      intro y
      have hmin : min (p y) (q y) + qm y = q y := by
        simp only [hqmdef]
        rcases le_total (p y) (q y) with h | h
        · rw [min_eq_left h, max_eq_left (by linarith)]; ring
        · rw [min_eq_right h, max_eq_right (by linarith)]; ring
      have hprod : ∑ x, pm x * qm y / T = qm y := by
        have e : ∑ x, pm x * qm y / T = (∑ x, pm x) * (qm y / T) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun x _ => by ring)
        rw [e, hsum_pm]; field_simp
      simp only [hJdef]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ y (fun x => min (p x) (q x)),
        if_pos (Finset.mem_univ y), hprod, hmin]
    set m : Fin d → ℝ := fun y => q y - J y y with hmdef
    have hm0 : ∀ y, 0 ≤ m y := by
      intro y
      have hle : J y y ≤ ∑ x, J x y := Finset.single_le_sum (fun x _ => hJ0 x y) (Finset.mem_univ y)
      rw [hcol y] at hle
      simp only [hmdef]; linarith
    have hmq : ∀ y, m y ≤ q y := by
      intro y; simp only [hmdef]; linarith [hJ0 y y]
    have hJyy_eq : ∀ y, J y y = q y - m y := fun y => by simp only [hmdef]; ring
    set T' := ∑ y, m y with hT'def
    have hT'0 : 0 ≤ T' := Finset.sum_nonneg (fun y _ => hm0 y)
    -- T' ≤ T
    have hmin_eq : ∀ y, min (p y) (q y) = q y - qm y := by
      intro y; simp only [hqmdef]
      rcases le_total (p y) (q y) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]; ring
      · rw [min_eq_right h, max_eq_right (by linarith)]; ring
    have hsumJyy_ge : (1 : ℝ) - T ≤ ∑ y, J y y := by
      have e : ∑ y, J y y = (∑ y, min (p y) (q y)) + ∑ y, pm y * qm y / T := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun y _ => hJyy y)
      have emin : ∑ y, min (p y) (q y) = 1 - T := by
        rw [Finset.sum_congr rfl (fun y _ => hmin_eq y), Finset.sum_sub_distrib, hq1, hsum_qm]
      have eprod : 0 ≤ ∑ y, pm y * qm y / T :=
        Finset.sum_nonneg (fun y _ => div_nonneg (mul_nonneg (hpm0 y) (hqm0 y)) hTpos.le)
      rw [e, emin]; linarith
    have hT'leT : T' ≤ T := by
      have hT'eq : T' = 1 - ∑ y, J y y := by
        rw [hT'def]; simp only [hmdef]; rw [Finset.sum_sub_distrib, hq1]
      rw [hT'eq]; linarith [hsumJyy_ge]
    -- (I) H(p) ≤ H(J)
    have hI : ∑ x, Real.negMulLog (p x) ≤ ∑ x, ∑ y, Real.negMulLog (J x y) := by
      apply Finset.sum_le_sum
      intro x _
      rw [← hrow x]
      exact negMulLog_sum_le Finset.univ (fun y => J x y) (fun y => hJ0 x y)
    -- (II) per-column bound, then summed
    have hcol_bound : ∀ y, (∑ x, Real.negMulLog (J x y)) - Real.negMulLog (q y)
        ≤ (Real.negMulLog (J y y) + Real.negMulLog (m y) - Real.negMulLog (q y))
          + m y * Real.log ((d : ℝ) - 1) := by
      intro y
      have hsplit : ∑ x, Real.negMulLog (J x y)
          = Real.negMulLog (J y y) + ∑ x ∈ Finset.univ \ {y}, Real.negMulLog (J x y) := by
        rw [← Finset.erase_eq,
          Finset.add_sum_erase Finset.univ (fun x => Real.negMulLog (J x y)) (Finset.mem_univ y)]
      have hmcol : ∑ x ∈ Finset.univ \ {y}, J x y = m y := by
        simp only [hmdef]
        rw [← Finset.erase_eq]
        have hae := Finset.add_sum_erase Finset.univ (fun x => J x y) (Finset.mem_univ y)
        rw [hcol y] at hae
        linarith [hae]
      have hspread := spreading_bound hd (fun x => J x y) (fun x => hJ0 x y) y
      rw [hmcol] at hspread
      rw [hsplit]; linarith [hspread]
    have hII : (∑ x, ∑ y, Real.negMulLog (J x y)) - ∑ y, Real.negMulLog (q y)
        ≤ Real.qaryEntropy d T' := by
      rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
      have hstep : ∑ y, ((∑ x, Real.negMulLog (J x y)) - Real.negMulLog (q y))
          ≤ ∑ y, ((Real.negMulLog (J y y) + Real.negMulLog (m y) - Real.negMulLog (q y))
              + m y * Real.log ((d : ℝ) - 1)) :=
        Finset.sum_le_sum (fun y _ => hcol_bound y)
      refine hstep.trans ?_
      rw [Finset.sum_add_distrib]
      have hlog : ∑ y, m y * Real.log ((d : ℝ) - 1) = T' * Real.log ((d : ℝ) - 1) := by
        rw [← Finset.sum_mul, ← hT'def]
      have hg : ∑ y, (Real.negMulLog (J y y) + Real.negMulLog (m y) - Real.negMulLog (q y))
          ≤ Real.binEntropy T' := by
        rw [hT'def, Finset.sum_congr rfl (fun y _ => by rw [hJyy_eq y])]
        exact sum_g_le_binEntropy Finset.univ q m (fun y _ => hq0 y) hq1
          (fun y _ => hm0 y) (fun y _ => hmq y)
      have hqe : Real.qaryEntropy d T' = T' * Real.log ((d : ℝ) - 1) + Real.binEntropy T' := by
        unfold Real.qaryEntropy; push_cast; ring
      rw [hlog, hqe]; linarith [hg]
    calc (∑ i, Real.negMulLog (p i)) - ∑ i, Real.negMulLog (q i)
        ≤ (∑ x, ∑ y, Real.negMulLog (J x y)) - ∑ i, Real.negMulLog (q i) := by linarith [hI]
      _ ≤ Real.qaryEntropy d T' := hII
      _ ≤ Real.qaryEntropy d T :=
          (Real.qaryEntropy_strictMonoOn hd).monotoneOn ⟨hT'0, le_trans hT'leT hTle⟩ ⟨hT0, hTle⟩ hT'leT

/-- **Classical sharp Fannes–Audenaert inequality (`log(d−1)` constant).** For probability distributions
`p, q : Fin d → ℝ` (`d ≥ 2`) with total-variation distance `T = ½∑ᵢ|pᵢ−qᵢ| ≤ 1 − 1/d`, the Shannon
entropies obey `|H(p) − H(q)| ≤ qaryEntropy d T = T·log(d−1) + H₂(T)` (`H = ∑ negMulLog`). Both directions
follow from the one-sided maximal-coupling bound `sharp_fannes_oneway` (the RHS is symmetric in `p, q`
since `∑|pᵢ−qᵢ| = ∑|qᵢ−pᵢ|`). This is the sharp `log(d−1)` improvement over the `log d` Fannes envelope
`fannes_entropy_bound`; it is exactly the classical content of the `hAud` hypothesis of
`quantum_fannes_audenaert`. -/
theorem sharp_fannes_classical {d : ℕ} (hd : 2 ≤ d) (p q : Fin d → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (hTle : (∑ i, |p i - q i|) / 2 ≤ 1 - 1 / (d : ℝ)) :
    |(∑ i, Real.negMulLog (p i)) - (∑ i, Real.negMulLog (q i))|
      ≤ Real.qaryEntropy d ((∑ i, |p i - q i|) / 2) := by
  have hsymm : ∑ i, |q i - p i| = ∑ i, |p i - q i| :=
    Finset.sum_congr rfl (fun i _ => abs_sub_comm (q i) (p i))
  rw [abs_le]
  refine ⟨?_, sharp_fannes_oneway hd p q hp0 hp1 hq0 hq1 hTle⟩
  have h := sharp_fannes_oneway hd q p hq0 hq1 hp0 hp1 (by rw [hsymm]; exact hTle)
  rw [hsymm] at h
  linarith [h]

/-! ## The unconditional quantum sharp Fannes–Audenaert bound (`hAud` discharged) -/

/-- **Quantum sharp Fannes–Audenaert continuity — FULLY UNCONDITIONAL (`hAud` discharged, sharp
`log(d−1)`).** For density operators `ρ, σ` (`d = dim ≥ 2`) with trace distance in the monotone regime
`½‖ρ−σ‖₁ ≤ 1 − 1/d`, the von Neumann entropies obey `|S(ρ) − S(σ)| ≤ qaryEntropy d (½‖ρ−σ‖₁)
= T·log(d−1) + H₂(T)` with `T = ½‖ρ−σ‖₁` — the Audenaert sharp constant `log(d−1)`, with **no residual
hypothesis**. This discharges the last hypothesis `hAud` of `quantum_fannes_audenaert`: the classical
sharp bound `sharp_fannes_classical` supplies it on the eigenvalue distributions (probability vectors via
`eigenvalues₀_mem_Icc` + trace `= 1`), the total-variation side-condition coming from `mirsky_unconditional`
(`∑ₖ|λ↓ₖρ−λ↓ₖσ| ≤ ‖ρ−σ‖₁`) and `hTV`. Combined with the already-unconditional Mirsky step, the entire
quantum continuity bound — `hB3`/Wielandt frame-existence eliminated, `hAud`/`log(d−1)` maximization now
proven — rests on no unproven residual. -/
theorem quantum_fannes_audenaert_sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hd : 2 ≤ Fintype.card ι)
    (hTV : traceNorm (ρ - σ) / 2 ≤ 1 - 1 / (Fintype.card ι : ℝ)) :
    |vonNeumannEntropy hρ.1.isHermitian - vonNeumannEntropy hσ.1.isHermitian|
      ≤ Real.qaryEntropy (Fintype.card ι) (traceNorm (ρ - σ) / 2) := by
  have hAud : |vonNeumannEntropy hρ.1.isHermitian - vonNeumannEntropy hσ.1.isHermitian|
      ≤ Real.qaryEntropy (Fintype.card ι)
          ((∑ k, |hρ.1.isHermitian.eigenvalues₀ k - hσ.1.isHermitian.eigenvalues₀ k|) / 2) := by
    rw [vonNeumannEntropy_eq_sum_negMulLog_eigenvalues₀ hρ.1.isHermitian,
      vonNeumannEntropy_eq_sum_negMulLog_eigenvalues₀ hσ.1.isHermitian]
    refine sharp_fannes_classical hd _ _ (fun k => (eigenvalues₀_mem_Icc hρ k).1) ?_
      (fun k => (eigenvalues₀_mem_Icc hσ k).1) ?_ ?_
    · rw [sum_eigenvalues₀_eq_trace_re hρ.1.isHermitian, hρ.2]; simp
    · rw [sum_eigenvalues₀_eq_trace_re hσ.1.isHermitian, hσ.2]; simp
    · have hM := mirsky_unconditional hρ.1.isHermitian hσ.1.isHermitian
      have hhalf : (∑ k, |hρ.1.isHermitian.eigenvalues₀ k - hσ.1.isHermitian.eigenvalues₀ k|) / 2
          ≤ traceNorm (ρ - σ) / 2 := by linarith [hM]
      linarith [hhalf, hTV]
  exact quantum_fannes_audenaert hρ.1.isHermitian hσ.1.isHermitian hd hTV hAud

end SKEFTHawking.QuantumNetwork
