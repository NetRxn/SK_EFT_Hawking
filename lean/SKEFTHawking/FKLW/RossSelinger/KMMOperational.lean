/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 38) — the operational KMM z-rotation bound on ℂ⁸

The inc-36 headline gives the two columns of `W` ring-exactly; this file converts them into the
**operational state-level statement**: for any system amplitudes `α, β`, applying the embedded word
to the ancilla-initialized state `(α|0⟩+β|1⟩)⊗|00⟩` lands within squared ℓ²-distance
`|β|²·(2/4ᵏ + 2√2/2ᵏ)` of the ideal output `α|000⟩ + β·e^{iφ}|100⟩` — the KMM
`|β(e^{iφ}−γ)|² + |β|²‖g‖²` error (arXiv:1212.0822 §2.2), with the word length linear in `k`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.Gate3Unitary

set_option autoImplicit false

open scoped Matrix

namespace SKEFTHawking.RossSelinger
namespace Gate3

open ZOmegaSqrt2

/-- The ancilla-initialized input state `(α|0⟩ + β|1⟩) ⊗ |00⟩` on ℂ⁸. -/
def initState (α β : ℂ) : Fin 2 × Fin 2 × Fin 2 → ℂ := fun j =>
  if j = (0, 0, 0) then α else if j = (1, 0, 0) then β else 0

/-- The ideal output state `α|000⟩ + β·e^{iφ}|100⟩`. -/
noncomputable def targetState (φ : ℝ) (α β : ℂ) : Fin 2 × Fin 2 × Fin 2 → ℂ := fun i =>
  if i = (0, 0, 0) then α
  else if i = (1, 0, 0) then β * Complex.exp ((φ : ℂ) * Complex.I) else 0

/-- `mulVec` against a two-point-supported vector collapses to the two columns. -/
theorem mulVec_two_support {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) {j₀ j₁ : I} (hne : j₀ ≠ j₁) (a b : ℂ) (i : I) :
    M.mulVec (fun j => if j = j₀ then a else if j = j₁ then b else 0) i
      = a * M i j₀ + b * M i j₁ := by
  rw [Matrix.mulVec, dotProduct]
  rw [show (∑ j, M i j * (if j = j₀ then a else if j = j₁ then b else 0))
      = ∑ j, ((if j = j₀ then M i j₀ * a else 0) + (if j = j₁ then M i j₁ * b else 0)) from
    Finset.sum_congr rfl fun j _ => by
      by_cases h0 : j = j₀
      · subst h0
        have h1 : ¬ j = j₁ := hne
        simp [h1]
      · by_cases h1 : j = j₁
        · subst h1
          simp [h0]
        · simp [h0, h1]]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j₀ (fun _ => M i j₀ * a),
    Finset.sum_ite_eq' Finset.univ j₁ (fun _ => M i j₁ * b),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  ring

/-- **The operational KMM z-rotation bound.** For every `φ` and `k` there is a three-qubit
Clifford+T word `W` of length `≤ 16800·k + 270` such that for **all** system amplitudes `α, β`,
the embedded word maps the initialized state within squared ℓ²-distance
`|β|²·(2/4ᵏ + 2·√2/2ᵏ)` of the ideal `α|000⟩ + β·e^{iφ}|100⟩` — the KMM amplitude + leakage
error, `O(2^{-k})` in squared distance. -/
theorem kmm_z_rotation_operational (φ : ℝ) (k : ℕ) :
    ∃ W : List Gate3, W.length ≤ 16800 * k + 270 ∧
      ∀ α β : ℂ,
        sumNormSq (fun i =>
            (toComplexMat8 (interp3 W)).mulVec (initState α β) i - targetState φ α β i)
          ≤ Complex.normSq β * (2 / 4 ^ k + 2 * (Real.sqrt 2 / 2 ^ k)) := by
  obtain ⟨W, v, hlen, hinit, hsys0, hsys1, hvunit, hv01, hamp, hleak⟩ := kmm_z_rotation_word φ k
  refine ⟨W, hlen, fun α β => ?_⟩
  -- the embedded columns
  have hcol0 : ∀ i, toComplexMat8 (interp3 W) i (0, 0, 0)
      = if i = (0, 0, 0) then 1 else 0 := fun i => by
    show ZOmegaSqrt2.toComplex (interp3 W i (0, 0, 0)) = _
    rw [hinit i, apply_ite ZOmegaSqrt2.toComplex, map_one, map_zero]
  have hcol1_0 : ∀ j, toComplexMat8 (interp3 W) (0, j) (1, 0, 0) = 0 := fun j => by
    show ZOmegaSqrt2.toComplex (interp3 W (0, j) (1, 0, 0)) = 0
    rw [hsys0 j, map_zero]
  have hcol1_1 : ∀ j, toComplexMat8 (interp3 W) (1, j) (1, 0, 0)
      = ZOmegaSqrt2.toComplex (v j) := fun j => by
    show ZOmegaSqrt2.toComplex (interp3 W (1, j) (1, 0, 0)) = _
    rw [hsys1 j]
  -- the action on the initialized state
  have hact : ∀ i, (toComplexMat8 (interp3 W)).mulVec (initState α β) i
      = α * toComplexMat8 (interp3 W) i (0, 0, 0)
        + β * toComplexMat8 (interp3 W) i (1, 0, 0) :=
    mulVec_two_support _ (by decide) α β
  -- the six vanishing difference entries and the three live ones
  have hcases : ∀ i : Fin 2 × Fin 2 × Fin 2, i = (0, 0, 0) ∨ i = (0, 0, 1) ∨ i = (0, 1, 0) ∨
      i = (0, 1, 1) ∨ i = (1, 0, 0) ∨ i = (1, 0, 1) ∨ i = (1, 1, 0) ∨ i = (1, 1, 1) := by decide
  have hd : ∀ i, (toComplexMat8 (interp3 W)).mulVec (initState α β) i - targetState φ α β i
      = if i = ((1 : Fin 2), (0 : Fin 2), (0 : Fin 2)) then
          β * (ZOmegaSqrt2.toComplex (v (0, 0)) - Complex.exp ((φ : ℂ) * Complex.I))
        else if i = ((1 : Fin 2), (1 : Fin 2), (0 : Fin 2)) then
          β * ZOmegaSqrt2.toComplex (v (1, 0))
        else if i = ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) then
          β * ZOmegaSqrt2.toComplex (v (1, 1))
        else 0 := by
    intro i
    rw [hact i]
    rcases hcases i with h | h | h | h | h | h | h | h <;> subst h
    · rw [hcol0, show toComplexMat8 (interp3 W) (0, 0, 0) (1, 0, 0) = 0 from hcol1_0 (0, 0)]
      simp [targetState]
    · rw [hcol0, show toComplexMat8 (interp3 W) (0, 0, 1) (1, 0, 0) = 0 from hcol1_0 (0, 1)]
      simp [targetState]
    · rw [hcol0, show toComplexMat8 (interp3 W) (0, 1, 0) (1, 0, 0) = 0 from hcol1_0 (1, 0)]
      simp [targetState]
    · rw [hcol0, show toComplexMat8 (interp3 W) (0, 1, 1) (1, 0, 0) = 0 from hcol1_0 (1, 1)]
      simp [targetState]
    · rw [hcol0, show toComplexMat8 (interp3 W) (1, 0, 0) (1, 0, 0)
          = ZOmegaSqrt2.toComplex (v (0, 0)) from hcol1_1 (0, 0)]
      simp [targetState]
      ring
    · rw [hcol0, show toComplexMat8 (interp3 W) (1, 0, 1) (1, 0, 0)
          = ZOmegaSqrt2.toComplex (v (0, 1)) from hcol1_1 (0, 1), hv01, map_zero]
      simp [targetState]
    · rw [hcol0, show toComplexMat8 (interp3 W) (1, 1, 0) (1, 0, 0)
          = ZOmegaSqrt2.toComplex (v (1, 0)) from hcol1_1 (1, 0)]
      simp [targetState]
    · rw [hcol0, show toComplexMat8 (interp3 W) (1, 1, 1) (1, 0, 0)
          = ZOmegaSqrt2.toComplex (v (1, 1)) from hcol1_1 (1, 1)]
      simp [targetState]
  -- assemble the sum
  have hsum : sumNormSq (fun i =>
      (toComplexMat8 (interp3 W)).mulVec (initState α β) i - targetState φ α β i)
      = Complex.normSq (β * (ZOmegaSqrt2.toComplex (v (0, 0))
          - Complex.exp ((φ : ℂ) * Complex.I)))
        + Complex.normSq (β * ZOmegaSqrt2.toComplex (v (1, 0)))
        + Complex.normSq (β * ZOmegaSqrt2.toComplex (v (1, 1))) := by
    rw [sumNormSq,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => congrArg Complex.normSq (hd i)]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [Complex.normSq_zero]
    ring
  rw [hsum, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
  have hampSq : Complex.normSq (ZOmegaSqrt2.toComplex (v (0, 0))
      - Complex.exp ((φ : ℂ) * Complex.I)) ≤ 2 / 4 ^ k := by
    have h1 : Complex.normSq (ZOmegaSqrt2.toComplex (v (0, 0))
        - Complex.exp ((φ : ℂ) * Complex.I))
        = ‖ZOmegaSqrt2.toComplex (v (0, 0)) - Complex.exp ((φ : ℂ) * Complex.I)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
    have hnn : (0 : ℝ) ≤ ‖ZOmegaSqrt2.toComplex (v (0, 0))
        - Complex.exp ((φ : ℂ) * Complex.I)‖ := norm_nonneg _
    have h2 : ‖ZOmegaSqrt2.toComplex (v (0, 0)) - Complex.exp ((φ : ℂ) * Complex.I)‖ ^ 2
        ≤ (Real.sqrt 2 / 2 ^ k) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hnn hamp
    have h3 : (Real.sqrt 2 / (2 : ℝ) ^ k) ^ 2 = 2 / 4 ^ k := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        show ((2 : ℝ) ^ k) ^ 2 = 4 ^ k from by
          rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul, Nat.mul_comm]]
    rw [h1]
    exact h2.trans (le_of_eq h3)
  have hleakC : Complex.normSq (ZOmegaSqrt2.toComplex (v (1, 0)))
      + Complex.normSq (ZOmegaSqrt2.toComplex (v (1, 1)))
      ≤ 2 * (Real.sqrt 2 / 2 ^ k) := hleak
  nlinarith [Complex.normSq_nonneg β, Complex.normSq_nonneg (ZOmegaSqrt2.toComplex (v (1, 0))),
    Complex.normSq_nonneg (ZOmegaSqrt2.toComplex (v (1, 1)))]

end Gate3
end SKEFTHawking.RossSelinger
