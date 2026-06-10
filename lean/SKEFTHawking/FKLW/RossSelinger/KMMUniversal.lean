/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 40) — the ∀U∈SU(2) KMM headline: composition machinery

The final assembly: three approximate z-rotation words (inc 38) interleaved with two exact system
Hadamards realize any `U ∈ SU(2)` up to global phase (inc 39), with the errors **adding** through
the composition — which requires unitarity (`sumNormSq_mulVec_interp3`, inc 37), since the
intermediate states leave the ancilla-initialized subspace only by the per-step error.

This file: the ℓ²-bridge to `EuclideanSpace` (Minkowski), the one-step composition triangle, the
**exact** system-Hadamard step on initialized states, and unit-pair preservation along the chain.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.KMMOperational
import SKEFTHawking.FKLW.RossSelinger.SU2Euler
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

set_option autoImplicit false

open scoped Matrix

namespace SKEFTHawking.RossSelinger
namespace Gate3

open ZOmegaSqrt2

/-! ### The ℓ²-bridge -/

/-- `sumNormSq` is the squared `EuclideanSpace` norm. -/
theorem sumNormSq_eq_norm_sq (x : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    sumNormSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_norm_sq _

theorem sumNormSq_nonneg (x : Fin 2 × Fin 2 × Fin 2 → ℂ) : 0 ≤ sumNormSq x :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- **One composition step**: if the unitary-word `P` is applied after an approximate step
(`u ≈ v`) and `P·v ≈ w`, the errors add in the ℓ²-distance (triangle + norm preservation). -/
theorem step_triangle (P : List Gate3) (u v w : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec u i - w i))
      ≤ Real.sqrt (sumNormSq (fun i => u i - v i))
        + Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)) := by
  have hsplit : (fun i => (toComplexMat8 (interp3 P)).mulVec u i - w i)
      = fun i => (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i
        + ((toComplexMat8 (interp3 P)).mulVec v i - w i) := by
    funext i
    rw [show (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i
        = (toComplexMat8 (interp3 P)).mulVec u i - (toComplexMat8 (interp3 P)).mulVec v i from by
      rw [show (fun j => u j - v j) = u - v from rfl, Matrix.mulVec_sub]
      rfl]
    ring
  rw [hsplit]
  have hpres := sumNormSq_mulVec_interp3 P (fun j => u j - v j)
  rw [show sumNormSq (fun j => u j - v j)
      = sumNormSq (fun i => u i - v i) from rfl] at hpres
  rw [show sumNormSq (fun i =>
        (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i
          + ((toComplexMat8 (interp3 P)).mulVec v i - w i))
      = ‖(WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i)
            : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))
          + (WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)
            : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ ^ 2 from by
    rw [← sumNormSq_eq_norm_sq]
    rfl]
  rw [Real.sqrt_sq (norm_nonneg _)]
  calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ = Real.sqrt (sumNormSq (fun i => u i - v i))
        + Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)) := by
      rw [show (‖(WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec
            (fun j => u j - v j) i) : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ : ℝ)
          = Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec
              (fun j => u j - v j) i)) from by
        rw [sumNormSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
        hpres,
        show (‖(WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)
            : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ : ℝ)
          = Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)) from by
        rw [sumNormSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]

/-! ### The exact system-Hadamard step and pair-norm preservation -/

/-- The system Hadamard acts **exactly** on initialized states:
`H_s · (ψ ⊗ |00⟩) = (Hψ) ⊗ |00⟩`. -/
theorem sysH_step (α' β' : ℂ) :
    (toComplexMat8 (gateMatrix3 (.onSys .H))).mulVec (initState α' β')
      = initState (((Real.sqrt 2)⁻¹ : ℂ) * (α' + β')) (((Real.sqrt 2)⁻¹ : ℂ) * (α' - β')) := by
  have hcases : ∀ i : Fin 2 × Fin 2 × Fin 2, i = (0, 0, 0) ∨ i = (0, 0, 1) ∨ i = (0, 1, 0) ∨
      i = (0, 1, 1) ∨ i = (1, 0, 0) ∨ i = (1, 0, 1) ∨ i = (1, 1, 0) ∨ i = (1, 1, 1) := by decide
  have hentry : ∀ (s p s' p'), toComplexMat8 (gateMatrix3 (.onSys .H)) (s, p) (s', p')
      = ZOmegaSqrt2.toComplex (CliffordTGate.gateMatrix .H s s' * (1 : Mat4) p p') := fun _ _ _ _ =>
    rfl
  have hone : ∀ p : Fin 2 × Fin 2, p ≠ ((0 : Fin 2), (0 : Fin 2)) →
      ∀ z : ZOmegaSqrt2, ZOmegaSqrt2.toComplex (z * (1 : Mat4) p ((0 : Fin 2), (0 : Fin 2))) = 0 :=
    fun p hp z => by rw [Matrix.one_apply_ne hp, mul_zero, map_zero]
  have hHcol : ∀ s : Fin 2, ∀ z : ZOmegaSqrt2,
      ZOmegaSqrt2.toComplex (z * (1 : Mat4) ((0 : Fin 2), (0 : Fin 2))
        ((0 : Fin 2), (0 : Fin 2))) = ZOmegaSqrt2.toComplex z := fun s z => by
    rw [Matrix.one_apply_eq, mul_one]
  funext i
  rw [show initState α' β' = (fun j => if j = ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) then α'
      else if j = ((1 : Fin 2), (0 : Fin 2), (0 : Fin 2)) then β' else 0) from rfl,
    mulVec_two_support _ (by decide)]
  have hinv := toComplex_invSqrt2
  rcases hcases i with h | h | h | h | h | h | h | h <;> subst h <;> rw [hentry, hentry]
  · rw [hHcol 0, hHcol 0,
      show CliffordTGate.gateMatrix .H 0 0 = ZOmegaSqrt2.invSqrt2 from rfl,
      show CliffordTGate.gateMatrix .H 0 1 = ZOmegaSqrt2.invSqrt2 from rfl, hinv,
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2))
        = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β') from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring
  · rw [hHcol 1, hHcol 1,
      show CliffordTGate.gateMatrix .H 1 0 = ZOmegaSqrt2.invSqrt2 from rfl,
      show CliffordTGate.gateMatrix .H 1 1 = -ZOmegaSqrt2.invSqrt2 from rfl, map_neg, hinv,
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 2))
        = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' - β') from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring

/-- `Λ`-steps preserve the system-pair norm. -/
theorem pair_norm_lam (φ : ℝ) (α' β' : ℂ) :
    Complex.normSq α' + Complex.normSq (β' * Complex.exp ((φ : ℂ) * Complex.I))
      = Complex.normSq α' + Complex.normSq β' := by
  rw [Complex.normSq_mul, show Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 from by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num]
  ring

/-- `H`-steps preserve the system-pair norm (the `ℂ`-parallelogram law). -/
theorem pair_norm_h (α' β' : ℂ) :
    Complex.normSq (((Real.sqrt 2)⁻¹ : ℂ) * (α' + β'))
      + Complex.normSq (((Real.sqrt 2)⁻¹ : ℂ) * (α' - β'))
      = Complex.normSq α' + Complex.normSq β' := by
  rw [Complex.normSq_mul, Complex.normSq_mul,
    show Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 1 / 2 from by
      rw [Complex.normSq_inv, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
  have hpar : Complex.normSq (α' + β') + Complex.normSq (α' - β')
      = 2 * (Complex.normSq α' + Complex.normSq β') := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im]
    ring
  linarith

/-! ### The ∀U headline -/

/-- Action of an appended word splits. -/
theorem mulVec_append (X Y : List Gate3) (z : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    (toComplexMat8 (interp3 (X ++ Y))).mulVec z
      = (toComplexMat8 (interp3 X)).mulVec ((toComplexMat8 (interp3 Y)).mulVec z) := by
  rw [interp3_append, toComplexMat8_mul, ← Matrix.mulVec_mulVec]

/-- Action of a cons word splits. -/
theorem mulVec_cons (g : Gate3) (Y : List Gate3) (z : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    (toComplexMat8 (interp3 (g :: Y))).mulVec z
      = (toComplexMat8 (gateMatrix3 g)).mulVec ((toComplexMat8 (interp3 Y)).mulVec z) := by
  rw [interp3_cons, toComplexMat8_mul, ← Matrix.mulVec_mulVec]

/-- **The three-step chain bound**: three approximate words interleaved with two exact
system-Hadamard steps compose with the errors **adding** — each step within `r` of its target
puts the full word within `3r` (triangle inequality through unitarity, `step_triangle`). -/
theorem chain_bound (Wa Wb Wc : List Gate3) (s₀ t₃ s₁ t₂ s₂ t₁ : Fin 2 × Fin 2 × Fin 2 → ℂ)
    (r : ℝ)
    (hc : Real.sqrt (sumNormSq (fun i =>
      (toComplexMat8 (interp3 Wc)).mulVec s₀ i - t₃ i)) ≤ r)
    (h₃ : (toComplexMat8 (gateMatrix3 (.onSys .H))).mulVec t₃ = s₁)
    (hb : Real.sqrt (sumNormSq (fun i =>
      (toComplexMat8 (interp3 Wb)).mulVec s₁ i - t₂ i)) ≤ r)
    (h₂ : (toComplexMat8 (gateMatrix3 (.onSys .H))).mulVec t₂ = s₂)
    (ha : Real.sqrt (sumNormSq (fun i =>
      (toComplexMat8 (interp3 Wa)).mulVec s₂ i - t₁ i)) ≤ r) :
    Real.sqrt (sumNormSq (fun i =>
      (toComplexMat8 (interp3 (Wa ++ .onSys .H :: (Wb ++ .onSys .H :: Wc)))).mulVec s₀ i - t₁ i))
      ≤ 3 * r := by
  have hsing : ∀ z : Fin 2 × Fin 2 × Fin 2 → ℂ,
      (toComplexMat8 (interp3 [(.onSys .H : Gate3)])).mulVec z
        = (toComplexMat8 (gateMatrix3 (.onSys .H))).mulVec z := fun z => by
    rw [mulVec_cons, interp3_nil, toComplexMat8_one, Matrix.one_mulVec]
  have hw : Wa ++ .onSys .H :: (Wb ++ .onSys .H :: Wc)
      = (Wa ++ .onSys .H :: (Wb ++ [.onSys .H])) ++ Wc := by simp
  have hp : Wa ++ .onSys .H :: (Wb ++ [.onSys .H])
      = (Wa ++ [.onSys .H]) ++ (Wb ++ [.onSys .H]) := by simp
  have eP : (toComplexMat8 (interp3 (Wa ++ .onSys .H :: (Wb ++ [.onSys .H])))).mulVec t₃
      = (toComplexMat8 (interp3 (Wa ++ [.onSys .H]))).mulVec
          ((toComplexMat8 (interp3 Wb)).mulVec s₁) := by
    rw [hp, mulVec_append, mulVec_append Wb [.onSys .H] t₃, hsing, h₃]
  have eA : (toComplexMat8 (interp3 (Wa ++ [.onSys .H]))).mulVec t₂
      = (toComplexMat8 (interp3 Wa)).mulVec s₂ := by
    rw [mulVec_append, hsing, h₂]
  have T1 := step_triangle (Wa ++ .onSys .H :: (Wb ++ [.onSys .H]))
    ((toComplexMat8 (interp3 Wc)).mulVec s₀) t₃ t₁
  have T2 := step_triangle (Wa ++ [.onSys .H])
    ((toComplexMat8 (interp3 Wb)).mulVec s₁) t₂ t₁
  rw [eP] at T1
  rw [eA] at T2
  rw [hw, mulVec_append]
  linarith

/-- Squaring a `√x ≤ 3·√b` bound: `x ≤ 9·b`. -/
theorem sq_le_of_sqrt_le_three_sqrt {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b)
    (h : Real.sqrt x ≤ 3 * Real.sqrt b) : x ≤ 9 * b := by
  rw [← Real.mul_self_sqrt hx]
  calc Real.sqrt x * Real.sqrt x ≤ (3 * Real.sqrt b) * (3 * Real.sqrt b) :=
        mul_self_le_mul_self (Real.sqrt_nonneg x) h
    _ = 9 * (Real.sqrt b * Real.sqrt b) := by ring
    _ = 9 * b := by rw [Real.mul_self_sqrt hb]

/-- **THE KMM ∀U HEADLINE (UNCONDITIONAL, O(log 1/ε) EXPONENT 1).** For every `U ∈ SU(2)` and
precision `k` there is an explicit three-qubit Clifford+T word `W` (system + 2 ancillas) of length
`≤ 50400·k + 812` — **linear in `k`**, i.e. `O(log 1/ε)` with exponent 1 for the squared error
`ε² = 9·(2/4ᵏ + 2√2/2ᵏ) = O(2^{-k})` — and a global phase `c` (`‖c‖ = 1`) such that for **every**
unit system state `α|0⟩+β|1⟩`, the embedded word maps the ancilla-initialized input within squared
ℓ²-distance `9·(2/4ᵏ + 2√2/2ᵏ)` of the ideal `(c⁻¹·U)`-rotated output. **No prime-density
hypothesis** — the inputs are Lagrange four-squares, the constructive column lemma, and the Euler
decomposition; this is the KMM arXiv:1212.0822 result, fully unconditional. -/
theorem kmm_universal_headline (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k : ℕ) :
    ∃ (W : List Gate3) (c : ℂ), ‖c‖ = 1 ∧ W.length ≤ 50400 * k + 812 ∧
      ∀ α β : ℂ, Complex.normSq α + Complex.normSq β = 1 →
        sumNormSq (fun i => (toComplexMat8 (interp3 W)).mulVec (initState α β) i
          - initState (c⁻¹ * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * α
              + (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * β))
            (c⁻¹ * ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * α
              + (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * β)) i)
          ≤ 9 * (2 / 4 ^ k + 2 * (Real.sqrt 2 / 2 ^ k)) := by
  obtain ⟨φ₁, φ₂, φ₃, c, hc, hU⟩ := su2_euler_decomposition U
  obtain ⟨W₁, hlen₁, herr₁⟩ := kmm_z_rotation_operational φ₁ k
  obtain ⟨W₂, hlen₂, herr₂⟩ := kmm_z_rotation_operational φ₂ k
  obtain ⟨W₃, hlen₃, herr₃⟩ := kmm_z_rotation_operational φ₃ k
  set B : ℝ := 2 / 4 ^ k + 2 * (Real.sqrt 2 / 2 ^ k) with hB
  have hBnn : 0 ≤ B := by positivity
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hc
    norm_num at hc
  refine ⟨W₁ ++ .onSys .H :: (W₂ ++ .onSys .H :: W₃), c, hc, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  intro α β hαβ
  -- the per-step error bounds (each ≤ B since the evolving pair stays unit)
  set invs : ℂ := (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ with hinvs
  set e₁ : ℂ := Complex.exp ((φ₁ : ℂ) * Complex.I) with he₁
  set e₂ : ℂ := Complex.exp ((φ₂ : ℂ) * Complex.I) with he₂
  set e₃ : ℂ := Complex.exp ((φ₃ : ℂ) * Complex.I) with he₃
  set a₁ : ℂ := invs * (α + β * e₃) with ha₁
  set b₁ : ℂ := invs * (α - β * e₃) with hb₁
  set a₂ : ℂ := invs * (a₁ + b₁ * e₂) with ha₂
  set b₂ : ℂ := invs * (a₁ - b₁ * e₂) with hb₂
  have hn₃ : Complex.normSq α + Complex.normSq (β * e₃) = 1 := by
    rw [he₃, pair_norm_lam]
    exact hαβ
  have hn₁ : Complex.normSq a₁ + Complex.normSq b₁ = 1 := by
    rw [ha₁, hb₁, hinvs, pair_norm_h]
    exact hn₃
  have hn₂' : Complex.normSq a₁ + Complex.normSq (b₁ * e₂) = 1 := by
    rw [he₂, pair_norm_lam]
    exact hn₁
  have hn₂ : Complex.normSq a₂ + Complex.normSq b₂ = 1 := by
    rw [ha₂, hb₂, hinvs, pair_norm_h]
    exact hn₂'
  have hβ1 : Complex.normSq β ≤ 1 := by nlinarith [Complex.normSq_nonneg α]
  have hb₁1 : Complex.normSq b₁ ≤ 1 := by nlinarith [Complex.normSq_nonneg a₁]
  have hb₂1 : Complex.normSq b₂ ≤ 1 := by nlinarith [Complex.normSq_nonneg a₂]
  -- the chain states (targetState φ x y = initState x (y·e^{iφ}) definitionally)
  have ht₃ : targetState φ₃ α β = initState α (β * e₃) := rfl
  have ht₂ : targetState φ₂ a₁ b₁ = initState a₁ (b₁ * e₂) := rfl
  have ht₁ : targetState φ₁ a₂ b₂ = initState a₂ (b₂ * e₁) := rfl
  -- the exact H-steps
  have hH₃ : (toComplexMat8 (gateMatrix3 (.onSys .H))).mulVec (initState α (β * e₃))
      = initState a₁ b₁ := by
    rw [sysH_step, ha₁, hb₁, hinvs]
  have hH₂ : (toComplexMat8 (gateMatrix3 (.onSys .H))).mulVec (initState a₁ (b₁ * e₂))
      = initState a₂ b₂ := by
    rw [sysH_step, ha₂, hb₂, hinvs]
  -- the final pair is the (c⁻¹·U)-action
  have hinv2 : invs * invs = 1 / 2 := by
    rw [hinvs, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hEab : ∀ i j, (U : Matrix (Fin 2) (Fin 2) ℂ) i j = c * eulerProd φ₁ φ₂ φ₃ i j := fun i j =>
    by rw [hU]; rfl
  have hfin₀ : c⁻¹ * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * α
      + (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * β) = a₂ := by
    rw [inv_mul_eq_iff_eq_mul₀ hcne, hEab, hEab, eulerProd_eq,
      show ((1 / 2 : ℂ) • !![1 + e₂, (1 - e₂) * e₃; e₁ * (1 - e₂), e₁ * e₃ * (1 + e₂)]) 0 0
        = (1 / 2 : ℂ) * (1 + e₂) from rfl,
      show ((1 / 2 : ℂ) • !![1 + e₂, (1 - e₂) * e₃; e₁ * (1 - e₂), e₁ * e₃ * (1 + e₂)]) 0 1
        = (1 / 2 : ℂ) * ((1 - e₂) * e₃) from rfl,
      ha₂, ha₁, hb₁]
    linear_combination (-(c * ((α + β * e₃) + (α - β * e₃) * e₂))) * hinv2
  have hfin₁ : c⁻¹ * ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * α
      + (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * β) = b₂ * e₁ := by
    rw [inv_mul_eq_iff_eq_mul₀ hcne, hEab, hEab, eulerProd_eq,
      show ((1 / 2 : ℂ) • !![1 + e₂, (1 - e₂) * e₃; e₁ * (1 - e₂), e₁ * e₃ * (1 + e₂)]) 1 0
        = (1 / 2 : ℂ) * (e₁ * (1 - e₂)) from rfl,
      show ((1 / 2 : ℂ) • !![1 + e₂, (1 - e₂) * e₃; e₁ * (1 - e₂), e₁ * e₃ * (1 + e₂)]) 1 1
        = (1 / 2 : ℂ) * (e₁ * e₃ * (1 + e₂)) from rfl,
      hb₂, ha₁, hb₁]
    linear_combination (-(c * e₁ * ((α + β * e₃) - (α - β * e₃) * e₂))) * hinv2
  rw [show initState (c⁻¹ * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * α
        + (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * β))
      (c⁻¹ * ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * α
        + (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * β)) = initState a₂ (b₂ * e₁) from by
    rw [hfin₀, hfin₁]]
  -- per-step error bounds
  have hd₃ : Real.sqrt (sumNormSq (fun i =>
      (toComplexMat8 (interp3 W₃)).mulVec (initState α β) i - initState α (β * e₃) i))
      ≤ Real.sqrt B := by
    refine Real.sqrt_le_sqrt ?_
    calc sumNormSq _ ≤ Complex.normSq β * B := by rw [← ht₃]; exact herr₃ α β
      _ ≤ 1 * B := by nlinarith
      _ = B := one_mul B
  have hd₂ : Real.sqrt (sumNormSq (fun i =>
      (toComplexMat8 (interp3 W₂)).mulVec (initState a₁ b₁) i - initState a₁ (b₁ * e₂) i))
      ≤ Real.sqrt B := by
    refine Real.sqrt_le_sqrt ?_
    calc sumNormSq _ ≤ Complex.normSq b₁ * B := by rw [← ht₂]; exact herr₂ a₁ b₁
      _ ≤ 1 * B := by nlinarith
      _ = B := one_mul B
  have hd₁ : Real.sqrt (sumNormSq (fun i =>
      (toComplexMat8 (interp3 W₁)).mulVec (initState a₂ b₂) i - initState a₂ (b₂ * e₁) i))
      ≤ Real.sqrt B := by
    refine Real.sqrt_le_sqrt ?_
    calc sumNormSq _ ≤ Complex.normSq b₂ * B := by rw [← ht₁]; exact herr₁ a₂ b₂
      _ ≤ 1 * B := by nlinarith
      _ = B := one_mul B
  -- the assembled distance bound (each step ≤ √B; the chain lemma adds them)
  have hD := chain_bound W₁ W₂ W₃ (initState α β) (initState α (β * e₃)) (initState a₁ b₁)
    (initState a₁ (b₁ * e₂)) (initState a₂ b₂) (initState a₂ (b₂ * e₁)) (Real.sqrt B)
    hd₃ hH₃ hd₂ hH₂ hd₁
  exact sq_le_of_sqrt_le_three_sqrt (sumNormSq_nonneg _) hBnn hD

end Gate3
end SKEFTHawking.RossSelinger