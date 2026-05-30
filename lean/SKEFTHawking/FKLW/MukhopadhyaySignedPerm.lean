/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ — signed permutation matrices (the finite channel-rep image of the Clifford group)

Mukhopadhyay 2024 (arXiv:2401.08950) Fact 3.9: a unitary is an exactly-implementable Clifford iff its
channel representation is a **signed permutation matrix** — exactly one `±1` per row and column. This
file develops the abstract algebra of signed permutation matrices over a finite index type `L`,
independent of any physics:

  * `signedPermMatrix σ ε` — the matrix `(i,j) ↦ ε j` if `i = σ j` else `0`, for a permutation `σ` and
    a sign function `ε`.
  * `IsSignedPerm A` — `A = signedPermMatrix σ ε` for some `σ` and some `±1`-valued `ε`.
  * The signed permutations form a **submonoid closed under inverses** (`isSignedPerm_one`,
    `isSignedPerm_mul`, `isSignedPerm_of_mul_eq_one`) and are a **finite** set (`signedPermSet_finite`),
    because they are parametrized by the finite type `Equiv.Perm L × (L → Bool)`.

These two facts — finiteness + closure under the monoid operations — are the entire combinatorial input
to the Phase 6x′ capstone (the 6z CCZ-essentiality converse): the channel rep is a monoid homomorphism
carrying the Clifford-only group `⟨H,S,CNOT⟩` into this finite set, so `⟨H,S,CNOT⟩` cannot be dense in
the (infinite) SU(8).

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure.

-/

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- **A signed permutation matrix**: `(i, j) ↦ ε j` when `i = σ j`, else `0`. One nonzero entry per
column (at row `σ j`, value `ε j`) and, since `σ` is a bijection, per row. -/
def signedPermMatrix (σ : Equiv.Perm L) (ε : L → ℂ) : Matrix L L ℂ :=
  fun i j => if i = σ j then ε j else 0

/-- **A matrix is a signed permutation** if it is `signedPermMatrix σ ε` for some permutation `σ` and
some `±1`-valued sign function `ε`. -/
def IsSignedPerm (A : Matrix L L ℂ) : Prop :=
  ∃ (σ : Equiv.Perm L) (ε : L → ℂ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ A = signedPermMatrix σ ε

/-- The identity permutation with all-`+1` signs is the identity matrix. -/
theorem signedPermMatrix_one : signedPermMatrix (1 : Equiv.Perm L) (fun _ => 1) = 1 := by
  ext i j
  simp only [signedPermMatrix, Equiv.Perm.one_apply, Matrix.one_apply]

/-- The identity matrix is a signed permutation. -/
theorem isSignedPerm_one : IsSignedPerm (1 : Matrix L L ℂ) :=
  ⟨1, fun _ => 1, fun _ => Or.inl rfl, signedPermMatrix_one.symm⟩

/-- **Signed permutations compose**: `signedPermMatrix σ₁ ε₁ * signedPermMatrix σ₂ ε₂` is the signed
permutation with permutation `σ₁ * σ₂` and sign `k ↦ ε₁ (σ₂ k) * ε₂ k`. -/
theorem signedPermMatrix_mul (σ₁ σ₂ : Equiv.Perm L) (ε₁ ε₂ : L → ℂ) :
    signedPermMatrix σ₁ ε₁ * signedPermMatrix σ₂ ε₂
      = signedPermMatrix (σ₁ * σ₂) (fun k => ε₁ (σ₂ k) * ε₂ k) := by
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ₂ k)]
  · simp only [signedPermMatrix, Equiv.Perm.mul_apply]
    by_cases h : i = σ₁ (σ₂ k) <;> simp [h]
  · intro j _ hj
    simp only [signedPermMatrix]
    rw [if_neg hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (σ₂ k)) h

/-- Signed permutations are closed under multiplication. -/
theorem isSignedPerm_mul {A B : Matrix L L ℂ} (hA : IsSignedPerm A) (hB : IsSignedPerm B) :
    IsSignedPerm (A * B) := by
  obtain ⟨σ₁, ε₁, hε₁, rfl⟩ := hA
  obtain ⟨σ₂, ε₂, hε₂, rfl⟩ := hB
  refine ⟨σ₁ * σ₂, fun k => ε₁ (σ₂ k) * ε₂ k, fun k => ?_, signedPermMatrix_mul σ₁ σ₂ ε₁ ε₂⟩
  rcases hε₁ (σ₂ k) with h1 | h1 <;> rcases hε₂ k with h2 | h2 <;> simp [h1, h2]

/-- A signed-permutation product collapses to `1` whenever the permutations cancel and the per-column
signs multiply to `1`. -/
theorem signedPermMatrix_mul_eq_one (σ₁ σ₂ : Equiv.Perm L) (ε₁ ε₂ : L → ℂ)
    (hσ : σ₁ * σ₂ = 1) (hsign : ∀ k, ε₁ (σ₂ k) * ε₂ k = 1) :
    signedPermMatrix σ₁ ε₁ * signedPermMatrix σ₂ ε₂ = 1 := by
  rw [signedPermMatrix_mul, hσ]
  rw [show (fun k => ε₁ (σ₂ k) * ε₂ k) = (fun _ => (1 : ℂ)) from funext hsign]
  exact signedPermMatrix_one

/-- The signed permutation `signedPermMatrix σ⁻¹ (i ↦ ε (σ⁻¹ i))` is a left inverse of
`signedPermMatrix σ ε` (for `±1`-valued `ε`). -/
theorem signedPermMatrix_inv_mul (σ : Equiv.Perm L) (ε : L → ℂ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    signedPermMatrix σ⁻¹ (fun i => ε (σ⁻¹ i)) * signedPermMatrix σ ε = 1 :=
  signedPermMatrix_mul_eq_one σ⁻¹ σ (fun i => ε (σ⁻¹ i)) ε (inv_mul_cancel σ)
    (fun k => by
      show ε (σ⁻¹ (σ k)) * ε k = 1
      have hk : σ⁻¹ (σ k) = k := by simp
      rw [hk]
      rcases hε k with h | h <;> simp [h])

/-- If `A` is a signed permutation and `A * B = 1`, then `B` is a signed permutation (it must be `A`'s
unique signed-permutation inverse). -/
theorem isSignedPerm_of_mul_eq_one {A B : Matrix L L ℂ} (hA : IsSignedPerm A) (hAB : A * B = 1) :
    IsSignedPerm B := by
  obtain ⟨σ, ε, hε, rfl⟩ := hA
  -- `C` is the explicit signed-permutation inverse; `C * (signedPermMatrix σ ε) = 1`.
  have hCA : signedPermMatrix σ⁻¹ (fun i => ε (σ⁻¹ i)) * signedPermMatrix σ ε = 1 :=
    signedPermMatrix_inv_mul σ ε hε
  have hBC : B = signedPermMatrix σ⁻¹ (fun i => ε (σ⁻¹ i)) := by
    calc B = 1 * B := (one_mul B).symm
    _ = (signedPermMatrix σ⁻¹ (fun i => ε (σ⁻¹ i)) * signedPermMatrix σ ε) * B := by rw [hCA]
    _ = signedPermMatrix σ⁻¹ (fun i => ε (σ⁻¹ i)) * (signedPermMatrix σ ε * B) := by
        rw [Matrix.mul_assoc]
    _ = signedPermMatrix σ⁻¹ (fun i => ε (σ⁻¹ i)) * 1 := by rw [hAB]
    _ = signedPermMatrix σ⁻¹ (fun i => ε (σ⁻¹ i)) := mul_one _
  refine ⟨σ⁻¹, fun i => ε (σ⁻¹ i), fun i => hε (σ⁻¹ i), hBC⟩

/-- **The set of signed permutation matrices**. -/
def signedPermSet : Set (Matrix L L ℂ) := {A | IsSignedPerm A}

/-- **The set of signed permutations is finite** — they are parametrized by the finite type
`Equiv.Perm L × (L → Bool)` (a permutation plus a `±1` sign per column). -/
theorem signedPermSet_finite : (signedPermSet : Set (Matrix L L ℂ)).Finite := by
  classical
  apply Set.Finite.subset (Set.finite_range
    (fun p : Equiv.Perm L × (L → Bool) =>
      signedPermMatrix p.1 (fun i => if p.2 i then (1 : ℂ) else -1)))
  rintro A ⟨σ, ε, hε, rfl⟩
  refine ⟨⟨σ, fun i => if ε i = 1 then true else false⟩, ?_⟩
  show signedPermMatrix σ (fun i => if (if ε i = 1 then true else false) then (1 : ℂ) else -1)
      = signedPermMatrix σ ε
  congr 1
  funext i
  by_cases h : ε i = 1
  · simp [h]
  · have h2 : ε i = -1 := (hε i).resolve_left h
    rw [if_neg h]
    simp [h2]

end SKEFTHawking.FKLW.MukhopadhyayCCZ
