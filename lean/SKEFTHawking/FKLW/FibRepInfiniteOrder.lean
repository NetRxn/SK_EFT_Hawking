/-
SK_EFT_Hawking Phase 6p Wave 2c.4a-R4 (sub-wave 1): Infinite-order witness
infrastructure for `(Set.range ρ_hom).Infinite` discharge.

This module ships the **structural infrastructure** needed to instantiate
the `h_inf : (Set.range ρ_hom).Infinite` hypothesis of the amended
`aa_residual_interior_at_one_for_hom` axiom (Wave 2c.4a-iteration,
2026-05-12). Given an eigenvalue analysis on some braid element, the
lemmas in this module discharge the infinite-order condition cleanly.

The structural lemmas are deliberately abstract: they do **not** depend
on the Fibonacci structure of `ρ`. Any concrete representation
`ρ : BraidGroup n → SU(d)` whose generators have an explicit irrational-
phase eigenvalue gets the `h_inf` hypothesis for free via these lemmas
+ `image_infinite_of_exists_not_finOrder` (already shipped in
`AharonovAradBridgeIteration.lean §3.5`).

## R4 program status (2026-05-13)

The full R4 deliverable — a concrete `ρ_Fib3 : BraidGroup 3 →* SU(d)`
MonoidHom built from the existing `Mat3K` data in `FibonacciQutrit.lean`
plus the eigenvalue witness — is multi-session work, primarily blocked
by:
  - Conversion `Mat3K → Matrix (Fin 3) (Fin 3) ℂ` (embedding Q(ζ₅, √φ) ↪ ℂ);
  - Det-normalization (the Fibonacci R-matrices are U(3), not SU(3));
  - PresentedGroup MonoidHom construction (verifying braid relations in ℂ).

**This module is sub-wave R4.1**: the structural lemmas + a concrete
synthetic demonstration. The structural lemmas slot into ANY future
concrete construction; the demonstration confirms the proof technique
works end-to-end against the existing axiom + iteration substrate by
shipping a *real* `BraidGroup 3 →* SU(2)` MonoidHom whose image is
provably infinite (cyclic on an irrational-phase diagonal generator).

The demonstration does NOT satisfy `LieSpanProp` (diagonal generators
commute, so the image is abelian and ℂ-spans only the diagonal 2D
subspace). The combined-with-LieSpan discharge for the full Fibonacci
case is a separate concrete task (R4.2+); this module establishes that
the `h_inf`-only direction of the AA hypothesis chain is *constructively
discharge-able* given any irrational-phase generator.

## Module content

  - `matrix_no_pow_eq_one_of_eigenvalue_not_rootOfUnity` — generic
    matrix-ring form: matrix with eigenvalue `z` and `z^n ≠ 1 ∀ n ≥ 1`
    has no positive power equal to identity.
  - `not_finOrder_of_eigenvalue_not_rootOfUnity` — SU(d)-subtype form:
    same conclusion lifted to `IsOfFinOrder` negation.
  - `complex_exp_not_root_of_unity` — for `θ ∈ ℝ` with `θ/(2π)`
    irrational, `exp(iθ)^n ≠ 1` for all `n ≥ 1`.
  - `irrational_pi_sqrt2_div_2pi` — the concrete irrationality witness
    `(π·√2)/(2π) = √2/2 ∈ Irrational`.

  - `infiniteOrderGen2` — a concrete 2×2 SU(2) matrix with infinite
    order in SU(2), via the eigenvalue + irrationality apparatus above.
  - `demo3StrandRep` — a concrete `BraidGroup 3 →* SU(2)` MonoidHom
    mapping both standard generators to `infiniteOrderGen2`.
  - `demo3StrandRep_image_infinite` — `(Set.range demo3StrandRep).Infinite`,
    discharging the `h_inf` hypothesis of `aa_residual_interior_at_one_for_hom`
    for this concrete MonoidHom.

## Pipeline Invariant compliance

  - Invariant #10 (no `set_option maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new project-local axioms): RESPECTED.
  - Preemptive-strengthening:
    * P2 (bundle redundancy): each lemma captures one mathematical content
      unit; no theorem statement is decomposable into independent conjuncts.
    * P3 (trivial discharge): every theorem requires the eigenvalue
      iteration / mulVec action / irrationality witness chain. None
      reduces to `rfl` or `decide`.
    * P5 (existential unfolding): `demo3StrandRep_image_infinite` is
      genuinely substantive — it composes the eigenvalue → matrix
      non-finite-order → SU(d) non-finite-order → image-infinite chain
      against a *concretely* constructed MonoidHom, not a structural
      tautology of the existing predicates.

Zero sorry. Zero new project-local axioms in this module.
-/

import Mathlib
import SKEFTHawking.BraidGroup
import SKEFTHawking.FKLW.AharonovAradBridgeIteration

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open scoped Matrix

/-! ## 1. Eigenvalue ⇒ infinite order (generic structural lemma)

If `A` is a square matrix and `v` is a nonzero eigenvector with eigenvalue
`z`, then `A^n` acts on `v` by `z^n`. Hence if `z` is not a root of unity
(`z^n ≠ 1` for all `n ≥ 1`), the matrix `A` cannot have finite order in
the matrix ring (no `n ≥ 1` satisfies `A^n = 1`).

This lemma is the workhorse: it factors the eigenvalue analysis (a
computation on a single complex number) from the matrix-level
infinite-order witness needed by the AA bridge.
-/

/-- **Generic eigenvector-based no-finite-power witness for matrices.**

If `A : Matrix (Fin d) (Fin d) ℂ` has a nonzero eigenvector `v` with
eigenvalue `z`, and `z` is not a root of unity, then no positive power
of `A` equals the identity. -/
theorem matrix_no_pow_eq_one_of_eigenvalue_not_rootOfUnity
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) (hv : v ≠ 0) (z : ℂ)
    (h_eig : A.mulVec v = z • v)
    (h_not_root : ∀ n : ℕ, 0 < n → z ^ n ≠ 1) :
    ∀ n : ℕ, 0 < n → A ^ n ≠ 1 := by
  intro n hn h_pow
  -- A^n acts on v by z^n.
  have h_pow_eig : (A ^ n).mulVec v = z ^ n • v := by
    clear hn h_pow h_not_root
    induction n with
    | zero => simp [Matrix.one_mulVec]
    | succ k ih =>
      rw [pow_succ,
          show ((A ^ k) * A).mulVec v = (A^k).mulVec (A.mulVec v) from
            (Matrix.mulVec_mulVec v (A^k) A).symm,
          h_eig, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  -- But A^n = 1, so A^n acts as identity on v.
  have h_one : (A ^ n).mulVec v = v := by
    rw [h_pow]; exact Matrix.one_mulVec v
  have h_eq : z ^ n • v = v := h_pow_eig ▸ h_one
  -- v ≠ 0 ⇒ some entry v i ≠ 0.
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    exact hv (funext h_all)
  -- (z^n) · v i = v i ⇒ z^n = 1.
  have h_entry : z ^ n * v i = v i := by
    have := congr_fun h_eq i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have h_zn : z ^ n = 1 := by
    have h_sub : (z ^ n - 1) * v i = 0 := by linear_combination h_entry
    rcases mul_eq_zero.mp h_sub with hzn | hvi
    · exact sub_eq_zero.mp hzn
    · exact absurd hvi hi
  exact h_not_root n hn h_zn

/-- **Eigenvalue-based infinite-order witness for SU(d) matrices.**

If `A : Matrix.specialUnitaryGroup (Fin d) ℂ` has (as a matrix) a
nonzero eigenvector `v` with eigenvalue `z` not a root of unity, then
`A` is not of finite order in the group `SU(d)`. -/
theorem not_finOrder_of_eigenvalue_not_rootOfUnity
    {d : ℕ} (A : Matrix.specialUnitaryGroup (Fin d) ℂ)
    (v : Fin d → ℂ) (hv : v ≠ 0) (z : ℂ)
    (h_eig : (A : Matrix (Fin d) (Fin d) ℂ).mulVec v = z • v)
    (h_not_root : ∀ n : ℕ, 0 < n → z ^ n ≠ 1) :
    ¬ IsOfFinOrder A := by
  set M : Matrix (Fin d) (Fin d) ℂ := (A : Matrix (Fin d) (Fin d) ℂ) with hM
  rw [isOfFinOrder_iff_pow_eq_one]
  push_neg
  intro n hn h_pow
  -- Lift A^n = 1 (in SU(d)) to M^n = 1 (in Matrix), via SubmonoidClass.coe_pow.
  have h_matrix_pow : M ^ n = (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [hM, ← SubmonoidClass.coe_pow A n, h_pow]
    rfl
  exact matrix_no_pow_eq_one_of_eigenvalue_not_rootOfUnity
    M v hv z h_eig h_not_root n hn h_matrix_pow

/-! ## 2. Irrational-phase non-root-of-unity witness

The most common eigenvalue source is `z = exp(i·θ)` for some explicit
`θ`. The lemma here reduces "`z` is not a root of unity" to
"`θ/(2π)` is irrational".
-/

/-- **Complex-exponential non-root-of-unity witness.**

If `θ : ℝ` and `θ/(2π)` is irrational, then `exp(i·θ)^n ≠ 1` for all
`n ≥ 1`. Useful eigenvalue source: `z = Complex.exp (θ · Complex.I)`
for irrational `θ/(2π)`. -/
theorem complex_exp_not_root_of_unity
    (θ : ℝ) (h_irr : Irrational (θ / (2 * Real.pi))) :
    ∀ n : ℕ, 0 < n → (Complex.exp ((θ : ℂ) * Complex.I)) ^ n ≠ 1 := by
  intro n hn h_eq
  rw [← Complex.exp_nat_mul] at h_eq
  rw [Complex.exp_eq_one_iff] at h_eq
  obtain ⟨k, hk⟩ := h_eq
  have h_I_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_real_C : (n : ℂ) * (θ : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    have hl : (n : ℂ) * ((θ : ℂ) * Complex.I) = ((n : ℂ) * (θ : ℂ)) * Complex.I := by
      ring
    have hr : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
              ((k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by ring
    rw [hl, hr] at hk
    exact mul_right_cancel₀ h_I_ne hk
  have h_real_R : (n : ℝ) * θ = (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re h_real_C
    simp at this
    exact this
  have hn_R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_R
  have h_2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  have h_div : θ / (2 * Real.pi) = (k : ℝ) / (n : ℝ) := by
    field_simp
    linarith
  apply h_irr
  rw [h_div]
  refine ⟨(k : ℚ) / (n : ℚ), ?_⟩
  push_cast
  rfl

/-- **Concrete irrationality witness: `(π·√2)/(2π) = √2/2 ∈ Irrational`.**

The simplest irrationality witness for use in the eigenvalue lemma:
take `θ = π·√2`, then `θ/(2π) = √2/2`, irrational since √2 is. -/
theorem irrational_pi_sqrt2_div_2pi :
    Irrational ((Real.pi * Real.sqrt 2) / (2 * Real.pi)) := by
  have h_pi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have heq : (Real.pi * Real.sqrt 2) / (2 * Real.pi) = Real.sqrt 2 / 2 := by
    field_simp
  rw [heq]
  exact_mod_cast irrational_sqrt_two.div_natCast (by norm_num : (2 : ℕ) ≠ 0)

/-! ## 3. Concrete demonstration: `BraidGroup 3 →* SU(2)` with infinite image

We construct an explicit MonoidHom witnessing `h_inf` for the
`aa_residual_interior_at_one_for_hom` axiom.

The construction:
  - `infiniteOrderGen2 := diag(exp(iπ√2), exp(-iπ√2))`
  - det = exp(iπ√2 - iπ√2) = 1 (so ∈ SU(2))
  - unitary (diagonal unit-modulus entries) → A · A⋆ = 1
  - eigenvalue exp(iπ√2) with eigenvector (1, 0)
  - exp(iπ√2)^n ≠ 1 for n ≥ 1 (irrational-phase witness)
  - so `infiniteOrderGen2` has infinite order in SU(2)

  - Map both BraidGroup 3 generators (σ₀, σ₁) to `infiniteOrderGen2`.
  - Braid relation σ₀σ₁σ₀ = σ₁σ₀σ₁ becomes A³ = A³ ✓.
  - No commutation relations apply (|0-1|=1 < 2).
  - So the MonoidHom factors through `PresentedGroup.toGroup`.

The image is `⟨infiniteOrderGen2⟩` (cyclic subgroup), countably infinite.
-/

/-- The concrete diagonal 2×2 matrix with eigenvalue `exp(iπ√2)` of
infinite order in SU(2). -/
noncomputable def infiniteOrderGen2Mat : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => match i with
    | ⟨0, _⟩ => Complex.exp ((Real.pi * Real.sqrt 2 : ℝ) * Complex.I)
    | ⟨1, _⟩ => Complex.exp (-(Real.pi * Real.sqrt 2 : ℝ) * Complex.I))

/-- `infiniteOrderGen2Mat` is unitary: `A · star A = 1`. -/
lemma infiniteOrderGen2Mat_unitary :
    infiniteOrderGen2Mat * star infiniteOrderGen2Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [infiniteOrderGen2Mat, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_apply]
  all_goals
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_I, Complex.conj_ofReal]

/-- `infiniteOrderGen2Mat` has determinant 1 (so ∈ SU(2)). -/
lemma infiniteOrderGen2Mat_det :
    infiniteOrderGen2Mat.det = 1 := by
  simp [infiniteOrderGen2Mat, Matrix.det_diagonal, Fin.prod_univ_succ]
  rw [← Complex.exp_add]
  ring_nf
  exact Complex.exp_zero

/-- `infiniteOrderGen2Mat` as an element of `Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
noncomputable def infiniteOrderGen2 :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨infiniteOrderGen2Mat,
    Matrix.mem_specialUnitaryGroup_iff.mpr
      ⟨Matrix.mem_unitaryGroup_iff.mpr infiniteOrderGen2Mat_unitary,
       infiniteOrderGen2Mat_det⟩⟩

/-- The standard basis vector `e₀ : Fin 2 → ℂ`. -/
noncomputable def e0 : Fin 2 → ℂ := fun j => if j = (0 : Fin 2) then 1 else 0

lemma e0_ne_zero : e0 ≠ 0 := by
  intro h
  have := congr_fun h (0 : Fin 2)
  simp [e0] at this

/-- The eigenvalue equation: `infiniteOrderGen2Mat · e₀ = exp(iπ√2) · e₀`. -/
lemma infiniteOrderGen2Mat_eig :
    infiniteOrderGen2Mat.mulVec e0 =
      Complex.exp ((Real.pi * Real.sqrt 2 : ℝ) * Complex.I) • e0 := by
  ext j
  fin_cases j
  · simp [infiniteOrderGen2Mat, e0, Matrix.mulVec_diagonal]
  · simp [infiniteOrderGen2Mat, e0, Matrix.mulVec_diagonal]

/-- `infiniteOrderGen2` has infinite order in SU(2). -/
theorem infiniteOrderGen2_not_finOrder :
    ¬ IsOfFinOrder infiniteOrderGen2 := by
  apply not_finOrder_of_eigenvalue_not_rootOfUnity
    infiniteOrderGen2 e0 e0_ne_zero
    (Complex.exp ((Real.pi * Real.sqrt 2 : ℝ) * Complex.I))
  · -- eigenvalue equation: (infiniteOrderGen2 : Matrix _).mulVec e0 = exp(...) • e0
    exact infiniteOrderGen2Mat_eig
  · -- exp(iπ√2)^n ≠ 1 for n ≥ 1
    have h_theta : (((Real.pi * Real.sqrt 2 : ℝ) : ℂ)) = (Real.pi * Real.sqrt 2 : ℝ) := rfl
    rw [h_theta]
    exact complex_exp_not_root_of_unity (Real.pi * Real.sqrt 2) irrational_pi_sqrt2_div_2pi

/-! ### 3.1. The MonoidHom `BraidGroup 3 →* SU(2)` -/

/-- The "constant" assignment of `infiniteOrderGen2` to every generator of
`BraidGroup 3`. -/
noncomputable def demo3StrandGen :
    Fin (3 - 1) → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun _ => infiniteOrderGen2

/-- All Artin relations of `BraidGroup 3` evaluate to 1 under the constant
assignment (trivial — same element on both sides of any relator). -/
lemma demo3StrandGen_rels_trivial (r : FreeGroup (Fin (3 - 1)))
    (hr : r ∈ SKEFTHawking.artinRelations 3) :
    (FreeGroup.lift demo3StrandGen) r = 1 := by
  rcases hr with hbraid | hcomm
  · -- Braid relation: σᵢσⱼσᵢ · (σⱼσᵢσⱼ)⁻¹ ↦ A³ · A⁻³ = 1
    obtain ⟨i, j, _hadj, h_eq⟩ := hbraid
    rw [h_eq, SKEFTHawking.braidRelation]
    simp [demo3StrandGen]
  · -- Commutation relation: vacuous at n = 3 (Fin (3-1) = Fin 2; max diff = 1 < 2).
    obtain ⟨i, j, h_far, _h_eq⟩ := hcomm
    exfalso
    have hi : i.val < 2 := i.isLt
    have hj : j.val < 2 := j.isLt
    -- (3 - 1) = 2, so i.val, j.val ∈ {0, 1}; |i.val - j.val| ≤ 1.
    omega

/-- The concrete `BraidGroup 3 →* SU(2)` MonoidHom (constant on
generators; image = ⟨infiniteOrderGen2⟩). -/
noncomputable def demo3StrandRep :
    SKEFTHawking.BraidGroup 3 →* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  PresentedGroup.toGroup demo3StrandGen_rels_trivial

/-! ### 3.2. The infinite-image conclusion -/

/-- The image of the generator under the demo MonoidHom is
`infiniteOrderGen2` (which has infinite order). -/
lemma demo3StrandRep_apply_gen (i : Fin (3 - 1)) :
    demo3StrandRep (SKEFTHawking.BraidGroup.σ i) = infiniteOrderGen2 := by
  show PresentedGroup.toGroup demo3StrandGen_rels_trivial (PresentedGroup.of i)
       = infiniteOrderGen2
  rw [PresentedGroup.toGroup.of]
  rfl

/-- The demo MonoidHom has a generator mapping to an infinite-order
element — concrete witness of `∃ b, ¬IsOfFinOrder (demo3StrandRep b)`. -/
theorem demo3StrandRep_exists_not_finOrder :
    ∃ b : SKEFTHawking.BraidGroup 3, ¬ IsOfFinOrder (demo3StrandRep b) := by
  refine ⟨SKEFTHawking.BraidGroup.σ (⟨0, by omega⟩ : Fin (3 - 1)), ?_⟩
  rw [demo3StrandRep_apply_gen]
  exact infiniteOrderGen2_not_finOrder

/-- **The R4 deliverable for the demo MonoidHom: image is infinite.**

Discharges the `h_inf : (Set.range ρ_hom).Infinite` hypothesis of
`aa_residual_interior_at_one_for_hom` for the concrete demo MonoidHom.
The full Fibonacci version (R4.2+) will use the same chain — replacing
`demo3StrandRep` with the concrete Fibonacci MonoidHom and the
eigenvalue argument with the Fibonacci R-matrix eigenvalue analysis. -/
theorem demo3StrandRep_image_infinite :
    (Set.range demo3StrandRep).Infinite :=
  SKEFTHawking.FKLW.AharonovAradBridge.image_infinite_of_exists_not_finOrder
    demo3StrandRep demo3StrandRep_exists_not_finOrder

/-! ## 4. Module summary

FibRepInfiniteOrder.lean (Wave 2c.4a-R4.1 ship, 2026-05-13):

**Structural lemmas (reusable infrastructure)**:
  - `matrix_no_pow_eq_one_of_eigenvalue_not_rootOfUnity` — matrix-ring
    form of eigenvalue → no finite-power-equal-identity.
  - `not_finOrder_of_eigenvalue_not_rootOfUnity` — SU(d) form of
    eigenvalue → infinite order.
  - `complex_exp_not_root_of_unity` — irrational-phase complex
    exponential is not a root of unity.
  - `irrational_pi_sqrt2_div_2pi` — concrete witness `(π√2)/(2π) ∈ Irrational`.

**Concrete demonstration (validates the discharge path)**:
  - `infiniteOrderGen2Mat` — diagonal 2×2 matrix `diag(exp(iπ√2), exp(-iπ√2))`.
  - `infiniteOrderGen2` — that matrix lifted to SU(2) (det = 1, unitary).
  - `infiniteOrderGen2_not_finOrder` — concrete `¬IsOfFinOrder` witness.
  - `demo3StrandGen_rels_trivial` — verifies all `BraidGroup 3` Artin
    relations evaluate to 1 under the constant assignment.
  - `demo3StrandRep : BraidGroup 3 →* SU(2)` — concrete MonoidHom.
  - `demo3StrandRep_exists_not_finOrder` — `∃ b, ¬IsOfFinOrder (ρ b)`.
  - `demo3StrandRep_image_infinite` — `(Set.range demo3StrandRep).Infinite`
    discharges `h_inf` for this concrete MonoidHom.

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new axioms): RESPECTED.

**Honest scope**:
  - The demo MonoidHom does NOT satisfy `LieSpanProp` (image is cyclic
    abelian, ℂ-spans only the diagonal subspace).
  - The full `aa_residual_interior_at_one_for_hom` discharge requires
    BOTH `LieSpanProp` AND `h_inf`. The combined witness for the
    Fibonacci case is sub-wave R4.2+ (concrete `ρ_Fib3` via
    `Mat3K → ℂ` conversion + det-normalization + braid-relation
    transport from the existing `FibonacciQutrit.lean` proofs).
  - This module ships the universal `h_inf` infrastructure (the
    structural lemmas slot into ANY future eigenvalue-based witness)
    and concretely validates the discharge path against the existing
    AA-axiom + iteration substrate.

Zero sorry. One project-local axiom upstream
(`aa_residual_interior_at_one_for_hom`); none introduced here.
-/

end SKEFTHawking.FKLW
