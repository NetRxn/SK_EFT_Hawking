/-
# Phase 5q.H · E1 — singular ℤ cohomology (toward the integral intersection form on H²(M⁴;ℤ))

Substrate-G foundation brick. The (A) signature route to `Ω₄^{Spin}≅ℤ` / the `÷32` Pin⁺-bounding
criterion needs the manifold's **integral** intersection form `H²(M;ℤ) × H²(M;ℤ) → ℤ`,
`(a,b) ↦ ⟨a∪b, [M]⟩`, as an even-unimodular integer matrix — then `σ÷16` via the already-done lattice
leg (`AlgebraicRokhlin.IsEvenUnimodular` + `LatticeSignature.latticeSig` on `Matrix (Fin n) (Fin n) ℤ`).

The obstruction (verified 2026-07-04, both on-main and via Mathlib semantic search): the entire on-main
cohomology is **mod-2** (`SingularCohomologyMod2.Cohomology X n` over `ZMod 2`; `cupH`/`cupH24` are
`ZMod 2`-linear — built for the Wu/w₂/Brown side). Mathlib has:
  * singular **homology** only (`AlgebraicTopology.singularChainComplexFunctor` / `singularHomologyFunctor`,
    bare functor, essentially no API beyond totally-disconnected special cases),
  * **no** singular cohomology, **no** cup product, **no** fundamental class, **no** Poincaré duality
    (`grep`ped the whole library 2026-07-04: `cupProduct`/`fundamentalClass`/`PoincareDuality` all absent),
  * the abstract quadratic-form signature (`QuadraticForm/Signature.lean`, already reused in
    `LatticeSignature`).

So the integral cohomology H²(M;ℤ) + integral cup product must be built from scratch. This module is the
FIRST foundation brick: the singular **integral** cochain complex `Cⁿ(X;ℤ)`, the coboundary `δ` (now with
the genuine alternating sign `(-1)^i`, which the mod-2 file could drop), the cochain-complex law `δ²=0`,
and integral cohomology `Hⁿ(X;ℤ) = ker δⁿ / im δⁿ⁻¹` as a genuine ℤ-module. The cup product (Alexander–
Whitney), the `[M]`-cap pairing, and Poincaré duality follow in later bricks (NOT this dispatch).

Mirrors `SingularCohomologyMod2` structurally, over the base ring ℤ. All proofs kernel-pure
(`propext`/`Classical.choice`/`Quot.sound` only); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib

namespace SKEFTHawking.SingularCohomologyInt

open CategoryTheory Opposite

/-- **Singular `n`-cochains** of a space `X` with **ℤ** coefficients: `ℤ`-valued functions on the
singular `n`-simplices `(TopCat.toSSet.obj X).obj (op [n])` (continuous maps `Δⁿ → X`). A genuine
`ℤ`-module (a Pi type over the commutative ring `ℤ`). -/
abbrev SingularCochainInt (X : TopCat) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) → ℤ

/-- The `i`-th face of a singular `(n+1)`-simplex `σ`: precompose with the `i`-th coface `δ i`. -/
noncomputable def face {X : TopCat} {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ

/-- **Faces compose to a composite coface.** `∂ⱼ(∂ᵢ σ)` is the face of `σ` along the composite
`δ j ≫ δ i : [n] ⟶ [n+2]` (functoriality of the singular simplicial set + the op-reversal of
composition). The key step for `δ² = 0`. -/
theorem face_face {X : TopCat} {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 2)))) :
    face j (face i σ)
      = (TopCat.toSSet.obj X).map (SimplexCategory.δ j ≫ SimplexCategory.δ i).op σ := by
  unfold face
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]

/-- The **signed singular coboundary** `δ : Cⁿ → Cⁿ⁺¹`, `(δ f)(σ) = ∑ᵢ (-1)^i · f(∂ᵢ σ)` over `ℤ`.
The alternating sign `(-1)^i` (which the mod-2 file dropped, `+1 = -1` in char 2) is genuine here. -/
noncomputable def coboundary (X : TopCat) (n : ℕ) (f : SingularCochainInt X n) :
    SingularCochainInt X (n + 1) :=
  fun σ => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * f (face i σ)

@[simp] theorem coboundary_apply (X : TopCat) (n : ℕ) (f : SingularCochainInt X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    coboundary X n f σ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * f (face i σ) := rfl

/-- The singular coboundary is **ℤ-linear**, packaged as `δⁿ : Cⁿ →ₗ[ℤ] Cⁿ⁺¹`. -/
noncomputable def coboundaryₗ (X : TopCat) (n : ℕ) :
    SingularCochainInt X n →ₗ[ℤ] SingularCochainInt X (n + 1) where
  toFun := coboundary X n
  map_add' f g := by
    funext σ
    simp only [coboundary_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' c f := by
    funext σ
    simp only [coboundary_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- **`δ² = 0`** — the singular cochain-complex condition. `(δ²f)(σ) = ∑ᵢ∑ⱼ (-1)^i (-1)^j f(∂ⱼ∂ᵢσ)`;
by `face_face` each summand is `f` of the composite coface `δ j ≫ δ i`, and the cosimplicial identity
`δ_comp_δ` pairs the index set into a fixed-point-free involution whose two members carry OPPOSITE signs
and equal `f`-values, so the sum vanishes over `ℤ`. -/
theorem coboundary_comp_coboundary (X : TopCat) (n : ℕ) (f : SingularCochainInt X n) :
    coboundary X (n + 1) (coboundary X n f) = 0 := by
  funext σ
  show (∑ i : Fin (n + 1 + 2), (-1 : ℤ) ^ (i : ℕ) *
      (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) * f (face j (face i σ)))) = 0
  simp only [face_face, Finset.mul_sum]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    (-1 : ℤ) ^ (p.1 : ℕ) * ((-1 : ℤ) ^ (p.2 : ℕ) *
      f ((TopCat.toSSet.obj X).map (SimplexCategory.δ p.2 ≫ SimplexCategory.δ p.1).op σ)))]
  refine Finset.sum_involution
    (fun p _ => if h : p.2.castSucc < p.1
      then (p.2.castSucc, p.1.pred ((Fin.zero_le _).trans_lt h).ne')
      else (p.2.succ, p.1.castPred (by
        simp only [not_lt] at h
        rw [Fin.ne_iff_vne, Fin.val_last]; have := p.2.isLt
        rw [Fin.le_def, Fin.val_castSucc] at h; omega))) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ -
    simp only
    by_cases h : j.castSucc < i
    · rw [dif_pos h]
      have hne : i ≠ 0 := ((Fin.zero_le _).trans_lt h).ne'
      have hle : j ≤ i.pred hne := by
        rw [Fin.le_def, Fin.val_pred]; rw [Fin.lt_def, Fin.val_castSucc] at h; omega
      have heq : SimplexCategory.δ j ≫ SimplexCategory.δ i
          = SimplexCategory.δ (i.pred hne) ≫ SimplexCategory.δ j.castSucc := by
        rw [← SimplexCategory.δ_comp_δ hle, Fin.succ_pred]
      rw [heq]
      -- sign cancellation: the two paired terms share the common face-value and carry opposite signs.
      simp only [Fin.val_castSucc, Fin.val_pred]
      have hi : (i : ℕ) = (i : ℕ) - 1 + 1 := by
        rw [Fin.lt_def, Fin.val_castSucc] at h; omega
      rw [show ((-1 : ℤ) ^ (i : ℕ)) = -(-1) ^ ((i : ℕ) - 1) by
        conv_lhs => rw [hi]
        rw [pow_succ]; ring]
      ring
    · rw [dif_neg h]
      simp only [not_lt] at h
      have hne : i ≠ Fin.last (n + 1 + 1) := by
        rw [Fin.ne_iff_vne, Fin.val_last]; have := j.isLt
        rw [Fin.le_def, Fin.val_castSucc] at h; omega
      have hle : i.castPred hne ≤ j := by
        rw [Fin.le_def, Fin.coe_castPred]; rw [Fin.le_def, Fin.val_castSucc] at h; omega
      have heq : SimplexCategory.δ j ≫ SimplexCategory.δ i
          = SimplexCategory.δ (i.castPred hne) ≫ SimplexCategory.δ j.succ := by
        rw [SimplexCategory.δ_comp_δ hle, Fin.castSucc_castPred]
      rw [heq]
      -- sign cancellation: the paired term carries an extra `δ j.succ` = one higher face index.
      simp only [Fin.val_succ, Fin.coe_castPred]
      rw [pow_succ]
      ring
  · rintro ⟨i, j⟩ - _
    by_cases h : j.castSucc < i
    · simp only [dif_pos h, ne_eq, Prod.mk.injEq]
      rintro ⟨hc, -⟩
      simp only [Fin.ext_iff, Fin.val_castSucc] at hc
      simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
    · simp only [dif_neg h, ne_eq, Prod.mk.injEq]
      rintro ⟨hc, -⟩
      simp only [Fin.ext_iff, Fin.val_succ] at hc
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at h; omega
  · intro a _; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ -
    by_cases h : j.castSucc < i
    · have hne : i ≠ 0 := ((Fin.zero_le _).trans_lt h).ne'
      have h2 : ¬ (i.pred hne).castSucc < j.castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_pred]
        simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
      simp only [dif_pos h, dif_neg h2, Fin.succ_pred, Fin.castPred_castSucc]
    · have hle : i ≤ j.castSucc := not_lt.mp h
      have hne : i ≠ Fin.last (n + 1 + 1) := by
        simp only [Fin.ne_iff_vne, Fin.val_last]; have := j.isLt
        simp only [Fin.le_def, Fin.val_castSucc] at hle; omega
      have h2 : i < j.succ := by
        simp only [Fin.lt_def, Fin.val_succ]
        simp only [Fin.le_def, Fin.val_castSucc] at hle; omega
      simp only [dif_neg h, Fin.castSucc_castPred, Fin.pred_succ, dif_pos h2]

/-- **Explicit degree-0 coboundary** `(δ⁰ f)(σ) = f(∂₀σ) − f(∂₁σ)`. The signed alternating sum over the
two faces of an edge — the concrete formula low-degree proofs (H⁰ = locally-constant, the pairing's
degree bookkeeping) pattern-match on. -/
theorem coboundary_zero_apply (X : TopCat) (f : SingularCochainInt X 0)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 1))) :
    coboundary X 0 f σ = f (face 0 σ) - f (face 1 σ) := by
  rw [coboundary_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul]
  ring

/-- **Explicit degree-1 coboundary** `(δ¹ f)(σ) = f(∂₀σ) − f(∂₁σ) + f(∂₂σ)`, the signed sum over the
three faces of a 2-simplex. Load-bearing for the cup-product Leibniz rule and the cocycle condition on
1-cochains (a 1-cochain `f` is a cocycle iff `f` is additive on the 2-simplices, i.e. `f∂₀ + f∂₂ = f∂₁`). -/
theorem coboundary_one_apply (X : TopCat) (f : SingularCochainInt X 1)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 2))) :
    coboundary X 1 f σ = f (face 0 σ) - f (face 1 σ) + f (face 2 σ) := by
  rw [coboundary_apply, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul, neg_one_mul]
  norm_num
  ring

/-! ## §2. Singular integral cohomology `Hⁿ(X; ℤ) = ker δⁿ / im δⁿ⁻¹` -/

/-- The submodule of `n`-coboundaries (image of the incoming `δⁿ⁻¹`), `⊥` in degree `0`. -/
noncomputable def coboundaryRange (X : TopCat) (n : ℕ) : Submodule ℤ (SingularCochainInt X n) :=
  match n with
  | 0 => ⊥
  | m + 1 => LinearMap.range (coboundaryₗ X m)

/-- Coboundaries are cocycles, `im δⁿ⁻¹ ≤ ker δⁿ` — the well-definedness of cohomology, from `δ² = 0`. -/
theorem coboundaryRange_le_ker (X : TopCat) (n : ℕ) :
    coboundaryRange X n ≤ LinearMap.ker (coboundaryₗ X n) := by
  cases n with
  | zero => exact bot_le
  | succ m =>
    show LinearMap.range (coboundaryₗ X m) ≤ LinearMap.ker (coboundaryₗ X (m + 1))
    rw [LinearMap.range_le_ker_iff]
    exact LinearMap.ext fun g => coboundary_comp_coboundary X m g

/-- **Singular integral cohomology** `Hⁿ(X; ℤ) = ker δⁿ / im δⁿ⁻¹` — a genuine quotient `ℤ`-module
(the integral cohomology of the topological space `X`, built from the singular cochain complex). -/
def Cohomology (X : TopCat) (n : ℕ) : Type :=
  (LinearMap.ker (coboundaryₗ X n)) ⧸
    (coboundaryRange X n).submoduleOf (LinearMap.ker (coboundaryₗ X n))

noncomputable instance (X : TopCat) (n : ℕ) : AddCommGroup (Cohomology X n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (X : TopCat) (n : ℕ) : Module ℤ (Cohomology X n) :=
  inferInstanceAs (Module ℤ (_ ⧸ _))

/-- The cohomology class of a cocycle. -/
noncomputable def Cohomology.mk (X : TopCat) (n : ℕ) (z : LinearMap.ker (coboundaryₗ X n)) :
    Cohomology X n :=
  Submodule.Quotient.mk z

end SKEFTHawking.SingularCohomologyInt
