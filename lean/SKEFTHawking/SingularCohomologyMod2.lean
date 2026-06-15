/-
# Phase 5q.F — singular ℤ/2 cohomology (toward the ABK β built from the bordism group)

The β bottleneck of the genuine Smith-LES endpoint: a homomorphism `β : DataBordismGrp ξ_Pin⁺ →+ ℤ/16`
(the ABK invariant) **built from the bordism group**, not supplied as a hypothesis
(`PinPlusBordismGroupDerived.dataBordism_iso_zmod16` takes it as one). That needs the ℤ/2 cohomology of
the underlying `SingularManifold` spaces — which Mathlib lacks (it has the singular *chain* complex,
`AlgebraicTopology.singularChainComplexFunctor`, but no singular cohomology). This module builds it
elementarily on Mathlib's singular simplicial set `TopCat.toSSet`: singular `n`-cochains are `ℤ/2`-valued
functions on singular `n`-simplices, with the coboundary the alternating (mod 2: plain) sum over faces.

First brick: the singular cochain group and the coboundary `δ`. The `δ² = 0` identity (from the
cosimplicial relations `SimplexCategory.δ_comp_δ`), cohomology `Hⁿ`, the cup product (Alexander–Whitney),
and the cellular-comparison computations follow.
-/
import Mathlib

namespace SKEFTHawking.SingularCohomologyMod2

open CategoryTheory Opposite

/-- **Singular `n`-cochains** of a space `X` with `ℤ/2` coefficients: `ℤ/2`-valued functions on the
singular `n`-simplices `(TopCat.toSSet.obj X).obj (op [n])` (continuous maps `Δⁿ → X`). A genuine
`ℤ/2`-vector space (a Pi type over the field `ZMod 2`). -/
abbrev SingularCochain (X : TopCat) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) → ZMod 2

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

/-- The **singular coboundary** `δ : Cⁿ → Cⁿ⁺¹`, `(δ f)(σ) = ∑ᵢ f(∂ᵢ σ)` over `ℤ/2` (the alternating
sign is `+1` mod 2). Genuine `ℤ/2`-linear (a sum of precompositions). -/
noncomputable def coboundary (X : TopCat) (n : ℕ) (f : SingularCochain X n) : SingularCochain X (n + 1) :=
  fun σ => ∑ i : Fin (n + 2), f (face i σ)

@[simp] theorem coboundary_apply (X : TopCat) (n : ℕ) (f : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    coboundary X n f σ = ∑ i : Fin (n + 2), f (face i σ) := rfl

/-- The singular coboundary is **`ℤ/2`-linear**, packaged as `δⁿ : Cⁿ →ₗ[ZMod 2] Cⁿ⁺¹`. -/
noncomputable def coboundaryₗ (X : TopCat) (n : ℕ) :
    SingularCochain X n →ₗ[ZMod 2] SingularCochain X (n + 1) where
  toFun := coboundary X n
  map_add' f g := by
    funext σ
    simp only [coboundary_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' c f := by
    funext σ
    simp only [coboundary_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- **`δ² = 0`** — the singular cochain complex condition. `(δ²f)(σ) = ∑ᵢ∑ⱼ f(∂ⱼ∂ᵢσ)`; by `face_face`
each summand is `f` of the composite coface `δ j ≫ δ i`, and the cosimplicial identity `δ_comp_δ` pairs
the index set `Fin(n+3) × Fin(n+2)` into a fixed-point-free involution with equal `f`-values, so the sum
vanishes over `ℤ/2`. -/
theorem coboundary_comp_coboundary (X : TopCat) (n : ℕ) (f : SingularCochain X n) :
    coboundary X (n + 1) (coboundary X n f) = 0 := by
  funext σ
  simp only [coboundary_apply, face_face, Pi.zero_apply]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    f ((TopCat.toSSet.obj X).map (SimplexCategory.δ p.2 ≫ SimplexCategory.δ p.1).op σ))]
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
      rw [heq]; exact CharTwo.add_self_eq_zero _
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
      rw [heq]; exact CharTwo.add_self_eq_zero _
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

/-! ## §2. Singular cohomology `Hⁿ(X; ℤ/2) = ker δⁿ / im δⁿ⁻¹` -/

/-- The submodule of `n`-coboundaries (image of the incoming `δⁿ⁻¹`), `⊥` in degree `0`. -/
noncomputable def coboundaryRange (X : TopCat) (n : ℕ) : Submodule (ZMod 2) (SingularCochain X n) :=
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

/-- **Singular `ℤ/2` cohomology** `Hⁿ(X; ℤ/2) = ker δⁿ / im δⁿ⁻¹` — a genuine quotient `ℤ/2`-vector
space (the cohomology of the topological space `X`, built from the singular cochain complex). -/
def Cohomology (X : TopCat) (n : ℕ) : Type :=
  (LinearMap.ker (coboundaryₗ X n)) ⧸
    (coboundaryRange X n).submoduleOf (LinearMap.ker (coboundaryₗ X n))

noncomputable instance (X : TopCat) (n : ℕ) : AddCommGroup (Cohomology X n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (X : TopCat) (n : ℕ) : Module (ZMod 2) (Cohomology X n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The cohomology class of a cocycle. -/
noncomputable def Cohomology.mk (X : TopCat) (n : ℕ) (z : LinearMap.ker (coboundaryₗ X n)) :
    Cohomology X n :=
  Submodule.Quotient.mk z

/-! ## §3. The cup product (Alexander–Whitney) -/

/-- The **front `p`-face inclusion** `[p] ⟶ [p+q]`, `i ↦ i` (`Fin.castLE`). -/
def frontIncl (p q : ℕ) : SimplexCategory.mk p ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom ⟨fun i => i.castLE (by omega), fun a b h => by
    rw [Fin.le_def] at h ⊢; simp only [Fin.val_castLE]; omega⟩

/-- The **back `q`-face inclusion** `[q] ⟶ [p+q]`, `i ↦ i + p` (`Fin.natAdd`). -/
def backIncl (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom ⟨fun i => Fin.natAdd p i, fun a b h => by
    rw [Fin.le_def] at h ⊢; simp only [Fin.val_natAdd]; omega⟩

/-- The **front `p`-face** of a singular `(p+q)`-simplex (`σ` restricted to `{0,…,p}`). -/
noncomputable def frontFace {X : TopCat} {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk p)) :=
  (TopCat.toSSet.obj X).map (frontIncl p q).op σ

/-- The **back `q`-face** of a singular `(p+q)`-simplex (`σ` restricted to `{p,…,p+q}`). -/
noncomputable def backFace {X : TopCat} {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk q)) :=
  (TopCat.toSSet.obj X).map (backIncl p q).op σ

/-- The **singular cup product** `⌣ : Cᵖ × Cᵍ → Cᵖ⁺ᵍ`, `(f ⌣ g)(σ) = f(frontₚ σ) · g(backᵧ σ)`
(Alexander–Whitney). -/
noncomputable def cup {X : TopCat} {p q : ℕ} (f : SingularCochain X p) (g : SingularCochain X q) :
    SingularCochain X (p + q) :=
  fun σ => f (frontFace σ) * g (backFace σ)

@[simp] theorem cup_apply {X : TopCat} {p q : ℕ} (f : SingularCochain X p) (g : SingularCochain X q)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    cup f g σ = f (frontFace σ) * g (backFace σ) := rfl

/-- The cup product is **left-additive**. -/
theorem cup_add_left {X : TopCat} {p q : ℕ} (f₁ f₂ : SingularCochain X p) (g : SingularCochain X q) :
    cup (f₁ + f₂) g = cup f₁ g + cup f₂ g := by
  funext σ; simp only [cup_apply, Pi.add_apply]; ring

/-- The cup product is **right-additive**. -/
theorem cup_add_right {X : TopCat} {p q : ℕ} (f : SingularCochain X p) (g₁ g₂ : SingularCochain X q) :
    cup f (g₁ + g₂) = cup f g₁ + cup f g₂ := by
  funext σ; simp only [cup_apply, Pi.add_apply]; ring

/-- The cup product is **left ℤ/2-linear in the scalar**. -/
theorem cup_smul_left {X : TopCat} {p q : ℕ} (c : ZMod 2) (f : SingularCochain X p)
    (g : SingularCochain X q) : cup (c • f) g = c • cup f g := by
  funext σ; simp only [cup_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The cup product is **right ℤ/2-linear in the scalar**. -/
theorem cup_smul_right {X : TopCat} {p q : ℕ} (c : ZMod 2) (f : SingularCochain X p)
    (g : SingularCochain X q) : cup f (c • g) = c • cup f g := by
  funext σ; simp only [cup_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The cup product as a **`ℤ/2`-bilinear map** `Cᵖ →ₗ Cᵍ →ₗ Cᵖ⁺ᵍ`. -/
noncomputable def cupₗ {X : TopCat} (p q : ℕ) :
    SingularCochain X p →ₗ[ZMod 2] SingularCochain X q →ₗ[ZMod 2] SingularCochain X (p + q) :=
  LinearMap.mk₂ (ZMod 2) cup cup_add_left cup_smul_left cup_add_right cup_smul_right

@[simp] theorem cupₗ_apply {X : TopCat} {p q : ℕ} (f : SingularCochain X p) (g : SingularCochain X q) :
    cupₗ p q f g = cup f g := rfl

end SKEFTHawking.SingularCohomologyMod2
