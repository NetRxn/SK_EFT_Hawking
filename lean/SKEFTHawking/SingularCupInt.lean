/-
# Phase 5q.H · E1 — the singular **integral** cup product (Alexander–Whitney, signed)

Second E1 foundation brick, building on `SingularCohomologyInt` (the integral singular cochain
complex `Cⁿ(X;ℤ)` + signed coboundary `δ` + `δ²=0` + `Hⁿ(X;ℤ) = ker δⁿ / im δⁿ⁻¹` as a ℤ-module,
all ON MAIN, kernel-pure). This module adds the ℤ cup product and descends it to cohomology.

Structurally mirrors `SingularCohomologyMod2.{cup, cupH, cupH24}` — the same Alexander–Whitney
front-`p`-face ∪ back-`q`-face pairing, the same six morphism identities (I1–I4, D1, D2) — but over
the base ring **ℤ** with the genuine **graded signs**. The load-bearing difference from the mod-2
file is the *signed* cup-Leibniz rule

  δ(f ∪ g) = δf ∪ g + (-1)ᵖ · (f ∪ δg)      (`coboundary_cup`)

whose `(-1)ᵖ` the mod-2 file could drop (`+1 = -1` in char 2). It is essential here: it is what makes
`cocycle ∪ cocycle` a cocycle and `cocycle ∪ coboundary`, `coboundary ∪ cocycle` coboundaries, so the
product descends to a well-defined ℤ-bilinear map on cohomology. The headline is

  `cupH24 : Cohomology X 2 →ₗ[ℤ] Cohomology X 2 →ₗ[ℤ] Cohomology X 4`

— the target of the integral intersection form `H²(M⁴;ℤ) × H²(M⁴;ℤ) → H⁴(M⁴;ℤ)` on a closed
4-manifold. Feeding it the fundamental class `[M]` (a LATER brick — needs the integral fundamental
class, community-scale) turns it into the even-unimodular integer matrix the DONE lattice leg
(`AlgebraicRokhlin.IsEvenUnimodular`, `LatticeSignature.latticeSig`) consumes for `σ ÷ 16`.

All proofs kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only);
no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyInt

namespace SKEFTHawking.SingularCohomologyInt

open CategoryTheory Opposite

/-! ## §3. The cup product (Alexander–Whitney) over ℤ -/

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

/-- The **singular integral cup product** `⌣ : Cᵖ × Cᵍ → Cᵖ⁺ᵍ`, `(f ⌣ g)(σ) = f(frontₚ σ) · g(backᵧ σ)`
(Alexander–Whitney; the sign is carried by `δ`, not `⌣`). -/
noncomputable def cup {X : TopCat} {p q : ℕ} (f : SingularCochainInt X p) (g : SingularCochainInt X q) :
    SingularCochainInt X (p + q) :=
  fun σ => f (frontFace σ) * g (backFace σ)

@[simp] theorem cup_apply {X : TopCat} {p q : ℕ} (f : SingularCochainInt X p)
    (g : SingularCochainInt X q)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    cup f g σ = f (frontFace σ) * g (backFace σ) := rfl

/-- The cup product is **left-additive**. -/
theorem cup_add_left {X : TopCat} {p q : ℕ} (f₁ f₂ : SingularCochainInt X p)
    (g : SingularCochainInt X q) : cup (f₁ + f₂) g = cup f₁ g + cup f₂ g := by
  funext σ; simp only [cup_apply, Pi.add_apply]; ring

/-- The cup product is **right-additive**. -/
theorem cup_add_right {X : TopCat} {p q : ℕ} (f : SingularCochainInt X p)
    (g₁ g₂ : SingularCochainInt X q) : cup f (g₁ + g₂) = cup f g₁ + cup f g₂ := by
  funext σ; simp only [cup_apply, Pi.add_apply]; ring

/-- The cup product is **left ℤ-linear in the scalar**. -/
theorem cup_smul_left {X : TopCat} {p q : ℕ} (c : ℤ) (f : SingularCochainInt X p)
    (g : SingularCochainInt X q) : cup (c • f) g = c • cup f g := by
  funext σ; simp only [cup_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The cup product is **right ℤ-linear in the scalar**. -/
theorem cup_smul_right {X : TopCat} {p q : ℕ} (c : ℤ) (f : SingularCochainInt X p)
    (g : SingularCochainInt X q) : cup f (c • g) = c • cup f g := by
  funext σ; simp only [cup_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The cup product as a **ℤ-bilinear map** `Cᵖ →ₗ Cᵍ →ₗ Cᵖ⁺ᵍ`. -/
noncomputable def cupₗ {X : TopCat} (p q : ℕ) :
    SingularCochainInt X p →ₗ[ℤ] SingularCochainInt X q →ₗ[ℤ] SingularCochainInt X (p + q) :=
  LinearMap.mk₂ ℤ cup cup_add_left cup_smul_left cup_add_right cup_smul_right

@[simp] theorem cupₗ_apply {X : TopCat} {p q : ℕ} (f : SingularCochainInt X p)
    (g : SingularCochainInt X q) : cupₗ p q f g = cup f g := rfl

/-! ## §4. The signed cup Leibniz rule `δ(f ⌣ g) = δf ⌣ g + (-1)ᵖ · (f ⌣ δg)`

The Alexander–Whitney coboundary identity over ℤ, cast-free at a fixed `(p+q+1)`-simplex `τ`. Same
front/back inclusion machinery as the mod-2 file; the six morphism identities (I1–I4, D1, D2) are
sign-free (about `SimplexCategory.δ` compositions), copied verbatim. The genuine ℤ content is the
sign bookkeeping in `coboundary_cup`: faces `i ≤ p` feed `δf ⌣ g` with their native sign `(-1)ⁱ`;
faces `i ≥ p+1` feed `(-1)ᵖ · f ⌣ δg`; the two diagonal terms carry OPPOSITE signs and cancel over ℤ
(the mod-2 file used `+1 = -1` instead). -/

/-- Inclusion `[p+1] ⟶ [p+q+1]` onto the front vertices `{0,…,p+1}`. -/
def frontBigIncl (p q : ℕ) : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom ⟨fun i => i.castLE (by omega), fun a b h => by
    rw [Fin.le_def] at h ⊢; simp only [Fin.val_castLE]; omega⟩

/-- Inclusion `[q] ⟶ [p+q+1]` onto the back vertices `{p+1,…,p+q+1}`. The `(p+1) + i` order matches
`backIncl`'s `Fin.natAdd`, so `backBig` and `backFace` agree definitionally. -/
def backBigIncl (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom ⟨fun i => ⟨(p + 1) + i.val, by have := i.isLt; omega⟩, fun a b h => by
    simp only [Fin.le_def] at h ⊢; omega⟩

/-- **Front `(p+1)`-face** of a `(p+q+1)`-simplex (vertices `{0,…,p+1}`); carries `δf`. -/
noncomputable def frontBig {X : TopCat} {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + 1))) :=
  (TopCat.toSSet.obj X).map (frontBigIncl p q).op σ

/-- **Back `q`-face** of a `(p+q+1)`-simplex (vertices `{p+1,…,p+q+1}`). -/
noncomputable def backBig {X : TopCat} {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk q)) :=
  (TopCat.toSSet.obj X).map (backBigIncl p q).op σ

/-- **Front `p`-face** of a `(p+q+1)`-simplex (vertices `{0,…,p}`); reuses `frontIncl p (q+1)`. -/
noncomputable def frontSmall {X : TopCat} {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk p)) :=
  (TopCat.toSSet.obj X).map (frontIncl p (q + 1)).op σ

/-- **Back `(q+1)`-face** of a `(p+q+1)`-simplex (vertices `{p,…,p+q+1}`); carries `δg`. -/
noncomputable def backSmall {X : TopCat} {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (q + 1))) :=
  (TopCat.toSSet.obj X).map (backIncl p (q + 1)).op σ

/-- The value of `Fin.succAbove`. The single arithmetic fact behind every face-commutation below. -/
theorem succAbove_val {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  rcases lt_or_ge i.castSucc p with h | h
  · rw [Fin.succAbove_of_castSucc_lt p i h, Fin.val_castSucc, if_pos]
    rwa [Fin.lt_def, Fin.val_castSucc] at h
  · rw [Fin.succAbove_of_le_castSucc p i h, Fin.val_succ, if_neg]
    rw [Fin.le_def, Fin.val_castSucc] at h; omega

/-- `δ i` as an order map evaluates to `Fin.succAbove` (definitional; for `simp` matching). -/
theorem toOrderHom_δ {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 1)) :
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) x = i.succAbove x := rfl

/-- `Hom.toOrderHom (mkHom f)` evaluates to `f` (definitional; for `simp` matching). -/
theorem toOrderHom_mkHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (n + 1)) :
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.mkHom f)) x = f x := rfl

/-- **(I1)** Front-face commutation for `i ≤ p`. -/
theorem front_comp_δ_of_le (p q : ℕ) (i : Fin (p + q + 2)) (h : i.val ≤ p) :
    frontIncl p q ≫ SimplexCategory.δ i
      = SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (p + 2)) ≫ frontBigIncl p q := by
  ext x : 3
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, toOrderHom_δ,
    frontIncl, frontBigIncl, toOrderHom_mkHom, OrderHom.coe_mk, succAbove_val, Fin.val_castLE]

/-- **(I2)** Back-face invariance for `i ≤ p`. -/
theorem back_comp_δ_of_le (p q : ℕ) (i : Fin (p + q + 2)) (h : i.val ≤ p) :
    backIncl p q ≫ SimplexCategory.δ i = backBigIncl p q := by
  ext x : 3
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, toOrderHom_δ,
    backIncl, backBigIncl, toOrderHom_mkHom, OrderHom.coe_mk, succAbove_val, Fin.val_natAdd]
  split <;> omega

/-- **(I3)** Front-face invariance for `i > p`. -/
theorem front_comp_δ_of_gt (p q : ℕ) (i : Fin (p + q + 2)) (h : p < i.val) :
    frontIncl p q ≫ SimplexCategory.δ i = frontIncl p (q + 1) := by
  ext x : 3
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, toOrderHom_δ,
    frontIncl, toOrderHom_mkHom, OrderHom.coe_mk, succAbove_val, Fin.val_castLE]
  have hx : x.val < p + 1 := x.isLt
  split_ifs <;> omega

/-- **(I4)** Back-face commutation for `i > p`. -/
theorem back_comp_δ_of_gt (p q : ℕ) (i : Fin (p + q + 2)) (h : p < i.val) :
    backIncl p q ≫ SimplexCategory.δ i
      = SimplexCategory.δ (⟨i.val - p, by have := i.isLt; omega⟩ : Fin (q + 2)) ≫ backIncl p (q + 1) := by
  ext x : 3
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, toOrderHom_δ,
    backIncl, toOrderHom_mkHom, OrderHom.coe_mk, succAbove_val, Fin.val_natAdd]
  split_ifs <;> omega

/-- **(D1)** Diagonal front term. -/
theorem δ_last_comp_frontBig (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ frontBigIncl p q = frontIncl p (q + 1) := by
  ext x : 3
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, toOrderHom_δ,
    frontIncl, frontBigIncl, toOrderHom_mkHom, OrderHom.coe_mk, succAbove_val, Fin.val_castLE,
    Fin.val_last]
  have hx : x.val < p + 1 := x.isLt
  split_ifs <;> omega

/-- **(D2)** Diagonal back term. -/
theorem δ_zero_comp_backSmall (p q : ℕ) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫ backIncl p (q + 1) = backBigIncl p q := by
  ext x : 3
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, toOrderHom_δ,
    backIncl, backBigIncl, toOrderHom_mkHom, OrderHom.coe_mk, succAbove_val, Fin.val_natAdd,
    Fin.val_zero]
  split_ifs <;> omega

/-! ### Per-term face evaluations (functoriality + the six morphism identities) -/

variable {X : TopCat} {p q : ℕ}
  (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1))))

/-- For `i ≤ p`: the front-`p` face of `∂ᵢτ` is the `i`-th face of the front-`(p+1)` face of `τ`. -/
theorem frontFace_face_of_le (i : Fin (p + q + 2)) (h : i.val ≤ p) :
    frontFace (face i τ) = face (⟨i.val, by omega⟩ : Fin (p + 2)) (frontBig τ) := by
  unfold frontFace face frontBig
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
    front_comp_δ_of_le p q i h]

/-- For `i ≤ p`: the back-`q` face of `∂ᵢτ` is the back-`q` face of `τ`. -/
theorem backFace_face_of_le (i : Fin (p + q + 2)) (h : i.val ≤ p) :
    backFace (face i τ) = backBig τ := by
  unfold backFace face backBig
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, back_comp_δ_of_le p q i h]

/-- For `i > p`: the front-`p` face of `∂ᵢτ` is the front-`p` face of `τ`. -/
theorem frontFace_face_of_gt (i : Fin (p + q + 2)) (h : p < i.val) :
    frontFace (face i τ) = frontSmall τ := by
  unfold frontFace face frontSmall
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, front_comp_δ_of_gt p q i h]

/-- For `i > p`: the back-`q` face of `∂ᵢτ` is the `(i-p)`-th face of the back-`(q+1)` face of `τ`. -/
theorem backFace_face_of_gt (i : Fin (p + q + 2)) (h : p < i.val) :
    backFace (face i τ) = face (⟨i.val - p, by have := i.isLt; omega⟩ : Fin (q + 2)) (backSmall τ) := by
  unfold backFace face backSmall
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
    back_comp_δ_of_gt p q i h]

/-- The last face of the front-`(p+1)` face of `τ` is its front-`p` face (the diagonal front term). -/
theorem face_last_frontBig : face (Fin.last (p + 1)) (frontBig τ) = frontSmall τ := by
  unfold face frontBig frontSmall
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ_last_comp_frontBig p q]

/-- The zeroth face of the back-`(q+1)` face of `τ` is its back-`q` face (the diagonal back term). -/
theorem face_zero_backSmall : face (0 : Fin (q + 2)) (backSmall τ) = backBig τ := by
  unfold face backSmall backBig
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ_zero_comp_backSmall p q]

/-! ### The signed cup Leibniz identity -/

/-- **Signed cup Leibniz** (over ℤ): `δ(f ⌣ g) = δf ⌣ g + (-1)ᵖ · (f ⌣ δg)`, cast-free at `τ`. The
left side sums `(-1)ⁱ · f(frontₚ ∂ᵢτ)·g(back_q ∂ᵢτ)` over all faces; the right side carries `δf` on
the front-`(p+1)` face and `δg` on the back-`(q+1)` face. Faces split at `i = p`: faces `i ≤ p` feed
`δf ⌣ g`, faces `i ≥ p+1` feed `(-1)ᵖ · f ⌣ δg`, and the two diagonal terms
(`δf`'s last face × `g`'s back = `+(-1)ᵖ·f(frontSmall)g(backBig)`, `f`'s front × `δg`'s first face
= `-(-1)ᵖ·f(frontSmall)g(backBig)`) carry OPPOSITE signs and cancel over ℤ. -/
theorem coboundary_cup (f : SingularCochainInt X p) (g : SingularCochainInt X q) :
    coboundary X (p + q) (cup f g) τ
      = coboundary X p f (frontBig τ) * g (backBig τ)
        + (-1 : ℤ) ^ p * (f (frontSmall τ) * coboundary X q g (backSmall τ)) := by
  rw [coboundary_apply, coboundary_apply, coboundary_apply]
  simp only [cup_apply]
  have h : p + 1 + (q + 1) = p + q + 2 := by omega
  -- RHS canonical middle form. First distribute the two coboundary sums.
  have hAB :
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) * f (face i (frontBig τ))) * g (backBig τ)
        + (-1 : ℤ) ^ p * (f (frontSmall τ) *
            ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) * g (face i (backSmall τ)))
      = (∑ j : Fin (p + 1), (-1 : ℤ) ^ (j.castSucc : ℕ) *
              (f (face j.castSucc (frontBig τ)) * g (backBig τ)))
        + (∑ k : Fin (q + 1), (-1 : ℤ) ^ (p + (k.succ : ℕ)) *
              (f (frontSmall τ) * g (face k.succ (backSmall τ)))) := by
    rw [Fin.sum_univ_castSucc (f := fun i => (-1 : ℤ) ^ (i : ℕ) * f (face i (frontBig τ))),
      Fin.sum_univ_succ (f := fun i => (-1 : ℤ) ^ (i : ℕ) * g (face i (backSmall τ))),
      face_last_frontBig, face_zero_backSmall]
    -- Distribute the front sum × g(backBig); expand the (-1)ᵖ·f(frontSmall) × back block.
    rw [add_mul, Finset.sum_mul, mul_add, Finset.mul_sum]
    -- Match the two surviving Σⱼ / Σₖ termwise, and cancel the two diagonal terms.
    have efront : (∑ i : Fin (p + 1),
          (-1 : ℤ) ^ (i.castSucc : ℕ) * f (face i.castSucc (frontBig τ)) * g (backBig τ))
        = ∑ j : Fin (p + 1),
          (-1 : ℤ) ^ (j.castSucc : ℕ) * (f (face j.castSucc (frontBig τ)) * g (backBig τ)) :=
      Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])
    -- The back block: (-1)ᵖ·(f·((-1)⁰·g(backBig)) + Σᵢ f·((-1)^i.succ·g)) — distribute (-1)ᵖ, then
    -- align the surviving Σₖ termwise and expose the back diagonal.
    have eback : (-1 : ℤ) ^ p * (f (frontSmall τ) * ((-1 : ℤ) ^ (0 : ℕ) * g (backBig τ))
          + ∑ i : Fin (q + 1), f (frontSmall τ) * ((-1 : ℤ) ^ (i.succ : ℕ) * g (face i.succ (backSmall τ))))
        = (-1 : ℤ) ^ p * (f (frontSmall τ) * g (backBig τ))
          + ∑ k : Fin (q + 1),
              (-1 : ℤ) ^ (p + (k.succ : ℕ)) * (f (frontSmall τ) * g (face k.succ (backSmall τ))) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · rw [pow_zero]; ring
      · exact Finset.sum_congr rfl (fun k _ => by rw [Fin.val_succ, pow_add]; ring)
    rw [Fin.val_zero, eback, efront]
    -- Remaining: Σⱼ + diag_front + (diag_back + Σₖ) = Σⱼ + Σₖ, with the two diagonals cancelling.
    rw [Fin.val_last]
    rw [add_assoc, ← add_assoc ((-1 : ℤ) ^ (p + 1) * f (frontSmall τ) * g (backBig τ))]
    have hdiag : (-1 : ℤ) ^ (p + 1) * f (frontSmall τ) * g (backBig τ)
        + (-1 : ℤ) ^ p * (f (frontSmall τ) * g (backBig τ)) = 0 := by
      rw [pow_succ]; ring
    rw [hdiag, zero_add]
  -- LHS reaches the same middle form: split `Fin (p+q+2)` at `p`, evaluate each face.
  have hL : (∑ i : Fin (p + q + 2), (-1 : ℤ) ^ (i : ℕ) *
        (f (frontFace (face i τ)) * g (backFace (face i τ))))
      = (∑ j : Fin (p + 1), (-1 : ℤ) ^ (j.castSucc : ℕ) *
              (f (face j.castSucc (frontBig τ)) * g (backBig τ)))
        + (∑ k : Fin (q + 1), (-1 : ℤ) ^ (p + (k.succ : ℕ)) *
              (f (frontSmall τ) * g (face k.succ (backSmall τ)))) := by
    rw [← Equiv.sum_comp (finCongr h)
        (fun i => (-1 : ℤ) ^ (i : ℕ) * (f (frontFace (face i τ)) * g (backFace (face i τ)))),
      Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      have hle : (finCongr h (Fin.castAdd (q + 1) j)).val ≤ p := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd]; omega
      rw [frontFace_face_of_le τ _ hle, backFace_face_of_le τ _ hle]
      have hidx : (⟨(finCongr h (Fin.castAdd (q + 1) j)).val, by omega⟩ : Fin (p + 2))
          = j.castSucc := by
        apply Fin.ext; simp [Fin.val_castSucc]
      rw [hidx]
      have hval : ((finCongr h (Fin.castAdd (q + 1) j)) : ℕ) = (j.castSucc : ℕ) := by
        simp [Fin.val_castSucc]
      rw [hval]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      have hgt : p < (finCongr h (Fin.natAdd (p + 1) k)).val := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [frontFace_face_of_gt τ _ hgt, backFace_face_of_gt τ _ hgt]
      have hidx : (⟨(finCongr h (Fin.natAdd (p + 1) k)).val - p, by have := k.isLt; omega⟩ : Fin (q + 2))
          = k.succ := by
        apply Fin.ext; simp only [Fin.val_succ, finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [hidx]
      have hval : ((finCongr h (Fin.natAdd (p + 1) k)) : ℕ) = p + (k.succ : ℕ) := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega
      rw [hval]
  rw [hL, ← hAB]

/-- **Cocycle ⌣ cocycle is a cocycle.** From the signed Leibniz `coboundary_cup`: both right-hand
terms carry a factor `δf` resp. `δg` (the `(-1)ᵖ` is irrelevant when `δg = 0`), which vanish. -/
theorem cup_cocycle (f : SingularCochainInt X p) (g : SingularCochainInt X q)
    (hf : coboundaryₗ X p f = 0) (hg : coboundaryₗ X q g = 0) :
    coboundaryₗ X (p + q) (cup f g) = 0 := by
  funext τ
  show coboundary X (p + q) (cup f g) τ = 0
  rw [coboundary_cup]
  have hf' : coboundary X p f (frontBig τ) = 0 := congrFun hf (frontBig τ)
  have hg' : coboundary X q g (backSmall τ) = 0 := congrFun hg (backSmall τ)
  rw [hf', hg', zero_mul, mul_zero, mul_zero, add_zero]

/-- **Cocycle ⌣ coboundary is a coboundary** (right argument): if `f` is a cocycle then
`(-1)ᵖ · (f ⌣ δb) = δ(f ⌣ b)`. From the signed Leibniz: `δf`'s term drops. This is the descent fact
`cupₗ` sends `ker δ × im δ → im δ` — the `(-1)ᵖ` is a unit so `f ⌣ δb` is still in `im δ`. -/
theorem cup_coboundary_right (f : SingularCochainInt X p) (b : SingularCochainInt X q)
    (hf : coboundaryₗ X p f = 0) :
    coboundaryₗ X (p + q) (cup f b) = (-1 : ℤ) ^ p • cup f (coboundaryₗ X q b) := by
  funext τ
  show coboundary X (p + q) (cup f b) τ = ((-1 : ℤ) ^ p • cup f (coboundaryₗ X q b)) τ
  rw [coboundary_cup]
  have hf' : coboundary X p f (frontBig τ) = 0 := congrFun hf (frontBig τ)
  rw [hf', zero_mul, zero_add]
  show _ = (-1 : ℤ) ^ p * cup f (coboundaryₗ X q b) τ
  rw [cup_apply]
  rfl

/-- **Coboundary ⌣ cocycle is a coboundary** (left argument, degrees `1,2`): if `g : C²` is a cocycle
then `δa ⌣ g = δ(a ⌣ g)` for `a : C¹`. From the signed Leibniz: `δg`'s term drops (no sign issue on
the left — `δf ⌣ g` is the sign-free RHS term). Cast-free at the concrete degrees `(1+2)+1 = 4 = 2+2`. -/
theorem cup_coboundary_left_1_2 (a : SingularCochainInt X 1) (g : SingularCochainInt X 2)
    (hg : coboundaryₗ X 2 g = 0) :
    coboundaryₗ X (1 + 2) (cup a g) = cup (coboundaryₗ X 1 a) g := by
  funext τ
  show coboundary X (1 + 2) (cup a g) τ = cup (coboundaryₗ X 1 a) g τ
  rw [coboundary_cup, cup_apply]
  have hg' : coboundary X 2 g (backSmall τ) = 0 := congrFun hg (backSmall τ)
  rw [hg', mul_zero, mul_zero, add_zero]
  rfl

/-! ### The cup product on cohomology `H² × H² → H⁴` (the integral 4-manifold intersection form) -/

/-- For a fixed degree-2 cocycle `fc`, cup-with-`fc` descends to a linear map `H² → H⁴`. The cup lands
in cocycles (`cup_cocycle`); it kills `H²`-coboundaries because `f ⌣ δb = (-1)² · δ(f ⌣ b) = δ(f ⌣ b)`
is in `im δ` (`cup_coboundary_right`; the `(-1)ᵖ` unit is absorbed). -/
noncomputable def cupRightH24 (fc : LinearMap.ker (coboundaryₗ X 2)) :
    Cohomology X 2 →ₗ[ℤ] Cohomology X 4 :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cupₗ 2 2 fc.1).domRestrict (LinearMap.ker (coboundaryₗ X 2))).codRestrict
        (LinearMap.ker (coboundaryₗ X 4)) fun gc => by
          rw [LinearMap.mem_ker]
          exact cup_cocycle fc.1 gc.1 (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)))
    (by
      intro gc hgc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hgc
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, cupₗ_apply]
      show cup fc.1 gc.1 ∈ LinearMap.range (coboundaryₗ X 3)
      obtain ⟨b, hb⟩ := hgc
      refine ⟨cup fc.1 b, ?_⟩
      show coboundaryₗ X (2 + 1) (cup fc.1 b) = cup fc.1 gc.1
      rw [cup_coboundary_right fc.1 b (LinearMap.mem_ker.mp fc.2)]
      show (-1 : ℤ) ^ 2 • cup fc.1 (coboundaryₗ X 1 b) = cup fc.1 gc.1
      rw [hb]
      norm_num)

/-- The computation rule for `cupRightH24` on a representative cocycle `gc`. -/
theorem cupRightH24_apply_mk (fc gc : LinearMap.ker (coboundaryₗ X 2)) :
    cupRightH24 fc (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 4)) := by
  rfl

/-- **The integral cup product on `H² × H² → H⁴`** — a genuine ℤ-bilinear map: the 4-manifold
integral intersection form `H²(M⁴;ℤ) × H²(M⁴;ℤ) → H⁴(M⁴;ℤ)`. Well-defined: `cup_cocycle` lands it in
cocycles; `cup_coboundary_right`/`cup_coboundary_left_1_2` kill coboundaries in each argument. The
integral degree-`(2,2)` intersection-form target — the object the DONE lattice leg consumes for
`σ ÷ 16` once paired against the fundamental class. -/
noncomputable def cupH24 : Cohomology X 2 →ₗ[ℤ] Cohomology X 2 →ₗ[ℤ] Cohomology X 4 :=
  Submodule.liftQ _
    { toFun := cupRightH24
      map_add' := fun fc fc' => by
        ext x
        obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp only [LinearMap.add_apply, cupRightH24_apply_mk]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_add, cup_add_left]
      map_smul' := fun c fc => by
        ext x
        obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp only [LinearMap.smul_apply, RingHom.id_apply, cupRightH24_apply_mk]
        congr 1
        apply Subtype.ext
        simp only [SetLike.val_smul, cup_smul_left] }
    (by
      intro fc hfc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hfc
      rw [LinearMap.mem_ker]
      ext x
      obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.zero_apply]
      change cupRightH24 fc (Submodule.Quotient.mk gc) = 0
      rw [cupRightH24_apply_mk]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      show cup fc.1 gc.1 ∈ LinearMap.range (coboundaryₗ X 3)
      obtain ⟨a, ha⟩ := hfc
      refine ⟨cup a gc.1, ?_⟩
      rw [← ha]
      exact cup_coboundary_left_1_2 a gc.1 (LinearMap.mem_ker.mp gc.2))

@[simp] theorem cupH24_mk_mk (fc gc : LinearMap.ker (coboundaryₗ X 2)) :
    cupH24 (Submodule.Quotient.mk fc) (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 4)) := by
  show cupRightH24 fc (Submodule.Quotient.mk gc) = _
  exact cupRightH24_apply_mk fc gc

end SKEFTHawking.SingularCohomologyInt
