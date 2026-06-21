/-
# Phase 5q.F — the mod-2 Bockstein `Sq¹` on singular ℤ/2 cohomology (the concrete cohomology operation)

`PoincareDualityWuFormula.lean` carries the degree-`(3,4)` operation `sq1₃ : H³ →ₗ H⁴` as an **abstract
field** of `structure PoincareDual4Lo`, because the project had no singular Bockstein. This module builds
the genuine operation.

The **mod-2 Bockstein** `Sq¹ : Hⁿ(X;ℤ/2) → Hⁿ⁺¹(X;ℤ/2)` is the connecting homomorphism of the
short-exact coefficient sequence `0 → ℤ/2 →·2 ℤ/4 → ℤ/2 → 0`. Concretely, for a mod-2 cocycle
`a : Cⁿ(X;ℤ/2)`:

* lift `a` set-theoretically to a ℤ/4-cochain `ã` (here: the `{0,1}`-valued lift `lift a`);
* the **signed** ℤ/4 coboundary `δ₄ ã` is divisible by `2` (because `a` is a mod-2 cocycle, `δ₄ ã`
  reduces to `δ₂ a = 0` mod 2);
* `Sq¹ a := (δ₄ ã)/2  (mod 2) : Cⁿ⁺¹(X;ℤ/2)`, which is itself a cocycle (from `δ₄² ã = 0`), and is
  well-defined on cohomology (independent of the lift and killing coboundaries).

Built on `SKEFTHawking.SingularCohomologyMod2` (singular `ℤ/2` cochains/cohomology, faces, `δ₂`,
`face_face`, the `δ²=0` involution) — we add the **signed ℤ/4 cochain complex** as the lift target,
the divisibility, and the Bockstein. The cross-check `Sq1_on_H1 : Sq1 x = x ∪ x` on `H¹` ties the
construction back to the project's `cupSquare`/`cupH`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularBockstein

open CategoryTheory Opposite SKEFTHawking.SingularCohomologyMod2

/-! ## §1. The signed ℤ/4 cochain complex (the lift target of the Bockstein) -/

/-- **Singular `n`-cochains with `ℤ/4` coefficients**: `ℤ/4`-valued functions on singular `n`-simplices.
The lift target for the Bockstein of the coefficient sequence `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0`. -/
abbrev Cochain4 (X : TopCat) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) → ZMod 4

/-- The **signed ℤ/4 coboundary** `δ₄ : C⁴ⁿ → C⁴ⁿ⁺¹`, `(δ₄ f)(σ) = ∑ᵢ (-1)ⁱ f(∂ᵢ σ)`. The genuine
alternating sign is needed over `ℤ/4` (unlike the mod-2 `coboundary`, where `-1 = 1`). -/
noncomputable def coboundary4 (X : TopCat) (n : ℕ) (f : Cochain4 X n) : Cochain4 X (n + 1) :=
  fun σ => ∑ i : Fin (n + 2), (-1 : ZMod 4) ^ (i : ℕ) * f (face i σ)

@[simp] theorem coboundary4_apply (X : TopCat) (n : ℕ) (f : Cochain4 X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    coboundary4 X n f σ = ∑ i : Fin (n + 2), (-1 : ZMod 4) ^ (i : ℕ) * f (face i σ) := rfl

/-! ## §2. `δ₄² = 0` — the signed ℤ/4 cochain complex condition (the crux)

The exact same fixed-point-free involution on `Fin (n+3) × Fin (n+2)` as the mod-2
`coboundary_comp_coboundary`, but now with signs. For each pair the partner morphism is the *same*
composite coface `δ ⋯ ≫ δ ⋯` (by `SimplexCategory.δ_comp_δ`), so the two `f`-values agree; the partner
always **flips the `i+j` parity** (`(j.castSucc, i.pred)` has exponent `i+j-1`; `(j.succ, i.castPred)`
has exponent `i+j+1`), so the two signed summands cancel: `(-1)^k·v + (-1)^(k±1)·v = (-1)^k·v·(1+(-1)) = 0`
in `ZMod 4`. This replaces the mod-2 `CharTwo.add_self_eq_zero` by the signed cancellation. -/

/-- Signed cancellation in `ZMod 4`: a term and its parity-flipped partner cancel. If exponents `e₁` and
`e₂` have opposite parity then `(-1)^e₁ * v + (-1)^e₂ * v = 0`. The arithmetic heart of `δ₄² = 0`. -/
theorem neg_one_pow_flip_add (e₁ e₂ : ℕ) (v : ZMod 4) (h : e₁ % 2 ≠ e₂ % 2) :
    (-1 : ZMod 4) ^ e₁ * v + (-1 : ZMod 4) ^ e₂ * v = 0 := by
  have hpar : ((-1 : ZMod 4) ^ e₁) = - ((-1 : ZMod 4) ^ e₂) := by
    rcases Nat.even_or_odd e₁ with h1 | h1 <;> rcases Nat.even_or_odd e₂ with h2 | h2
    · exact absurd (by rw [Nat.even_iff] at h1; rw [Nat.even_iff] at h2; omega) h
    · rw [Even.neg_one_pow h1, Odd.neg_one_pow h2]; ring
    · rw [Odd.neg_one_pow h1, Even.neg_one_pow h2]
    · exact absurd (by rw [Nat.odd_iff] at h1; rw [Nat.odd_iff] at h2; omega) h
  rw [hpar]; ring

/-- **`δ₄² = 0`** — the signed ℤ/4 cochain complex condition. Same involution as the mod-2
`coboundary_comp_coboundary`; the partner always flips the `i+j` parity, so the signed summands cancel
pairwise via `neg_one_pow_flip_add` (replacing the mod-2 `CharTwo.add_self_eq_zero`). -/
theorem coboundary4_comp_coboundary4 (X : TopCat) (n : ℕ) (f : Cochain4 X n) :
    coboundary4 X (n + 1) (coboundary4 X n f) = 0 := by
  funext σ
  simp only [coboundary4_apply, face_face, Pi.zero_apply, Finset.mul_sum]
  -- pull the outer sign through the inner sum, reindex to a single sum over the product
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    (-1 : ZMod 4) ^ (p.1 : ℕ) * ((-1 : ZMod 4) ^ (p.2 : ℕ) *
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
      -- exponents: (i.val + j.val) vs (j.castSucc.val + (i.pred).val) = (j.val + (i.val - 1)); flip parity
      rw [heq]
      rw [show ((-1 : ZMod 4) ^ (i : ℕ) * ((-1 : ZMod 4) ^ (j : ℕ) *
            f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.pred hne) ≫
              SimplexCategory.δ j.castSucc).op σ)))
          = (-1 : ZMod 4) ^ ((i : ℕ) + (j : ℕ)) *
              f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.pred hne) ≫
                SimplexCategory.δ j.castSucc).op σ) by rw [pow_add]; ring,
        show ((-1 : ZMod 4) ^ ((j.castSucc : Fin (n + 2 + 1)) : ℕ) *
            ((-1 : ZMod 4) ^ ((i.pred hne : Fin (n + 2)) : ℕ) *
            f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.pred hne) ≫
              SimplexCategory.δ j.castSucc).op σ)))
          = (-1 : ZMod 4) ^ ((j.castSucc : Fin (n + 2 + 1)).val + (i.pred hne : Fin (n + 2)).val) *
              f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.pred hne) ≫
                SimplexCategory.δ j.castSucc).op σ) by rw [pow_add]; ring]
      apply neg_one_pow_flip_add
      simp only [Fin.val_castSucc, Fin.val_pred]
      have hi : 1 ≤ (i : ℕ) := by rw [Fin.lt_def, Fin.val_castSucc] at h; omega
      omega
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
      rw [show ((-1 : ZMod 4) ^ (i : ℕ) * ((-1 : ZMod 4) ^ (j : ℕ) *
            f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.castPred hne) ≫
              SimplexCategory.δ j.succ).op σ)))
          = (-1 : ZMod 4) ^ ((i : ℕ) + (j : ℕ)) *
              f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.castPred hne) ≫
                SimplexCategory.δ j.succ).op σ) by rw [pow_add]; ring,
        show ((-1 : ZMod 4) ^ ((j.succ : Fin (n + 2 + 1)) : ℕ) *
            ((-1 : ZMod 4) ^ ((i.castPred hne : Fin (n + 2)) : ℕ) *
            f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.castPred hne) ≫
              SimplexCategory.δ j.succ).op σ)))
          = (-1 : ZMod 4) ^ ((j.succ : Fin (n + 2 + 1)).val + (i.castPred hne : Fin (n + 2)).val) *
              f ((TopCat.toSSet.obj X).map (SimplexCategory.δ (i.castPred hne) ≫
                SimplexCategory.δ j.succ).op σ) by rw [pow_add]; ring]
      apply neg_one_pow_flip_add
      simp only [Fin.val_succ, Fin.coe_castPred]
      omega
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

/-! ## §3. The `{0,1}` lift, the half map, and the divisibility `2 ∣ δ₄(lift a)`

For a mod-2 cochain `a`, the canonical set-theoretic lift `lift a := fun σ => ((a σ).val : ZMod 4)`
takes values in `{0,1} ⊂ ZMod 4`. When `a` is a *cocycle* (`δ₂ a = 0`), the signed ℤ/4 coboundary
`δ₄(lift a)` is **even**: modulo 2 the signs are trivial and `δ₄(lift a)` reduces to `δ₂ a = 0`, so
each value lies in `{0,2}`. The half map `half y := (y.val / 2 : ZMod 2)` then extracts the Bockstein. -/

/-- The canonical `{0,1}`-valued ℤ/4 lift of a mod-2 cochain: `(lift a)(σ) = ((a σ).val : ZMod 4)`. -/
noncomputable def lift {X : TopCat} {n : ℕ} (a : SingularCochain X n) : Cochain4 X n :=
  fun σ => ((a σ).val : ZMod 4)

@[simp] theorem lift_apply {X : TopCat} {n : ℕ} (a : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    lift a σ = ((a σ).val : ZMod 4) := rfl

/-- The **half map** `ZMod 4 → ZMod 2`, `y ↦ (y.val / 2 : ℕ)`: sends `0,1 ↦ 0` and `2,3 ↦ 1`. The
nonlinear "divide by 2 then reduce" map carrying the connecting homomorphism of `0→ℤ/2→ℤ/4→ℤ/2→0`. -/
def half (y : ZMod 4) : ZMod 2 := (y.val / 2 : ℕ)

@[simp] theorem half_zero : half 0 = 0 := by decide
@[simp] theorem half_two : half 2 = 1 := by decide

/-- On the even elements of `ZMod 4`, `half` is additive: `half (2*m + 2*k) = m + k`-type behaviour.
Stated as the only instance we need — `half (2 • t)`-vs-doubling — via the decidable check that
`half` is the section of `(· * 2) : ZMod 2 → ZMod 4`. For `t : ZMod 2`, `half (2 * (t.val : ZMod 4)) = t`. -/
theorem half_two_mul (t : ZMod 2) : half (2 * (t.val : ZMod 4)) = t := by
  fin_cases t <;> decide

/-- `lift a` reduced mod 2 is `a`: the ring hom `castHom (2 ∣ 4) : ZMod 4 →+* ZMod 2` sends `(lift a)(σ)`
back to `a σ` (since `a σ ∈ {0,1}` lifts to `{0,1} ⊂ ZMod 4`). The "section then reduce = identity" leg. -/
theorem castHom_lift {X : TopCat} {n : ℕ} (a : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (lift a σ) = a σ := by
  rw [lift_apply]
  rw [map_natCast]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- **Divisibility `2 ∣ δ₄(lift a)`** pointwise, for a mod-2 *cocycle* `a`. Modulo 2 the signs vanish
(`(-1) ≡ 1`) and `δ₄(lift a)(σ)` reduces to `δ₂ a (σ) = 0`, so the value is even. Concretely: the ring
hom `castHom (2∣4)` sends `δ₄(lift a) σ` to `coboundary a σ = 0`, i.e. `δ₄(lift a) σ ∈ ker(castHom) = 2·ZMod 4`. -/
theorem castHom_coboundary4_lift {X : TopCat} {n : ℕ} (a : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (coboundary4 X n (lift a) σ)
      = coboundary X n a σ := by
  rw [coboundary4_apply, coboundary_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, castHom_lift]
  rw [map_pow, map_neg, map_one]
  rw [show ((-1 : ZMod 2)) = 1 from by decide, one_pow, one_mul]

/-! ## §4. The Bockstein `Sq¹` on cochains and its descent to cohomology

`Sq1cochain a := fun σ => half (δ₄(lift a) σ)`. For a cocycle `a` this is a `ℤ/2`-cocycle (from
`δ₄² = 0`); on cohomology `[a] ↦ [Sq1cochain a]` is well-defined and `ℤ/2`-linear. The linearity uses
the clean cochain identity `Sq1cochain (a+b) = Sq1cochain a + Sq1cochain b + δ₂(a · b)` (the lift defect
`lift(a+b) − lift a − lift b = 2·lift(a·b)` becomes a coboundary after `half∘δ₄`). -/

/-- `half` is additive on the **even** elements of `ZMod 4` (the only place it is): if `y₁, y₂` reduce to
`0` under `castHom (2∣4)` then `half (y₁ + y₂) = half y₁ + half y₂`. -/
theorem half_add_of_even (y₁ y₂ : ZMod 4)
    (h₁ : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) y₁ = 0)
    (h₂ : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) y₂ = 0) :
    half (y₁ + y₂) = half y₁ + half y₂ := by
  revert h₁ h₂; revert y₁ y₂; decide

/-- `half (2 • y) = castHom (2∣4) y` — halving a doubled element is its mod-2 reduction. -/
theorem half_two_smul (y : ZMod 4) :
    half (2 * y) = (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) y := by
  revert y; decide

/-- The **pointwise lift defect**: `lift(a+b) − lift a − lift b = 2 · lift(a·b)` as ℤ/4 values, where
`(a·b)(σ) = a σ * b σ` over `ZMod 2`. A `decide` on the four cases of `(a σ, b σ) ∈ (ZMod 2)²`. -/
theorem lift_add_defect {X : TopCat} {n : ℕ} (a b : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    lift (a + b) σ = lift a σ + lift b σ + 2 * lift (fun τ => a τ * b τ) σ := by
  simp only [lift_apply, Pi.add_apply]
  have h : ∀ x y : ZMod 2,
      (((x + y).val : ZMod 4)) = (x.val : ZMod 4) + (y.val : ZMod 4) + 2 * ((x * y).val : ZMod 4) := by
    decide
  exact h (a σ) (b σ)

/-- The **Bockstein on cochains**: `Sq1cochain a := fun σ => half (δ₄(lift a) σ)`. -/
noncomputable def Sq1cochain {X : TopCat} {n : ℕ} (a : SingularCochain X n) : SingularCochain X (n + 1) :=
  fun σ => half (coboundary4 X n (lift a) σ)

@[simp] theorem Sq1cochain_apply {X : TopCat} {n : ℕ} (a : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    Sq1cochain a σ = half (coboundary4 X n (lift a) σ) := rfl

/-- **The cochain-level additivity defect of the Bockstein** (for cocycles `a, b`):
`Sq1cochain (a+b) = Sq1cochain a + Sq1cochain b + coboundary (a·b)`. The lift defect `lift_add_defect`
makes `δ₄(lift(a+b)) = δ₄(lift a) + δ₄(lift b) + 2·δ₄(lift(a·b))`; for *cocycles* the first two summands
are even (`castHom_coboundary4_lift` gives `δ₂ a = 0`, `δ₂ b = 0`), so `half` is additive on them, and
`half(2·δ₄(lift(a·b))) = δ₂(a·b)`. The `coboundary (a·b)` term is a coboundary, so it dies on cohomology. -/
theorem Sq1cochain_add {X : TopCat} {n : ℕ} (a b : SingularCochain X n)
    (ha : coboundaryₗ X n a = 0) (hb : coboundaryₗ X n b = 0) :
    Sq1cochain (a + b)
      = Sq1cochain a + Sq1cochain b + coboundary X n (fun τ => a τ * b τ) := by
  funext σ
  simp only [Sq1cochain_apply, Pi.add_apply]
  -- δ₄(lift(a+b)) = δ₄(lift a) + δ₄(lift b) + 2·δ₄(lift(a·b))  pointwise at σ
  have hsplit : coboundary4 X n (lift (a + b)) σ
      = coboundary4 X n (lift a) σ + coboundary4 X n (lift b) σ
        + 2 * coboundary4 X n (lift (fun τ => a τ * b τ)) σ := by
    simp only [coboundary4_apply]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lift_add_defect]
    ring
  rw [hsplit]
  -- the first two summands are even because a, b are cocycles
  have ha' : coboundary X n a σ = 0 := congrFun ha σ
  have hb' : coboundary X n b σ = 0 := congrFun hb σ
  have he1 : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (coboundary4 X n (lift a) σ) = 0 := by
    rw [castHom_coboundary4_lift, ha']
  have he2 : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (coboundary4 X n (lift b) σ) = 0 := by
    rw [castHom_coboundary4_lift, hb']
  have he3 : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
      (2 * coboundary4 X n (lift (fun τ => a τ * b τ)) σ) = 0 := by
    rw [map_mul]; rw [show (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) 2 = 0 from by decide]
    rw [zero_mul]
  -- half is additive over the three even summands
  rw [half_add_of_even _ _ (by rw [map_add, he1, he2, add_zero]) he3,
    half_add_of_even _ _ he1 he2]
  -- the doubled term: half(2·δ₄(lift(a·b))) = δ₂(a·b)
  rw [half_two_smul, castHom_coboundary4_lift]

/-- `half` is additive over a finite **sum of even elements**: if every `y i` reduces to `0` under
`castHom (2∣4)` then `half (∑ i, y i) = ∑ i, half (y i)`. Iterated `half_add_of_even`. The key fact
turning the unsigned `δ₄²` sum into a sum of `half`-values. -/
theorem half_sum_of_even {ι : Type*} (s : Finset ι) (y : ι → ZMod 4)
    (hy : ∀ i ∈ s, (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (y i) = 0) :
    half (∑ i ∈ s, y i) = ∑ i ∈ s, half (y i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [half]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hya : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (y a) = 0 :=
      hy a (Finset.mem_insert_self a s)
    have hyrest : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (∑ i ∈ s, y i) = 0 := by
      rw [map_sum]; apply Finset.sum_eq_zero
      intro i hi; exact hy i (Finset.mem_insert_of_mem hi)
    rw [half_add_of_even _ _ hya hyrest, ih (fun i hi => hy i (Finset.mem_insert_of_mem hi))]

/-- For an **even** `y : ZMod 4`, the sign is absorbed: `(-1)^k * y = y` (because `-2 = 2` in `ZMod 4`,
so negation fixes the even subgroup `{0,2}`). -/
theorem neg_one_pow_mul_even (k : ℕ) (y : ZMod 4)
    (hy : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) y = 0) :
    (-1 : ZMod 4) ^ k * y = y := by
  have hneg : (-1 : ZMod 4) * y = y := by revert hy; revert y; decide
  rcases Nat.even_or_odd k with hk | hk
  · rw [Even.neg_one_pow hk, one_mul]
  · rw [Odd.neg_one_pow hk, hneg]

/-- **`Sq1cochain a` is a `ℤ/2`-cocycle** for a cocycle `a`. From `δ₄²(lift a) = 0`: every summand
`δ₄(lift a)(∂ᵢσ)` is even (cocycle ⟹ `castHom = δ₂ a = 0`), so the signs collapse and the *unsigned*
sum `∑ᵢ δ₄(lift a)(∂ᵢσ) = 0`; halving (additive on evens) gives `∑ᵢ half(...) = 0`, i.e. `δ₂(Sq1cochain a) = 0`. -/
theorem Sq1cochain_cocycle {X : TopCat} {n : ℕ} (a : SingularCochain X n)
    (ha : coboundaryₗ X n a = 0) :
    coboundaryₗ X (n + 1) (Sq1cochain a) = 0 := by
  funext σ
  show coboundary X (n + 1) (Sq1cochain a) σ = 0
  rw [coboundary_apply]
  simp only [Sq1cochain_apply]
  -- each δ₄(lift a)(∂ᵢσ) is even
  have heven : ∀ i : Fin (n + 1 + 2),
      (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (coboundary4 X n (lift a) (face i σ)) = 0 := by
    intro i
    rw [castHom_coboundary4_lift]
    exact congrFun ha (face i σ)
  -- the unsigned sum equals half of the unsigned ZMod 4 sum, which the δ₄² identity forces to 0
  rw [← half_sum_of_even Finset.univ _ (fun i _ => heven i)]
  -- ∑ᵢ δ₄(lift a)(∂ᵢσ) = ∑ᵢ (-1)ⁱ δ₄(lift a)(∂ᵢσ) = (δ₄² lift a)(σ) = 0
  have hsigned : (∑ i : Fin (n + 1 + 2), coboundary4 X n (lift a) (face i σ))
      = coboundary4 X (n + 1) (coboundary4 X n (lift a)) σ := by
    rw [coboundary4_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_one_pow_mul_even _ _ (heven i)]
  rw [hsigned, coboundary4_comp_coboundary4]
  show half (0 : ZMod 4) = 0
  exact half_zero

/-! ### §4.1 Descent to cohomology

`Sq1cochain` carries cocycles to cocycles (`Sq1cochain_cocycle`) and — the well-definedness leg —
coboundaries to coboundaries (`Sq1cochain_coboundary`), so `[a] ↦ [Sq1cochain a]` is a well-defined map
`Hⁿ → Hⁿ⁺¹`. It is additive (the `coboundary (a·b)` defect of `Sq1cochain_add` dies on cohomology) and
`ℤ/2`-linear (scalars are `{0,1}`). -/

/-- The **even halving section**: for an *even* `y : ZMod 4` (`castHom (2∣4) y = 0`),
`2 * ((half y).val : ZMod 4) = y`. The pointwise inverse to doubling on the even subgroup `{0,2}`. -/
theorem two_mul_half_val_of_even (y : ZMod 4)
    (hy : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) y = 0) :
    2 * (((half y).val : ℕ) : ZMod 4) = y := by
  revert hy; revert y; decide

/-- `castHom (2∣4)` commutes with the (mod-2, plain) coboundary on the cochain `castHom ∘ g`:
`castHom (δ₄ g σ) = coboundary (castHom ∘ g) σ`. The signs collapse mod 2. -/
theorem castHom_coboundary4 {X : TopCat} {n : ℕ} (g : Cochain4 X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (coboundary4 X n g σ)
      = coboundary X n (fun τ => (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (g τ)) σ := by
  rw [coboundary4_apply, coboundary_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_neg, map_one]
  rw [show ((-1 : ZMod 2)) = 1 from by decide, one_pow, one_mul]

/-- **Bockstein of a coboundary is a coboundary** (well-definedness leg): for `b : Cⁿ` the class
`Sq1cochain (δ b)` lies in `im δ`. Both `lift(δb)` and `δ₄(lift b)` reduce mod 2 to `δb`, so their
difference is even: `lift(δb) − δ₄(lift b) = 2·g` for the explicit even-defect cochain
`g σ := ((half (lift(δb)σ − δ₄(lift b)σ)).val : ZMod 4)`. Then `δ₄(lift(δb)) = δ₄(δ₄(lift b)) + 2·δ₄ g =
2·δ₄ g` (by `δ₄² = 0`), so `Sq1cochain(δb) = half(2·δ₄ g) = castHom(δ₄ g) = δ₂(castHom ∘ g)` — a coboundary. -/
theorem Sq1cochain_coboundary {X : TopCat} {n : ℕ} (b : SingularCochain X n) :
    Sq1cochain (coboundaryₗ X n b) ∈ LinearMap.range (coboundaryₗ X (n + 1)) := by
  set d : SingularCochain X (n + 1) := coboundaryₗ X n b with hd
  -- the even defect g : Cochain4 X (n+1)
  set g : Cochain4 X (n + 1) :=
    fun σ => ((half (lift d σ - coboundary4 X n (lift b) σ)).val : ZMod 4) with hg
  -- defect identity: lift d − δ₄(lift b) = 2 • g, because both reduce mod 2 to d
  have hdefect : ∀ σ, lift d σ - coboundary4 X n (lift b) σ = 2 * g σ := by
    intro σ
    have heven : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
        (lift d σ - coboundary4 X n (lift b) σ) = 0 := by
      rw [map_sub, castHom_coboundary4_lift]
      rw [show (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (lift d σ) = d σ from castHom_lift d σ]
      rw [hd]; show d σ - coboundary X n b σ = 0
      rw [hd]; show coboundary X n b σ - coboundary X n b σ = 0; ring
    rw [hg]; rw [two_mul_half_val_of_even _ heven]
  -- δ₄(lift d) = 2 · δ₄ g  pointwise
  have hcob : ∀ σ, coboundary4 X (n + 1) (lift d) σ = 2 * coboundary4 X (n + 1) g σ := by
    intro σ
    have hsub : lift d = coboundary4 X n (lift b) + fun σ => 2 * g σ := by
      funext σ; rw [Pi.add_apply]; rw [← hdefect σ]; ring
    rw [hsub, coboundary4_apply]
    simp only [Pi.add_apply]
    have hsplit : coboundary4 X (n + 1) (coboundary4 X n (lift b)) σ
        + ∑ i : Fin (n + 1 + 2), (-1 : ZMod 4) ^ (i : ℕ) * (2 * g (face i σ))
        = ∑ i : Fin (n + 1 + 2), (-1 : ZMod 4) ^ (i : ℕ) *
            (coboundary4 X n (lift b) (face i σ) + 2 * g (face i σ)) := by
      rw [coboundary4_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [← hsplit, coboundary4_comp_coboundary4 X n (lift b)]
    show (0 : ZMod 4) + _ = _
    rw [zero_add, coboundary4_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  -- Sq1cochain d = δ₂(castHom ∘ g) : a coboundary
  refine ⟨fun τ => (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (g τ), ?_⟩
  funext σ
  show coboundary X (n + 1) (fun τ => (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (g τ)) σ
      = Sq1cochain d σ
  rw [← castHom_coboundary4]
  rw [Sq1cochain_apply, hcob, half_two_smul]

/-- **Key descent identity**: for cocycles `a, a'` with `a - a'` a coboundary, `Sq1cochain a` and
`Sq1cochain a'` differ by a coboundary. Combines `Sq1cochain_add` (additivity defect `= coboundary(·)`)
with `Sq1cochain_coboundary` (Bockstein of the coboundary `a - a'` is itself a coboundary). -/
theorem Sq1cochain_sub_mem_range {X : TopCat} {m : ℕ} (a a' : SingularCochain X (m + 1))
    (_ha : coboundaryₗ X (m + 1) a = 0) (ha' : coboundaryₗ X (m + 1) a' = 0)
    (hc : a - a' ∈ LinearMap.range (coboundaryₗ X m)) :
    Sq1cochain a - Sq1cochain a' ∈ LinearMap.range (coboundaryₗ X (m + 1)) := by
  obtain ⟨b, hb⟩ := hc
  -- c := δ b is a coboundary cocycle and a = a' + c
  set c : SingularCochain X (m + 1) := coboundaryₗ X m b with hc_def
  have hcc : coboundaryₗ X (m + 1) c = 0 := by
    rw [hc_def]; exact congrFun (by funext g; exact coboundary_comp_coboundary X m g) b
  have hac : a = a' + c := by rw [hb]; abel
  rw [hac, Sq1cochain_add a' c ha' hcc]
  -- Sq1cochain c is a coboundary; coboundary(a'·c) is a coboundary; the rest cancels
  have h1 : Sq1cochain c ∈ LinearMap.range (coboundaryₗ X (m + 1)) := by
    rw [hc_def]; exact Sq1cochain_coboundary b
  obtain ⟨e1, he1⟩ := h1
  refine ⟨e1 + (fun τ => a' τ * c τ), ?_⟩
  rw [map_add, he1]
  show _ = (Sq1cochain a' + Sq1cochain c + coboundary X (m + 1) (fun τ => a' τ * c τ)) - Sq1cochain a'
  rw [show coboundaryₗ X (m + 1) (fun τ => a' τ * c τ) = coboundary X (m + 1) (fun τ => a' τ * c τ) from rfl]
  abel

/-- The underlying set-function of the Bockstein on cohomology: `[a] ↦ [Sq1cochain a]`. Well-defined by
`Sq1cochain_cocycle` (lands in cocycles) and `Sq1cochain_sub_mem_range` (kills the difference of
cohomologous cocycles). Defined at the successor degree `m+1` (the only degree the quotient relation
exposes a coboundary representative). -/
noncomputable def Sq1fun {X : TopCat} {m : ℕ} (x : Cohomology X (m + 1)) : Cohomology X (m + 1 + 1) := by
  refine Quotient.liftOn' x
    (fun a => Submodule.Quotient.mk
      (⟨Sq1cochain a.1, Sq1cochain_cocycle a.1 a.2⟩ : LinearMap.ker (coboundaryₗ X (m + 1 + 1)))) ?_
  rintro a a' hrel
  rw [Submodule.quotientRel_def] at hrel
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub] at hrel
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  -- a.1 - a'.1 ∈ coboundaryRange (m+1) = range (coboundaryₗ X m)
  exact Sq1cochain_sub_mem_range a.1 a'.1 a.2 a'.2 hrel

@[simp] theorem Sq1fun_mk {X : TopCat} {m : ℕ} (a : LinearMap.ker (coboundaryₗ X (m + 1))) :
    Sq1fun (Submodule.Quotient.mk a)
      = Submodule.Quotient.mk
        (⟨Sq1cochain a.1, Sq1cochain_cocycle a.1 a.2⟩ : LinearMap.ker (coboundaryₗ X (m + 1 + 1))) :=
  rfl

/-- `Sq1fun` is **additive**: the `coboundary (a·b)` additivity defect of `Sq1cochain_add` is a coboundary,
hence vanishes in `Hⁿ⁺¹`. -/
theorem Sq1fun_add {X : TopCat} {m : ℕ} (x y : Cohomology X (m + 1)) :
    Sq1fun (x + y) = Sq1fun x + Sq1fun y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  -- `mk a + mk b = mk (a + b)` holds by `rfl` (the quotient `+`), so `show` reassociates by defeq
  -- (`rw` can't keyed-match the `+` across the `Cohomology` def-wrap).
  show Sq1fun (Submodule.Quotient.mk (a + b))
      = Sq1fun (Submodule.Quotient.mk a) + Sq1fun (Submodule.Quotient.mk b)
  rw [Sq1fun_mk, Sq1fun_mk, Sq1fun_mk]
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
  -- `erw` (default transparency) sees through the `Cohomology` def-wrap on the quotient `+`
  -- where `rw` (reducible) cannot combine `mk _ + mk _` into `mk (_ + _)`.
  erw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub, AddMemClass.coe_add]
  -- Sq1cochain (a+b) - (Sq1cochain a + Sq1cochain b) = coboundary (a·b) ∈ range δ
  rw [Sq1cochain_add a.1 b.1 a.2 b.2]
  refine ⟨fun τ => a.1 τ * b.1 τ, ?_⟩
  show coboundary X (m + 1) (fun τ => a.1 τ * b.1 τ) = _
  abel

/-- `Sq1cochain 0 = 0` at the cochain level (`lift 0 = 0`, so `δ₄(lift 0) = 0`, and `half 0 = 0`). -/
theorem Sq1cochain_zero {X : TopCat} {m : ℕ} :
    Sq1cochain (0 : SingularCochain X (m + 1)) = 0 := by
  funext σ
  simp only [Sq1cochain_apply]
  rw [show lift (0 : SingularCochain X (m + 1)) = 0 from by funext τ; simp [lift]]
  rw [show coboundary4 X (m + 1) (0 : Cochain4 X (m + 1)) = 0 from by funext τ; simp [coboundary4]]
  exact half_zero

/-- `Sq1fun 0 = 0` — the Bockstein of the zero class vanishes (`Sq1cochain 0 = 0`). The two
`(0 : Cohomology) = mk 0` rewrites are done in **term mode** (`(mk_zero _).symm`), which sees through the
`Cohomology` quotient-def by defeq where `rw [← mk_zero]` cannot. -/
theorem Sq1fun_zero {X : TopCat} {m : ℕ} : Sq1fun (0 : Cohomology X (m + 1)) = 0 := by
  rw [show (0 : Cohomology X (m + 1)) = Submodule.Quotient.mk
        (⟨(0 : SingularCochain X (m + 1)), by simp⟩ : LinearMap.ker (coboundaryₗ X (m + 1)))
        from (Submodule.Quotient.mk_zero _).symm]
  rw [Sq1fun_mk]
  rw [show (0 : Cohomology X (m + 1 + 1)) = Submodule.Quotient.mk
        (⟨(0 : SingularCochain X (m + 1 + 1)), by simp⟩ :
          LinearMap.ker (coboundaryₗ X (m + 1 + 1))) from (Submodule.Quotient.mk_zero _).symm]
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub, sub_zero]
  rw [Sq1cochain_zero]
  exact Submodule.zero_mem _

/-- `Sq1fun` is **`ℤ/2`-scalar-linear**: over `ZMod 2` the scalars are `{0,1}`, so `c • x` is `0`
(→ `Sq1fun_zero`) or `x`. `rcases (by decide : c = 0 ∨ c = 1)` substitutes the *literal* `0`/`1` (not the
`fin_cases` anonymous `⟨·,·⟩` form) so `zero_smul`/`one_smul` fire. -/
theorem Sq1fun_smul {X : TopCat} {m : ℕ} (c : ZMod 2) (x : Cohomology X (m + 1)) :
    Sq1fun (c • x) = c • Sq1fun x := by
  rcases (by decide +revert : c = 0 ∨ c = 1) with rfl | rfl
  · rw [zero_smul, zero_smul, Sq1fun_zero]
  · rw [one_smul, one_smul]

/-- **The mod-2 Bockstein `Sq¹ : Hⁿ⁺¹(X;ℤ/2) →ₗ[ZMod 2] Hⁿ⁺²(X;ℤ/2)`** — the genuine cohomology
operation, the connecting homomorphism of `0 → ℤ/2 →·² ℤ/4 → ℤ/2 → 0`. Concrete realisation of the
abstract `PoincareDualityWuFormula.PoincareDual4Lo.sq1₃` (at degree `n+1 = 3`). `ℤ/2`-linear by
`Sq1fun_add` / `Sq1fun_smul`. -/
noncomputable def Sq1 {X : TopCat} {n : ℕ} :
    Cohomology X (n + 1) →ₗ[ZMod 2] Cohomology X (n + 1 + 1) where
  toFun := Sq1fun
  map_add' := Sq1fun_add
  map_smul' := Sq1fun_smul

/-- The computation rule for `Sq¹` on a representative cocycle. -/
@[simp] theorem Sq1_apply {X : TopCat} {m : ℕ} (a : LinearMap.ker (coboundaryₗ X (m + 1))) :
    Sq1 (Submodule.Quotient.mk a)
      = Submodule.Quotient.mk
        (⟨Sq1cochain a.1, Sq1cochain_cocycle a.1 a.2⟩ : LinearMap.ker (coboundaryₗ X (m + 1 + 1))) :=
  rfl

/-! ### §4.2 The cross-check `Sq¹ = (·)∪(·)` on `H¹`

The classical degree-1 Wu identity `Sq¹ a = a ∪ a`, here **on the nose at the cochain level** for a
`1`-cocycle `a`. On a `2`-simplex `σ`, `Sq1cochain a σ = half((a∂₀σ).val − (a∂₁σ).val + (a∂₂σ).val)` and,
substituting the cocycle relation `a∂₁σ = a∂₀σ + a∂₂σ` (mod 2), this equals `a∂₂σ · a∂₀σ = cup a a σ`
(a `decide` on the four cases of `(a∂₀σ, a∂₂σ) ∈ (ZMod 2)²`). Hence `Sq¹[a] = [a∪a] = cupH [a] [a]`. -/

/-- **`Sq1cochain a = cup a a` on the nose** for a `1`-cocycle `a` (cochain-level degree-1 Wu identity).
The four-case `ZMod` identity `half(x − y + z) = z·x` under the cocycle substitution `y = x + z`. -/
theorem Sq1cochain_eq_cup_on_C1 {X : TopCat} (a : SingularCochain X 1)
    (ha : coboundaryₗ X 1 a = 0) :
    Sq1cochain a = cup a a := by
  funext σ
  -- cocycle relation at σ: a(face 1 σ) = a(face 0 σ) + a(face 2 σ)
  have hcoc : a (face 1 σ) = a (face 0 σ) + a (face 2 σ) := by
    have h : coboundary X 1 a σ = 0 := congrFun ha σ
    rw [coboundary_apply, Fin.sum_univ_three] at h
    rw [← sub_eq_zero, CharTwo.sub_eq_add, ← h]; ring
  rw [Sq1cochain_apply, coboundary4_apply, Fin.sum_univ_three]
  rw [cup_apply, frontFace_eq_face_two, backFace_eq_face_zero]
  simp only [lift_apply]
  -- signs: (-1)^0 = 1, (-1)^1 = -1, (-1)^2 = 1 in ZMod 4
  rw [show ((-1 : ZMod 4) ^ (0 : Fin 3).val) = 1 from by decide,
    show ((-1 : ZMod 4) ^ (1 : Fin 3).val) = -1 from by decide,
    show ((-1 : ZMod 4) ^ (2 : Fin 3).val) = 1 from by decide]
  -- substitute the cocycle relation and reduce the ZMod 4 / ZMod 2 identity by cases
  rw [hcoc]
  have key : ∀ x z : ZMod 2,
      half (1 * ((x).val : ZMod 4) + (-1) * (((x + z)).val : ZMod 4) + 1 * ((z).val : ZMod 4))
        = z * x := by decide
  exact key (a (face 0 σ)) (a (face 2 σ))

/-- **The Wu cross-check `Sq¹ x = x ∪ x` on `H¹`** — the degree-1 Steenrod identity `Sq¹ = (·)²`,
matching `PoincareDualityWuFormula.cupSquareₗ` (`= cupH x x`). The Bockstein realisation of the
project's `cupSquare`/`cupSquareHom`, now proved (not posited) for the genuine singular Bockstein. -/
theorem Sq1_on_H1 {X : TopCat} (x : Cohomology X 1) : Sq1 x = cupH x x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Sq1_apply, cupH_mk_mk]
  -- both sides are the class of cup a a (Sq1cochain a = cup a a on the nose)
  congr 1
  apply Subtype.ext
  show Sq1cochain a.1 = cup a.1 a.1
  exact Sq1cochain_eq_cup_on_C1 a.1 (LinearMap.mem_ker.mp a.2)

end SKEFTHawking.SingularBockstein
