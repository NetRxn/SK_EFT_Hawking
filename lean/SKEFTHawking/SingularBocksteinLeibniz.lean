import Mathlib
import SKEFTHawking.SingularBockstein

/-!
# Phase 5q.G (B-arc, M4-c1) — the signed `ℤ/4` cup and its Leibniz rule

The keystone of the Bockstein-derivation property: the Alexander–Whitney product over `ℤ/4`
satisfies the **signed Leibniz rule** `δ₄(u ⌣₄ v) = δ₄u ⌣₄ v + (-1)ᵖ u ⌣₄ δ₄v` (stated
cast-free at a fixed simplex, exactly as the mod-2 `coboundary_cup`). The combinatorial
face-splitting lemmas (`frontFace_face_of_le/gt`, `face_last_frontBig`, `face_zero_backSmall`)
are coefficient-independent and are reused verbatim; the two diagonal terms now cancel by
genuine sign-opposition `(-1)^{p+1} + (-1)^p = 0` instead of characteristic 2.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularBockstein

namespace SKEFTHawking.SingularBocksteinLeibniz

variable {X : TopCat} {p q : ℕ}

/-- The **`ℤ/4` Alexander–Whitney cup product** `(u ⌣₄ v)(σ) = u(frontₚσ) · v(back_qσ)`. -/
noncomputable def cup4 (u : Cochain4 X p) (v : Cochain4 X q) : Cochain4 X (p + q) :=
  fun σ => u (frontFace σ) * v (backFace σ)

@[simp] theorem cup4_apply (u : Cochain4 X p) (v : Cochain4 X q)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    cup4 u v σ = u (frontFace σ) * v (backFace σ) := rfl

/-- **The signed `ℤ/4` cup Leibniz rule**, cast-free at the simplex `τ`:
`δ₄(u ⌣₄ v)(τ) = δ₄u(front₊τ)·v(back₋τ) + (-1)ᵖ·u(front₋τ)·δ₄v(back₊τ)`. -/
theorem coboundary4_cup4 (u : Cochain4 X p) (v : Cochain4 X q)
    (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    coboundary4 X (p + q) (cup4 u v) τ
      = coboundary4 X p u (frontBig τ) * v (backBig τ)
        + (-1 : ZMod 4) ^ p * (u (frontSmall τ) * coboundary4 X q v (backSmall τ)) := by
  have h : p + 1 + (q + 1) = p + q + 2 := by omega
  have hsign : (-1 : ZMod 4) ^ (p + 1) + (-1 : ZMod 4) ^ p = 0 := by
    rw [pow_succ]
    ring
  -- the canonical middle form
  set S₁ := ∑ j : Fin (p + 1), (-1 : ZMod 4) ^ (j : ℕ)
    * (u (face j.castSucc (frontBig τ)) * v (backBig τ)) with hS₁
  set S₂ := ∑ k : Fin (q + 1), (-1 : ZMod 4) ^ (p + 1 + (k : ℕ))
    * (u (frontSmall τ) * v (face k.succ (backSmall τ))) with hS₂
  have hR : coboundary4 X p u (frontBig τ) * v (backBig τ)
        + (-1 : ZMod 4) ^ p * (u (frontSmall τ) * coboundary4 X q v (backSmall τ))
      = S₁ + S₂ := by
    rw [coboundary4_apply, coboundary4_apply,
      Fin.sum_univ_castSucc
        (f := fun i : Fin (p + 2) => (-1 : ZMod 4) ^ (i : ℕ) * u (face i (frontBig τ))),
      Fin.sum_univ_succ
        (f := fun k : Fin (q + 2) => (-1 : ZMod 4) ^ (k : ℕ) * v (face k (backSmall τ))),
      face_last_frontBig, face_zero_backSmall]
    have e1 : (∑ i : Fin (p + 1),
          (-1 : ZMod 4) ^ ((i.castSucc : Fin (p + 2)) : ℕ) * u (face i.castSucc (frontBig τ))
          + (-1 : ZMod 4) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) * u (frontSmall τ))
          * v (backBig τ)
        = S₁ + (-1 : ZMod 4) ^ (p + 1) * (u (frontSmall τ) * v (backBig τ)) := by
      rw [add_mul, Finset.sum_mul, hS₁]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Fin.val_castSucc, mul_assoc]
      · rw [Fin.val_last, mul_assoc]
    have e2 : (-1 : ZMod 4) ^ p * (u (frontSmall τ)
          * ((-1 : ZMod 4) ^ ((0 : Fin (q + 2)) : ℕ) * v (backBig τ)
            + ∑ k : Fin (q + 1),
              (-1 : ZMod 4) ^ ((k.succ : Fin (q + 2)) : ℕ) * v (face k.succ (backSmall τ))))
        = (-1 : ZMod 4) ^ p * (u (frontSmall τ) * v (backBig τ)) + S₂ := by
      rw [mul_add, Finset.mul_sum, mul_add, Finset.mul_sum, hS₂]
      congr 1
      · rw [Fin.val_zero, pow_zero, one_mul]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [Fin.val_succ, pow_add, pow_add, pow_one]
        ring
    rw [e1, e2]
    have hcanc : (-1 : ZMod 4) ^ (p + 1) * (u (frontSmall τ) * v (backBig τ))
        + (-1 : ZMod 4) ^ p * (u (frontSmall τ) * v (backBig τ)) = 0 := by
      rw [← add_mul, hsign, zero_mul]
    linear_combination hcanc
  have hL : coboundary4 X (p + q) (cup4 u v) τ = S₁ + S₂ := by
    rw [coboundary4_apply]
    simp only [cup4_apply]
    rw [← Equiv.sum_comp (finCongr h)
      (fun i => (-1 : ZMod 4) ^ (i : ℕ) * (u (frontFace (face i τ)) * v (backFace (face i τ)))),
      Fin.sum_univ_add, hS₁, hS₂]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hle : (finCongr h (Fin.castAdd (q + 1) j)).val ≤ p := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd]
        omega
      have hval : ((finCongr h (Fin.castAdd (q + 1) j)) : ℕ) = (j : ℕ) := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd]
      have hidx : (⟨(finCongr h (Fin.castAdd (q + 1) j)).val, by omega⟩ : Fin (p + 2))
          = j.castSucc := by
        apply Fin.ext
        simp only [Fin.val_castSucc, finCongr_apply, Fin.val_cast, Fin.val_castAdd]
      rw [frontFace_face_of_le τ _ hle, backFace_face_of_le τ _ hle, hidx, hval]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hgt : p < (finCongr h (Fin.natAdd (p + 1) k)).val := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]
        omega
      have hval : ((finCongr h (Fin.natAdd (p + 1) k)) : ℕ) = p + 1 + (k : ℕ) := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]
      have hidx : (⟨(finCongr h (Fin.natAdd (p + 1) k)).val - p,
          by have := k.isLt; omega⟩ : Fin (q + 2)) = k.succ := by
        apply Fin.ext
        simp only [Fin.val_succ, finCongr_apply, Fin.val_cast, Fin.val_natAdd]
        omega
      rw [frontFace_face_of_gt τ _ hgt, backFace_face_of_gt τ _ hgt, hidx, hval]
  rw [hL, hR]

/-! ## §2. The Bockstein is a derivation (on cocycles, at the cochain level) -/

/-- **The `{0,1}`-lift is multiplicative**: `lift(a ⌣ b) = lift a ⌣₄ lift b` on the nose. -/
theorem lift_cup {X : TopCat} (a : SingularCochain X p) (b : SingularCochain X q) :
    lift (cup a b) = cup4 (lift a) (lift b) := by
  funext σ
  simp only [lift_apply, cup_apply, cup4_apply]
  have h : ∀ x y : ZMod 2,
      (((x * y).val : ℕ) : ZMod 4) = ((x.val : ℕ) : ZMod 4) * ((y.val : ℕ) : ZMod 4) := by
    decide
  exact h _ _

/-- `half (e · t̂) = half e · t` for even `e` and a `{0,1}`-lift `t̂`. -/
theorem half_mul_val : ∀ (e : ZMod 4) (t : ZMod 2),
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) e = 0 →
    half (e * ((t.val : ℕ) : ZMod 4)) = half e * t := by
  decide

/-- `half (t̂ · e) = t · half e` for even `e` and a `{0,1}`-lift `t̂`. -/
theorem half_val_mul : ∀ (t : ZMod 2) (e : ZMod 4),
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) e = 0 →
    half (((t.val : ℕ) : ZMod 4) * e) = t * half e := by
  decide

/-- The sign is invisible to `half` on even elements: `half((-1)ᵖ · e) = half e`. -/
theorem half_neg_one_pow_mul (p : ℕ) : ∀ (e : ZMod 4),
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) e = 0 →
    half ((-1 : ZMod 4) ^ p * e) = half e := by
  have hp : (-1 : ZMod 4) ^ p = 1 ∨ (-1 : ZMod 4) ^ p = 3 := by
    rcases Nat.even_or_odd p with h | h
    · left
      exact h.neg_one_pow
    · right
      rw [h.neg_one_pow]
      decide
  rcases hp with h | h <;> rw [h] <;> decide

/-- **The Bockstein–Leibniz rule** (cochain level, value form, for cocycles):
`Sq¹(a ⌣ b)(τ) = Sq¹a(front₊τ)·b(back₋τ) + a(front₋τ)·Sq¹b(back₊τ)`. The signed `ℤ/4`
Leibniz (§1) + lift-multiplicativity + the half-arithmetic on even elements. -/
theorem Sq1cochain_cup {X : TopCat}
    (a : SingularCochain X p) (ha : coboundary X p a = 0)
    (b : SingularCochain X q) (hb : coboundary X q b = 0)
    (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    Sq1cochain (cup a b) τ
      = Sq1cochain a (frontBig τ) * b (backBig τ)
        + a (frontSmall τ) * Sq1cochain b (backSmall τ) := by
  rw [Sq1cochain_apply, lift_cup, coboundary4_cup4]
  have hev_a : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
      (coboundary4 X p (lift a) (frontBig τ)) = 0 := by
    rw [castHom_coboundary4_lift, ha]
    rfl
  have hev_b : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
      (coboundary4 X q (lift b) (backSmall τ)) = 0 := by
    rw [castHom_coboundary4_lift, hb]
    rfl
  have hev₁ : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
      (coboundary4 X p (lift a) (frontBig τ) * lift b (backBig τ)) = 0 := by
    rw [map_mul, hev_a, zero_mul]
  have hev₂ : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
      ((-1 : ZMod 4) ^ p * (lift a (frontSmall τ)
        * coboundary4 X q (lift b) (backSmall τ))) = 0 := by
    rw [map_mul, map_mul, hev_b, mul_zero, mul_zero]
  rw [half_add_of_even _ _ hev₁ hev₂,
    half_neg_one_pow_mul p _ (by rw [map_mul, hev_b, mul_zero])]
  simp only [lift_apply]
  rw [half_mul_val _ _ hev_a, half_val_mul _ _ hev_b]
  rfl

end SKEFTHawking.SingularBocksteinLeibniz
