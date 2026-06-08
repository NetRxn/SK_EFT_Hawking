/-
# Rank-4 Hasse–Minkowski: local isotropy of even unimodular forms

The weak [HM] hypothesis (`RokhlinFromHM.HasWeakIsotropicVectorHyp`) is discharged at rank ≥ 5
(`RokhlinHMDischarge.weakIsotropic_of_five_le`) and at ranks 1, 2, 3 (elementary / vacuous). The lone
remaining rank is **4**, the sub-frontier where local universality fails (anisotropic rank-4 forms exist
over each `ℚ_p`). For an *even unimodular* form the local inputs are nonetheless available:

* **odd `p`** — the form is `ℤ_p`-unimodular, so its mod-`p` reduction is a nondegenerate rank-4 form over
  `𝔽_p`, isotropic by Chevalley–Warning (`finite_field_form_isotropic`); the isotropic point is automatically
  *simple* (nondegeneracy ⟹ nonzero gradient), so a single-variable Hensel lift (`hensels_lemma`) produces a
  `ℚ_p`-isotropic vector. This file builds that input (`evenUnimodular_isotropic_odd_padic`).

The reusable engine is `mulVec_update_coord_quadratic`: varying one coordinate `j` of a vector turns the
quadratic form into a univariate quadratic `A j j · t² + 2·(A *ᵥ y) j · t + y ⬝ᵥ A *ᵥ y`, which is the
polynomial Hensel acts on.

Kernel-pure, no axioms.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.HasseMinkowskiLocal
import SKEFTHawking.PadicSquare
import SKEFTHawking.HilbertProductFormula

namespace SKEFTHawking

open scoped BigOperators
open Matrix

/-- **One-coordinate variation of a quadratic form is a univariate quadratic.** For a symmetric matrix
`A`, replacing coordinate `j` of `y` by `t` (where `y j = 0`) gives
`(y + t·e_j) ⬝ᵥ A *ᵥ (y + t·e_j) = A j j · t² + 2·(A *ᵥ y) j · t + y ⬝ᵥ A *ᵥ y`. The cross terms coincide
by symmetry of `A`. This is the polynomial Hensel's lemma acts on for the local lift. -/
theorem mulVec_update_coord_quadratic {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hsymm : A.transpose = A) (y : Fin n → R) (j : Fin n) (t : R) :
    (y + t • (Pi.single j 1 : Fin n → R)) ⬝ᵥ A *ᵥ (y + t • (Pi.single j 1 : Fin n → R))
      = A j j * t ^ 2 + 2 * (A *ᵥ y) j * t + y ⬝ᵥ A *ᵥ y := by
  have hsingle : A *ᵥ (Pi.single j 1 : Fin n → R) = fun i => A i j := by
    ext i; rw [mulVec_single]; simp
  have hyAe : y ⬝ᵥ A *ᵥ (Pi.single j 1 : Fin n → R) = (A *ᵥ y) j := by
    rw [hsingle]
    show ∑ i, y i * A i j = (A *ᵥ y) j
    rw [mulVec]
    show ∑ i, y i * A i j = ∑ i, A j i * y i
    refine Finset.sum_congr rfl fun i _ => ?_
    have hij : A i j = A j i := by
      have h := congrFun (congrFun hsymm j) i; rwa [Matrix.transpose_apply] at h
    rw [hij]; ring
  have heAe : (Pi.single j (1 : R)) ⬝ᵥ A *ᵥ Pi.single j (1 : R) = A j j := by
    rw [hsingle, single_dotProduct]; simp
  have heAy : (Pi.single j (1 : R)) ⬝ᵥ A *ᵥ y = (A *ᵥ y) j := by
    rw [single_dotProduct]; simp
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    mulVec_smul, dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct,
    hyAe, heAe, heAy]
  simp only [smul_eq_mul]
  ring

open Polynomial in
/-- **Odd-`p` local isotropy of a `ℤ_p`-unimodular form (rank ≥ 3).** A symmetric matrix over `ℤ_[p]`
(`p` odd) with unit determinant is isotropic over `ℤ_[p]` (hence `ℚ_[p]`). Its mod-`p` reduction is a
nondegenerate rank-≥3 form over `𝔽_p`, isotropic by Chevalley–Warning; the isotropic point is *simple*
(nondegeneracy ⟹ the gradient `Ā *ᵥ x̄` is nonzero), so a single-variable Hensel lift in the
gradient-nonzero coordinate produces an exact `ℤ_[p]` zero. -/
theorem isotropic_padicInt_of_unit_det {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ_[p]) (hsymm : A.transpose = A) (hdet : IsUnit A.det) :
    ∃ v : Fin n → ℤ_[p], v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = 0 := by
  classical
  set f : ℤ_[p] →+* ZMod p := PadicInt.toZMod with hf
  set Abar : Matrix (Fin n) (Fin n) (ZMod p) := A.map f with hAbar
  -- mod-p reduction is nondegenerate
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hdetbar : Abar.det ≠ 0 := by
    have hd : Abar.det = f A.det := by rw [hAbar]; exact (RingHom.map_det f A).symm
    rw [hd]; exact (hdet.map f).ne_zero
  -- the residue form is isotropic (Chevalley–Warning, rank ≥ 3)
  obtain ⟨xbar, hxbar0, hxbarz⟩ := finite_field_form_isotropic (K := ZMod p) hn Abar
  -- the isotropic point is simple: the gradient is nonzero
  have hgrad : Abar *ᵥ xbar ≠ 0 := by
    intro h
    exact hdetbar (Matrix.exists_mulVec_eq_zero_iff.mp ⟨xbar, hxbar0, h⟩)
  obtain ⟨j, hj⟩ : ∃ j, (Abar *ᵥ xbar) j ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hgrad (funext h)
  -- lift the residue solution to ℤ_[p]
  have hlift : ∀ i, ∃ X : ℤ_[p], f X = xbar i := fun i => ZMod.ringHom_surjective f (xbar i)
  choose x0 hx0 using hlift
  have hx0fun : (fun k => f (x0 k)) = xbar := funext hx0
  -- map-commutes for the matrix-vector product
  have hmapmv : ∀ (w : Fin n → ℤ_[p]) (i : Fin n),
      f ((A *ᵥ w) i) = (Abar *ᵥ (fun k => f (w k))) i := by
    intro w i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hAbar, Matrix.map_apply]
  -- zero out coordinate j
  set y : Fin n → ℤ_[p] := Function.update x0 j 0 with hy
  set a : ℤ_[p] := x0 j with ha
  have hrestore : x0 = y + a • (Pi.single j 1 : Fin n → ℤ_[p]) := by
    ext i; rcases eq_or_ne i j with rfl | hij
    · simp [hy, ha]
    · simp [hy, Function.update_of_ne hij, Pi.single_eq_of_ne hij]
  -- the Hensel polynomial
  set F : ℤ_[p][X] := C (A j j) * X ^ 2 + C (2 * (A *ᵥ y) j) * X + C (y ⬝ᵥ A *ᵥ y) with hF
  have hFe : ∀ x : ℤ_[p], (aeval x) F = A j j * x ^ 2 + 2 * (A *ᵥ y) j * x + y ⬝ᵥ A *ᵥ y := by
    intro x; simp [hF]
  have hFda : (aeval a) (derivative F) = 2 * A j j * a + 2 * (A *ᵥ y) j := by
    simp [hF, derivative_add, derivative_mul]; ring
  -- F at a evaluates to the full quadratic Q(x0)
  have hQx0 : (aeval a) F = x0 ⬝ᵥ A *ᵥ x0 := by
    rw [hFe]
    have h := mulVec_update_coord_quadratic A hsymm y j a
    rw [← hrestore] at h; rw [h]
  -- F'(a) = 2·(A *ᵥ x0) j
  have hgradx0 : 2 * A j j * a + 2 * (A *ᵥ y) j = 2 * (A *ᵥ x0) j := by
    have : (A *ᵥ x0) j = (A *ᵥ y) j + a * A j j := by
      rw [hrestore]
      simp [Matrix.mulVec_add, Matrix.mulVec_smul, mulVec_single]
    rw [this]; ring
  -- residue facts
  have hmod0 : f (x0 ⬝ᵥ A *ᵥ x0) = 0 := by
    have : f (x0 ⬝ᵥ A *ᵥ x0) = xbar ⬝ᵥ Abar *ᵥ xbar := by
      simp only [dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx0, hmapmv x0 i, hx0fun]
    rw [this, hxbarz]
  have h2 : f (2 : ℤ_[p]) ≠ 0 := by
    have he : f (2 : ℤ_[p]) = ((2 : ℕ) : ZMod p) := by
      rw [hf, show (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) by norm_num, map_natCast]
    rw [he, Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hdvd
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  have hderiv_ne : f ((aeval a) (derivative F)) ≠ 0 := by
    rw [hFda, hgradx0, map_mul, hmapmv x0 j, hx0fun]
    exact mul_ne_zero h2 hj
  -- Hensel lift
  have ha1 : ‖(aeval a) (derivative F)‖ = 1 := by
    rcases lt_or_eq_of_le (PadicInt.norm_le_one ((aeval a) (derivative F))) with h | h
    · exact absurd ((toZMod_eq_zero_iff_norm_lt_one _).mpr h) hderiv_ne
    · exact h
  have hnorm : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    rw [ha1, one_pow]
    rw [hQx0]
    exact (toZMod_eq_zero_iff_norm_lt_one _).mp hmod0
  obtain ⟨z, hz, _⟩ := hensels_lemma (F := F) (a := a) hnorm
  -- assemble the lifted isotropic vector
  refine ⟨y + z • (Pi.single j 1 : Fin n → ℤ_[p]), ?_, ?_⟩
  · -- nonzero
    intro hv0
    have hsupp : ∀ i, i ≠ j → xbar i = 0 := by
      intro i hij
      have hvi := congrFun hv0 i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero, add_zero,
        Pi.zero_apply, hy, Function.update_of_ne hij] at hvi
      rw [← hx0 i, hvi, map_zero]
    have hxbarj : xbar j ≠ 0 := by
      intro hjz
      refine hxbar0 (funext fun i => ?_)
      rcases eq_or_ne i j with rfl | h
      · exact hjz
      · exact hsupp i h
    have hgv : (Abar *ᵥ xbar) j = Abar j j * xbar j := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
      · intro b _ hb; rw [hsupp b hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hquad : Abar j j * xbar j ^ 2 = 0 := by
      have := hxbarz
      rw [dotProduct, Finset.sum_eq_single j] at this
      · rw [hgv] at this; rw [← this]; ring
      · intro b _ hb; rw [hsupp b hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hAbarjj : Abar j j = 0 := by
      rcases mul_eq_zero.mp hquad with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hxbarj
    rw [hgv, hAbarjj, zero_mul] at hj; exact hj rfl
  · -- isotropic
    have h := mulVec_update_coord_quadratic A hsymm y j z
    rw [h, ← hFe z]; exact hz

/-! ## p = 2 from reciprocity (the lone sub-frontier, square-discriminant case)

For a square-discriminant rank-4 form the local isotropy at a place `v` is governed by a *single* binary
Hilbert symbol `(α, β)_v` (`α = -ab`, `β = ac`) via the norm-form reduction
`quaternary_sqdisc_iso_iff_ternary` + the per-place symbol bridges. The product formula
`hilbertGlobalProd_eq_one` then forces the `p = 2` factor once all other places are `1` — so a
square-disc form isotropic at `ℝ` and every *odd* prime is automatically isotropic at `2`. -/

open HilbertSymbol in
/-- **Reciprocity completeness for the binary symbol.** If `(α,β)_∞ = 1` and `(α,β)_p = 1` for every odd
prime `p`, then `(α,β)_2 = 1` — the `p = 2` factor is pinned by the Hilbert product formula
`hilbertGlobalProd_eq_one` (every other factor being `1`). -/
theorem hilbertPrime_two_eq_one_of_real_odd {α β : ℤ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hreal : HilbertSymbol.hilbertReal (α : ℝ) (β : ℝ) = 1)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → HilbertSymbol.hilbertPrime p α β = 1) :
    HilbertSymbol.hilbertPrime 2 α β = 1 := by
  have hglob := hilbertGlobalProd_eq_one hα hβ
  rw [hilbertGlobalProd] at hglob
  have hfin : ∏ᶠ p : ℕ, HilbertSymbol.hilbertPrime p α β = HilbertSymbol.hilbertPrime 2 α β := by
    refine finprod_eq_single _ 2 (fun p hp2 => ?_)
    by_cases hpp : p.Prime
    · exact hodd p hpp hp2
    · exact hilbertPrime_of_not_prime hpp α β
  rw [hfin, hreal, one_mul] at hglob
  exact hglob

/-- **Square-discriminant quaternary Hasse–Minkowski, without the place `2`.** For nonzero integers with
`a·b·c·d = s²`, if `a x² + b y² − c z² − d w² = 0` is solvable over `ℝ` and over every *odd* `ℚ_p`, it is
solvable over `ℚ`. The `p = 2` local solvability — the lone gap in the shipped
`quaternary_sqdisc_solvable_of_local` — is supplied by reciprocity: each place's isotropy is the symbol
`(−ab, ac)_v = 1`, and `hilbertPrime_two_eq_one_of_real_odd` pins the `2`-factor from the others. -/
theorem quaternary_sqdisc_solvable_of_local_no_two {a b c d s : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hsq : a * b * c * d = s ^ 2)
    (hR : ∃ x y z w : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 - (c : ℝ) * z ^ 2 - (d : ℝ) * w ^ 2 = 0)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ x y z w : ℚ_[p],
      ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 - (c : ℚ_[p]) * z ^ 2 - (d : ℚ_[p]) * w ^ 2 = 0) :
    ∃ x y z w : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 - (c : ℚ) * z ^ 2 - (d : ℚ) * w ^ 2 = 0 := by
  set α : ℤ := -(a * b) with hαdef
  set β : ℤ := a * c with hβdef
  have hα : α ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha hb)
  have hβ : β ≠ 0 := mul_ne_zero ha hc
  -- real place: the symbol (α,β)_∞ = 1
  have hreal : HilbertSymbol.hilbertReal (α : ℝ) (β : ℝ) = 1 := by
    obtain ⟨X, Y, Z, hnzt, het⟩ :=
      (quaternary_sqdisc_iso_iff_ternary (a := (a : ℝ)) (b := (b : ℝ)) (c := (c : ℝ)) (d := (d : ℝ))
        (s := (s : ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
        (by exact_mod_cast hd) (by exact_mod_cast hsq)).mp hR
    have het' : Z ^ 2 = (α : ℝ) * X ^ 2 + (β : ℝ) * Y ^ 2 := by
      rw [het, hαdef, hβdef]; push_cast; ring
    rw [HilbertSymbol.hilbertReal_eq_one_iff (by exact_mod_cast hα) (by exact_mod_cast hβ)]
    refine ⟨X, Y, Z, ?_, het'⟩
    intro h
    rw [Prod.mk_eq_zero] at h
    obtain ⟨hX, hYZ⟩ := h
    rw [Prod.mk_eq_zero] at hYZ
    exact hnzt ⟨hX, hYZ.1, hYZ.2⟩
  -- odd primes: the symbol (α,β)_p = 1
  have hoddsym : ∀ p : ℕ, p.Prime → p ≠ 2 → HilbertSymbol.hilbertPrime p α β = 1 := by
    intro p hp hp2
    haveI := Fact.mk hp
    rw [HilbertSymbol.hilbertPrime_odd hp hp2, ← solvable_padic_iff_hilbertPadicInt_one hp2 hα hβ]
    obtain ⟨X, Y, Z, hnzt, het⟩ :=
      (quaternary_sqdisc_iso_iff_ternary (a := (a : ℚ_[p])) (b := (b : ℚ_[p])) (c := (c : ℚ_[p]))
        (d := (d : ℚ_[p])) (s := (s : ℚ_[p])) (by exact_mod_cast ha) (by exact_mod_cast hb)
        (by exact_mod_cast hc) (by exact_mod_cast hd) (by exact_mod_cast hsq)).mp (hodd p hp2)
    exact ⟨X, Y, Z, hnzt, by rw [het, hαdef, hβdef]; push_cast; ring⟩
  -- p = 2 from reciprocity
  have h2sym : HilbertSymbol.hilbert2Int α β = 1 := by
    rw [← HilbertSymbol.hilbertPrime_two]
    exact hilbertPrime_two_eq_one_of_real_odd hα hβ hreal hoddsym
  have h2loc : ∃ x y z w : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[2]) * x ^ 2 + (b : ℚ_[2]) * y ^ 2 - (c : ℚ_[2]) * z ^ 2 - (d : ℚ_[2]) * w ^ 2 = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨X, Y, Z, hnzt, het⟩ := (solvable_2adic_iff_hilbert2Int hα hβ).mpr h2sym
    refine (quaternary_sqdisc_iso_iff_ternary (a := (a : ℚ_[2])) (b := (b : ℚ_[2])) (c := (c : ℚ_[2]))
      (d := (d : ℚ_[2])) (s := (s : ℚ_[2])) (by exact_mod_cast ha) (by exact_mod_cast hb)
      (by exact_mod_cast hc) (by exact_mod_cast hd) (by exact_mod_cast hsq)).mpr ⟨X, Y, Z, hnzt, ?_⟩
    rw [het, hαdef, hβdef]; push_cast; ring
  -- combine all places and invoke the full square-disc Hasse–Minkowski
  have hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z w : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 - (c : ℚ_[p]) * z ^ 2 - (d : ℚ_[p]) * w ^ 2 = 0 := by
    intro p _
    by_cases hp2 : p = 2
    · subst hp2; exact h2loc
    · exact hodd p hp2
  have hQ := quaternary_sqdisc_solvable_of_local (a := (a : ℚ)) (b := (b : ℚ)) (c := (c : ℚ))
    (d := (d : ℚ)) (s := (s : ℚ)) (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
    (by exact_mod_cast hd) (by exact_mod_cast hsq) ?_ ?_
  · obtain ⟨x, y, z, w, hnz, he⟩ := hQ
    exact ⟨x, y, z, w, hnz, by push_cast at he ⊢; linear_combination he⟩
  · obtain ⟨x, y, z, w, hnz, he⟩ := hR
    exact ⟨x, y, z, w, hnz, by push_cast at he ⊢; linear_combination he⟩
  · intro p _
    obtain ⟨x, y, z, w, hnz, he⟩ := hloc p
    exact ⟨x, y, z, w, hnz, by push_cast at he ⊢; linear_combination he⟩

end SKEFTHawking
