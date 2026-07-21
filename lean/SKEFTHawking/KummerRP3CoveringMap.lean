import Mathlib
import SKEFTHawking.KummerRP3Covering

/-!
# The antipodal quotient map `S³ → ℝP³` is a covering map

Mirror of `RP4Covering` one dimension down, on the pinned `ℂ²`-carrier
(`KummerResolutionPiece.S3`, `RP3 = Quotient antipSetoid`): the antipodal `ℤˣ`-action
`u • (a, b) = (u·a, u·b)` is continuous, properly discontinuous (finite group) and free
(`IsCancelSMul`), so Mathlib's quotient-covering machinery makes the orbit map a covering map;
the bespoke `antipSetoid` is *equal* to the orbit setoid, so **`mkRP3` itself is a covering map**
(`rp3_isCoveringMap`) — the input to the integral simplex-lift transfer (`KummerRP3TransferInt`)
that drives `H_*(ℝP³; ℤ)` for the K7 seam.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (negS3_free)

namespace SKEFTHawking.KummerRP3CoveringMap

/-- The antipodal `ℤˣ`-action on `S³ ⊂ ℂ²`: `u • (a, b) = (u·a, u·b)` (complex scalar `±1`). -/
noncomputable instance : SMul ℤˣ S3 where
  smul u x := ⟨(((u : ℤ) : ℂ) * x.1.1, ((u : ℤ) : ℂ) * x.1.2), by
    have habs : |((u : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> norm_num
    simpa [norm_mul, habs] using x.2⟩

@[simp] theorem smul_fst (u : ℤˣ) (x : S3) : (u • x).1.1 = ((u : ℤ) : ℂ) * x.1.1 := rfl

@[simp] theorem smul_snd (u : ℤˣ) (x : S3) : (u • x).1.2 = ((u : ℤ) : ℂ) * x.1.2 := rfl

noncomputable instance : MulAction ℤˣ S3 where
  one_smul x := Subtype.ext (by apply Prod.ext <;> simp)
  mul_smul u v x := Subtype.ext (by
    apply Prod.ext <;> simp [Units.val_mul, mul_assoc])

instance : ContinuousConstSMul ℤˣ S3 :=
  ⟨fun _u => Continuous.subtype_mk
    ((continuous_const.mul (continuous_subtype_val.fst)).prodMk
      (continuous_const.mul (continuous_subtype_val.snd))) _⟩

/-- The antipodal action is properly discontinuous (`ℤˣ` is finite). -/
instance : ProperlyDiscontinuousSMul ℤˣ S3 :=
  ⟨fun _ _ => Set.toFinite _⟩

/-- **`(-1) • x = negS3 x`** — the `ℤˣ`-action's nontrivial element IS the pinned antipodal map. -/
theorem neg_one_smul_eq_negS3 (x : S3) : (-1 : ℤˣ) • x = negS3 x := by
  apply Subtype.ext
  apply Prod.ext <;> simp [negS3]

/-- **The antipodal action is cancellative/free** (`negS3` is fixed-point-free on the sphere). -/
instance : IsCancelSMul ℤˣ S3 where
  left_cancel' u x y h := by
    have h1 : (u⁻¹ * u) • x = (u⁻¹ * u) • y := by
      rw [mul_smul, mul_smul, h]
    simpa using h1
  right_cancel' u v x h := by
    rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or v with hv | hv <;>
      subst hu <;> subst hv
    · rfl
    · exfalso
      rw [one_smul, neg_one_smul_eq_negS3] at h
      exact negS3_free x h.symm
    · exfalso
      rw [one_smul, neg_one_smul_eq_negS3] at h
      exact negS3_free x h
    · rfl

/-- **The orbit setoid of the antipodal action equals the pinned `antipSetoid`** — the bespoke
antipodal relation of `KummerResolutionPiece` is exactly the `ℤˣ`-orbit relation. -/
theorem orbitRel_eq_antipSetoid : MulAction.orbitRel ℤˣ S3 = antipSetoid := by
  ext x y
  constructor
  · rintro ⟨u, rfl⟩
    rcases Int.units_eq_one_or u with hu | hu <;> subst hu
    · exact Or.inl (by simp)
    · refine Or.inr ?_
      change y = negS3 ((-1 : ℤˣ) • y)
      rw [neg_one_smul_eq_negS3, negS3_involutive]
  · rintro (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · refine ⟨-1, ?_⟩
      show (-1 : ℤˣ) • negS3 x = x
      rw [neg_one_smul_eq_negS3, negS3_involutive]

/-- **`mkRP3 : S³ → ℝP³` is a covering map** — the antipodal quotient by the free, properly
discontinuous `ℤˣ`-action, transported along `orbitRel_eq_antipSetoid`. The lifting input for
the integral Smith-sequence transfer of `H_*(ℝP³; ℤ)`. -/
theorem rp3_isCoveringMap : IsCoveringMap mkRP3 := by
  have h := (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := ℤˣ)
    (E := S3)).isCoveringMap
  rw [orbitRel_eq_antipSetoid] at h
  exact h

/-- **The fiber is the antipodal pair**: two points of `S³` with the same class in `ℝP³` are equal
or antipodal. -/
theorem fiber_pair {e y : S3} (h : mkRP3 e = mkRP3 y) : e = y ∨ e = negS3 y := by
  have h' : antipRel e y := Quotient.exact (s := antipSetoid) h
  rcases h' with h1 | h1
  · exact Or.inl h1.symm
  · rw [h1]
    exact Or.inr (negS3_involutive e).symm

end SKEFTHawking.KummerRP3CoveringMap
