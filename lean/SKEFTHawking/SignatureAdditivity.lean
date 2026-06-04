/-
Phase 5q.B (research-grade, zero-axiom): additivity of the signature over orthogonal direct sums.

The classification route to van der Blij's `8 ∣ σ` reduces an even unimodular form to the generators
`E₈, -E₈, H` and concludes `σ = 8(a-b)` from **additivity of the signature over orthogonal direct
sums**. Mathlib has the direct-sum quadratic form `QuadraticMap.prod` and `sigPos`/`sigNeg` (Sylvester
inertia indices) but **no additivity of `sigPos` over `prod`** — this module supplies it.

Strategy (kernel-pure, no axiom): the ≥ direction combines maximal positive-definite subspaces
(`V₁.prod V₂` is positive-definite of dimension `sigPos Q₁ + sigPos Q₂`); applying it to `-Qᵢ` gives the
matching `sigNeg` inequality. The reverse inequalities (hence full additivity) come from the inertia
dimension identity `sigPos + sigNeg + dim(radical) = dim` (next sub-wave); for the *nondegenerate*
forms that arise from unimodular lattices the radical vanishes and additivity is immediate.

All proofs kernel-pure (`propext`/`Classical.choice`/`Quot.sound`); no `native_decide`, no axiom.
-/

import Mathlib

namespace SKEFTHawking

open QuadraticMap

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [Module ℝ M₁] [Module ℝ M₂]
  [FiniteDimensional ℝ M₁] [FiniteDimensional ℝ M₂]

/-- The product submodule `V₁.prod V₂ ⊆ M₁ × M₂` is linearly isomorphic to `V₁ × V₂`. -/
def prodSubEquiv (V₁ : Submodule ℝ M₁) (V₂ : Submodule ℝ M₂) :
    ↥(V₁.prod V₂) ≃ₗ[ℝ] ↥V₁ × ↥V₂ where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

/-- Finrank of a product submodule is the sum of the finranks. -/
theorem finrank_prodSub (V₁ : Submodule ℝ M₁) (V₂ : Submodule ℝ M₂) :
    Module.finrank ℝ (V₁.prod V₂) = Module.finrank ℝ V₁ + Module.finrank ℝ V₂ := by
  rw [(prodSubEquiv V₁ V₂).finrank_eq, Module.finrank_prod]

/-- **Positive-inertia superadditivity:** `sigPos Q₁ + sigPos Q₂ ≤ sigPos (Q₁.prod Q₂)`. A maximal
positive-definite subspace `V₁` of `Q₁` and `V₂` of `Q₂` give a positive-definite subspace `V₁.prod V₂`
of `Q₁.prod Q₂` of dimension `sigPos Q₁ + sigPos Q₂`. -/
theorem le_sigPos_prod (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂) :
    sigPos Q₁ + sigPos Q₂ ≤ sigPos (Q₁.prod Q₂) := by
  obtain ⟨V₁, hV₁, hp₁⟩ := exists_finrank_eq_sigPos_and_posDef Q₁
  obtain ⟨V₂, hV₂, hp₂⟩ := exists_finrank_eq_sigPos_and_posDef Q₂
  have hpos : ((Q₁.prod Q₂).restrict (V₁.prod V₂)).PosDef := by
    intro x hx
    have hmem := Submodule.mem_prod.mp x.2
    rw [QuadraticMap.restrict_apply, QuadraticMap.prod_apply]
    have ha : (0 : ℝ) ≤ Q₁ x.1.1 := by
      rcases eq_or_ne x.1.1 0 with h | h
      · rw [h]; simp
      · have := hp₁ ⟨x.1.1, hmem.1⟩ (by simpa [Subtype.ext_iff] using h)
        rw [QuadraticMap.restrict_apply] at this; exact le_of_lt this
    have hb : (0 : ℝ) ≤ Q₂ x.1.2 := by
      rcases eq_or_ne x.1.2 0 with h | h
      · rw [h]; simp
      · have := hp₂ ⟨x.1.2, hmem.2⟩ (by simpa [Subtype.ext_iff] using h)
        rw [QuadraticMap.restrict_apply] at this; exact le_of_lt this
    have hne : x.1.1 ≠ 0 ∨ x.1.2 ≠ 0 := by
      have hx1 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
      rw [Ne, Prod.ext_iff, not_and_or] at hx1; exact hx1
    rcases hne with h | h
    · have hpa := hp₁ ⟨x.1.1, hmem.1⟩ (by simpa [Subtype.ext_iff] using h)
      rw [QuadraticMap.restrict_apply] at hpa; linarith
    · have hpb := hp₂ ⟨x.1.2, hmem.2⟩ (by simpa [Subtype.ext_iff] using h)
      rw [QuadraticMap.restrict_apply] at hpb; linarith
  have := le_sigPos_of_posDef (Q₁.prod Q₂) hpos
  rwa [finrank_prodSub, hV₁, hV₂] at this

/-- The direct sum of negated forms is the negation of the direct sum. -/
theorem neg_prod (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂) :
    (-Q₁).prod (-Q₂) = -(Q₁.prod Q₂) := by
  ext x; simp [QuadraticMap.prod_apply]; ring

/-- **Negative-inertia superadditivity:** `sigNeg Q₁ + sigNeg Q₂ ≤ sigNeg (Q₁.prod Q₂)` (apply
`le_sigPos_prod` to the negated forms). -/
theorem le_sigNeg_prod (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂) :
    sigNeg Q₁ + sigNeg Q₂ ≤ sigNeg (Q₁.prod Q₂) := by
  have h := le_sigPos_prod (-Q₁) (-Q₂)
  rwa [neg_prod] at h

/-- **The radical of a direct sum of nondegenerate forms vanishes.** If `Q₁` and `Q₂` are
nondegenerate (zero radical), so is `Q₁.prod Q₂`. (A radical vector `(a,b)` forces, via the
product polar `polar(prod)(a,b)(c,d) = polar Q₁ a c + polar Q₂ b d` evaluated at `(c,0)` and `(0,d)`,
that `a ∈ radical Q₁` and `b ∈ radical Q₂`, using `polar Q a a = 2 • Q a` to recover `Q a = 0`.) -/
theorem radical_prod_eq_bot (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
    (h₁ : Q₁.radical = ⊥) (h₂ : Q₂.radical = ⊥) : (Q₁.prod Q₂).radical = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hQ, hpol⟩ := hx
  have hpol1 : ∀ c, polar Q₁ x.1 c = 0 := by
    intro c
    have := DFunLike.congr_fun hpol (c, 0)
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod, QuadraticMap.polar] using this
  have hpol2 : ∀ d, polar Q₂ x.2 d = 0 := by
    intro d
    have := DFunLike.congr_fun hpol (0, d)
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod, QuadraticMap.polar] using this
  have ha : x.1 ∈ Q₁.radical := by
    refine ⟨?_, ?_⟩
    · have := hpol1 x.1; rw [polar_self] at this; simpa using this
    · ext c; simpa [QuadraticMap.polarBilin_apply_apply] using hpol1 c
  have hb : x.2 ∈ Q₂.radical := by
    refine ⟨?_, ?_⟩
    · have := hpol2 x.2; rw [polar_self] at this; simpa using this
    · ext d; simpa [QuadraticMap.polarBilin_apply_apply] using hpol2 d
  rw [h₁] at ha; rw [h₂] at hb
  simp only [Submodule.mem_bot] at ha hb
  rw [Submodule.mem_bot, Prod.ext_iff]
  exact ⟨ha, hb⟩

/-- **Signature additivity (positive inertia), nondegenerate case:**
`sigPos (Q₁.prod Q₂) = sigPos Q₁ + sigPos Q₂` when both forms are nondegenerate. The two
superadditivity inequalities, combined with the inertia dimension identity
`sigPos + sigNeg + dim(radical) = dim` (radical `= ⊥`), force equality. -/
theorem sigPos_prod_of_nondeg (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
    (h₁ : Q₁.radical = ⊥) (h₂ : Q₂.radical = ⊥) :
    sigPos (Q₁.prod Q₂) = sigPos Q₁ + sigPos Q₂ := by
  have hr := radical_prod_eq_bot Q₁ Q₂ h₁ h₂
  have d1 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₁)
  have d2 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₂)
  have dp := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₁.prod Q₂)
  rw [h₁, finrank_bot, add_zero] at d1
  rw [h₂, finrank_bot, add_zero] at d2
  rw [hr, finrank_bot, add_zero, Module.finrank_prod] at dp
  have hp := le_sigPos_prod Q₁ Q₂
  have hn := le_sigNeg_prod Q₁ Q₂
  omega

/-- **Signature additivity (negative inertia), nondegenerate case.** -/
theorem sigNeg_prod_of_nondeg (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
    (h₁ : Q₁.radical = ⊥) (h₂ : Q₂.radical = ⊥) :
    sigNeg (Q₁.prod Q₂) = sigNeg Q₁ + sigNeg Q₂ := by
  have hr := radical_prod_eq_bot Q₁ Q₂ h₁ h₂
  have d1 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₁)
  have d2 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₂)
  have dp := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₁.prod Q₂)
  rw [h₁, finrank_bot, add_zero] at d1
  rw [h₂, finrank_bot, add_zero] at d2
  rw [hr, finrank_bot, add_zero, Module.finrank_prod] at dp
  have hp := le_sigPos_prod Q₁ Q₂
  have hn := le_sigNeg_prod Q₁ Q₂
  omega

/-! ## Definiteness ⟹ nondegeneracy

Positive- (resp. negative-) definite forms are nondegenerate: a radical vector `x` has `Q x = 0`, but
definiteness forces `Q x > 0` (resp. `< 0`) for `x ≠ 0`. These supply the `radical = ⊥` hypothesis of
the additivity theorems for the definite generators `E₈` and `-E₈`. -/

/-- A positive-definite quadratic form is nondegenerate (`radical = ⊥`). -/
theorem posDef_radical_eq_bot {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (hQ : Q.PosDef) : Q.radical = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  by_contra h
  have hpos := hQ x h
  have hzero : Q x = 0 := hx.1
  linarith

/-- A negative-definite quadratic form (`-Q` positive-definite) is nondegenerate. -/
theorem negDef_radical_eq_bot {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (hQ : (-Q).PosDef) : Q.radical = ⊥ := by
  have heq : Q.radical = (-Q).radical := by
    ext x; simp [QuadraticMap.mem_radical_iff']
  rw [heq]; exact posDef_radical_eq_bot _ hQ

end SKEFTHawking
