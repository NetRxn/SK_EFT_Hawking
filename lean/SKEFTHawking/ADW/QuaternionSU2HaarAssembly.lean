import SKEFTHawking.ADW.QuaternionSU2HaarPolynomial

/-!
# Haar contraction of the shifted finite Dirac determinant

The assembly is specialized on the original link carrier before integration.
The raw source jet retains both derivative positions, including coincident labels.
-/

set_option autoImplicit false

open MeasureTheory

namespace SKEFTHawking.ADW.QuaternionSU2Sphere

open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin FiniteDiracQuaternionSpecialization
open FiniteDiracExecutableAssembly

/-- The coordinates of each actual chiral link have unit norm. -/
theorem anchoredCoordinate_unit {L : Torus} (U : Links L) (x : Site L)
    (μ : Fin 4) (side : Bool) :
    UnitQuaternion (fun k ↦ anchoredCoordinate U (x, μ, side, k)) := by
  cases side
  · exact unit_coordinates (U x μ).1
  · exact unit_coordinates (U x μ).2

/-- The coordinate specialization reconstructs the actual original link at every anchor. -/
theorem quaternionLinks_anchoredCoordinate {L : Torus} (U : Links L) :
    quaternionLinks L (anchoredCoordinate U) (anchoredCoordinate_unit U) = U := by
  funext x μ
  apply Prod.ext <;> apply Subtype.ext
  · exact block_coordinates (U x μ).1
  · exact block_coordinates (U x μ).2

/-- The shifted determinant in executable auxiliary coordinates on the original links. -/
noncomputable def transportedShiftedDet (L : Torus) (anti : Fin 4 → Bool)
    (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ) (U : Links L) :
    MvPolynomial (Auxiliary L) ℂ :=
  MvPolynomial.rename (sourceCoordinate L axis).symm
    (shiftedDiracDetAtLink L (twistedLinks L anti U) (J ∘ (sourceCoordinate L axis).symm))

/-- Pointwise specialization of the symbolic determinant on the actual original links. -/
theorem specialize_symbolicDet (L : Torus) (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4)
    (J : Auxiliary L → ℂ) (U : Links L) :
    specialize L J (anchoredCoordinate U) (symbolicAssembly L anti axis).det =
      transportedShiftedDet L anti axis J U := by
  rw [symbolicAssembly_det L anti axis J _ (anchoredCoordinate_unit U),
    quaternionLinks_anchoredCoordinate]
  rfl

/-- Exact Haar transfer of the shifted determinant with the original source-label transport. -/
theorem integral_transportedShiftedDet (L : Torus) (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4)
    (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) :
    (∫ U : Links L, MvPolynomial.eval (fun a ↦ (h a : ℂ))
      (transportedShiftedDet L anti axis J U) ∂linkHaar L) =
      MvPolynomial.eval (Sum.elim (fun a ↦ (h a : ℂ)) J)
        (contractSymbolic L (symbolicAssembly L anti axis).det) := by
  simpa only [specialize_symbolicDet] using
    integral_specialize_eq_contractSymbolic L (symbolicAssembly L anti axis).det h J

private theorem specialize_pderiv (L : Torus) (J : Auxiliary L → ℂ)
    (q : QuaternionVariables L → ℝ) (a : Auxiliary L) (P : Symbolic L) :
    specialize L J q (MvPolynomial.pderiv (.inl a) P) =
      MvPolynomial.pderiv a (specialize L J q P) := by
  let f : Auxiliary L ⊕ QuaternionVariables L → ℂ := Sum.elim J (fun v ↦ (q v : ℂ))
  have heval (Q : Symbolic L) :
      specialize L J q Q =
        MvPolynomial.aeval (Sum.elim MvPolynomial.X (MvPolynomial.C ∘ f)) Q := by
    rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.algebraMap_eq]
    have hf : Sum.elim MvPolynomial.X (MvPolynomial.C ∘ f) =
        (Sum.elim MvPolynomial.X
          (Sum.elim (MvPolynomial.C ∘ J) (fun i ↦ MvPolynomial.C (q i : ℂ))) :
            FiniteDiracQuaternionSpecialization.Variables L → MvPolynomial (Auxiliary L) ℂ) := by
      funext x
      rcases x with x | x | x <;> rfl
    rw [hf]
    rfl
  rw [heval, heval]
  exact MvPolynomial.aeval_sumElim_pderiv_inl P f a

/-- Differentiating a retained label leaves every quaternion power unchanged. -/
theorem contract_pderiv {L : Torus} {ρ : Type*} (a : ρ)
    (P : MvPolynomial (ρ ⊕ QuaternionVariables L) ℂ) :
    contract L ρ (MvPolynomial.pderiv (.inl a) P) =
      MvPolynomial.pderiv a (contract L ρ P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    obtain ⟨⟨d, p⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective e
    change contract L ρ (MvPolynomial.pderiv (.inl a) (MvPolynomial.monomial (d.sumElim p) c)) =
      MvPolynomial.pderiv a (contract L ρ (MvPolynomial.monomial (d.sumElim p) c))
    have hs : d.sumElim p - Finsupp.single (.inl a) 1 =
        (d - Finsupp.single a 1).sumElim p := by
      ext i
      cases i <;> simp [Finsupp.tsub_apply, Finsupp.sumElim_inl, Finsupp.sumElim_inr,
        Finsupp.single_apply]
    simp only [MvPolynomial.pderiv_monomial, hs, Finsupp.sumElim_inl, contract_monomial]
    congr 1
    ring
  | add P Q hP hQ => simp only [map_add, hP, hQ]

private theorem contractSymbolic_pderiv (L : Torus) (a : Auxiliary L) (P : Symbolic L) :
    contractSymbolic L (MvPolynomial.pderiv (.inl a) P) =
      MvPolynomial.pderiv (.inl a) (contractSymbolic L P) := by
  let e := (Equiv.sumAssoc (Auxiliary L) (Auxiliary L) (QuaternionVariables L)).symm
  change contract L _ (MvPolynomial.rename e (MvPolynomial.pderiv (.inl a) P)) = _
  rw [← MvPolynomial.pderiv_rename e.injective (.inl a)]
  exact @contract_pderiv L (Auxiliary L ⊕ Auxiliary L) (.inl a) (MvPolynomial.rename e P)

/-- Differentiation in an executable slot uses the transported physical source label. -/
theorem pderiv_transportedShiftedDet (L : Torus) (anti : Fin 4 → Bool)
    (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ) (U : Links L) (a : Auxiliary L) :
    MvPolynomial.pderiv a (transportedShiftedDet L anti axis J U) =
      MvPolynomial.rename (sourceCoordinate L axis).symm
        (MvPolynomial.pderiv (sourceCoordinate L axis a)
          (shiftedDiracDetAtLink L (twistedLinks L anti U)
            (J ∘ (sourceCoordinate L axis).symm))) := by
  unfold transportedShiftedDet
  simpa only [Equiv.symm_apply_apply] using
    MvPolynomial.pderiv_rename (sourceCoordinate L axis).symm.injective
      (sourceCoordinate L axis a)
      (shiftedDiracDetAtLink L (twistedLinks L anti U)
        (J ∘ (sourceCoordinate L axis).symm))

/-- The first raw source derivative is transferred without dividing by the determinant. -/
theorem integral_transportedShiftedDet_first (L : Torus) (anti : Fin 4 → Bool)
    (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ)
    (a : Auxiliary L) :
    (∫ U : Links L, MvPolynomial.eval (fun j ↦ (h j : ℂ))
      (MvPolynomial.pderiv a (transportedShiftedDet L anti axis J U)) ∂linkHaar L) =
      MvPolynomial.eval (Sum.elim (fun j ↦ (h j : ℂ)) J)
        (MvPolynomial.pderiv (.inl a)
          (contractSymbolic L (symbolicAssembly L anti axis).det)) := by
  simpa only [specialize_pderiv, specialize_symbolicDet, contractSymbolic_pderiv] using
    integral_specialize_eq_contractSymbolic L
      (MvPolynomial.pderiv (.inl a) (symbolicAssembly L anti axis).det) h J

/-- The second raw source derivative transfers for any two labels, including equal labels. -/
theorem integral_transportedShiftedDet_second (L : Torus) (anti : Fin 4 → Bool)
    (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ)
    (a b : Auxiliary L) :
    (∫ U : Links L, MvPolynomial.eval (fun j ↦ (h j : ℂ))
      (MvPolynomial.pderiv b (MvPolynomial.pderiv a (transportedShiftedDet L anti axis J U)))
      ∂linkHaar L) =
      MvPolynomial.eval (Sum.elim (fun j ↦ (h j : ℂ)) J)
        (MvPolynomial.pderiv (.inl b) (MvPolynomial.pderiv (.inl a)
          (contractSymbolic L (symbolicAssembly L anti axis).det))) := by
  simpa only [specialize_pderiv, specialize_symbolicDet, contractSymbolic_pderiv] using
    integral_specialize_eq_contractSymbolic L
      (MvPolynomial.pderiv (.inl b)
        (MvPolynomial.pderiv (.inl a) (symbolicAssembly L anti axis).det)) h J

open FiniteDeterminantRawJet in
/-- Each raw slot of the original finite determinant program integrates to the same slot of
the contracted symbolic determinant. The derivative positions stay independent when a = b. -/
theorem integral_shiftedAssembly_rawJet (L : Torus) (anti : Fin 4 → Bool)
    (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ)
    (a b : Auxiliary L) :
    let z : Auxiliary L → ℂ := fun j ↦ (h j : ℂ)
    let jet (U : Links L) := determinantJet
      ((polynomialJet z a b).mapMatrix (shiftedAssembly L anti U axis J))
    ofSlots (∫ U : Links L, value (jet U) ∂linkHaar L)
      (∫ U : Links L, firstOuter (jet U) ∂linkHaar L)
      (∫ U : Links L, firstInner (jet U) ∂linkHaar L)
      (∫ U : Links L, second (jet U) ∂linkHaar L) =
        polynomialJet (Sum.elim z J) (.inl a) (.inl b)
          (contractSymbolic L (symbolicAssembly L anti axis).det) := by
  dsimp only
  have hdet (U : Links L) :
      MvPolynomial.rename (sourceCoordinate L axis).symm
        (shiftedDiracDetAtLink L (twistedLinks L anti U) (J ∘ (sourceCoordinate L axis).symm)) =
      transportedShiftedDet L anti axis J U := rfl
  simp_rw [shiftedAssembly_rawJet, hdet, polynomialJet_eq_select, select]
  simp only [value, firstOuter, firstInner, second, ofSlots, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk, integral_transportedShiftedDet,
    integral_transportedShiftedDet_first, integral_transportedShiftedDet_second]

/-- At identity axis and periodic boundary the original polynomial needs no label transport. -/
theorem integral_shiftedDet_periodic (L : Torus) (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) :
    (∫ U : Links L, MvPolynomial.eval (fun a ↦ (h a : ℂ))
      (shiftedDiracDetAtLink L U J) ∂linkHaar L) =
      MvPolynomial.eval (Sum.elim (fun a ↦ (h a : ℂ)) J)
        (contractSymbolic L (symbolicAssembly L (fun _ ↦ false) (Equiv.refl _)).det) := by
  have he : sourceCoordinate L (Equiv.refl _) = Equiv.refl _ := by
    apply Equiv.ext
    intro a
    rcases a with ⟨x, μ, γ⟩
    rfl
  have ht (U : Links L) : twistedLinks L (fun _ ↦ false) U = U := by
    funext x μ
    simp [twistedLinks]
  simpa [transportedShiftedDet, he, ht] using
    integral_transportedShiftedDet L (fun _ ↦ false) (Equiv.refl _) J h

-- Swapping gamma axes transports the gamma label while retaining the step direction.
example (L : Torus) (x : Site L) (μ : Fin 4) :
    sourceCoordinate L (Equiv.swap (0 : Fin 4) 1) (x, μ, 0) = (x, μ, 1) := by
  change (x, μ, Equiv.swap (0 : Fin 4) 1 0) = (x, μ, 1)
  rw [Equiv.swap_apply_left]

-- The same swapped-axis raw jet permits a repeated source label and a boundary twist.
open FiniteDeterminantRawJet in
example (L : Torus) (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) (a : Auxiliary L) :
    let anti : Fin 4 → Bool := fun μ ↦ decide (μ = 0)
    let axis := Equiv.swap (0 : Fin 4) 1
    let z : Auxiliary L → ℂ := fun j ↦ (h j : ℂ)
    let jet (U : Links L) := determinantJet
      ((polynomialJet z a a).mapMatrix (shiftedAssembly L anti U axis J))
    ofSlots (∫ U : Links L, value (jet U) ∂linkHaar L)
      (∫ U : Links L, firstOuter (jet U) ∂linkHaar L)
      (∫ U : Links L, firstInner (jet U) ∂linkHaar L)
      (∫ U : Links L, second (jet U) ∂linkHaar L) =
        polynomialJet (Sum.elim z J) (.inl a) (.inl a)
          (contractSymbolic L (symbolicAssembly L anti axis).det) :=
  integral_shiftedAssembly_rawJet L (fun μ ↦ decide (μ = 0)) (Equiv.swap 0 1) J h a a

end SKEFTHawking.ADW.QuaternionSU2Sphere
