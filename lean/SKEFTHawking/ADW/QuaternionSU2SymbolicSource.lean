import SKEFTHawking.ADW.QuaternionSU2HaarAssembly

/-!
# Quaternion-polynomial source for the original compensated action

The printed and closed words keep their original anchors and order.
Only the coefficient ring changes, so specializing the actual link coordinates
leaves the local coframe variables available for compensation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SKEFTHawking.ADW.QuaternionSU2Sphere

open FiniteGrassmannCoframe FiniteDiracQuaternionSpecialization
open FiniteGrassmannSourceAuxiliary

abbrev QuaternionCoefficients (L : Torus) := MvPolynomial (QuaternionVariables L) ℂ

abbrev QuaternionSource (L : Torus) := MvPolynomial D (QuaternionCoefficients L)

private def quaternionPart (L : Torus) : Symbolic L →+* QuaternionCoefficients L :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim 0 (Sum.elim 0 MvPolynomial.X))

/-- Evaluate quaternion coefficients on the actual anchored chiral links. -/
def evaluateQuaternion {L : Torus} (U : Links L) : QuaternionCoefficients L →+* ℂ :=
  MvPolynomial.eval (fun v ↦ (anchoredCoordinate U v : ℂ))

private theorem evaluateQuaternion_quaternionPart {L : Torus} (U : Links L) :
    (evaluateQuaternion U).comp (quaternionPart L) =
      (MvPolynomial.eval 0).comp (specialize L 0 (anchoredCoordinate U)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [evaluateQuaternion, quaternionPart, specialize]
  · intro v
    rcases v with v | v | v <;> simp [evaluateQuaternion, quaternionPart, specialize]

private def quaternionLink (L : Torus) (x : Site L) (k : Fin 4) :
    Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L) :=
  (symbolicLink L x k).map (quaternionPart L)

private def quaternionDagger (L : Torus) (x : Site L) (k : Fin 4) :
    Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L) :=
  (symbolicDagger L x k).map (quaternionPart L)

private theorem quaternionLink_eval {L : Torus} (U : Links L) (x : Site L) (k : Fin 4) :
    (quaternionLink L x k).map (evaluateQuaternion U) = dirac (U x k) := by
  rw [quaternionLink, Matrix.map_map]
  change (symbolicLink L x k).map ((evaluateQuaternion U).comp (quaternionPart L)) = _
  rw [evaluateQuaternion_quaternionPart U]
  change (symbolicLink L x k).map
    ((MvPolynomial.eval 0) ∘ (specialize L 0 (anchoredCoordinate U))) = _
  rw [← Matrix.map_map,
    symbolicLink_specialize L 0 _ (anchoredCoordinate_unit U), quaternionLinks_anchoredCoordinate U,
    Matrix.map_map]
  ext i j
  simp [Function.comp_def]

private theorem quaternionDagger_eval {L : Torus} (U : Links L) (x : Site L) (k : Fin 4) :
    (quaternionDagger L x k).map (evaluateQuaternion U) = (dirac (U x k)).conjTranspose := by
  rw [quaternionDagger, Matrix.map_map]
  change (symbolicDagger L x k).map ((evaluateQuaternion U).comp (quaternionPart L)) = _
  rw [evaluateQuaternion_quaternionPart U]
  change (symbolicDagger L x k).map
    ((MvPolynomial.eval 0) ∘ (specialize L 0 (anchoredCoordinate U))) = _
  rw [← Matrix.map_map,
    symbolicDagger_specialize L 0 _ (anchoredCoordinate_unit U),
    quaternionLinks_anchoredCoordinate U, Matrix.map_map]
  ext i j
  simp [Function.comp_def]

/-- Quaternion-polynomial form of the original printed word. -/
def quaternionPlaquettePrinted (L : Torus) (x : Site L) (k l : Fin 4) :
    Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L) :=
  quaternionLink L x k * quaternionLink L (forward L x k) l *
    quaternionDagger L (forward L x l) k * quaternionDagger L x l

/-- Quaternion-polynomial form of the separately labelled closed word. -/
def quaternionPlaquetteClosed (L : Torus) (x : Site L) (k l : Fin 4) :
    Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L) :=
  quaternionDagger L x l * quaternionDagger L (forward L x l) k *
    quaternionLink L (forward L x k) l * quaternionLink L x k

theorem quaternionPlaquettePrinted_eval {L : Torus} (U : Links L) (x : Site L) (k l : Fin 4) :
    (quaternionPlaquettePrinted L x k l).map (evaluateQuaternion U) =
      plaquettePrinted L U x k l := by
  simp only [quaternionPlaquettePrinted, Matrix.map_mul, quaternionLink_eval,
    quaternionDagger_eval, plaquettePrinted]

theorem quaternionPlaquetteClosed_eval {L : Torus} (U : Links L) (x : Site L) (k l : Fin 4) :
    (quaternionPlaquetteClosed L x k l).map (evaluateQuaternion U) =
      plaquetteClosed L U x k l := by
  simp only [quaternionPlaquetteClosed, Matrix.map_mul, quaternionLink_eval,
    quaternionDagger_eval, plaquetteClosed]

private def quaternionCurvatureCoefficient {L : Torus}
    (F : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L))
    (m n A B : Fin 4) : QuaternionCoefficients L :=
  ∑ k, ∑ l, MvPolynomial.C (epsilon4 k l m n) *
    Matrix.trace (F k l * (gamma A).map MvPolynomial.C *
      (gamma B).map MvPolynomial.C * gamma5.map MvPolynomial.C)

private theorem evaluateQuaternion_C {L : Torus} (U : Links L) (c : ℂ) :
    evaluateQuaternion U (MvPolynomial.C c) = c := by
  simp [evaluateQuaternion]

private theorem evaluateQuaternion_trace {L : Torus} (U : Links L)
    (M : Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L)) :
    evaluateQuaternion U M.trace = (M.map (evaluateQuaternion U)).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

private theorem evaluateQuaternion_matrix_C {L : Torus} (U : Links L)
    (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (M.map (MvPolynomial.C : ℂ →+* QuaternionCoefficients L)).map (evaluateQuaternion U) =
      M := by
  ext i j
  exact evaluateQuaternion_C U (M i j)

private theorem quaternionCurvatureCoefficient_eval {L : Torus} (U : Links L)
    (F : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L))
    (m n A B : Fin 4) :
    evaluateQuaternion U (quaternionCurvatureCoefficient F m n A B) =
      curvatureCoefficient (fun k l ↦ (F k l).map (evaluateQuaternion U)) m n A B := by
  simp only [quaternionCurvatureCoefficient, curvatureCoefficient, map_sum, map_mul,
    evaluateQuaternion_C, evaluateQuaternion_trace, Matrix.map_mul, evaluateQuaternion_matrix_C]

private def quaternionAction {L : Torus}
    (F : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L))
    (g1 g2 : ℂ) : QuaternionSource L :=
  MvPolynomial.map (MvPolynomial.C : ℂ →+* QuaternionCoefficients L) (cosmological g1) +
    ∑ m, ∑ n, ∑ A, ∑ B,
      MvPolynomial.C (MvPolynomial.C (g2 / 4) * quaternionCurvatureCoefficient F m n A B) *
        (MvPolynomial.X (m,A) * MvPolynomial.X (n,B))

private theorem quaternionAction_eval {L : Torus} (U : Links L)
    (F : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L)) (g1 g2 : ℂ) :
    MvPolynomial.map (evaluateQuaternion U) (quaternionAction F g1 g2) =
      source (fun k l ↦ (F k l).map (evaluateQuaternion U)) g1 g2 := by
  have he : (evaluateQuaternion U).comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    exact evaluateQuaternion_C U c
  simp only [quaternionAction, source, einsteinCartan, map_add, map_sum, map_mul,
    MvPolynomial.map_map, he, MvPolynomial.map_id, MvPolynomial.map_C, MvPolynomial.map_X,
    evaluateQuaternion_C, quaternionCurvatureCoefficient_eval]

private theorem quaternionAction_constantCoeff {L : Torus}
    (F : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) (QuaternionCoefficients L)) (g1 g2 : ℂ) :
    (quaternionAction F g1 g2).constantCoeff = 0 := by
  simp [quaternionAction, cosmological]

/-- Original printed C3 action over quaternion coefficients, with the local coframe variables. -/
def quaternionPrintedSource (L : Torus) (x : Site L) (g1 g2 : ℂ) : QuaternionSource L :=
  quaternionAction (quaternionPlaquettePrinted L x) g1 g2

/-- Original closed C3 action over quaternion coefficients, with the local coframe variables. -/
def quaternionClosedSource (L : Torus) (x : Site L) (g1 g2 : ℂ) : QuaternionSource L :=
  quaternionAction (quaternionPlaquetteClosed L x) g1 g2

theorem quaternionPrintedSource_eval {L : Torus} (U : Links L) (x : Site L) (g1 g2 : ℂ) :
    MvPolynomial.map (evaluateQuaternion U) (quaternionPrintedSource L x g1 g2) =
      printedSource L U x g1 g2 := by
  simp only [quaternionPrintedSource, quaternionAction_eval, quaternionPlaquettePrinted_eval,
    printedSource]

theorem quaternionClosedSource_eval {L : Torus} (U : Links L) (x : Site L) (g1 g2 : ℂ) :
    MvPolynomial.map (evaluateQuaternion U) (quaternionClosedSource L x g1 g2) =
      closedSource L U x g1 g2 := by
  simp only [quaternionClosedSource, quaternionAction_eval, quaternionPlaquetteClosed_eval,
    closedSource]

theorem quaternionPrintedSource_constantCoeff (L : Torus) (x : Site L) (g1 g2 : ℂ) :
    (quaternionPrintedSource L x g1 g2).constantCoeff = 0 :=
  quaternionAction_constantCoeff _ g1 g2

theorem quaternionClosedSource_constantCoeff (L : Torus) (x : Site L) (g1 g2 : ℂ) :
    (quaternionClosedSource L x g1 g2).constantCoeff = 0 :=
  quaternionAction_constantCoeff _ g1 g2

/-- The retained local compensation coefficient before any link evaluation.
The degree cutoff acts only on coframe variables. -/
def quaternionCompensationCoeff {L : Torus} (M : ℕ) (σ : ℝ)
    (S : QuaternionSource L) (β : D →₀ ℕ) : QuaternionCoefficients L :=
  if auxiliaryDegree β ≤ M then
    ∑ k ∈ Finset.range (M + 1), ∑ l ∈ Finset.range (M + 1),
      MvPolynomial.C (((k.factorial : ℂ)⁻¹) * ((l.factorial : ℂ)⁻¹)) *
        (S ^ k * (-MvPolynomial.map (MvPolynomial.C : ℂ →+* QuaternionCoefficients L)
          (auxiliaryQuadraticPolynomial σ)) ^ l).coeff β
  else 0

/-- Link evaluation commutes with the complete retained compensation coefficient formula. -/
theorem quaternionCompensationCoeff_eval {L : Torus} (U : Links L) (M : ℕ) (σ : ℝ)
    (S : QuaternionSource L) (hS : S.constantCoeff = 0) (β : D →₀ ℕ) :
    evaluateQuaternion U (quaternionCompensationCoeff M σ S β) =
      (compensationPolynomial M σ (MvPolynomial.map (evaluateQuaternion U) S)).coeff β := by
  have h0 : (MvPolynomial.map (evaluateQuaternion U) S).constantCoeff = 0 := by
    rw [MvPolynomial.constantCoeff_map, hS, map_zero]
  have he : (evaluateQuaternion U).comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    exact evaluateQuaternion_C U c
  rw [compensationPolynomial_coeff_finite M σ _ h0]
  by_cases hβ : auxiliaryDegree β ≤ M
  · simp only [quaternionCompensationCoeff, if_pos hβ, map_sum, map_mul, evaluateQuaternion_C,
      ← MvPolynomial.coeff_map, map_pow, map_neg, MvPolynomial.map_map, he, MvPolynomial.map_id]
  · simp [quaternionCompensationCoeff, hβ]

/-- Every retained coefficient for the actual printed C3 source. -/
theorem quaternionPrintedCompensation_eval {L : Torus} (U : Links L)
    (σ : ℝ) (x : Site L) (g1 g2 : ℂ) (β : D →₀ ℕ) :
    evaluateQuaternion U (quaternionCompensationCoeff (4 * volume L) σ
      (quaternionPrintedSource L x g1 g2) β) =
      (compensationPolynomial (4 * volume L) σ (printedSource L U x g1 g2)).coeff β := by
  rw [quaternionCompensationCoeff_eval U _ _ _ (quaternionPrintedSource_constantCoeff ..),
    quaternionPrintedSource_eval]

/-- Every retained coefficient for the separately labelled closed C3 source. -/
theorem quaternionClosedCompensation_eval {L : Torus} (U : Links L)
    (σ : ℝ) (x : Site L) (g1 g2 : ℂ) (β : D →₀ ℕ) :
    evaluateQuaternion U (quaternionCompensationCoeff (4 * volume L) σ
      (quaternionClosedSource L x g1 g2) β) =
      (compensationPolynomial (4 * volume L) σ (closedSource L U x g1 g2)).coeff β := by
  rw [quaternionCompensationCoeff_eval U _ _ _ (quaternionClosedSource_constantCoeff ..),
    quaternionClosedSource_eval]

private def turnSU2 : SU2 := ⟨!![0, 1; -1, 0], by
  constructor
  · change _ ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · norm_num [Matrix.det_fin_two]⟩

private def turnSpin4 : Spin4 := (turnSU2, 1)

private def wordOrderLinks : Links controlTorus :=
  fun x k ↦ if x = 0 ∧ k = 0 then phaseSpin4 else
    if x = forward controlTorus 0 0 ∧ k = 1 then turnSpin4 else 1

private theorem dirac_phase :
    dirac phaseSpin4 = !![Complex.I, 0, 0, 0; 0, -Complex.I, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem dirac_turn :
    dirac turnSpin4 = !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem wordOrder_printed :
    plaquettePrinted controlTorus wordOrderLinks 0 0 1 0 1 = Complex.I := by
  have h₀ : forward controlTorus 0 0 ≠ 0 := by decide
  have h₁ : forward controlTorus 0 1 ≠ 0 := by decide
  simp [plaquettePrinted, wordOrderLinks, h₀, h₁, Ne.symm h₀, dirac_identity]
  norm_num [dirac_phase, dirac_turn, Matrix.mul_apply, Fin.sum_univ_four]
  change Complex.I + (0 : ℂ) * 0 + 0 * 0 = _
  simp

private theorem wordOrder_closed :
    plaquetteClosed controlTorus wordOrderLinks 0 0 1 0 1 = -Complex.I := by
  have h₀ : forward controlTorus 0 0 ≠ 0 := by decide
  have h₁ : forward controlTorus 0 1 ≠ 0 := by decide
  simp [plaquetteClosed, wordOrderLinks, h₀, h₁, Ne.symm h₀, dirac_identity]
  norm_num [dirac_phase, dirac_turn, Matrix.mul_apply, Fin.sum_univ_four]
  change -Complex.I + (0 : ℂ) * 0 + 0 * 0 = _
  simp

/-- Two actual noncommuting links distinguish the printed and closed words. -/
theorem quaternionPlaquette_wordOrder_control :
    ∃ U : Links controlTorus,
      ((quaternionPlaquettePrinted controlTorus 0 0 1).map (evaluateQuaternion U)) 0 1 =
          Complex.I ∧
        ((quaternionPlaquetteClosed controlTorus 0 0 1).map (evaluateQuaternion U)) 0 1 =
          -Complex.I := by
  refine ⟨wordOrderLinks, ?_⟩
  rw [quaternionPlaquettePrinted_eval, quaternionPlaquetteClosed_eval]
  exact ⟨wordOrder_printed, wordOrder_closed⟩

end SKEFTHawking.ADW.QuaternionSU2Sphere
