import SKEFTHawking.ADW.FiniteDiracExecutableAssembly

/-!
# Symbolic quaternion specialization of the original finite Dirac assembly

The independent real quaternion coordinates reproduce Python's plus-i chiral blocks.
Specializing them on the unit sphere and supplying the complex sources leaves an auxiliary
polynomial. The specialized determinant and its raw derivatives agree with the original
fixed-link expressions for both gamma conventions and every paired boundary sign.
-/

noncomputable section
open Matrix
namespace SKEFTHawking.ADW.FiniteDiracQuaternionSpecialization
open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin FiniteDiracExecutableAssembly

/-- The Python plus-i quaternion block over the chosen coefficient ring. -/
def quaternionBlock {R : Type*} [Ring R] (I : R) (q : Fin 4 → R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![q 0 + q 3 * I, q 2 + q 1 * I; -q 2 + q 1 * I, q 0 - q 3 * I]

/-- Each independent quaternion is constrained by its real unit sphere. -/
def UnitQuaternion (q : Fin 4 → ℝ) : Prop :=
  q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1

/-- The real unit sphere normalizes the determinant to one. -/
theorem quaternionBlock_det (q : Fin 4 → ℝ) (h : UnitQuaternion q) :
    (quaternionBlock Complex.I fun i ↦ (q i : ℂ)).det = 1 := by
  unfold UnitQuaternion at h
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [quaternionBlock, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] <;> nlinarith

/-- The same unit sphere gives a unitary quaternion block. -/
theorem quaternionBlock_unitary (q : Fin 4 → ℝ) (h : UnitQuaternion q) :
    quaternionBlock Complex.I (fun i ↦ (q i : ℂ)) *
      (quaternionBlock Complex.I (fun i ↦ (q i : ℂ)))ᴴ = 1 := by
  unfold UnitQuaternion at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternionBlock, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] <;> nlinarith

/-- Normalizing each real block gives the physical fundamental representation. -/
def quaternionSU2 (q : Fin 4 → ℝ) (h : UnitQuaternion q) : SU2 :=
  ⟨quaternionBlock Complex.I (fun i ↦ (q i : ℂ)), Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr (by
      rw [Matrix.star_eq_conjTranspose]
      exact quaternionBlock_unitary q h), quaternionBlock_det q h⟩⟩

/-- Ring homomorphisms preserve the four quaternion entries. -/
theorem quaternionBlock_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (I : R) (q : Fin 4 → R) :
    (quaternionBlock I q).map f = quaternionBlock (f I) (f ∘ q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionBlock]

/-- With real quaternion coordinates, the dagger conjugates the imaginary unit and transposes. -/
theorem quaternionBlock_dagger (q : Fin 4 → ℝ) :
    (quaternionBlock Complex.I (fun i ↦ (q i : ℂ)))ᴴ =
      (quaternionBlock (-Complex.I) (fun i ↦ (q i : ℂ)))ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionBlock, Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- The two chiral blocks use the same flattened index as the physical Dirac matrix. -/
def spinBlock {R : Type*} [Zero R] (A B : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 4) (Fin 4) R :=
  Matrix.reindex diracIndex diracIndex (Matrix.fromBlocks A 0 0 B)

private theorem spinBlock_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (A B : Matrix (Fin 2) (Fin 2) R) :
    (spinBlock A B).map f = spinBlock (A.map f) (B.map f) := by
  ext i j
  obtain ⟨i, rfl⟩ := diracIndex.surjective i
  obtain ⟨j, rfl⟩ := diracIndex.surjective j
  cases i <;> cases j <;> simp [spinBlock, Matrix.reindex_apply, Matrix.submatrix]

private theorem spinBlock_dagger (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinBlock A B)ᴴ = spinBlock Aᴴ Bᴴ := by
  ext i j
  obtain ⟨i, rfl⟩ := diracIndex.surjective i
  obtain ⟨j, rfl⟩ := diracIndex.surjective j
  cases i <;> cases j <;>
    simp [spinBlock, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix]

/-- Distinct anchored forward links have independent left and right quaternion coordinates. -/
abbrev QuaternionVariables (L : Torus) := Site L × Fin 4 × Bool × Fin 4

/-- Auxiliary coordinates, independent source coordinates, and link coordinates. -/
abbrev Variables (L : Torus) := Auxiliary L ⊕ (Auxiliary L ⊕ QuaternionVariables L)

abbrev Symbolic (L : Torus) := MvPolynomial (Variables L) ℂ

/-- The two normalized Python chiral quaternions at each anchor. -/
def quaternionLinks (L : Torus) (q : QuaternionVariables L → ℝ)
    (unit : ∀ x μ side, UnitQuaternion (fun k ↦ q (x, μ, side, k))) : Links L :=
  fun x μ ↦ (quaternionSU2 (fun k ↦ q (x, μ, false, k)) (unit x μ false),
    quaternionSU2 (fun k ↦ q (x, μ, true, k)) (unit x μ true))

/-- Retain h as polynomial variables while substituting the supplied source and real link values. -/
def specialize (L : Torus) (J : Auxiliary L → ℂ) (q : QuaternionVariables L → ℝ) :
    Symbolic L →+* MvPolynomial (Auxiliary L) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (Sum.elim (MvPolynomial.C ∘ J) (fun i ↦ MvPolynomial.C (q i : ℂ))))

private def symbolicBlock (L : Torus) (x : Site L) (μ : Fin 4) (side : Bool)
    (I : Symbolic L) : Matrix (Fin 2) (Fin 2) (Symbolic L) :=
  quaternionBlock I (fun k ↦ MvPolynomial.X (.inr (.inr (x, μ, side, k))))

/-- The symbolic matrix used by the executable plus-i link constructor. -/
def symbolicLink (L : Torus) (x : Site L) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) (Symbolic L) :=
  spinBlock (symbolicBlock L x μ false (MvPolynomial.C Complex.I))
    (symbolicBlock L x μ true (MvPolynomial.C Complex.I))

/-- Conjugate the coefficients and transpose, retaining the real link-coordinate symbols. -/
def symbolicDagger (L : Torus) (x : Site L) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) (Symbolic L) :=
  spinBlock (symbolicBlock L x μ false (MvPolynomial.C (-Complex.I)))ᵀ
    (symbolicBlock L x μ true (MvPolynomial.C (-Complex.I)))ᵀ

private theorem symbolicBlock_specialize (L : Torus) (J : Auxiliary L → ℂ)
    (q : QuaternionVariables L → ℝ) (x : Site L) (μ : Fin 4) (side : Bool) (I : ℂ) :
    (symbolicBlock L x μ side (MvPolynomial.C I)).map (specialize L J q) =
      (quaternionBlock I (fun k ↦ (q (x, μ, side, k) : ℂ))).map MvPolynomial.C := by
  rw [symbolicBlock, quaternionBlock_map, quaternionBlock_map]
  simp [specialize, Function.comp_def]

/-- The symbolic plus-i block specializes to the original Spin(4) Dirac link. -/
theorem symbolicLink_specialize (L : Torus) (J : Auxiliary L → ℂ)
    (q : QuaternionVariables L → ℝ)
    (unit : ∀ x μ side, UnitQuaternion (fun k ↦ q (x, μ, side, k)))
    (x : Site L) (μ : Fin 4) :
    (symbolicLink L x μ).map (specialize L J q) =
      (dirac (quaternionLinks L q unit x μ)).map MvPolynomial.C := by
  change (symbolicLink L x μ).map (specialize L J q) =
    (spinBlock (quaternionBlock Complex.I (fun k ↦ (q (x, μ, false, k) : ℂ)))
      (quaternionBlock Complex.I (fun k ↦ (q (x, μ, true, k) : ℂ)))).map MvPolynomial.C
  simp only [symbolicLink, spinBlock_map, symbolicBlock_specialize]

/-- The symbolic dagger specializes to the actual conjugate transpose. -/
theorem symbolicDagger_specialize (L : Torus) (J : Auxiliary L → ℂ)
    (q : QuaternionVariables L → ℝ)
    (unit : ∀ x μ side, UnitQuaternion (fun k ↦ q (x, μ, side, k)))
    (x : Site L) (μ : Fin 4) :
    (symbolicDagger L x μ).map (specialize L J q) =
      (dirac (quaternionLinks L q unit x μ))ᴴ.map MvPolynomial.C := by
  change (symbolicDagger L x μ).map (specialize L J q) =
    (spinBlock (quaternionBlock Complex.I (fun k ↦ (q (x, μ, false, k) : ℂ)))
      (quaternionBlock Complex.I (fun k ↦ (q (x, μ, true, k) : ℂ))))ᴴ.map MvPolynomial.C
  simp only [symbolicDagger, spinBlock_dagger, spinBlock_map, Matrix.transpose_map,
    symbolicBlock_specialize, quaternionBlock_dagger]

private def symbolicScatter (L : Torus) (y z : Site L) (c : ℂ)
    (A : Matrix (Fin 4) (Fin 4) (Symbolic L)) (p q : Fermion L) : Symbolic L :=
  if p.1 = y ∧ q.1 = z then MvPolynomial.C c * A p.2 q.2 else 0

/-- The executable signed quarter-block polynomial before specializing link coordinates. -/
def symbolicCoframe (L : Torus) (anti : Fin 4 → Bool)
    (x : Site L) (μ C : Fin 4) (p q : Fermion L) : Symbolic L :=
  let f := forward L x μ
  let b := backward L x μ
  let sf := forwardSign L anti x μ
  let sb := backwardSign L anti x μ
  let g := (gamma C).map MvPolynomial.C
  symbolicScatter L x f (sf / 4) (g * symbolicDagger L x μ) p q +
    symbolicScatter L f x (-sf / 4) (symbolicLink L x μ * g) p q +
    symbolicScatter L x b (-sb / 4) (g * symbolicLink L b μ) p q +
    symbolicScatter L b x (sb / 4) (symbolicDagger L b μ * g) p q

private theorem constantMatrix_specialize (L : Torus) (J : Auxiliary L → ℂ)
    (q : QuaternionVariables L → ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (A.map MvPolynomial.C).map (specialize L J q) = A.map MvPolynomial.C := by
  ext i j
  simp [specialize]

/-- Specializing each link and its dagger preserves all four signed scatter contributions. -/
theorem symbolicCoframe_specialize (L : Torus) (anti : Fin 4 → Bool)
    (J : Auxiliary L → ℂ) (q : QuaternionVariables L → ℝ)
    (unit : ∀ x μ side, UnitQuaternion (fun k ↦ q (x, μ, side, k)))
    (x : Site L) (μ C : Fin 4) (p r : Fermion L) :
    specialize L J q (symbolicCoframe L anti x μ C p r) =
      MvPolynomial.C (assembledCoframe L anti (quaternionLinks L q unit) x μ C p r) := by
  let ev := specialize L J q
  have hconst (v : ℂ) : ev (MvPolynomial.C v) = MvPolynomial.C v := by simp [ev, specialize]
  have hmul (A B : Matrix (Fin 4) (Fin 4) (Symbolic L))
      (A' B' : Matrix (Fin 4) (Fin 4) ℂ)
      (ha : A.map ev = A'.map MvPolynomial.C) (hb : B.map ev = B'.map MvPolynomial.C) :
      (A * B).map ev = (A' * B').map MvPolynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, ha, hb]
  have hs (y z : Site L) (v : ℂ)
      (A : Matrix (Fin 4) (Fin 4) (Symbolic L)) (A' : Matrix (Fin 4) (Fin 4) ℂ)
      (h : A.map ev = A'.map MvPolynomial.C) :
      ev (symbolicScatter L y z v A p r) =
        MvPolynomial.C (if p.1 = y ∧ r.1 = z then v * A' p.2 r.2 else 0) := by
    by_cases hy : p.1 = y ∧ r.1 = z
    · simp only [symbolicScatter, if_pos hy, map_mul, hconst]
      change MvPolynomial.C v * (A.map ev) p.2 r.2 = _
      rw [h]
      rfl
    · simp [symbolicScatter, hy]
  have hg := constantMatrix_specialize L J q (gamma C)
  have hl := symbolicLink_specialize L J q unit
  have hd := symbolicDagger_specialize L J q unit
  change ev (symbolicCoframe L anti x μ C p r) = _
  simp only [symbolicCoframe, assembledCoframe, map_add]
  rw [hs _ _ _ _ _ (hmul _ _ _ _ hg (hd x μ)),
    hs _ _ _ _ _ (hmul _ _ _ _ (hl x μ) hg),
    hs _ _ _ _ _ (hmul _ _ _ _ hg (hl (backward L x μ) μ)),
    hs _ _ _ _ _ (hmul _ _ _ _ (hd (backward L x μ) μ) hg)]
  rfl

/-- The default executable assembly over distinct h, J and anchored real q variables. -/
def symbolicAssembly (L : Torus) (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4) :
    Matrix (Fin (4 * volume L)) (Fin (4 * volume L)) (Symbolic L) :=
  fun i j ↦ ∑ a, (MvPolynomial.X (.inl a) + MvPolynomial.X (.inr (.inl a))) *
    symbolicCoframe L anti a.1 a.2.1 (axis a.2.2)
      ((executableFermionIndex L).symm i) ((executableFermionIndex L).symm j)

/-- The full symbolic matrix specializes to the physical shifted assembly for either axis
convention and every paired boundary sign. -/
theorem symbolicAssembly_specialize (L : Torus) (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4)
    (J : Auxiliary L → ℂ) (q : QuaternionVariables L → ℝ)
    (unit : ∀ x μ side, UnitQuaternion (fun k ↦ q (x, μ, side, k))) :
    (specialize L J q).mapMatrix (symbolicAssembly L anti axis) =
      shiftedAssembly L anti (quaternionLinks L q unit) axis J := by
  apply Matrix.ext
  intro i j
  change specialize L J q (symbolicAssembly L anti axis i j) = _
  simp only [symbolicAssembly, map_sum, map_mul, map_add,
    symbolicCoframe_specialize L anti J q unit, shiftedAssembly, assembleDirac]
  apply Finset.sum_congr rfl
  intro a _
  simp [specialize]

/-- The symbolic determinant specializes to the original finite source determinant
with the same auxiliary-label transport and boundary twists. -/
theorem symbolicAssembly_det (L : Torus) (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4)
    (J : Auxiliary L → ℂ) (q : QuaternionVariables L → ℝ)
    (unit : ∀ x μ side, UnitQuaternion (fun k ↦ q (x, μ, side, k))) :
    specialize L J q (symbolicAssembly L anti axis).det =
      MvPolynomial.rename (sourceCoordinate L axis).symm
        (shiftedDiracDetAtLink L (twistedLinks L anti (quaternionLinks L q unit))
          (J ∘ (sourceCoordinate L axis).symm)) := by
  rw [(specialize L J q).map_det, symbolicAssembly_specialize L anti axis J q unit,
    shiftedAssembly_det]

/-- The specialized symbolic assembly also computes the original selected raw derivatives. -/
theorem symbolicAssembly_rawJet (L : Torus) (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4)
    (J h : Auxiliary L → ℂ) (q : QuaternionVariables L → ℝ)
    (unit : ∀ x μ side, UnitQuaternion (fun k ↦ q (x, μ, side, k))) (a b : Auxiliary L) :
    FiniteDeterminantRawJet.determinantJet
        ((FiniteDeterminantRawJet.polynomialJet h a b).mapMatrix
          ((specialize L J q).mapMatrix (symbolicAssembly L anti axis))) =
      FiniteDeterminantRawJet.polynomialJet h a b
        (MvPolynomial.rename (sourceCoordinate L axis).symm
          (shiftedDiracDetAtLink L (twistedLinks L anti (quaternionLinks L q unit))
            (J ∘ (sourceCoordinate L axis).symm))) := by
  rw [symbolicAssembly_specialize L anti axis J q unit, shiftedAssembly_rawJet]

end SKEFTHawking.ADW.FiniteDiracQuaternionSpecialization
