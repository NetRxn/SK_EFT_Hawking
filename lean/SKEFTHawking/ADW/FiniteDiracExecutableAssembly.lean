import SKEFTHawking.ADW.FiniteGrassmannComplementaryMinor
import SKEFTHawking.ADW.FiniteGrassmannShiftedDiracBerezin
import SKEFTHawking.ADW.FiniteDeterminantRawJet

/-!
# Executable assembly of the original finite Dirac matrix

The four Python block increments scatter additively onto the mixed-radix matrix indices.
The scalar comparison evaluates link matrices and auxiliary weights before scattering.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace SKEFTHawking.ADW.FiniteDiracExecutableAssembly

open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin

/-- The forward coordinate is the Python successor followed by reduction modulo the extent. -/
theorem forward_digit (L : Torus) (x : Site L) (μ : Fin 4) :
    (forward L x μ μ).val = ((x μ).val + 1) % L.extent μ := by
  simp only [forward, Pi.add_apply, Pi.single_eq_same]
  rw [← ZMod.natCast_zmod_val (x μ), ← Nat.cast_one, ← Nat.cast_add, ZMod.val_natCast]
  simp only [ZMod.natCast_zmod_val]

/-- The backward coordinate is the Python predecessor reduced modulo the positive extent. -/
theorem backward_digit (L : Torus) (x : Site L) (μ : Fin 4) :
    (backward L x μ μ).val = ((x μ).val + L.extent μ - 1) % L.extent μ := by
  simp only [backward, Pi.sub_apply, Pi.single_eq_same]
  have h : 1 ≤ (x μ).val + L.extent μ := by have := L.positive μ; omega
  rw [← ZMod.val_natCast, Nat.cast_sub h, Nat.cast_add, ZMod.natCast_zmod_val,
    ZMod.natCast_self, add_zero, Nat.cast_one]

/-- Stepping in one direction leaves every other digit fixed. -/
theorem step_other_digit (L : Torus) (x : Site L) {μ ν : Fin 4} (h : ν ≠ μ) :
    (forward L x μ ν).val = (x ν).val ∧ (backward L x μ ν).val = (x ν).val := by
  simp [forward, backward, Pi.single_eq_of_ne h]

private theorem zero_forward_iff_wrap (L : Torus) (x : Site L) (μ : Fin 4) :
    (forward L x μ μ).val = 0 ↔ L.extent μ ≤ (x μ).val + 1 := by
  rw [forward_digit]
  have hv := ZMod.val_lt (x μ)
  by_cases h : L.extent μ ≤ (x μ).val + 1
  · have he : (x μ).val + 1 = L.extent μ := by omega
    simp [he]
  · rw [Nat.mod_eq_of_lt (by omega : (x μ).val + 1 < L.extent μ)]
    simp [h]

/-- The backward Python wrap test is the forward wrap test at the preceding link's anchor. -/
theorem backward_wrap_iff (L : Torus) (x : Site L) (μ : Fin 4) :
    (x μ).val = 0 ↔ L.extent μ ≤ (backward L x μ μ).val + 1 := by
  rw [← zero_forward_iff_wrap, forward_backward]

/-- At extent one both traversals wrap, including when their endpoints coincide. -/
theorem wraps_at_unit_extent (L : Torus) (x : Site L) (μ : Fin 4) (h : L.extent μ = 1) :
    L.extent μ ≤ (x μ).val + 1 ∧ (x μ).val = 0 := by
  have hv := ZMod.val_lt (x μ)
  omega

/-- The Python metric gamma-axis labels 0,1,2,3 select source labels 3,0,1,2. -/
def metricAxis : Fin 4 ≃ Fin 4 where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide
  right_inv := by decide

/-- A Python endpoint block contributes its weighted entry if both endpoints match. -/
private def scatter (L : Torus) (y z : Site L) (c : ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ)
    (p q : Fermion L) : ℂ :=
  if p.1 = y ∧ q.1 = z then c * A p.2 q.2 else 0

/-- Antiperiodic axes put a real minus sign on the anchored boundary link. -/
def forwardSign (L : Torus) (anti : Fin 4 → Bool) (x : Site L) (μ : Fin 4) : ℂ :=
  if anti μ = true ∧ L.extent μ ≤ (x μ).val + 1 then -1 else 1

/-- The Python negative step wraps exactly when the current digit is zero. -/
def backwardSign (L : Torus) (anti : Fin 4 → Bool) (x : Site L) (μ : Fin 4) : ℂ :=
  if anti μ = true ∧ (x μ).val = 0 then -1 else 1

theorem backwardSign_eq_forwardSign (L : Torus) (anti : Fin 4 → Bool) (x : Site L) (μ : Fin 4) :
    backwardSign L anti x μ = forwardSign L anti (backward L x μ) μ := by
  simp only [backwardSign, forwardSign, backward_wrap_iff]

/-- The central minus sign acts on both fundamental Spin(4) blocks. -/
def twistedLinks (L : Torus) (anti : Fin 4 → Bool) (U : Links L) : Links L :=
  fun x μ ↦ if anti μ = true ∧ L.extent μ ≤ (x μ).val + 1
    then (minusIdentitySU2, minusIdentitySU2) * U x μ else U x μ

private theorem dirac_central_minus (U : Spin4) :
    dirac ((minusIdentitySU2, minusIdentitySU2) * U) = -dirac U := by
  ext i j
  obtain ⟨i, rfl⟩ := diracIndex.surjective i
  obtain ⟨j, rfl⟩ := diracIndex.surjective j
  cases i <;> cases j <;>
    simp [dirac, Matrix.reindex_apply, Matrix.submatrix, minusIdentitySU2, Matrix.neg_apply]

/-- At each anchor the twisted group link implements the real step sign on its Dirac block. -/
theorem dirac_twistedLinks (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (x : Site L) (μ : Fin 4) :
    dirac (twistedLinks L anti U x μ) = forwardSign L anti x μ • dirac (U x μ) := by
  by_cases h : anti μ = true ∧ L.extent μ ≤ (x μ).val + 1
  · simp [twistedLinks, forwardSign, h, dirac_central_minus]
  · simp [twistedLinks, forwardSign, h]

private theorem star_forwardSign (L : Torus) (anti : Fin 4 → Bool) (x : Site L) (μ : Fin 4) :
    star (forwardSign L anti x μ) = forwardSign L anti x μ := by
  unfold forwardSign
  split <;> simp

/-- The four independently added Python block increments at a fixed coframe coordinate. -/
def assembledCoframe (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (x : Site L) (μ C : Fin 4) (p q : Fermion L) : ℂ :=
  let f := forward L x μ
  let b := backward L x μ
  let sf := forwardSign L anti x μ
  let sb := backwardSign L anti x μ
  let uf := dirac (U x μ)
  let ub := dirac (U b μ)
  let g := gamma C
  scatter L x f (sf / 4) (g * ufᴴ) p q +
    scatter L f x (-sf / 4) (uf * g) p q +
    scatter L x b (-sb / 4) (g * ub) p q +
    scatter L b x (sb / 4) (ubᴴ * g) p q

/-- Scattering retains all four summands even when endpoints or anchors coincide. -/
theorem assembledCoframe_eq_hopping (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (x : Site L) (μ C : Fin 4) (p q : Fermion L) :
    assembledCoframe L anti U x μ C p q =
      hopping L (twistedLinks L anti U) x μ C p.1 q.1 p.2 q.2 := by
  simp only [assembledCoframe, scatter, backwardSign_eq_forwardSign, hopping,
    dirac_twistedLinks, Matrix.conjTranspose_smul, star_forwardSign,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply, smul_eq_mul, Matrix.ite_apply, Matrix.zero_apply]
  split <;> split <;> split <;> split <;> ring

/-- Relabel only the gamma axis. The lattice step direction stays in the original slot. -/
def sourceCoordinate (L : Torus) (axis : Fin 4 ≃ Fin 4) : Auxiliary L ≃ Auxiliary L :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) axis)

/-- Scatter each weighted coframe onto the Python flat row and column indices. -/
def assembleDirac {R : Type*} [CommRing R] (coeff : ℂ →+* R)
    (L : Torus) (anti : Fin 4 → Bool) (U : Links L) (axis : Fin 4 ≃ Fin 4)
    (weight : Auxiliary L → R) : Matrix (Fin (4 * volume L)) (Fin (4 * volume L)) R :=
  fun i j ↦ ∑ a, weight a * coeff (assembledCoframe L anti U a.1 a.2.1 (axis a.2.2)
    ((executableFermionIndex L).symm i) ((executableFermionIndex L).symm j))

/-- Matrix reindexing and source-label transport recover the original global matrix. -/
theorem assembleDirac_eq_global (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (axis : Fin 4 ≃ Fin 4) (weight : Auxiliary L → ℂ) :
    assembleDirac (RingHom.id ℂ) L anti U axis weight =
      Matrix.reindex (executableFermionIndex L) (executableFermionIndex L)
        (globalMatrix L (twistedLinks L anti U) (weight ∘ (sourceCoordinate L axis).symm)) := by
  ext i j
  simp only [assembleDirac, RingHom.id_apply, assembledCoframe_eq_hopping, Matrix.reindex_apply,
    Matrix.submatrix, globalMatrix]
  apply Finset.sum_equiv (sourceCoordinate L axis)
  · simp
  · intro a _
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rfl

/-- Fixed-link polynomial assembly with a source shift in each auxiliary coordinate. -/
def shiftedAssembly (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ) :
    Matrix (Fin (4 * volume L)) (Fin (4 * volume L)) (MvPolynomial (Auxiliary L) ℂ) :=
  assembleDirac MvPolynomial.C L anti U axis (fun a ↦ MvPolynomial.X a + MvPolynomial.C (J a))

/-- Evaluating the shifted assembly gives the original flat matrix with weights h+J. -/
theorem shiftedAssembly_eval (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (axis : Fin 4 ≃ Fin 4) (J h : Auxiliary L → ℂ) :
    (MvPolynomial.eval h).mapMatrix (shiftedAssembly L anti U axis J) =
      Matrix.reindex (executableFermionIndex L) (executableFermionIndex L)
        (globalMatrix L (twistedLinks L anti U)
          ((fun a ↦ h a + J a) ∘ (sourceCoordinate L axis).symm)) := by
  rw [← assembleDirac_eq_global]
  ext i j
  change MvPolynomial.eval h (shiftedAssembly L anti U axis J i j) = _
  simp [shiftedAssembly, assembleDirac]

/-- The bitmask program evaluates the original finite determinant without an inverse. -/
theorem assembledDet_eq_global (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (axis : Fin 4 ≃ Fin 4) (weight : Auxiliary L → ℂ) :
    FiniteDeterminantSubsetDP.maskSubsetDP
        (fun i j ↦ if h : i < 4 * volume L
          then assembleDirac (RingHom.id ℂ) L anti U axis weight ⟨i, h⟩ j else 0)
        (4 * volume L) ((1 <<< (4 * volume L)) - 1) =
      (globalMatrix L (twistedLinks L anti U) (weight ∘ (sourceCoordinate L axis).symm)).det := by
  rw [FiniteDeterminantSubsetDP.maskSubsetDP_eq_det, assembleDirac_eq_global,
    Matrix.det_reindex_self]

/-- Renaming the auxiliary variables transports the source determinant to the executable order. -/
theorem shiftedAssembly_det (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ) :
    (shiftedAssembly L anti U axis J).det =
      MvPolynomial.rename (sourceCoordinate L axis).symm
        (shiftedDiracDetAtLink L (twistedLinks L anti U)
          (J ∘ (sourceCoordinate L axis).symm)) := by
  apply MvPolynomial.funext
  intro h
  rw [(MvPolynomial.eval h).map_det, shiftedAssembly_eval, Matrix.det_reindex_self,
    MvPolynomial.eval_rename, shiftedDiracDetAtLink_eval]
  rfl

/-- The raw determinant program computes the same selected derivatives of the shifted source
polynomial, including a repeated coordinate and both gamma-axis conventions. -/
theorem shiftedAssembly_rawJet (L : Torus) (anti : Fin 4 → Bool) (U : Links L)
    (axis : Fin 4 ≃ Fin 4) (J h : Auxiliary L → ℂ) (a b : Auxiliary L) :
    FiniteDeterminantRawJet.determinantJet
        ((FiniteDeterminantRawJet.polynomialJet h a b).mapMatrix
          (shiftedAssembly L anti U axis J)) =
      FiniteDeterminantRawJet.polynomialJet h a b
        (MvPolynomial.rename (sourceCoordinate L axis).symm
          (shiftedDiracDetAtLink L (twistedLinks L anti U)
            (J ∘ (sourceCoordinate L axis).symm))) := by
  rw [FiniteDeterminantRawJet.determinantJet_polynomial, shiftedAssembly_det]

end SKEFTHawking.ADW.FiniteDiracExecutableAssembly
