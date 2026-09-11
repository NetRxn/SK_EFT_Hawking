import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Isomorphisms
import SKEFTHawking.QuantumNetwork.FiniteInstrument

/-! Finite complex positive kernels. The coefficient seminorm is derived from the
Hermitian positive semidefinite matrix. Its separation quotient removes exactly
zero-energy differences and has the induced, positive definite inner product.
No ambient reconstructed space is assumed. -/

noncomputable section
open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace SKEFTHawking.FinitePositiveKernel

variable {ι : Type*} [Fintype ι]

/-- A type synonym keeps the kernel seminorm separate from the usual function norm. -/
def Coefficients {K : Matrix ι ι ℂ} (_hK : K.PosSemidef) := ι → ℂ

instance {K : Matrix ι ι ℂ} (hK : K.PosSemidef) : AddCommGroup (Coefficients hK) :=
  inferInstanceAs (AddCommGroup (ι → ℂ))
instance {K : Matrix ι ι ℂ} (hK : K.PosSemidef) : Module ℂ (Coefficients hK) :=
  inferInstanceAs (Module ℂ (ι → ℂ))

/-- The sesquilinear extension of the kernel to finite coefficient vectors. -/
def pairing (K : Matrix ι ι ℂ) (x y : ι → ℂ) : ℂ :=
  star x ⬝ᵥ (K *ᵥ y)

/-- Positivity and Hermitian symmetry supply the entire seminorm construction. -/
@[reducible] def core (K : Matrix ι ι ℂ) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (Coefficients hK) where
  inner := pairing K
  conj_inner_symm x y := by
    change star (star y ⬝ᵥ (K *ᵥ x)) = star x ⬝ᵥ (K *ᵥ y)
    rw [← star_dotProduct, star_mulVec, hK.isHermitian.eq, dotProduct_mulVec]
  re_inner_nonneg x := (hK.dotProduct_mulVec_nonneg x).1
  add_left x y z := by
    unfold Coefficients at x y z
    change star (x + y) ⬝ᵥ (K *ᵥ z) = _
    simp [pairing, star_add, add_dotProduct]
  smul_left x y r := by
    unfold Coefficients at x y
    change star (r • x) ⬝ᵥ (K *ᵥ y) = _
    simp [pairing, star_smul, smul_dotProduct, smul_eq_mul]

section Reconstruction
variable (K : Matrix ι ι ℂ) (hK : K.PosSemidef)

local instance : PreInnerProductSpace.Core ℂ (Coefficients hK) := core K hK
local instance : SeminormedAddCommGroup (Coefficients hK) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
local instance : InnerProductSpace ℂ (Coefficients hK) := InnerProductSpace.ofCore (core K hK)

/-- The null-space quotient of the coefficient space. Its normed structure is
Mathlib's separation quotient of the kernel-derived seminorm. -/
def Space := SeparationQuotient (Coefficients hK)

instance : NormedAddCommGroup (Space K hK) :=
  inferInstanceAs (NormedAddCommGroup (SeparationQuotient (Coefficients hK)))
instance : InnerProductSpace ℂ (Space K hK) :=
  inferInstanceAs (InnerProductSpace ℂ (SeparationQuotient (Coefficients hK)))

/-- Send coefficients to their class modulo zero kernel energy. -/
def mk (x : Coefficients hK) : Space K hK := SeparationQuotient.mk x

/-- The quotient pairing is well-defined and recovers the coefficient form. -/
theorem inner_mk (x y : Coefficients hK) :
    ⟪mk K hK x, mk K hK y⟫_ℂ = pairing K x y := rfl

/-- Kernel vectors are the classes of the point masses. -/
def feature [DecidableEq ι] (i : ι) : Space K hK := mk K hK (Pi.single i 1)

/-- Every original matrix entry is an inner product in the constructed space. -/
theorem inner_feature [DecidableEq ι] (i j : ι) :
    ⟪feature K hK i, feature K hK j⟫_ℂ = K i j := by
  simp [feature, inner_mk, pairing, dotProduct, mulVec, Pi.single_apply]

/-- The quotient projection is linear. -/
def mkLinear : Coefficients hK →ₗ[ℂ] Space K hK :=
  (SeparationQuotient.mkCLM ℂ (Coefficients hK)).toLinearMap

/-- A coefficient vector vanishes in the quotient exactly when its energy is zero. -/
theorem mk_eq_zero_iff (x : Coefficients hK) :
    mk K hK x = 0 ↔ pairing K x x = 0 := by
  rw [← inner_mk K hK, inner_self_eq_zero]

/-- Equality of classes is precisely the null-space equivalence relation. -/
theorem mk_eq_mk_iff (x y : Coefficients hK) :
    mk K hK x = mk K hK y ↔ pairing K (x - y) (x - y) = 0 := by
  rw [← mk_eq_zero_iff K hK]
  change _ ↔ SeparationQuotient.mk (x - y) = 0
  rw [SeparationQuotient.mk_sub, sub_eq_zero]
  rfl

/-- The zero-energy vectors form a complex linear subspace. -/
def nullSpace : Submodule ℂ (Coefficients hK) := (mkLinear K hK).ker

theorem mem_nullSpace_iff (x : Coefficients hK) :
    x ∈ nullSpace K hK ↔ pairing K x x = 0 :=
  mk_eq_zero_iff K hK x

/-- Changing either representative by a null vector leaves the pairing unchanged. -/
theorem pairing_well_defined (x x' y y' : Coefficients hK)
    (hx : x - x' ∈ nullSpace K hK) (hy : y - y' ∈ nullSpace K hK) :
    pairing K x y = pairing K x' y' := by
  have hx' := (mk_eq_mk_iff K hK x x').mpr ((mem_nullSpace_iff K hK _).mp hx)
  have hy' := (mk_eq_mk_iff K hK y y').mpr ((mem_nullSpace_iff K hK _).mp hy)
  rw [← inner_mk K hK, ← inner_mk K hK, hx', hy']

/-- Every class is represented by finite coefficients. -/
theorem mk_surjective : Function.Surjective (mk K hK) :=
  SeparationQuotient.surjective_mk

/-- Null energy is equivalent to the usual matrix null-space condition. -/
theorem null_iff_mulVec_eq_zero [DecidableEq ι] (x : Coefficients hK) :
    pairing K x x = 0 ↔ K *ᵥ x = 0 := by
  constructor
  · intro hx
    have hz := (mk_eq_zero_iff K hK x).mpr hx
    apply funext
    intro i
    have hi : pairing K (Pi.single i 1) x = 0 := by
      rw [← inner_mk K hK, hz, inner_zero_right]
    simpa [pairing, dotProduct, Pi.single_apply] using hi
  · intro hx
    simp [pairing, hx]

/-- The topological construction is linearly equivalent to the algebraic null-space quotient. -/
def quotientEquiv : (Coefficients hK ⧸ nullSpace K hK) ≃ₗ[ℂ] Space K hK :=
  (mkLinear K hK).quotKerEquivOfSurjective (mk_surjective K hK)

instance : FiniteDimensional ℂ (Space K hK) := by
  letI : Module.Finite ℂ (Coefficients hK) :=
    inferInstanceAs (Module.Finite ℂ (ι → ℂ))
  exact Module.Finite.of_surjective (mkLinear K hK) (mk_surjective K hK)

instance : CompleteSpace (Space K hK) := FiniteDimensional.complete ℂ _

/-- Reconstruction uses at most one dimension per kernel index. -/
theorem finrank_le_card : Module.finrank ℂ (Space K hK) ≤ Fintype.card ι := by
  letI : Module.Finite ℂ (Coefficients hK) :=
    inferInstanceAs (Module.Finite ℂ (ι → ℂ))
  have h := LinearMap.finrank_le_finrank_of_surjective (f := mkLinear K hK)
    (mk_surjective K hK)
  exact h.trans_eq (Module.finrank_pi ℂ)

/-- The feature family generates every vector, not just a subspace of a larger space. -/
theorem exists_feature_sum [DecidableEq ι] (z : Space K hK) :
    ∃ c : ι → ℂ, z = ∑ i, c i • feature K hK i := by
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  refine ⟨x, ?_⟩
  let c : ι → ℂ := x
  have hx : x = ∑ i, (x : ι → ℂ) i • (Pi.single i 1 : Coefficients hK) := by
    apply funext
    intro j
    change c j = (∑ i, c i • Pi.single i (1 : ℂ)) j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    mk K hK x = mkLinear K hK (∑ i, c i • (Pi.single i 1 : Coefficients hK)) :=
      congrArg (mkLinear K hK) hx
    _ = ∑ i, mkLinear K hK (c i • (Pi.single i 1 : Coefficients hK)) :=
      map_sum (mkLinear K hK) _ _
    _ = ∑ i, c i • feature K hK i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (mkLinear K hK).map_smul (c i) (Pi.single i 1)

end Reconstruction

section Examples

/-- A rank-one kernel with two identical nonzero feature vectors. -/
def degenerate : Matrix (Fin 2) (Fin 2) ℂ := fun _ _ => 1

theorem degenerate_posSemidef : degenerate.PosSemidef := by
  have he : degenerate = Matrix.vecMulVec (star (fun _ : Fin 2 => (1 : ℂ)))
      (fun _ : Fin 2 => (1 : ℂ)) := by ext i j; simp [degenerate, Matrix.vecMulVec]
  rw [he]
  exact Matrix.posSemidef_vecMulVec_star_self _

theorem degenerate_nonzero : degenerate ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [degenerate] at this

/-- The nonzero vector (1,-1) has zero energy. -/
theorem degenerate_null : pairing degenerate ![1, -1] ![1, -1] = 0 := by
  norm_num [pairing, degenerate, dotProduct, mulVec, Fin.sum_univ_two]

theorem degenerate_difference_nonzero : (![1, -1] : Fin 2 → ℂ) ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num at this

/-- The quotient actually identifies distinct coefficient vectors. -/
theorem degenerate_class_zero :
    mk degenerate degenerate_posSemidef ![1, -1] = 0 :=
  (mk_eq_zero_iff _ _ _).mpr degenerate_null

/-- The reconstructed space is nevertheless nonzero. -/
theorem degenerate_feature_nonzero : feature degenerate degenerate_posSemidef 0 ≠ 0 := by
  intro h
  have hi := inner_feature degenerate degenerate_posSemidef 0 0
  rw [h, inner_zero_left] at hi
  norm_num [degenerate] at hi

/-- Positive diagonal entries alone do not imply positivity of a kernel. -/
def badDiagonal : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 2, 1]

theorem badDiagonal_isHermitian : badDiagonal.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [badDiagonal, Matrix.conjTranspose_apply]

theorem badDiagonal_diag (i : Fin 2) : badDiagonal i i = 1 := by
  fin_cases i <;> rfl

theorem badDiagonal_diag_pos (i : Fin 2) : 0 < badDiagonal i i := by
  rw [badDiagonal_diag]
  norm_num [Complex.lt_def]

theorem badDiagonal_energy : pairing badDiagonal ![1, -1] ![1, -1] = -2 := by
  norm_num [pairing, badDiagonal, dotProduct, mulVec, Fin.sum_univ_two]

theorem badDiagonal_not_posSemidef : ¬ badDiagonal.PosSemidef := by
  intro h
  have hq := h.dotProduct_mulVec_nonneg ![1, -1]
  change 0 ≤ pairing badDiagonal ![1, -1] ![1, -1] at hq
  rw [badDiagonal_energy] at hq
  norm_num [Complex.le_def] at hq

end Examples

section QuantumConsumer
variable [DecidableEq ι] {o : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The branch-state Gram kernel of probe columns after a finite quantum instrument.
Branches remain unnormalized, including impossible outcomes. -/
def branchGram (I : QuantumNetwork.FiniteInstrument ι o) (a : Fin o)
    (ρ : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  Bᴴ * I.branch a ρ * B

omit [DecidableEq κ] in
theorem branchGram_posSemidef (I : QuantumNetwork.FiniteInstrument ι o) (a : Fin o)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (B : Matrix ι κ ℂ) :
    (branchGram I a ρ B).PosSemidef :=
  (I.branch_posSemidef a hρ).conjTranspose_mul_mul_same B

/-- The reconstructed Gram vectors reproduce actual instrument branch-state probe pairings. -/
theorem branchGram_reconstruction (I : QuantumNetwork.FiniteInstrument ι o) (a : Fin o)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (B : Matrix ι κ ℂ) (i j : κ) :
    ⟪feature _ (branchGram_posSemidef I a hρ B) i,
      feature _ (branchGram_posSemidef I a hρ B) j⟫_ℂ =
        star (fun r => B r i) ⬝ᵥ (I.branch a ρ *ᵥ (fun r => B r j)) := by
  rw [inner_feature]
  simp only [branchGram, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, mulVec,
    Pi.star_apply]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

end QuantumConsumer
/-! A finite reflected-kernel specialization. Reflection positivity below is a
full sesquilinear-form condition on the positive sector. No time evolution,
Euclidean-field reconstruction, or Osterwalder-Schrader dynamics is asserted. -/
section ReflectedKernel

variable {X : Type*} [Fintype X]

/-- Ambient covariance data and an embedded positive sector. The reflection is
an actual involution; positivity is a separate condition on the reflected kernel. -/
structure ReflectionData (X ι : Type*) [Fintype X] [Fintype ι] where
  theta : X → X
  involutive : Function.Involutive theta
  positiveSector : ι ↪ X
  covariance : Matrix X X ℂ

namespace ReflectionData

/-- Reflect the first covariance argument and restrict both arguments to the sector. -/
def kernel (R : ReflectionData X ι) : Matrix ι ι ℂ :=
  fun i j => R.covariance (R.theta (R.positiveSector i)) (R.positiveSector j)

/-- Reflection positivity includes Hermitian symmetry and nonnegativity for every
complex coefficient vector, not merely nonnegative diagonal entries. -/
def Positive (R : ReflectionData X ι) : Prop := R.kernel.PosSemidef

theorem positive_iff (R : ReflectionData X ι) : R.Positive ↔
    R.kernel.IsHermitian ∧ ∀ c : ι → ℂ,
      0 ≤ ∑ i, ∑ j, star (c i) *
        R.covariance (R.theta (R.positiveSector i)) (R.positiveSector j) * c j := by
  rw [Positive, Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [kernel, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

/-- The finite reflected space is constructed from the null quotient above. -/
abbrev Reconstructed (R : ReflectionData X ι) (hR : R.Positive) := Space R.kernel hR

/-- The constructed sector vectors recover reflected covariance values. -/
theorem inner_reconstructed [DecidableEq ι] (R : ReflectionData X ι) (hR : R.Positive)
    (i j : ι) :
    ⟪feature R.kernel hR i, feature R.kernel hR j⟫_ℂ =
      R.covariance (R.theta (R.positiveSector i)) (R.positiveSector j) :=
  inner_feature R.kernel hR i j

end ReflectionData

/-- Two finite sectors exchanged by reflection, with a nonzero constant covariance. -/
def twoSectorReflection : ReflectionData (Bool × Fin 2) (Fin 2) where
  theta x := (!x.1, x.2)
  involutive := by
    intro x
    rcases x with ⟨b, i⟩
    cases b <;> rfl
  positiveSector := ⟨fun i => (false, i), by
    intro i j h
    exact congrArg Prod.snd h⟩
  covariance _ _ := 1

theorem twoSectorReflection_nonidentity : twoSectorReflection.theta ≠ id := by
  intro h
  have hh := congrFun h (false, 0)
  simp [twoSectorReflection] at hh

/-- The embedded sector and its reflection are disjoint in this concrete model. -/
theorem twoSectorReflection_disjoint (i j : Fin 2) :
    twoSectorReflection.theta (twoSectorReflection.positiveSector i) ≠
      twoSectorReflection.positiveSector j := by
  simp [twoSectorReflection]

/-- The reflected kernel is the previously verified nonzero degenerate kernel. -/
theorem twoSectorReflection_kernel : twoSectorReflection.kernel = degenerate := rfl

theorem twoSectorReflection_positive : twoSectorReflection.Positive := by
  change twoSectorReflection.kernel.PosSemidef
  rw [twoSectorReflection_kernel]
  exact degenerate_posSemidef

/-- Explicit vectors in the reflected null quotient have the prescribed unit pairing. -/
theorem twoSectorReflection_pairing (i j : Fin 2) :
    ⟪feature _ twoSectorReflection_positive i,
      feature _ twoSectorReflection_positive j⟫_ℂ = 1 :=
  ReflectionData.inner_reconstructed twoSectorReflection twoSectorReflection_positive i j

/-- A nonzero feature survives reflection reconstruction despite the null direction. -/
theorem twoSectorReflection_feature_nonzero :
    feature _ twoSectorReflection_positive 0 ≠ 0 := by
  intro h
  have hi := twoSectorReflection_pairing 0 0
  rw [h, inner_zero_left] at hi
  norm_num at hi

theorem twoSectorReflection_null :
    mk _ twoSectorReflection_positive ![1, -1] = 0 := by
  apply (mk_eq_zero_iff _ _ _).mpr
  change pairing degenerate ![1, -1] ![1, -1] = 0
  exact degenerate_null

end ReflectedKernel

end SKEFTHawking.FinitePositiveKernel
