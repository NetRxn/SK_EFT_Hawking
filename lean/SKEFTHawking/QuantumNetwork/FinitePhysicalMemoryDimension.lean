import SKEFTHawking.QuantumNetwork.FiniteAdaptiveKrausRealization
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basis

/-!
# The complete retained carrier at a common experimental cut

The carrier `S × E` includes every record accessible to a suffix, including
classical labels, controller state, seeds and retained ancillas. A suffix is
indexed by its commanded experiment, never by the prefix label. The actual
append semantics supplies the probability matrix. Its complex rank bound is
derived by expanding the unnormalized prefix states in matrix units.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FinitePhysicalMemoryDimension
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open scoped BigOperators ComplexOrder

variable {S E I J : Type*} [Fintype S] [DecidableEq S]
  [Fintype E] [DecidableEq E] {o : ℕ}

/-- Actual prefix and suffix trees sharing one complete retained carrier.
The suffix may adapt to its own outcomes, but has no free prefix-label input.
Lengths may differ between commands; any readable position record belongs to
the carrier. No factorization or rank bound is a field of this structure. -/
structure CommonCut (S E I J : Type*) [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] (o : ℕ) where
  initial : Matrix (S × E) (S × E) ℂ
  density : IsDensityOperator initial
  prefixLength : J → ℕ
  prefixTree : (j : J) → Tree S E o (prefixLength j)
  prefixHistory : (j : J) → History o (prefixLength j)
  suffixLength : I → ℕ
  suffixTree : (i : I) → Tree S E o (suffixLength i)
  suffixHistory : (i : I) → History o (suffixLength i)

namespace CommonCut
variable (C : CommonCut S E I J o)

def prefixState (j : J) : Matrix (S × E) (S × E) ℂ :=
  run S E o (C.prefixTree j) (C.prefixHistory j) C.initial

/-- Trace of the actual suffix branch, complex-linear on all matrices. -/
def suffixFunctional (i : I) : Matrix (S × E) (S × E) ℂ →ₗ[ℂ] ℂ where
  toFun X := (run S E o (C.suffixTree i) (C.suffixHistory i) X).trace
  map_add' X Y := by rw [run_add, Matrix.trace_add]
  map_smul' c X := by rw [run_smul, Matrix.trace_smul]; rfl

/-- Joint weights are defined by actual appended trees, without conditioning. -/
def probability : Matrix I J ℝ := fun i j =>
  weight S E o (appendTree (C.prefixTree j) (fun _ => C.suffixTree i))
    (appendHistory (C.prefixHistory j) (C.suffixHistory i)) C.initial

theorem prefixState_posSemidef (j : J) : (C.prefixState j).PosSemidef :=
  run_posSemidef S E o _ _ C.density.1

theorem probability_nonneg (i : I) (j : J) : 0 ≤ C.probability i j :=
  weight_nonneg S E o _ _ C.density.1

theorem probability_le_one (i : I) (j : J) : C.probability i j ≤ 1 :=
  weight_le_one S E o _ _ C.density

/-- Positivity identifies the real probability with the complex trace.
Taking the real part is used only here, not as a complex-linear map. -/
theorem complex_probability (i : I) (j : J) :
    (C.probability i j : ℂ) = C.suffixFunctional i (C.prefixState j) := by
  have h := run_posSemidef S E o (C.suffixTree i) (C.suffixHistory i)
    (C.prefixState_posSemidef j)
  change ((run S E o _ _ C.initial).trace.re : ℂ) = _
  rw [append_run]
  apply Complex.ext
  · rfl
  · exact (Complex.le_def.mp h.trace_nonneg).2

end CommonCut

/-- Matrix units span all complex matrices, including on the empty carrier. -/
theorem matrix_unit_expansion {R : Type*} [Fintype R] [DecidableEq R]
    (X : Matrix R R ℂ) :
    X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, ite_and]
  simp

namespace CommonCut
variable [Fintype I] [Fintype J] (C : CommonCut S E I J o)

def suffixCoordinates : Matrix I ((S × E) × (S × E)) ℂ := fun i ab =>
  C.suffixFunctional i (Matrix.single ab.1 ab.2 1)

def prefixCoordinates : Matrix ((S × E) × (S × E)) J ℂ := fun ab j =>
  C.prefixState j ab.1 ab.2

omit [Fintype I] [Fintype J] in
/-- The factorization follows from append, positivity and matrix-unit expansion. -/
theorem probability_factorization :
    (C.probability.map Complex.ofReal) = C.suffixCoordinates * C.prefixCoordinates := by
  ext i j
  rw [Matrix.map_apply, C.complex_probability]
  conv_lhs => rw [matrix_unit_expansion (C.prefixState j)]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mul_apply,
    Fintype.sum_prod_type, suffixCoordinates, prefixCoordinates]
  simp only [mul_comm]

omit [Fintype I] in
/-- Complex dimension is the square of the complete retained Hilbert dimension. -/
theorem probability_rank_le :
    (C.probability.map Complex.ofReal).rank ≤ (Fintype.card (S × E)) ^ 2 := by
  rw [C.probability_factorization]
  calc
    (C.suffixCoordinates * C.prefixCoordinates).rank ≤ C.suffixCoordinates.rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card ((S × E) × (S × E)) := Matrix.rank_le_card_width _
    _ = (Fintype.card (S × E)) ^ 2 := by simp [pow_two]

/-- A nonsingular real minor remains nonsingular over the complex numbers. -/
theorem dimension_bound_of_det_ne_zero [DecidableEq I]
    (C : CommonCut S E I I o) (h : C.probability.det ≠ 0) :
    Fintype.card I ≤ (Fintype.card (S × E)) ^ 2 := by
  have hc : (C.probability.map Complex.ofReal).det ≠ 0 := by
    change (Complex.ofRealHom.mapMatrix C.probability).det ≠ 0
    rw [← Complex.ofRealHom.map_det]
    change (C.probability.det : ℂ) ≠ 0
    simpa only [ne_eq, Complex.ofReal_eq_zero] using h
  have hu : IsUnit (C.probability.map Complex.ofReal) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hc)
  rw [← Matrix.rank_of_isUnit _ hu]
  exact C.probability_rank_le

theorem dimension_ge_three (C : CommonCut S E (Fin 5) (Fin 5) o)
    (h : C.probability.det ≠ 0) : 3 ≤ Fintype.card (S × E) := by
  have hd := dimension_bound_of_det_ne_zero C h
  have : 5 ≤ (Fintype.card (S × E)) ^ 2 := by simpa using hd
  by_contra hn
  have hl : Fintype.card (S × E) ≤ 2 := by omega
  interval_cases hcard : Fintype.card (S × E) <;> norm_num [hcard] at this

end CommonCut
end SKEFTHawking.QuantumNetwork.FinitePhysicalMemoryDimension
