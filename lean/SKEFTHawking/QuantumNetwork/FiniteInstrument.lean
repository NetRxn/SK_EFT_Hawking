import SKEFTHawking.QuantumNetwork.FiniteMemoryPartialInteraction
import SKEFTHawking.QuantumNetwork.NegativityMonotoneGeneral
import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper

/-! Finite Kraus instruments. Branches are unnormalized positive matrices, including zero.
Normalization is a condition on the sum over every outcome and internal Kraus index. -/
namespace SKEFTHawking.QuantumNetwork
open Matrix
open scoped BigOperators ComplexOrder Kronecker

structure FiniteInstrument (ι : Type*) [Fintype ι] [DecidableEq ι] (o : ℕ) where
  count : ℕ
  operators : Fin o → Fin count → Matrix ι ι ℂ
  normalized : ∑ a, ∑ k, (operators a k)ᴴ * operators a k = 1

namespace FiniteInstrument
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {o : ℕ}

noncomputable def branch (I : FiniteInstrument ι o) (a : Fin o) (X : Matrix ι ι ℂ) :=
  krausMap (I.operators a) X

noncomputable def weight (I : FiniteInstrument ι o) (a : Fin o) (X : Matrix ι ι ℂ) : ℝ :=
  (I.branch a X).trace.re

theorem branch_posSemidef (I : FiniteInstrument ι o) (a : Fin o)
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : (I.branch a X).PosSemidef :=
  krausMap_posSemidef _ hX

theorem branch_add (I : FiniteInstrument ι o) (a : Fin o) (X Y : Matrix ι ι ℂ) :
    I.branch a (X+Y) = I.branch a X+I.branch a Y := krausMap_add _ _ _

theorem branch_smul (I : FiniteInstrument ι o) (a : Fin o) (c : ℂ) (X : Matrix ι ι ℂ) :
    I.branch a (c • X) = c • I.branch a X := krausMap_smul _ _ _

theorem branch_zero (I : FiniteInstrument ι o) (a : Fin o) : I.branch a 0 = 0 := by
  simp [branch, krausMap]

theorem weight_nonneg (I : FiniteInstrument ι o) (a : Fin o)
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : 0 ≤ I.weight a X :=
  (Complex.le_def.mp (I.branch_posSemidef a hX).trace_nonneg).1

theorem sum_trace (I : FiniteInstrument ι o) (X : Matrix ι ι ℂ) :
    ∑ a, (I.branch a X).trace = X.trace := by
  simp only [branch, krausMap, Matrix.trace_sum]
  have hc : ∀ a k, (I.operators a k * X * (I.operators a k)ᴴ).trace =
      ((I.operators a k)ᴴ * I.operators a k * X).trace :=
    fun a k => Matrix.trace_mul_cycle _ _ _
  simp_rw [hc, ← Matrix.trace_sum]
  congr 1
  simp_rw [← Finset.sum_mul]
  rw [I.normalized, Matrix.one_mul]

theorem sum_weight (I : FiniteInstrument ι o) (X : Matrix ι ι ℂ) :
    ∑ a, I.weight a X = X.trace.re := by
  simpa [weight] using congrArg Complex.re (I.sum_trace X)

theorem weight_le_trace (I : FiniteInstrument ι o) (a : Fin o)
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : I.weight a X ≤ X.trace.re := by
  rw [← I.sum_weight X]
  exact Finset.single_le_sum (fun b _ => I.weight_nonneg b hX) (Finset.mem_univ a)

/-- Explicit spectator lift, allowing unrelated finite system/environment dimensions. -/
noncomputable def lift (I : FiniteInstrument ι o) (ε : Type*) [Fintype ε] [DecidableEq ε] :
    FiniteInstrument (ι × ε) o where
  count := I.count
  operators a k := (I.operators a k) ⊗ₖ (1 : Matrix ε ε ℂ)
  normalized := by
    simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    simp_rw [sum_kronOne_general]
    rw [I.normalized, Matrix.one_kronecker_one]

/-- Complete positivity witnessed constructively at every finite spectator dimension. -/
theorem lift_branch_posSemidef (I : FiniteInstrument ι o) (ε : Type*) [Fintype ε] [DecidableEq ε]
    (a : Fin o) {X : Matrix (ι × ε) (ι × ε) ℂ} (hX : X.PosSemidef) :
    ((I.lift ε).branch a X).PosSemidef := (I.lift ε).branch_posSemidef a hX

/-- A normalized channel is a one-outcome instrument. -/
noncomputable def singleton {k : ℕ} (K : Fin k → Matrix ι ι ℂ) (hK : IsKrausChannel K) :
    FiniteInstrument ι 1 where
  count := k
  operators _ := K
  normalized := by simpa [IsKrausChannel] using hK

theorem singleton_branch {k : ℕ} (K : Fin k → Matrix ι ι ℂ) (hK : IsKrausChannel K)
    (X : Matrix ι ι ℂ) : (singleton K hK).branch 0 X = krausMap K X := rfl

noncomputable def identity : FiniteInstrument ι 1 :=
  singleton (fun _ : Fin 1 => (1 : Matrix ι ι ℂ)) (by simp [IsKrausChannel])

theorem identity_branch (X : Matrix ι ι ℂ) : (identity : FiniteInstrument ι 1).branch 0 X = X := by
  simp [identity, singleton, branch, krausMap]

noncomputable def reset : FiniteInstrument (Fin 2) 1 :=
  singleton FiniteMemoryProcess.resetKraus FiniteMemoryProcess.resetKraus_normalized

theorem reset_branch (X : Matrix (Fin 2) (Fin 2) ℂ) :
    reset.branch 0 X = krausMap FiniteMemoryProcess.resetKraus X := rfl

theorem lifted_reset_eq (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (reset.lift (Fin 2)).branch 0 X = FiniteMemoryProcess.resetSystem X := rfl

/-- Zero operators represent impossible outcomes without division by their probability. -/
theorem zero_outcome (I : FiniteInstrument ι o) (a : Fin o)
    (ha : ∀ k, I.operators a k = 0) (X : Matrix ι ι ℂ) : I.branch a X = 0 := by
  simp [branch, krausMap, ha]

/-- A projective computational-basis instrument. -/
noncomputable def computational : FiniteInstrument (Fin 2) 2 where
  count := 1
  operators a _ := FiniteMemoryProcess.basisState a
  normalized := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [FiniteMemoryProcess.basisState, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.one_apply]

/-- Outcome `b` prepares basis state `b`; the other outcome is impossible. -/
noncomputable def prepare (b : Fin 2) : FiniteInstrument (Fin 2) 2 where
  count := 2
  operators a k := if a = b then Matrix.single b k 1 else 0
  normalized := by
    ext i j
    fin_cases b <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single, Fin.sum_univ_two,
        Matrix.one_apply]

theorem prepare_other (b a : Fin 2) (hab : a ≠ b) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (prepare b).branch a X = 0 := by
  apply zero_outcome
  intro k
  simp [prepare, hab]

theorem prepare_trace (b : Fin 2) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ((prepare b).branch b X).trace = X.trace := by
  have h := (prepare b).sum_trace X
  have he : (∑ a, ((prepare b).branch a X).trace) = ((prepare b).branch b X).trace := by
    apply Finset.sum_eq_single b
    · intro a _ hab
      rw [prepare_other b a hab, Matrix.trace_zero]
    · simp
  rwa [he] at h

/-- Distinct continuations really prepare different physical states. -/
theorem prepare_state (b : Fin 2) :
    (prepare b).branch b (FiniteMemoryProcess.basisState 0) = FiniteMemoryProcess.basisState b := by
  simp only [branch, prepare, ite_true]
  ext i j
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [prepare, branch, krausMap, FiniteMemoryProcess.basisState, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single, Fin.sum_univ_two]

theorem lift_prepare_other (ε : Type*) [Fintype ε] [DecidableEq ε]
    (b a : Fin 2) (hab : a ≠ b) (X : Matrix (Fin 2 × ε) (Fin 2 × ε) ℂ) :
    ((prepare b).lift ε).branch a X = 0 := by
  apply zero_outcome
  intro k
  simp [lift, prepare, hab]

theorem lift_prepare_trace (ε : Type*) [Fintype ε] [DecidableEq ε]
    (b : Fin 2) (X : Matrix (Fin 2 × ε) (Fin 2 × ε) ℂ) :
    (((prepare b).lift ε).branch b X).trace = X.trace := by
  have h := ((prepare b).lift ε).sum_trace X
  have he : (∑ a, (((prepare b).lift ε).branch a X).trace) =
      (((prepare b).lift ε).branch b X).trace := by
    apply Finset.sum_eq_single b
    · intro a _ hab
      rw [lift_prepare_other ε b a hab, Matrix.trace_zero]
    · simp
  rwa [he] at h

end FiniteInstrument
end SKEFTHawking.QuantumNetwork
