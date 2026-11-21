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

variable {q : ℕ}

private noncomputable def relabelOperator (I : FiniteInstrument ι o) (f : Fin o → Fin q)
    (b : Fin q) (j : Fin o × Fin I.count) : Matrix ι ι ℂ :=
  if f j.1 = b then I.operators j.1 j.2 else 0

private theorem sum_relabelOperator_gram (I : FiniteInstrument ι o) (f : Fin o → Fin q)
    (j : Fin o × Fin I.count) :
    (∑ b, (relabelOperator I f b j)ᴴ * relabelOperator I f b j) =
      (I.operators j.1 j.2)ᴴ * I.operators j.1 j.2 := by
  calc
    _ = ∑ b : Fin q, if f j.1 = b then
        (I.operators j.1 j.2)ᴴ * I.operators j.1 j.2 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : f j.1 = b <;> simp [relabelOperator, h]
    _ = _ := by simp [Finset.sum_ite_eq]

/-- Report a function of the actual outcome while retaining each Kraus alternative. -/
noncomputable def relabel (I : FiniteInstrument ι o) (f : Fin o → Fin q) : FiniteInstrument ι q where
  count := o * I.count
  operators b k := relabelOperator I f b (finProdFinEquiv.symm k)
  normalized := by
    change (∑ b : Fin q, ∑ k : Fin (o * I.count),
      (relabelOperator I f b (finProdFinEquiv.symm k))ᴴ *
        relabelOperator I f b (finProdFinEquiv.symm k)) = 1
    have reindex (b : Fin q) :=
      (finProdFinEquiv (m := o) (n := I.count)).symm.sum_comp
        (fun j => (relabelOperator I f b j)ᴴ * relabelOperator I f b j)
    simp_rw [reindex]
    rw [Finset.sum_comm]
    simp only [sum_relabelOperator_gram, Fintype.sum_prod_type, I.normalized]

/-- A reported branch is the sum of the original branches in its fiber. -/
theorem relabel_branch (I : FiniteInstrument ι o) (f : Fin o → Fin q) (b : Fin q)
    (X : Matrix ι ι ℂ) :
    (I.relabel f).branch b X = ∑ a ∈ Finset.univ.filter (fun a => f a = b), I.branch a X := by
  change (∑ k : Fin (o * I.count),
    relabelOperator I f b (finProdFinEquiv.symm k) * X *
      (relabelOperator I f b (finProdFinEquiv.symm k))ᴴ) = _
  rw [(finProdFinEquiv (m := o) (n := I.count)).symm.sum_comp
    (fun j => relabelOperator I f b j * X * (relabelOperator I f b j)ᴴ),
      Fintype.sum_prod_type, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp [relabelOperator, h, branch, krausMap]

theorem relabel_lift_branch (I : FiniteInstrument ι o) (f : Fin o → Fin q) (b : Fin q)
    (A : Type*) [Fintype A] [DecidableEq A] (X : Matrix (ι × A) (ι × A) ℂ) :
    ((I.relabel f).lift A).branch b X =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), (I.lift A).branch a X := by
  rw [← relabel_branch]
  unfold branch krausMap
  apply Finset.sum_congr rfl
  intro k _
  let j : Fin o × Fin I.count := finProdFinEquiv.symm k
  have hop : (((I.relabel f).lift A).operators b k) =
      (((I.lift A).relabel f).operators b k) := by
    change (relabelOperator I f b j) ⊗ₖ (1 : Matrix A A ℂ) =
      relabelOperator (I.lift A) f b j
    by_cases h : f j.1 = b <;> simp [relabelOperator, h, lift]
  rw [hop]

/-- Two successively reported labels have the same branches as their composition. -/
theorem relabel_relabel_branch {r : ℕ} (I : FiniteInstrument ι o) (f : Fin o → Fin q)
    (g : Fin q → Fin r) (c : Fin r) (X : Matrix ι ι ℂ) :
    ((I.relabel f).relabel g).branch c X = (I.relabel (g ∘ f)).branch c X := by
  simp only [relabel_branch, Finset.sum_filter, Function.comp_apply]
  calc
    _ = ∑ b : Fin q, ∑ a : Fin o, if f a = b then
        if g b = c then I.branch a X else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : g b = c
      · simp only [hb, if_true]
      · simp [hb]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

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

section Contraction

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

omit [DecidableEq ι] in
private theorem star_dot_self_eq_norm_sq (x : ι → ℂ) :
    star x ⬝ᵥ x = ((‖(EuclideanSpace.equiv ι ℂ).symm x‖ ^ 2 : ℝ) : ℂ) := by
  let v := (EuclideanSpace.equiv ι ℂ).symm x
  change star v.ofLp ⬝ᵥ v.ofLp = ((‖v‖ ^ 2 : ℝ) : ℂ)
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_pow]
  rfl

private theorem defect_nonneg (K : Matrix ι ι ℂ) (hK : ‖K‖ ≤ 1) : 0 ≤ 1 - Kᴴ * K := by
  apply Matrix.PosSemidef.nonneg
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (Matrix.posSemidef_conjTranspose_mul_self K).isHermitian) ?_
  intro x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (star x) Kᴴ (K *ᵥ x), Matrix.vecMul_conjTranspose, star_star]
  rw [star_dot_self_eq_norm_sq x, star_dot_self_eq_norm_sq (K *ᵥ x), ← Complex.ofReal_sub]
  let v := (EuclideanSpace.equiv ι ℂ).symm x
  have hv := (K.l2_opNorm_mulVec v).trans (mul_le_of_le_one_left (norm_nonneg v) hK)
  apply Complex.zero_le_real.mpr
  exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hv 2)

private theorem effect_add_sqrt_defect_gram (A : Matrix ι ι ℂ) (hA : 0 ≤ 1 - A) :
    A + star (CFC.sqrt (1 - A)) * CFC.sqrt (1 - A) = 1 := by
  rw [(CFC.sqrt_nonneg (1 - A)).star_eq, CFC.sqrt_mul_sqrt_self _ hA]
  abel

/-- Complete a contraction to a two-outcome instrument whose success
operator is the contraction itself. -/
noncomputable def ofContraction (K : Matrix ι ι ℂ) (hK : ‖K‖ ≤ 1) :
    FiniteInstrument ι 2 where
  count := 1
  operators a _ := ![K, CFC.sqrt (1 - Kᴴ * K)] a
  normalized := by
    classical
    simp only [Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    change Kᴴ * K + star (CFC.sqrt (1 - Kᴴ * K)) * CFC.sqrt (1 - Kᴴ * K) = 1
    exact effect_add_sqrt_defect_gram (Kᴴ * K) (defect_nonneg K hK)

/-- The success flag uses the exact operator supplied by the caller. -/
theorem ofContraction_success_operator (K : Matrix ι ι ℂ) (hK : ‖K‖ ≤ 1) :
    (ofContraction K hK).operators 0 = fun _ => K := rfl

/-- The unnormalized success branch acts by the specified Kraus operator. -/
theorem ofContraction_success_branch (K : Matrix ι ι ℂ) (hK : ‖K‖ ≤ 1)
    (X : Matrix ι ι ℂ) : (ofContraction K hK).branch 0 X = K * X * Kᴴ := by
  simp [ofContraction, branch, krausMap]

/-- Add a failure flag to a finite family of selected Kraus operators
whose total effect is bounded by the identity. -/
noncomputable def completeSelectedKraus {k : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) ≤ 1) : FiniteInstrument ι 2 where
  count := k + 1
  operators a := if a = 0 then Fin.cases 0 K else
    Fin.cases (CFC.sqrt (1 - ∑ i, (K i)ᴴ * K i)) (fun _ => 0)
  normalized := by
    classical
    rw [Fin.sum_univ_two]
    simp only [if_true, if_neg (by decide : (1 : Fin 2) ≠ 0), Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, Matrix.conjTranspose_zero, Matrix.zero_mul, zero_add,
      Finset.sum_const_zero, add_zero]
    let A : Matrix ι ι ℂ := ∑ i, (K i)ᴴ * K i
    change A + star (CFC.sqrt (1 - A)) * CFC.sqrt (1 - A) = 1
    exact effect_add_sqrt_defect_gram A (sub_nonneg.mpr hK)

/-- The success flag keeps all the chosen Kraus terms. -/
theorem completeSelectedKraus_success_branch {k : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) ≤ 1) (X : Matrix ι ι ℂ) :
    (completeSelectedKraus K hK).branch 0 X = krausMap K X := by
  change (∑ j : Fin (k + 1), (Fin.cases 0 K j) * X * (Fin.cases 0 K j)ᴴ) = krausMap K X
  rw [Fin.sum_univ_succ]
  simp [krausMap]

/-- Complete the dephased timing branch using its two half-scaled arm operators. -/
noncomputable def halfArmInstrument (E L : Matrix ι ι ℂ) (hE : ‖E‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    FiniteInstrument ι 2 := completeSelectedKraus ![(1 / 2 : ℂ) • E, (1 / 2 : ℂ) • L] (by
  rw [Fin.sum_univ_two]
  change ((1 / 2 : ℂ) • E)ᴴ * ((1 / 2 : ℂ) • E) +
    ((1 / 2 : ℂ) • L)ᴴ * ((1 / 2 : ℂ) • L) ≤ 1
  apply sub_nonneg.mp
  have hE' := (defect_nonneg E hE).posSemidef
  have hL' := (defect_nonneg L hL).posSemidef
  have hQuarter : (0 : ℂ) ≤ (1 / 4 : ℂ) := by
    convert Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 4 by norm_num) using 1
    norm_num
  have hHalf : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
    convert Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num) using 1
    norm_num
  have h := ((hE'.smul hQuarter).add (hL'.smul hQuarter)).add
    ((Matrix.PosSemidef.one : (1 : Matrix ι ι ℂ).PosSemidef).smul hHalf)
  have he (A : Matrix ι ι ℂ) :
      ((1 / 2 : ℂ) • A)ᴴ * ((1 / 2 : ℂ) • A) = (1 / 4 : ℂ) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    simp
    ring
  rw [he, he]
  apply Matrix.PosSemidef.nonneg
  convert h using 1
  module)

/-- The selected outcome keeps the two arm densities as separate Kraus terms. -/
theorem halfArmInstrument_success_branch (E L X : Matrix ι ι ℂ) (hE : ‖E‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    (halfArmInstrument E L hE hL).branch 0 X =
      (1 / 4 : ℂ) • (E * X * Eᴴ + L * X * Lᴴ) := by
  rw [halfArmInstrument, completeSelectedKraus_success_branch, krausMap, Fin.sum_univ_two]
  change ((1 / 2 : ℂ) • E) * X * ((1 / 2 : ℂ) • E)ᴴ +
    ((1 / 2 : ℂ) • L) * X * ((1 / 2 : ℂ) • L)ᴴ = _
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
  congr 2 <;> simp <;> ring

end Contraction

end FiniteInstrument
end SKEFTHawking.QuantumNetwork
