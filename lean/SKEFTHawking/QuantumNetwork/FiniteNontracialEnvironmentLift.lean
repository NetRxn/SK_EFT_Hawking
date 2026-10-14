import SKEFTHawking.FiniteNontracialReflectionDynamics
import SKEFTHawking.QuantumNetwork.FiniteMemoryProcess
/-!
# Actual environment-only nontracial qubit channels

Joint indices are ordered S × E. The Kraus lift is I_S tensor K_E.
Its arbitrary-joint identities are derived entrywise through environment
blocks, without a product-state assumption. State and observable algebra is
over complex matrices; positivity statements name their hypotheses.

This independent foundation supplies the generic lift, unchanged S marginal,
literal local-instrument propagation, Gibbs reset and computational dephasing.
Its primitive two-rate action is tied to the existing normalized channel.
Schedule specialization, Hermitian same-marginal contraction, retained-readout
consumers and field-history transfer remain separate M1–M8 obligations.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialEnvironmentLift
open Matrix
open scoped Kronecker BigOperators ComplexOrder
open FinitePositiveKernel.GibbsObservable
abbrev Q := Fin 2
abbrev MatQ := Matrix Q Q ℂ
abbrev Joint := Q × Q
abbrev MatJoint := Matrix Joint Joint ℂ
/-- Preserve the Kraus index while acting on the second factor. -/
def liftKraus {m : ℕ} (K : Fin m → MatQ) (k : Fin m) : MatJoint := 1 ⊗ₖ K k
def liftState {m : ℕ} (K : Fin m → MatQ) (X : MatJoint) : MatJoint := krausMap (liftKraus K) X
def liftObservable {m : ℕ} (K : Fin m → MatQ) (A : MatJoint) : MatJoint := Channel.heisenberg (liftKraus K) A
/-- The environment matrix at a fixed pair of spectator indices. -/
def block (X : MatJoint) (s t : Q) : MatQ := fun e f => X (s,e) (t,f)
theorem sandwich_block (K : MatQ) (X : MatJoint) (s t e f : Q) :
 (((1 : MatQ) ⊗ₖ K) * X * ((1 : MatQ) ⊗ₖ K)ᴴ) (s,e) (t,f) = (K * block X s t * Kᴴ) e f := by
 fin_cases t <;> simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, block, Matrix.one_apply]
theorem liftState_block {m : ℕ} (K : Fin m → MatQ) (X : MatJoint) (s t : Q) :
 block (liftState K X) s t = krausMap K (block X s t) := by
 ext e f
 simp only [block, liftState, krausMap, Matrix.sum_apply, liftKraus, sandwich_block]
theorem sum_kronecker_right {m : ℕ} (K : Fin m → MatQ) :
 (∑ k, (1 : MatQ) ⊗ₖ K k) = (1 : MatQ) ⊗ₖ (∑ k, K k) := by
 ext ⟨s,e⟩ ⟨t,f⟩
 simp [Matrix.sum_apply, Finset.mul_sum]
theorem normalized {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K) :
 IsKrausChannel (liftKraus K) := by
 unfold IsKrausChannel liftKraus
 simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
   ← Matrix.mul_kronecker_mul, one_mul]
 rw [sum_kronecker_right, hK, Matrix.one_kronecker_one]
theorem product_action {m : ℕ} (K : Fin m → MatQ) (A B : MatQ) :
 liftState K (A ⊗ₖ B) = A ⊗ₖ krausMap K B := by
 unfold liftState krausMap liftKraus
 simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
  ← Matrix.mul_kronecker_mul, one_mul, mul_one]
 ext ⟨s,e⟩ ⟨t,f⟩
 simp [Matrix.sum_apply, Finset.mul_sum]
theorem observable_product_action {m : ℕ} (K : Fin m → MatQ) (A B : MatQ) :
 liftObservable K (A ⊗ₖ B) = A ⊗ₖ Channel.heisenberg K B := by
 unfold liftObservable Channel.heisenberg liftKraus
 simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
  ← Matrix.mul_kronecker_mul, one_mul, mul_one]
 ext ⟨s,e⟩ ⟨t,f⟩
 simp [Matrix.sum_apply, Finset.mul_sum]
theorem liftObservable_block {m : ℕ} (K : Fin m → MatQ) (A : MatJoint) (s t : Q) :
 block (liftObservable K A) s t = Channel.heisenberg K (block A s t) := by
 have h : liftObservable K A = liftState (fun k => (K k)ᴴ) A := by
  simp [liftObservable, liftState, liftKraus, Channel.heisenberg, krausMap,
   Matrix.conjTranspose_kronecker]
 rw [h, liftState_block]
 simp [krausMap, Channel.heisenberg]
theorem trace_duality {m : ℕ} (K : Fin m → MatQ) (A X : MatJoint) :
 (A * liftState K X).trace = (liftObservable K A * X).trace := by
 rw [Matrix.trace_mul_comm, liftState, liftObservable, ← Channel.trace_duality,
  Matrix.trace_mul_comm]
/-- Literal trace over E; this preserves the first-factor S carrier. -/
def ptrace2 (X : MatJoint) : MatQ := fun s t => ∑ e, X (s,e) (t,e)
theorem ptrace2_kronecker (A B : MatQ) : ptrace2 (A ⊗ₖ B) = B.trace • A := by
 ext s t
 simp [ptrace2, Matrix.trace, mul_add, mul_comm]
theorem ptrace2_sub (X Y : MatJoint) : ptrace2 (X - Y) = ptrace2 X - ptrace2 Y := by
 ext s t; simp [ptrace2, Finset.sum_sub_distrib]
theorem ptrace2_smul (c : ℂ) (X : MatJoint) : ptrace2 (c • X) = c • ptrace2 X := by
 ext s t; simp [ptrace2, mul_add]
theorem ptrace2_block (X : MatJoint) (s t : Q) :
 ptrace2 X s t = (block X s t).trace := rfl
/-- Trace preservation of every environment block proves the arbitrary-joint invariant. -/
theorem spectator {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K) (X : MatJoint) :
 ptrace2 (liftState K X) = ptrace2 X := by
 ext s t
 rw [ptrace2_block, liftState_block, trace_krausMap hK, ← ptrace2_block]
def localBranch (L : MatQ) (X : MatJoint) : MatJoint :=
 (L ⊗ₖ (1 : MatQ)) * X * (L ⊗ₖ (1 : MatQ))ᴴ
theorem local_environment_commute (L K : MatQ) :
 ((1 : MatQ) ⊗ₖ K) * (L ⊗ₖ (1 : MatQ)) =
 (L ⊗ₖ (1 : MatQ)) * ((1 : MatQ) ⊗ₖ K) := by
 simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one]
theorem sandwich_local_commute (K L : MatQ) (X : MatJoint) :
 ((1 : MatQ) ⊗ₖ K) * localBranch L X * ((1 : MatQ) ⊗ₖ K)ᴴ =
 localBranch L (((1 : MatQ) ⊗ₖ K) * X * ((1 : MatQ) ⊗ₖ K)ᴴ) := by
 have h := local_environment_commute L K
 have hs := congrArg Matrix.conjTranspose h
 simp only [Matrix.conjTranspose_mul] at hs
 unfold localBranch
 calc
  _ = (((1 : MatQ) ⊗ₖ K) * (L ⊗ₖ (1 : MatQ))) * X *
    ((L ⊗ₖ (1 : MatQ))ᴴ * ((1 : MatQ) ⊗ₖ K)ᴴ) := by noncomm_ring
  _ = ((L ⊗ₖ (1 : MatQ)) * ((1 : MatQ) ⊗ₖ K)) * X *
    (((1 : MatQ) ⊗ₖ K)ᴴ * (L ⊗ₖ (1 : MatQ))ᴴ) := by rw [h, hs]
  _ = _ := by noncomm_ring
theorem liftState_localBranch {m : ℕ} (K : Fin m → MatQ) (L : MatQ) (X : MatJoint) :
 liftState K (localBranch L X) = localBranch L (liftState K X) := by
 simp only [liftState, krausMap, liftKraus, sandwich_local_commute]
 simp only [localBranch, Matrix.mul_sum, Matrix.sum_mul]
/-- A single actual S-local branch propagates the marginal without conditioning. -/
theorem ptrace2_localBranch (L : MatQ) (X : MatJoint) :
 ptrace2 (localBranch L X) = L * ptrace2 X * Lᴴ := by
 ext s t
 fin_cases s <;> fin_cases t <;>
  simp [ptrace2, localBranch, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring
theorem liftState_sum {m : ℕ} (K : Fin m → MatQ) {ι : Type*} [Fintype ι]
 (X : ι → MatJoint) : liftState K (∑ i, X i) = ∑ i, liftState K (X i) := by
 simp only [liftState, krausMap, Matrix.mul_sum, Matrix.sum_mul]
 rw [Finset.sum_comm]
theorem ptrace2_sum {ι : Type*} [Fintype ι] (X : ι → MatJoint) :
 ptrace2 (∑ i, X i) = ∑ i, ptrace2 (X i) := by
 ext s t
 simp only [ptrace2, Matrix.sum_apply]
 rw [Finset.sum_comm]
theorem instrument_branch_commute {m o : ℕ} (K : Fin m → MatQ)
 (I : FiniteInstrument Q o) (a : Fin o) (X : MatJoint) :
 liftState K ((I.lift Q).branch a X) = (I.lift Q).branch a (liftState K X) := by
 change liftState K (∑ k, localBranch (I.operators a k) X) =
  ∑ k, localBranch (I.operators a k) (liftState K X)
 rw [liftState_sum]
 simp_rw [liftState_localBranch]
theorem instrument_branch_marginal {o : ℕ} (I : FiniteInstrument Q o)
 (a : Fin o) (X : MatJoint) :
 ptrace2 ((I.lift Q).branch a X) = I.branch a (ptrace2 X) := by
 change ptrace2 (∑ k, localBranch (I.operators a k) X) =
  ∑ k, I.operators a k * ptrace2 X * (I.operators a k)ᴴ
 rw [ptrace2_sum]
 simp_rw [ptrace2_localBranch]
theorem same_marginal_local {o : ℕ} (I : FiniteInstrument Q o) (a : Fin o)
 {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
 ptrace2 ((I.lift Q).branch a X) = ptrace2 ((I.lift Q).branch a Y) := by
 rw [instrument_branch_marginal, instrument_branch_marginal, h]
theorem same_marginal_environment {m : ℕ} {K : Fin m → MatQ}
 (hK : IsKrausChannel K) {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
 ptrace2 (liftState K X) = ptrace2 (liftState K Y) := by
 rw [spectator hK, spectator hK, h]
theorem liftState_trace {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K) (X : MatJoint) :
 (liftState K X).trace = X.trace := trace_krausMap (normalized hK) X
theorem liftState_posSemidef {m : ℕ} (K : Fin m → MatQ) {X : MatJoint} (hX : X.PosSemidef) :
 (liftState K X).PosSemidef := krausMap_posSemidef (liftKraus K) hX
theorem liftState_isHermitian {m : ℕ} (K : Fin m → MatQ) {X : MatJoint} (hX : X.IsHermitian) :
 (liftState K X).IsHermitian := krausMap_isHermitian (liftKraus K) hX
theorem liftState_density {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K)
 {X : MatJoint} (hX : IsDensityOperator X) : IsDensityOperator (liftState K X) :=
 krausMap_isDensityOperator (normalized hK) hX
open NontracialPauliReflection
open FinitePositiveKernel
def gibbsResetKraus := GibbsReset.resetKraus weights
def gibbsReset (X : MatJoint) : MatJoint := liftState gibbsResetKraus X
theorem gibbsReset_normalized : IsKrausChannel (liftKraus gibbsResetKraus) :=
 normalized (GibbsReset.reset_normalized weights weights_nonnegative weights_normalized)
/-- An actual Gibbs channel discards E on arbitrary, including correlated, inputs. -/
theorem gibbsReset_eq (X : MatJoint) : gibbsReset X = ptrace2 X ⊗ₖ rhoN := by
 ext ⟨s,e⟩ ⟨t,f⟩
 change block (liftState gibbsResetKraus X) s t e f = _
 rw [liftState_block]
 unfold gibbsResetKraus
 rw [GibbsReset.reset_state weights weights_nonnegative, weights_density]
 rfl
def dephaseKraus (b : Q) : MatQ := FiniteMemoryProcess.basisState b
def dephase (X : MatJoint) : MatJoint := liftState dephaseKraus X
theorem dephaseKraus_normalized : IsKrausChannel dephaseKraus := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  norm_num [IsKrausChannel, dephaseKraus, FiniteMemoryProcess.basisState,
   Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
theorem dephase_normalized : IsKrausChannel (liftKraus dephaseKraus) :=
 normalized dephaseKraus_normalized
theorem dephase_action (B : MatQ) :
 krausMap dephaseKraus B = NontracialReflectionDynamics.diagonalPart B := by
 ext e f
 fin_cases e <;> fin_cases f <;>
  simp [krausMap, dephaseKraus, FiniteMemoryProcess.basisState,
   NontracialReflectionDynamics.diagonalPart, Matrix.mul_apply,
   Matrix.conjTranspose_apply, Fin.sum_univ_two]
theorem dephase_entry (X : MatJoint) (s t e f : Q) :
 dephase X (s,e) (t,f) = if e = f then X (s,e) (t,f) else 0 := by
 change block (liftState dephaseKraus X) s t e f = _
 rw [liftState_block, dephase_action]
 by_cases h : e = f
 · subst f; simp [NontracialReflectionDynamics.diagonalPart, block]
 · simp [NontracialReflectionDynamics.diagonalPart, block, h]
def primitive (γ η t : ℝ) (X : MatJoint) : MatJoint :=
 liftState (NontracialReflectionDynamics.timeKraus γ η t) X
theorem stationary_product (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (A : MatQ) :
 primitive γ η t (A ⊗ₖ rhoN) = A ⊗ₖ rhoN := by
 rw [primitive, product_action]
 change A ⊗ₖ NontracialReflectionDynamics.state γ η t rhoN = _
 rw [NontracialReflectionDynamics.stationary γ η t hγ hη ht]
theorem primitive_normalized (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
 IsKrausChannel (liftKraus (NontracialReflectionDynamics.timeKraus γ η t)) :=
 normalized (NontracialReflectionDynamics.normalized γ η t hγ hη ht)
theorem primitive_spectator (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
 (X : MatJoint) : ptrace2 (primitive γ η t X) = ptrace2 X :=
 spectator (NontracialReflectionDynamics.normalized γ η t hγ hη ht) X
theorem primitive_density (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
 {X : MatJoint} (hX : IsDensityOperator X) : IsDensityOperator (primitive γ η t X) :=
 liftState_density (NontracialReflectionDynamics.normalized γ η t hγ hη ht) hX
theorem primitive_block (γ η t : ℝ) (X : MatJoint) (s u : Q) :
 block (primitive γ η t X) s u =
 NontracialReflectionDynamics.state γ η t (block X s u) := liftState_block _ _ _ _
theorem dephase_block (X : MatJoint) (s u : Q) :
 block (dephase X) s u = NontracialReflectionDynamics.diagonalPart (block X s u) := by
 rw [dephase, liftState_block, dephase_action]
theorem gibbsReset_block (X : MatJoint) (s u : Q) :
 block (gibbsReset X) s u = (block X s u).trace • rhoN := by
 rw [gibbsReset, liftState_block, gibbsResetKraus, GibbsReset.reset_state weights weights_nonnegative,
  weights_density]
theorem primitive_formula (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
 (X : MatJoint) :
 primitive γ η t X =
  ((1 - Real.exp (-γ*t) : ℝ) : ℂ) • gibbsReset X +
  ((Real.exp (-γ*t) - Real.exp (-(γ+η)*t) : ℝ) : ℂ) • dephase X +
  (Real.exp (-(γ+η)*t) : ℂ) • X := by
 ext ⟨s,e⟩ ⟨u,f⟩
 have h := congrArg (fun B : MatQ => B e f)
  (NontracialReflectionDynamics.state_formula γ η t hγ hη ht (block X s u))
 rw [← primitive_block, ← gibbsReset_block, ← dephase_block] at h
 simp only [block, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at h
 simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub,
  Complex.ofReal_one]
 rw [h]
 ring
theorem common_reset {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
 gibbsReset X = gibbsReset Y := by rw [gibbsReset_eq, gibbsReset_eq, h]
def spectatorState (b : Q) : MatJoint := FiniteMemoryProcess.basisState b ⊗ₖ rhoN
theorem spectatorState_density (b : Q) : IsDensityOperator (spectatorState b) := by
 exact ⟨(FiniteMemoryProcess.basisState_density b).1.kronecker rhoN_density.1,
  by rw [spectatorState, Matrix.trace_kronecker, (FiniteMemoryProcess.basisState_density b).2,
   rhoN_trace, one_mul]⟩
theorem spectatorState_stationary (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (b : Q) :
 primitive γ η t (spectatorState b) = spectatorState b := stationary_product γ η t hγ hη ht _
theorem spectatorState_distinct : spectatorState 0 ≠ spectatorState 1 := by
 intro h
 have he := congrArg (fun X : MatJoint => X (0,0) (0,0)) h
 norm_num [spectatorState, FiniteMemoryProcess.basisState, rhoN] at he
theorem spectator_perfect_error :
 povmAvgError (spectatorState 0) (spectatorState 1)
  (FiniteMemoryProcess.basisState 0 ⊗ₖ (1 : MatQ)) = 0 := by
 norm_num [povmAvgError, spectatorState, FiniteMemoryProcess.basisState, rhoN,
  Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
theorem spectatorState_distance : traceDist (spectatorState 0) (spectatorState 1) = 1 := by
 have hu := (traceDist_mem_Icc (spectatorState_density 0) (spectatorState_density 1)).2
 have hl := helstrom_le_povmAvgError (spectatorState_density 0) (spectatorState_density 1)
  FiniteMemoryProcess.systemEffect_binary
 rw [spectator_perfect_error] at hl
 linarith
/-- Distinct stationary S preparations forbid a strict global mixing coefficient. -/
theorem no_global_strict_contraction (γ η t α : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
 (ht : 0 ≤ t) (hα : α < 1) :
 ¬ ∀ X Y : MatJoint, IsDensityOperator X → IsDensityOperator Y →
  traceDist (primitive γ η t X) (primitive γ η t Y) ≤ α * traceDist X Y := by
 intro h
 have hx := h (spectatorState 0) (spectatorState 1)
  (spectatorState_density 0) (spectatorState_density 1)
 rw [spectatorState_stationary γ η t hγ hη ht,
  spectatorState_stationary γ η t hγ hη ht, spectatorState_distance, mul_one] at hx
 linarith
theorem ptrace2_eq_standard (X : MatJoint) :
 ptrace2 X = SKEFTHawking.QuantumNetwork.ptrace2 X := rfl
theorem basisProduct_marginal (a b : Q) :
 ptrace2 (FiniteMemoryProcess.basisState a ⊗ₖ FiniteMemoryProcess.basisState b) =
  FiniteMemoryProcess.basisState a := by
 ext s t
 fin_cases a <;> fin_cases b <;>
  simp [ptrace2, FiniteMemoryProcess.basisState]
/-- A normalized local reset followed by SWAP can invalidate a later noise-cut premise. -/
theorem swap_after_local_reset_breaks_same_marginal :
 let X : MatJoint := FiniteMemoryProcess.basisState 0 ⊗ₖ FiniteMemoryProcess.basisState 0
 let Y : MatJoint := FiniteMemoryProcess.basisState 0 ⊗ₖ FiniteMemoryProcess.basisState 1
 ptrace2 X = ptrace2 Y ∧
  ptrace2 (FiniteMemoryProcess.swapJoint (FiniteMemoryProcess.resetSystem X)) ≠
  ptrace2 (FiniteMemoryProcess.swapJoint (FiniteMemoryProcess.resetSystem Y)) := by
 dsimp
 rw [FiniteMemoryProcess.resetSystem_basis, FiniteMemoryProcess.resetSystem_basis,
  FiniteMemoryProcess.swapJoint_basis, FiniteMemoryProcess.swapJoint_basis]
 simp only [basisProduct_marginal]
 refine ⟨True.intro, ?_⟩
 intro h
 have he := congrArg (fun A : MatQ => A 0 0) h
 norm_num [FiniteMemoryProcess.basisState] at he
end SKEFTHawking.QuantumNetwork.FiniteNontracialEnvironmentLift