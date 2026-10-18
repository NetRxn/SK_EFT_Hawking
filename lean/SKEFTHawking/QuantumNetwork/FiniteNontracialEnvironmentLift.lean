import SKEFTHawking.QuantumNetwork.FiniteNontracialSchedule
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutDiscrimination
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

/-!
## Full M2 schedule action and checked noise cuts

The schedule extension consumes the integrated chronological Kraus family.
All-complex state and observable formulas hold on arbitrary joint matrices.
A strict decay estimate requires Hermitian differences and the literal S
marginal equality at every branch at the relevant cut. Shared continuations
earn ordinary contractivity; a second decay factor uses a new proved cut.

This completes the M2 mathematical source clauses. The actual attained
retained-readout consumers and field-history bridges remain M3–M8 work.
-/
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialEnvironmentLift
open Matrix
open FiniteNontracialSchedule (Schedule Slice alpha beta G D)
open FinitePositiveKernel.GibbsObservable
open scoped BigOperators Kronecker ComplexOrder

/-- The actual finite chronological schedule acting only on E. -/
def scheduleKraus (s : Schedule) : Fin (FiniteNontracialSchedule.count s) → MatJoint :=
 liftKraus (FiniteNontracialSchedule.scheduleKraus s)
def scheduleState (s : Schedule) (X : MatJoint) : MatJoint := krausMap (scheduleKraus s) X
def scheduleObservable (s : Schedule) (A : MatJoint) : MatJoint := Channel.heisenberg (scheduleKraus s) A

theorem schedule_normalized (s : Schedule) : IsKrausChannel (scheduleKraus s) :=
 normalized (FiniteNontracialSchedule.normalized s)
theorem block_ext {X Y : MatJoint} (h : ∀ s t, block X s t = block Y s t) : X = Y := by
 ext ⟨s,e⟩ ⟨t,f⟩
 exact congrArg (fun B : MatQ => B e f) (h s t)
theorem scheduleState_block (s : Schedule) (X : MatJoint) (a b : Q) :
 block (scheduleState s X) a b = FiniteNontracialSchedule.state s (block X a b) :=
 liftState_block _ _ _ _
theorem scheduleObservable_block (s : Schedule) (X : MatJoint) (a b : Q) :
 block (scheduleObservable s X) a b = FiniteNontracialSchedule.observable s (block X a b) :=
 liftObservable_block _ _ _ _
theorem schedule_product (s : Schedule) (A B : MatQ) :
 scheduleState s (A ⊗ₖ B) = A ⊗ₖ FiniteNontracialSchedule.state s B := product_action _ _ _
theorem schedule_observable_product (s : Schedule) (A B : MatQ) :
 scheduleObservable s (A ⊗ₖ B) = A ⊗ₖ FiniteNontracialSchedule.observable s B :=
 observable_product_action _ _ _
theorem schedule_trace_dual (s : Schedule) (A X : MatJoint) :
 (A * scheduleState s X).trace = (scheduleObservable s A * X).trace := trace_duality _ _ _
theorem schedule_spectator (s : Schedule) (X : MatJoint) :
 ptrace2 (scheduleState s X) = ptrace2 X := spectator (FiniteNontracialSchedule.normalized s) X
theorem schedule_trace (s : Schedule) (X : MatJoint) :
 (scheduleState s X).trace = X.trace := trace_krausMap (schedule_normalized s) X
theorem schedule_posSemidef (s : Schedule) {X : MatJoint} (hX : X.PosSemidef) :
 (scheduleState s X).PosSemidef := krausMap_posSemidef _ hX
theorem schedule_isHermitian (s : Schedule) {X : MatJoint} (hX : X.IsHermitian) :
 (scheduleState s X).IsHermitian := krausMap_isHermitian _ hX
theorem schedule_density (s : Schedule) {X : MatJoint} (hX : IsDensityOperator X) :
 IsDensityOperator (scheduleState s X) := krausMap_isDensityOperator (schedule_normalized s) hX
theorem schedule_nil (X : MatJoint) : scheduleState [] X = X := by
 apply block_ext
 intro a b
 rw [scheduleState_block, FiniteNontracialSchedule.state_nil]
theorem schedule_cons (h : Slice) (t : Schedule) (X : MatJoint) :
 scheduleState (h :: t) X = scheduleState t (primitive h.gamma h.eta h.duration X) := by
 apply block_ext
 intro a b
 rw [scheduleState_block, scheduleState_block, primitive_block, FiniteNontracialSchedule.state_cons]
theorem schedule_append (s t : Schedule) (X : MatJoint) :
 scheduleState (s ++ t) X = scheduleState t (scheduleState s X) := by
 apply block_ext
 intro a b
 rw [scheduleState_block, scheduleState_block, scheduleState_block,
  FiniteNontracialSchedule.state_append]
theorem schedule_observable_nil (A : MatJoint) : scheduleObservable [] A = A := by
 apply block_ext
 intro a b
 rw [scheduleObservable_block, FiniteNontracialSchedule.observable_nil]
theorem schedule_observable_cons (h : Slice) (t : Schedule) (A : MatJoint) :
 scheduleObservable (h :: t) A =
 liftObservable (NontracialReflectionDynamics.timeKraus h.gamma h.eta h.duration)
  (scheduleObservable t A) := by
 apply block_ext
 intro a b
 rw [scheduleObservable_block, liftObservable_block, scheduleObservable_block]
 exact FiniteNontracialSchedule.observable_cons h t _
theorem schedule_observable_append (s t : Schedule) (A : MatJoint) :
 scheduleObservable (s ++ t) A = scheduleObservable s (scheduleObservable t A) := by
 apply block_ext
 intro a b
 rw [scheduleObservable_block, scheduleObservable_block, scheduleObservable_block,
  FiniteNontracialSchedule.observable_append]
theorem schedule_effective (s : Schedule) (X : MatJoint) :
 scheduleState s X = primitive (G s) (D s) 1 X := by
 apply block_ext
 intro a b
 rw [scheduleState_block, primitive_block, FiniteNontracialSchedule.state_effective]
theorem schedule_observable_effective (s : Schedule) (A : MatJoint) :
 scheduleObservable s A = liftObservable (NontracialReflectionDynamics.timeKraus (G s) (D s) 1) A := by
 apply block_ext
 intro a b
 rw [scheduleObservable_block, liftObservable_block]
 exact FiniteNontracialSchedule.observable_effective s _
theorem schedule_formula (s : Schedule) (X : MatJoint) :
 scheduleState s X =
  ((1-alpha s : ℝ):ℂ) • gibbsReset X +
  ((alpha s-beta s : ℝ):ℂ) • dephase X + (beta s:ℂ) • X := by
 rw [schedule_effective, primitive_formula (G s) (D s) 1
  (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one]
 simp only [alpha, beta, mul_one]


theorem schedule_sub (s : Schedule) (X Y : MatJoint) :
 scheduleState s (X-Y) = scheduleState s X-scheduleState s Y := krausMap_sub _ _ _
theorem dephase_sub (X Y : MatJoint) :
 dephase (X-Y) = dephase X-dephase Y := krausMap_sub _ _ _
theorem schedule_difference (s : Schedule) {X Y : MatJoint}
 (h : ptrace2 X = ptrace2 Y) :
 scheduleState s X-scheduleState s Y =
  ((alpha s-beta s:ℝ):ℂ) • dephase (X-Y) + (beta s:ℂ) • (X-Y) := by
 rw [schedule_formula, schedule_formula, dephase_sub, common_reset h]
 module
/-- The norm estimate is restricted to Hermitian differences at a checked S-marginal cut. -/
theorem schedule_traceNorm_contraction (s : Schedule) {X Y : MatJoint}
 (hX : X.IsHermitian) (hY : Y.IsHermitian) (h : ptrace2 X = ptrace2 Y) :
 traceNorm (scheduleState s X-scheduleState s Y) ≤ alpha s * traceNorm (X-Y) := by
 have hc := FiniteNontracialSchedule.coefficients s
 have hd : 0 ≤ alpha s-beta s := sub_nonneg.mpr hc.2.1
 have hb : 0 ≤ beta s := hc.1.le
 have hk : traceNorm (dephase (X-Y)) ≤ traceNorm (X-Y) :=
  traceNorm_krausMap_le dephase_normalized (hX.sub hY)
 rw [schedule_difference s h]
 calc
  _ ≤ traceNorm (((alpha s-beta s:ℝ):ℂ) • dephase (X-Y)) +
    traceNorm ((beta s:ℂ) • (X-Y)) := traceNorm_triangle _ _
  _ = (alpha s-beta s)*traceNorm (dephase (X-Y)) + beta s*traceNorm (X-Y) := by
    rw [traceNorm_smul_nonneg hd, traceNorm_smul_nonneg hb]
  _ ≤ (alpha s-beta s)*traceNorm (X-Y) + beta s*traceNorm (X-Y) :=
    add_le_add (mul_le_mul_of_nonneg_left hk hd) le_rfl
  _ = _ := by ring
theorem schedule_traceDist_contraction (s : Schedule) {X Y : MatJoint}
 (hX : X.IsHermitian) (hY : Y.IsHermitian) (h : ptrace2 X = ptrace2 Y) :
 traceDist (scheduleState s X) (scheduleState s Y) ≤ alpha s * traceDist X Y := by
 have hn := schedule_traceNorm_contraction s hX hY h
 unfold traceDist
 nlinarith

open FiniteAdaptiveReadoutDiscrimination
theorem ptrace2_trace (X : MatJoint) : (ptrace2 X).trace = X.trace := by
 simp [ptrace2, Matrix.trace, Fintype.sum_prod_type]
/-- Preserve all histories, including unnormalized and impossible branches. -/
def scheduleFamily {H : Type*} (s : Schedule) (A : H → MatJoint) : H → MatJoint :=
 fun h => scheduleState s (A h)
theorem scheduleFamily_trace {H : Type*} (s : Schedule) (A : H → MatJoint) (h : H) :
 (scheduleFamily s A h).trace = (A h).trace := schedule_trace s _
theorem scheduleFamily_valid {H : Type*} [Fintype H] (s : Schedule)
 {A : H → MatJoint} (hA : IsBranchFamily A) : IsBranchFamily (scheduleFamily s A) := by
 refine ⟨fun h => schedule_posSemidef s (hA.1 h), ?_⟩
 simp_rw [scheduleFamily_trace]
 exact hA.2
theorem scheduleFamily_history_law {H : Type*} (s : Schedule) (A : H → MatJoint) :
 (fun h => (scheduleFamily s A h).trace.re) = (fun h => (A h).trace.re) := by
 funext h
 rw [scheduleFamily_trace]
theorem branchwise_same_trace {H : Type*} {A B : H → MatJoint}
 (h : ∀ k, ptrace2 (A k) = ptrace2 (B k)) (k : H) : (A k).trace = (B k).trace := by
 have ht := congrArg Matrix.trace (h k)
 simpa only [ptrace2_trace] using ht
theorem branchwise_identical_history_laws {H : Type*} (s : Schedule) {A B : H → MatJoint}
 (h : ∀ k, ptrace2 (A k) = ptrace2 (B k)) :
 (fun k => (scheduleFamily s A k).trace.re) = (fun k => (scheduleFamily s B k).trace.re) := by
 funext k
 rw [scheduleFamily_trace, scheduleFamily_trace, branchwise_same_trace h k]
/-- Equality is required at every history at this noise cut. -/
theorem scheduleFamily_contraction {H : Type*} [Fintype H] (s : Schedule)
 {A B : H → MatJoint} (hA : IsBranchFamily A) (hB : IsBranchFamily B)
 (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h)) :
 branchDistance (scheduleFamily s A) (scheduleFamily s B) ≤ alpha s * branchDistance A B := by
 unfold branchDistance
 rw [Finset.mul_sum]
 apply Finset.sum_le_sum
 intro h _
 exact schedule_traceDist_contraction s (hA.1 h).isHermitian (hB.1 h).isHermitian (hm h)
/-- All history-indexed binary effects share the same noise-cut bound. -/
theorem scheduleFamily_readout_lower {H : Type*} [Fintype H] (s : Schedule)
 {A B E : H → MatJoint} (hA : IsBranchFamily A) (hB : IsBranchFamily B)
 (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h)) (hE : ∀ h, IsBinaryPOVM (E h)) :
 (1-alpha s*branchDistance A B)/2 ≤ readoutError (scheduleFamily s A) (scheduleFamily s B) E := by
 have hc := scheduleFamily_contraction s hA hB hm
 have hl := readoutError_lower (scheduleFamily_valid s hA) (scheduleFamily_valid s hB) hE
 linarith

theorem block_add (X Y : MatJoint) (a b : Q) :
 block (X+Y) a b = block X a b+block Y a b := rfl
theorem block_smul (c : ℂ) (X : MatJoint) (a b : Q) :
 block (c • X) a b = c • block X a b := rfl
theorem dephaseKraus_adjoint (k : Q) : (dephaseKraus k)ᴴ = dephaseKraus k := by
 ext i j
 fin_cases k <;> fin_cases i <;> fin_cases j <;>
  simp [dephaseKraus, FiniteMemoryProcess.basisState, Matrix.conjTranspose_apply]
theorem dephase_observable (A : MatJoint) : liftObservable dephaseKraus A = dephase A := by
 simp [liftObservable, dephase, liftState, liftKraus, Channel.heisenberg, krausMap,
  Matrix.conjTranspose_kronecker, dephaseKraus_adjoint]
theorem gibbsObservable_block (A : MatJoint) (a b : Q) :
 block (liftObservable gibbsResetKraus A) a b = (NontracialPauliReflection.rhoN*block A a b).trace • (1:MatQ) := by
 rw [liftObservable_block, gibbsResetKraus,
  FinitePositiveKernel.GibbsReset.reset_observable NontracialPauliReflection.weights
   NontracialPauliReflection.weights_nonnegative,
  NontracialPauliReflection.weights_density]
theorem schedule_observable_formula (s : Schedule) (A : MatJoint) :
 scheduleObservable s A =
  ((1-alpha s:ℝ):ℂ) • liftObservable gibbsResetKraus A +
  ((alpha s-beta s:ℝ):ℂ) • dephase A + (beta s:ℂ) • A := by
 apply block_ext
 intro a b
 rw [scheduleObservable_block, block_add, block_add, block_smul, block_smul, block_smul,
  gibbsObservable_block, dephase_block, FiniteNontracialSchedule.observable_convex_formula]
 simp only [Complex.ofReal_sub, Complex.ofReal_one]
/-- Realize the allowed chronology with the existing normalized process-step constructor. -/
def scheduleStep {o : ℕ} (s : Schedule) (I : FiniteInstrument Q o) :
 FiniteInterventionProcess.Step Q Q o :=
 FiniteAdaptiveMapPerturbation.realizedStep Q Q o (scheduleKraus s) (schedule_normalized s) I
theorem scheduleStep_branch {o : ℕ} (s : Schedule) (I : FiniteInstrument Q o) (a : Fin o) (X : MatJoint) :
 (scheduleStep s I).branch Q Q o a X = (I.lift Q).branch a (scheduleState s X) := rfl
theorem scheduleStep_marginal {o : ℕ} (s : Schedule) (I : FiniteInstrument Q o) (a : Fin o) (X : MatJoint) :
 ptrace2 ((scheduleStep s I).branch Q Q o a X) = I.branch a (ptrace2 X) := by
 rw [scheduleStep_branch, instrument_branch_marginal, schedule_spectator]
theorem scheduleStep_same_marginal {o : ℕ} (s : Schedule) (I : FiniteInstrument Q o) (a : Fin o)
 {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
 ptrace2 ((scheduleStep s I).branch Q Q o a X) = ptrace2 ((scheduleStep s I).branch Q Q o a Y) := by
 rw [scheduleStep_branch, scheduleStep_branch]
 exact same_marginal_local I a (same_marginal_environment (FiniteNontracialSchedule.normalized s) h)
/-- Noise commutes with every literal S-local instrument branch, including zero branches. -/
theorem schedule_instrument_commute {o : ℕ} (s : Schedule) (I : FiniteInstrument Q o)
 (a : Fin o) (X : MatJoint) :
 scheduleState s ((I.lift Q).branch a X) = (I.lift Q).branch a (scheduleState s X) :=
 instrument_branch_commute _ _ _ _

/-- This predicate restricts every actual node to TP E-only evolution and an S-local instrument. -/
inductive IsLocalScheduleTree {o : ℕ} : {n : ℕ} → FiniteInterventionProcess.Tree Q Q o n → Prop
 | done : IsLocalScheduleTree .done
 | node {n : ℕ} (s : Schedule) (I : FiniteInstrument Q o)
    (F : Fin o → FiniteInterventionProcess.Tree Q Q o n) (hF : ∀ a, IsLocalScheduleTree (F a)) :
    IsLocalScheduleTree (.node (scheduleStep s I) F)
theorem localScheduleTree_same_marginal {o n : ℕ} {T : FiniteInterventionProcess.Tree Q Q o n}
 (hT : IsLocalScheduleTree T) {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y)
 (k : FiniteInterventionProcess.History o n) :
 ptrace2 (FiniteInterventionProcess.run Q Q o T k X) =
 ptrace2 (FiniteInterventionProcess.run Q Q o T k Y) := by
 induction hT generalizing X Y with
 | done => exact h
 | node s I F hF ih =>
   rcases k with ⟨a,k⟩
   exact ih a (scheduleStep_same_marginal s I a h) k

theorem schedule_stationary_product (s : Schedule) (A : MatQ) :
 scheduleState s (A ⊗ₖ NontracialPauliReflection.rhoN) = A ⊗ₖ NontracialPauliReflection.rhoN := by
 rw [schedule_product, FiniteNontracialSchedule.state_stationary]
theorem schedule_spectatorState_stationary (s : Schedule) (b : Q) :
 scheduleState s (spectatorState b) = spectatorState b := schedule_stationary_product s _
theorem schedule_spectator_distance (s : Schedule) :
 traceDist (scheduleState s (spectatorState 0)) (scheduleState s (spectatorState 1)) = 1 := by
 rw [schedule_spectatorState_stationary, schedule_spectatorState_stationary, spectatorState_distance]
theorem schedule_no_global_strict_contraction (s : Schedule) (c : ℝ) (hc : c < 1) :
 ¬ ∀ X Y : MatJoint, IsDensityOperator X → IsDensityOperator Y →
  traceDist (scheduleState s X) (scheduleState s Y) ≤ c*traceDist X Y := by
 intro h
 have hh := h (spectatorState 0) (spectatorState 1) (spectatorState_density 0) (spectatorState_density 1)
 rw [schedule_spectator_distance, spectatorState_distance, mul_one] at hh
 linarith

open FiniteInterventionProcess
/-- A shared normalized continuation earns contractivity, with no additional decay coefficient. -/
theorem shared_tree_traceDist {o n : ℕ} (T : Tree Q Q o n) {X Y : MatJoint}
 (hX : X.IsHermitian) (hY : Y.IsHermitian) :
 ∑ k, traceDist (run Q Q o T k X) (run Q Q o T k Y) ≤ traceDist X Y := by
 unfold traceDist
 simp_rw [← FiniteAdaptiveMapPerturbation.run_sub Q Q o T]
 rw [← Finset.mul_sum]
 exact mul_le_mul_of_nonneg_left
  (FiniteAdaptiveMapPerturbation.tree_contraction Q Q o T (hX.sub hY)) (by norm_num)
def continueFamily {H : Type*} {o n : ℕ} (T : H → Tree Q Q o n) (A : H → MatJoint) :
 H × History o n → MatJoint := fun k => run Q Q o (T k.1) k.2 (A k.1)
theorem continueFamily_valid {H : Type*} [Fintype H] {o n : ℕ}
 (T : H → Tree Q Q o n) {A : H → MatJoint} (hA : IsBranchFamily A) :
 IsBranchFamily (continueFamily T A) := by
 refine ⟨fun k => run_posSemidef Q Q o (T k.1) k.2 (hA.1 k.1), ?_⟩
 simp only [continueFamily, Fintype.sum_prod_type]
 simp_rw [← Complex.re_sum, sum_trace Q Q o]
 simpa only [Complex.re_sum] using hA.2
theorem continueFamily_contraction {H : Type*} [Fintype H] {o n : ℕ}
 (T : H → Tree Q Q o n) {A B : H → MatJoint} (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
 branchDistance (continueFamily T A) (continueFamily T B) ≤ branchDistance A B := by
 simp only [branchDistance, continueFamily, Fintype.sum_prod_type]
 apply Finset.sum_le_sum
 intro h _
 exact shared_tree_traceDist (T h) (hA.1 h).isHermitian (hB.1 h).isHermitian
theorem scheduleFamily_downstream_contraction {H : Type*} [Fintype H] {o n : ℕ}
 (s : Schedule) (T : H → Tree Q Q o n) {A B : H → MatJoint}
 (hA : IsBranchFamily A) (hB : IsBranchFamily B) (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h)) :
 branchDistance (continueFamily T (scheduleFamily s A)) (continueFamily T (scheduleFamily s B)) ≤
 alpha s * branchDistance A B :=
 (continueFamily_contraction T (scheduleFamily_valid s hA) (scheduleFamily_valid s hB)).trans
  (scheduleFamily_contraction s hA hB hm)
theorem scheduleFamily_downstream_readout_lower {H : Type*} [Fintype H] {o n : ℕ}
 (s : Schedule) (T : H → Tree Q Q o n) {A B : H → MatJoint}
 (hA : IsBranchFamily A) (hB : IsBranchFamily B) (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h))
 (E : H × History o n → MatJoint) (hE : ∀ k, IsBinaryPOVM (E k)) :
 (1-alpha s*branchDistance A B)/2 ≤
 readoutError (continueFamily T (scheduleFamily s A)) (continueFamily T (scheduleFamily s B)) E := by
 have hc := scheduleFamily_downstream_contraction s T hA hB hm
 have hl := readoutError_lower (continueFamily_valid T (scheduleFamily_valid s hA))
  (continueFamily_valid T (scheduleFamily_valid s hB)) hE
 linarith
theorem schedule_zero_dose (s : Schedule) (hG : G s=0) (hD : D s=0) (X : MatJoint) :
 scheduleState s X=X ∧ scheduleObservable s X=X := by
 constructor
 · apply block_ext
   intro a b
   rw [scheduleState_block]
   exact (FiniteNontracialSchedule.zero_dose_actions s hG hD _).1
 · apply block_ext
   intro a b
   rw [scheduleObservable_block]
   exact (FiniteNontracialSchedule.zero_dose_actions s hG hD _).2
theorem schedule_zero_duration (s : Schedule) (hz : ∀ h∈s, h.duration=0) (X : MatJoint) :
 scheduleState s X=X ∧ scheduleObservable s X=X :=
 schedule_zero_dose s (FiniteNontracialSchedule.zero_duration_doses s hz).1
  (FiniteNontracialSchedule.zero_duration_doses s hz).2 X
theorem schedule_zero_rates (s : Schedule) (hz : ∀ h∈s, h.gamma=0 ∧ h.eta=0) (X : MatJoint) :
 scheduleState s X=X ∧ scheduleObservable s X=X :=
 schedule_zero_dose s (FiniteNontracialSchedule.zero_rate_doses s hz).1
  (FiniteNontracialSchedule.zero_rate_doses s hz).2 X
/-- The all-complex formula applies to an imaginary matrix unit without a density claim. -/
theorem schedule_imaginary_tensor (s : Schedule) (A : MatQ) :
 scheduleState s (A ⊗ₖ Matrix.single 0 1 Complex.I) =
 (beta s:ℂ) • (A ⊗ₖ Matrix.single 0 1 Complex.I) := by
 rw [schedule_product, FiniteNontracialSchedule.imaginary_offDiagonal]
 ext ⟨a,e⟩ ⟨b,f⟩
 simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
 ring

theorem imaginary_tensor_not_hermitian :
 ¬ (FiniteMemoryProcess.basisState 0 ⊗ₖ (Matrix.single 0 1 Complex.I : MatQ)).IsHermitian := by
 intro h
 have he := congrArg (fun X : MatJoint => X (0,0) (0,1)) h.eq
 simp [Matrix.conjTranspose_apply, FiniteMemoryProcess.basisState, Matrix.single] at he
 have hi := congrArg Complex.im he
 norm_num at hi
theorem schedule_no_global_alpha_contraction (s : Schedule) (hG : 0 < G s) :
 ¬ ∀ X Y : MatJoint, IsDensityOperator X → IsDensityOperator Y →
  traceDist (scheduleState s X) (scheduleState s Y) ≤ alpha s*traceDist X Y := by
 apply schedule_no_global_strict_contraction
 exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hG)

/-- The branchwise premise reaches a later cut only through the proved literal constructor invariant. -/
theorem continueFamily_same_marginal {H : Type*} {o n : ℕ}
 (T : H → Tree Q Q o n) (hT : ∀ h, IsLocalScheduleTree (T h))
 {A B : H → MatJoint} (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h))
 (k : H × History o n) :
 ptrace2 (continueFamily T A k) = ptrace2 (continueFamily T B k) :=
 localScheduleTree_same_marginal (hT k.1) (hm k.1) k.2
/-- An additional decay factor requires a new checked noise cut after the literal local tree. -/
theorem schedule_after_localTree_contraction {H : Type*} [Fintype H] {o n : ℕ}
 (s t : Schedule) (T : H → Tree Q Q o n) (hT : ∀ h, IsLocalScheduleTree (T h))
 {A B : H → MatJoint} (hA : IsBranchFamily A) (hB : IsBranchFamily B)
 (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h)) :
 branchDistance (scheduleFamily t (continueFamily T (scheduleFamily s A)))
   (scheduleFamily t (continueFamily T (scheduleFamily s B))) ≤
 (alpha t*alpha s)*branchDistance A B := by
 have hms : ∀ h, ptrace2 (scheduleFamily s A h) = ptrace2 (scheduleFamily s B h) :=
  fun h => same_marginal_environment (FiniteNontracialSchedule.normalized s) (hm h)
 have hcut := continueFamily_same_marginal T hT hms
 have hfirst := scheduleFamily_downstream_contraction s T hA hB hm
 have hsecond := scheduleFamily_contraction t
  (continueFamily_valid T (scheduleFamily_valid s hA))
  (continueFamily_valid T (scheduleFamily_valid s hB)) hcut
 have hapos : 0 ≤ alpha t := le_trans (FiniteNontracialSchedule.coefficients t).1.le
  (FiniteNontracialSchedule.coefficients t).2.1
 calc
  _ ≤ alpha t*branchDistance (continueFamily T (scheduleFamily s A))
     (continueFamily T (scheduleFamily s B)) := hsecond
  _ ≤ alpha t*(alpha s*branchDistance A B) := mul_le_mul_of_nonneg_left hfirst hapos
  _ = _ := by ring
end SKEFTHawking.QuantumNetwork.FiniteNontracialEnvironmentLift
