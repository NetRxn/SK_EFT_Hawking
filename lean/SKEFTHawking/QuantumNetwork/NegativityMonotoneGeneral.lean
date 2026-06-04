import SKEFTHawking.QuantumNetwork.PartialTransposeGeneral
import SKEFTHawking.QuantumNetwork.CPTPChannel

/-!
# Negativity monotonicity under local operations, general bipartite parties (Phase 6AK, Wave FU-6)

Generalizes the two-qubit monotonicity (`NegativityMonotone`, FU-3) to an arbitrary bipartite system
`A × B` (any finite parties), on top of the general partial transpose `ptB`. The partial transpose
commutes with a local operation on the first (`A`) party (`ptB_conj_kronOne`), so the trace norm of
the partial transpose — hence the negativity / log-negativity — is non-increasing under any local
`A`-channel (`traceNorm_ptB_localKraus_le`). This is brick 1 of the regularized `E_D ≤ E_N` rate
bound. Arbitrary parties (instantiating `A := Fin dA`, or `A := KronIdx _ n` for grouped `n`-copy).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {m : ℕ}

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- The partial transpose preserves Hermiticity (general parties). -/
theorem ptB_isHermitian {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.IsHermitian) :
    (ptB ρ).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, ptB, Matrix.of_apply]
  exact hρ.apply (p.1, q.2) (q.1, p.2)

omit [DecidableEq A] in
/-- **Left multiplication by a local `A`-operator commutes with the `B`-partial-transpose.** -/
theorem ptB_kronOne_mul (M : Matrix A A ℂ)
    (X : Matrix (A × B) (A × B) ℂ) :
    ptB ((M ⊗ₖ (1 : Matrix B B ℂ)) * X) = (M ⊗ₖ 1) * ptB X := by
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [ptB, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

omit [DecidableEq A] in
/-- **Right multiplication by a local `A`-operator commutes with the `B`-partial-transpose.** -/
theorem ptB_mul_kronOne (N : Matrix A A ℂ)
    (X : Matrix (A × B) (A × B) ℂ) :
    ptB (X * (N ⊗ₖ (1 : Matrix B B ℂ))) = ptB X * (N ⊗ₖ 1) := by
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [ptB, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [DecidableEq A] in
/-- **The `B`-partial-transpose commutes with conjugation by a local `A`-operator.** -/
theorem ptB_conj_kronOne (M : Matrix A A ℂ)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptB ((M ⊗ₖ (1 : Matrix B B ℂ)) * ρ * (M ⊗ₖ 1)ᴴ)
      = (M ⊗ₖ 1) * ptB ρ * (M ⊗ₖ 1)ᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ptB_mul_kronOne, ptB_kronOne_mul]

omit [Fintype A] [DecidableEq A] [Fintype B] in
/-- `∑ₐ (Xₐ ⊗ 1) = (∑ₐ Xₐ) ⊗ 1` (general parties). -/
theorem sum_kronOne_general (X : Fin m → Matrix A A ℂ) :
    (∑ a, X a ⊗ₖ (1 : Matrix B B ℂ)) = (∑ a, X a) ⊗ₖ 1 := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [Matrix.sum_apply, Matrix.kronecker_apply]
  rw [← Finset.sum_mul]

/-- **A local `A`-channel is a CPTP channel** on the joint system. -/
theorem isKrausChannel_kronOne_general {M : Fin m → Matrix A A ℂ}
    (hM : IsKrausChannel M) :
    IsKrausChannel (fun a => M a ⊗ₖ (1 : Matrix B B ℂ)) := by
  unfold IsKrausChannel
  have hcongr : (fun a => (M a ⊗ₖ (1 : Matrix B B ℂ))ᴴ * (M a ⊗ₖ 1))
      = fun a => ((M a)ᴴ * M a) ⊗ₖ (1 : Matrix B B ℂ) := by
    funext a
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  rw [hcongr, sum_kronOne_general, hM, Matrix.one_kronecker_one]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- The partial transpose is additive over finite sums (it is a linear reindexing). -/
theorem ptB_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (A × B) (A × B) ℂ) :
    ptB (∑ i ∈ s, f i) = ∑ i ∈ s, ptB (f i) := by
  ext p q; simp only [ptB, Matrix.of_apply, Matrix.sum_apply]

omit [DecidableEq A] in
/-- **The partial transpose commutes with a local `A`-channel.** -/
theorem ptB_krausMap_localA {M : Fin m → Matrix A A ℂ}
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptB (krausMap (fun a => M a ⊗ₖ (1 : Matrix B B ℂ)) ρ)
      = krausMap (fun a => M a ⊗ₖ 1) (ptB ρ) := by
  unfold krausMap
  rw [ptB_sum]
  exact Finset.sum_congr rfl fun a _ => ptB_conj_kronOne (M a) ρ

/-- **Entanglement monotonicity at general bipartite parties:** the trace norm of the partial
transpose — hence the negativity — is non-increasing under any local operation on the first party. -/
theorem traceNorm_ptB_localKraus_le {M : Fin m → Matrix A A ℂ} (hM : IsKrausChannel M)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.IsHermitian) :
    traceNorm (ptB (krausMap (fun a => M a ⊗ₖ 1) ρ)) ≤ traceNorm (ptB ρ) := by
  rw [ptB_krausMap_localA]
  exact traceNorm_krausMap_le (isKrausChannel_kronOne_general hM) (ptB_isHermitian hρ)

end SKEFTHawking.QuantumNetwork
