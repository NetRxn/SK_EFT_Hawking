import SKEFTHawking.QuantumNetwork.BellNegativity

/-!
# Negativity is monotone under local operations (Phase 6AK, Wave FU-3 — rung 1)

The negativity built in `BellNegativity.lean` is an *entanglement monotone*: it cannot increase under
local operations on one party. This is the first rung of a decomposition of the Vidal–Werner
upper bound `E_D ≤ E_N` that avoids formalising the full LOCC theory. The load-bearing inequality
(trace-norm contractivity under any CPTP channel, `traceNorm_krausMap_le`) is already shipped; the only
new ingredient is that the partial transpose on the *second* qubit **commutes with a local operation on
the first qubit** (`A`-side Kraus operators `Kₐ = Mₐ ⊗ 1`):

`Tᵦ((M⊗1) ρ (M⊗1)ᴴ) = (M⊗1) (Tᵦ ρ) (M⊗1)ᴴ`  (`pt2_conj_kronOne`).

Because `M` touches only the `A`-indices and `Tᵦ` permutes only the `B`-indices, they commute. Hence the
trace norm of the partial transpose — and therefore the negativity — is non-increasing under any local
`A`-channel (`traceNorm_pt2_localKraus_le`, `negativity` monotone). Combined with the exact target value
`N(Bell pair) = ½`, this gives a genuine **one-shot distillation no-go**: a state with negativity below
the Bell-pair value cannot be converted to a Bell pair by local operations on one party.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

/-- The partial transpose preserves Hermiticity. -/
theorem pt2_isHermitian {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hρ : ρ.IsHermitian) :
    (pt2 ρ).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, pt2, Matrix.of_apply]
  exact hρ.apply (p.1, q.2) (q.1, p.2)

/-- **Left multiplication by a local `A`-operator commutes with the `B`-partial-transpose.** -/
theorem pt2_kronOne_mul (M : Matrix (Fin 2) (Fin 2) ℂ)
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pt2 ((M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * X) = (M ⊗ₖ 1) * pt2 X := by
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [pt2, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-- **Right multiplication by a local `A`-operator commutes with the `B`-partial-transpose.** -/
theorem pt2_mul_kronOne (N : Matrix (Fin 2) (Fin 2) ℂ)
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pt2 (X * (N ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) = pt2 X * (N ⊗ₖ 1) := by
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [pt2, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- **The `B`-partial-transpose commutes with conjugation by a local `A`-operator.** -/
theorem pt2_conj_kronOne (M : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pt2 ((M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ρ * (M ⊗ₖ 1)ᴴ)
      = (M ⊗ₖ 1) * pt2 ρ * (M ⊗ₖ 1)ᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, pt2_mul_kronOne, pt2_kronOne_mul]

/-! ## Local channels and trace-norm contractivity of the partial transpose -/

variable {m : ℕ}

/-- `∑ₐ (Xₐ ⊗ 1) = (∑ₐ Xₐ) ⊗ 1`. -/
theorem sum_kronOne (X : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a, X a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (∑ a, X a) ⊗ₖ 1 := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [Matrix.sum_apply, Matrix.kronecker_apply]
  rw [← Finset.sum_mul]

/-- **A local `A`-channel is a CPTP channel** on the joint system. -/
theorem isKrausChannel_kronOne {M : Fin m → Matrix (Fin 2) (Fin 2) ℂ} (hM : IsKrausChannel M) :
    IsKrausChannel (fun a => M a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold IsKrausChannel
  have hcongr : (fun a => (M a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (M a ⊗ₖ 1))
      = fun a => ((M a)ᴴ * M a) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext a
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  rw [hcongr, sum_kronOne, hM, Matrix.one_kronecker_one]

/-- **The partial transpose commutes with a local `A`-channel.** -/
theorem pt2_krausMap_localA {M : Fin m → Matrix (Fin 2) (Fin 2) ℂ}
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pt2 (krausMap (fun a => M a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ρ)
      = krausMap (fun a => M a ⊗ₖ 1) (pt2 ρ) := by
  unfold krausMap
  rw [pt2_sum]
  exact Finset.sum_congr rfl fun a _ => pt2_conj_kronOne (M a) ρ

/-- **Entanglement monotonicity (rung 1):** the trace norm of the partial transpose — hence the
negativity — is non-increasing under any local operation on one party. Proof: the partial transpose
commutes with the local channel (`pt2_krausMap_localA`), and the trace norm contracts under any CPTP
channel (`traceNorm_krausMap_le`). No LOCC theory required. -/
theorem traceNorm_pt2_localKraus_le {M : Fin m → Matrix (Fin 2) (Fin 2) ℂ} (hM : IsKrausChannel M)
    {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hρ : ρ.IsHermitian) :
    traceNorm (pt2 (krausMap (fun a => M a ⊗ₖ 1) ρ)) ≤ traceNorm (pt2 ρ) := by
  rw [pt2_krausMap_localA]
  exact traceNorm_krausMap_le (isKrausChannel_kronOne hM) (pt2_isHermitian hρ)

/-! ## One-shot distillation no-go -/

/-- `‖(Φ⁺)^Γ‖₁ = 2` for the Bell pair `|Φ⁺⟩⟨Φ⁺| = bellDiagState ![1,0,0,0]` (negativity `½`). -/
theorem traceNorm_pt2_bellPair : traceNorm (pt2 (bellDiagState ![1, 0, 0, 0])) = 2 := by
  rw [traceNorm_pt2_bellDiagState, Fin.sum_univ_four]
  have h0 : bellPTeig ![1, 0, 0, 0] 0 = 1 / 2 := by
    simp [bellPTeig, bellY, Fin.sum_univ_four] <;> norm_num
  have h1 : bellPTeig ![1, 0, 0, 0] 1 = 1 / 2 := by
    simp [bellPTeig, bellY, Fin.sum_univ_four] <;> norm_num
  have h2 : bellPTeig ![1, 0, 0, 0] 2 = -(1 / 2) := by
    simp [bellPTeig, bellY, Fin.sum_univ_four] <;> norm_num
  have h3 : bellPTeig ![1, 0, 0, 0] 3 = 1 / 2 := by
    simp [bellPTeig, bellY, Fin.sum_univ_four] <;> norm_num
  rw [h0, h1, h2, h3]; norm_num

/-- **One-shot local-distillation no-go:** if `‖ρ^Γ‖₁ < 2` (negativity below the Bell-pair value `½`),
no local operation on one party can convert `ρ` into the Bell pair. The honest, kernel-pure operational
content of "you cannot create entanglement (beyond what's present) by local operations alone" — proven
from monotonicity alone, with no asymptotics, no LOCC abstraction, and no axiom. -/
theorem no_local_distillation_to_bellPair {M : Fin m → Matrix (Fin 2) (Fin 2) ℂ}
    (hM : IsKrausChannel M) {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hρ : ρ.IsHermitian)
    (hlow : traceNorm (pt2 ρ) < 2) :
    krausMap (fun a => M a ⊗ₖ 1) ρ ≠ bellDiagState ![1, 0, 0, 0] := by
  intro h
  have hmono := traceNorm_pt2_localKraus_le hM hρ
  rw [h, traceNorm_pt2_bellPair] at hmono
  linarith

end SKEFTHawking.QuantumNetwork
