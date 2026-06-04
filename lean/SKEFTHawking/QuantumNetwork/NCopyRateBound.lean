import SKEFTHawking.QuantumNetwork.KroneckerPower
import SKEFTHawking.QuantumNetwork.MaxEntNegativity

/-!
# Regularized n-copy distillation rate bound (Phase 6AK, Wave FU-6 brick 6b)

The asymptotic capstone of `E_D ≤ E_N`. Working on the **grouped `n`-copy bipartite system**
`(KronIdx (Fin dA) n) × (KronIdx (Fin dB) n)` (all `A`-subsystems on one side, all `B`-subsystems on
the other), this module proves:

* `logNegB_ncopy : E_N(ρ^⊗n) = n·E_N(ρ)` — n-fold additivity on the actual grouped state (not just
  the representative of brick 3), via the grouped-tensor partial-transpose distribution;
* `logNegB_ncopy_localKraus_le : E_N(Λ(ρ^⊗n)) ≤ n·E_N(ρ)` — the **regularized rate bound**: any
  local operation on `n` copies of `ρ` produces at most `n·E_N(ρ)` of log-negativity. With the
  max-entangled target value `E_N(Φ_k) = log₂ k` (brick 4) this is the per-`n` reading
  `log₂ k ≤ n·E_N(ρ)` of `E_D ≤ E_N`.

Key technical bricks: cross-type trace-norm reindex invariance (`traceNorm_reindex_cross`), the
grouped-tensor partial-transpose distribution (`ptB_gtensor`), and the grouped `n`-copy `ncopy`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

/-- **Cross-type trace-norm reindex invariance:** `‖M.submatrix e e‖₁ = ‖M‖₁` for any bijection
`e : ι ≃ κ` (the trace norm depends only on the singular charpoly, preserved by simultaneous
row/column reindexing). Generalizes `traceNorm_submatrix_equiv` from `ι ≃ ι` to `ι ≃ κ`. -/
theorem traceNorm_reindex_cross {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix κ κ ℂ) : traceNorm (M.submatrix e e) = traceNorm M := by
  rw [traceNorm_eq_sqrtRootSum, traceNorm_eq_sqrtRootSum, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  congr 1
  rw [show (Mᴴ * M).submatrix (⇑e) (⇑e) = Matrix.reindex e.symm e.symm (Mᴴ * M) by
        simp [Matrix.reindex_apply], Matrix.charpoly_reindex]

variable {A B A' B' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']

/-- The **bipartite regroup** `(A × B) × (A' × B') ≃ (A × A') × (B × B')`: gather the two `A`-parties
and the two `B`-parties. This is `Equiv.prodProdProdComm`. -/
abbrev regroupBip : (A × B) × (A' × B') ≃ (A × A') × (B × B') := Equiv.prodProdProdComm A B A' B'

/-- The **grouped tensor product**: `ρ ⊗ σ` reindexed so the `A`-parties group and the `B`-parties
group, living on `(A × A') × (B × B')`. -/
noncomputable def gtensor (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix (A' × B') (A' × B') ℂ) :
    Matrix ((A × A') × (B × B')) ((A × A') × (B × B')) ℂ :=
  Matrix.reindex regroupBip regroupBip (ρ ⊗ₖ σ)

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- **The partial transpose distributes over the grouped tensor:**
`(ρ ⊗ σ)^Γ = ρ^Γ ⊗ σ^Γ` on the grouped system. -/
theorem ptB_gtensor (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix (A' × B') (A' × B') ℂ) :
    ptB (gtensor ρ σ) = gtensor (ptB ρ) (ptB σ) := by
  ext p q
  obtain ⟨⟨a, a'⟩, ⟨b, b'⟩⟩ := p
  obtain ⟨⟨c, c'⟩, ⟨d, d'⟩⟩ := q
  simp only [ptB, gtensor, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    regroupBip, Equiv.prodProdProdComm, Equiv.symm, Equiv.coe_fn_mk, Matrix.kronecker_apply]

/-- **Trace-norm multiplicativity over the grouped tensor:** `‖(ρ ⊗ σ)^Γ‖₁ = ‖ρ^Γ‖₁·‖σ^Γ‖₁`. -/
theorem traceNorm_ptB_gtensor (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix (A' × B') (A' × B') ℂ) :
    traceNorm (ptB (gtensor ρ σ)) = traceNorm (ptB ρ) * traceNorm (ptB σ) := by
  rw [ptB_gtensor, gtensor, Matrix.reindex_apply, traceNorm_reindex_cross, traceNorm_kronecker]

variable {dA dB : ℕ}

/-- The **grouped `n`-copy state** `ρ^⊗n` on `(KronIdx (Fin dA) n) × (KronIdx (Fin dB) n)`: all `A`
parties on one side, all `B` parties on the other. Recursively `ρ^⊗(n+1) = ρ ⊗ ρ^⊗n` (grouped). -/
noncomputable def ncopy (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    ∀ n, Matrix (KronIdx (Fin dA) n × KronIdx (Fin dB) n)
      (KronIdx (Fin dA) n × KronIdx (Fin dB) n) ℂ
  | 0 => 1
  | n + 1 => gtensor ρ (ncopy ρ n)

/-- `‖1‖₁ = 1` for the identity on the trivial `(Fin 1 × Fin 1)` index. -/
theorem traceNorm_one_unit :
    traceNorm (1 : Matrix (KronIdx (Fin dA) 0 × KronIdx (Fin dB) 0)
      (KronIdx (Fin dA) 0 × KronIdx (Fin dB) 0) ℂ) = 1 := by
  have hc : Fintype.card (KronIdx (Fin dA) 0 × KronIdx (Fin dB) 0) = 1 := rfl
  rw [traceNorm_posSemidef Matrix.PosSemidef.one, Matrix.trace_one, hc]
  simp

/-- The partial transpose of the identity on the trivial unit index is the identity. -/
theorem ptB_one_unit :
    ptB (1 : Matrix (KronIdx (Fin dA) 0 × KronIdx (Fin dB) 0)
      (KronIdx (Fin dA) 0 × KronIdx (Fin dB) 0) ℂ) = 1 := by
  haveI : Subsingleton (KronIdx (Fin dA) 0) := inferInstanceAs (Subsingleton (Fin 1))
  haveI : Subsingleton (KronIdx (Fin dB) 0) := inferInstanceAs (Subsingleton (Fin 1))
  ext p q
  simp only [ptB, Matrix.of_apply]
  rw [Subsingleton.elim (p.1, q.2) p, Subsingleton.elim (q.1, p.2) q]

/-- **n-fold trace-norm multiplicativity:** `‖(ρ^⊗n)^Γ‖₁ = ‖ρ^Γ‖₁ⁿ`. -/
theorem traceNorm_ptB_ncopy (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (n : ℕ) :
    traceNorm (ptB (ncopy ρ n)) = (traceNorm (ptB ρ)) ^ n := by
  induction n with
  | zero => rw [pow_zero, ncopy, ptB_one_unit, traceNorm_one_unit]
  | succ k ih =>
    rw [pow_succ', ← ih]
    exact traceNorm_ptB_gtensor ρ (ncopy ρ k)

/-- **n-fold log-negativity additivity on the actual grouped `n`-copy state:**
`E_N(ρ^⊗n) = n·E_N(ρ)`. -/
theorem logNegB_ncopy (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (n : ℕ) :
    logNegB (ncopy ρ n) = n * logNegB ρ := by
  unfold logNegB
  rw [traceNorm_ptB_ncopy, Real.logb_pow]

/-- **Regularized `n`-copy distillation rate bound:** a local operation on the first party of the
grouped `n`-copy state `ρ^⊗n` produces at most `n·E_N(ρ)` of log-negativity. With the maximally
entangled target value `E_N(Φ_k) = log₂ k` (brick 4), this is the per-`n` reading
`log₂ k ≤ n·E_N(ρ)` of the regularized `E_D ≤ E_N` bound. -/
theorem logNegB_ncopy_localKraus_le {n m : ℕ}
    {M : Fin m → Matrix (KronIdx (Fin dA) n) (KronIdx (Fin dA) n) ℂ} (hM : IsKrausChannel M)
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hρ : (ncopy ρ n).IsHermitian)
    (hpos : 0 < traceNorm (ptB (krausMap (fun a => M a ⊗ₖ 1) (ncopy ρ n)))) :
    logNegB (krausMap (fun a => M a ⊗ₖ 1) (ncopy ρ n)) ≤ n * logNegB ρ := by
  calc logNegB (krausMap (fun a => M a ⊗ₖ 1) (ncopy ρ n))
      ≤ logNegB (ncopy ρ n) := logNegB_localKraus_le hM hρ hpos
    _ = n * logNegB ρ := logNegB_ncopy ρ n

end SKEFTHawking.QuantumNetwork
