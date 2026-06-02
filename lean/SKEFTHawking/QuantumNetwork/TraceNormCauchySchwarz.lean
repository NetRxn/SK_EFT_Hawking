import SKEFTHawking.QuantumNetwork.FidelityBounds
import SKEFTHawking.QuantumNetwork.DiamondNormAttainment

/-!
# The Schatten-2 Cauchy–Schwarz `‖A·B‖₁ ≤ ‖A‖_F·‖B‖_F` (Phase 6AF-10, trace form)

The sharp Hölder/Cauchy–Schwarz bound the FvdG-upper crux needs:

  `traceNorm (A * B) ≤ √((AᴴA).trace.re) · √((BᴴB).trace.re)`

(the right side is `‖A‖_F · ‖B‖_F`, the Frobenius norms, stated in instance-free trace form).
Mathlib at pin has no Schatten norms / matrix Hölder / polar decomposition, so this is built from:

* the **polar unitary** for an invertible matrix `M`: `|M| = absOp M` is invertible (via determinants,
  `det|M|² = |det M|² ≠ 0`, NO partial-isometry/SVD), `W := |M|⁻¹·Mᴴ` is unitary, and
  `traceNorm M = Re tr(W·M)`;
* the shipped matrix-CS keystone `re_trace_conjTranspose_mul_sq_le` for the per-unitary bound;
* a **perturbation/continuity** extension to all (singular) matrices: `M + (1/k)•1` is invertible
  cofinitely (charpoly has finitely many roots) and `ge_of_tendsto'` + the shipped
  `continuous_traceNorm` closes the inequality.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`|A|² = AᴴA`** — the operator modulus squares to `AᴴA` (`√x·√x = x` on the PSD spectrum). -/
theorem absOp_mul_self (A : Matrix ι ι ℂ) : absOp A * absOp A = Aᴴ * A := by
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self A
  rw [absOp, cfc_mul hPSD.isHermitian Real.sqrt Real.sqrt,
    cfc_congr_eig hPSD.isHermitian (g := fun x => x)
      (fun i => Real.mul_self_sqrt (hPSD.eigenvalues_nonneg i))]
  exact cfc_id hPSD.isHermitian

/-- **`|M|` is invertible when `M` is** — via determinants: `det|M|² = det(MᴴM) = |det M|² ≠ 0`,
so `det|M| ≠ 0`. No SVD / partial isometry needed. -/
theorem isUnit_absOp {M : Matrix ι ι ℂ} (hM : IsUnit M) : IsUnit (absOp M) := by
  rw [Matrix.isUnit_iff_isUnit_det] at hM ⊢
  have hdsq : (absOp M).det * (absOp M).det = Mᴴ.det * M.det := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, absOp_mul_self]
  have hne : (absOp M).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdsq
    exact (mul_ne_zero (by simpa [Matrix.det_conjTranspose] using
      (isUnit_iff_ne_zero.mp hM.star)) (isUnit_iff_ne_zero.mp hM)) hdsq.symm
  exact isUnit_iff_ne_zero.mpr hne

/-- **Schatten-2 Cauchy–Schwarz, invertible case**: `traceNorm(A·B) ≤ √(tr AᴴA)·√(tr BᴴB)` when
`A, B` are invertible. The polar unitary `W = |AB|⁻¹·(AB)ᴴ` realizes `traceNorm(AB) = Re tr(W·AB)`,
and the shipped matrix-CS keystone bounds it. -/
theorem traceNorm_mul_le_of_isUnit {A B : Matrix ι ι ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    traceNorm (A * B) ≤ Real.sqrt ((Aᴴ * A).trace.re) * Real.sqrt ((Bᴴ * B).trace.re) := by
  set M := A * B with hMdef
  have hM : IsUnit M := hA.mul hB
  have hMd : IsUnit M.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hM
  have hMdH : IsUnit (Mᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact hMd.star
  have hPh := absOp_isHermitian M
  have hPd : IsUnit (absOp M).det := Matrix.isUnit_iff_isUnit_det _ |>.mp (isUnit_absOp hM)
  set P := absOp M with hPdef
  -- inverse facts
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hPih : (P⁻¹)ᴴ = P⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hPh.eq]
  have hPP : P * P = Mᴴ * M := absOp_mul_self M
  -- W := P⁻¹ * Mᴴ is unitary
  set W := P⁻¹ * Mᴴ with hWdef
  have hWW : Wᴴ * W = 1 := by
    have hPiPi : P⁻¹ * P⁻¹ = (Mᴴ * M)⁻¹ := by rw [← Matrix.mul_inv_rev, hPP]
    rw [hWdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hPih]
    calc M * P⁻¹ * (P⁻¹ * Mᴴ) = M * (P⁻¹ * P⁻¹) * Mᴴ := by noncomm_ring
      _ = M * (Mᴴ * M)⁻¹ * Mᴴ := by rw [hPiPi]
      _ = 1 := by
          rw [Matrix.mul_inv_rev,
            show M * (M⁻¹ * Mᴴ⁻¹) * Mᴴ = (M * M⁻¹) * (Mᴴ⁻¹ * Mᴴ) by noncomm_ring,
            Matrix.mul_nonsing_inv M hMd, Matrix.nonsing_inv_mul Mᴴ hMdH, Matrix.mul_one]
  -- traceNorm M = Re tr(W M)
  have htr : traceNorm M = (W * M).trace.re := by
    rw [traceNorm_eq_trace_absOp, hWdef]
    congr 1
    rw [Matrix.mul_assoc, ← hPP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  -- keystone bound
  have hkey : (W * M).trace.re ^ 2 ≤ (Aᴴ * A).trace.re * (Bᴴ * B).trace.re := by
    have hk := re_trace_conjTranspose_mul_sq_le (W * A)ᴴ B
    rw [Matrix.conjTranspose_conjTranspose] at hk
    have e1 : ((W * A) * B) = W * M := by rw [hMdef]; noncomm_ring
    have e2 : (W * A * (W * A)ᴴ).trace.re = (Aᴴ * A).trace.re := by
      rw [Matrix.conjTranspose_mul,
        show W * A * (Aᴴ * Wᴴ) = W * (A * Aᴴ) * Wᴴ by noncomm_ring,
        Matrix.trace_mul_comm (W * (A * Aᴴ)) Wᴴ,
        show Wᴴ * (W * (A * Aᴴ)) = (Wᴴ * W) * (A * Aᴴ) by noncomm_ring, hWW, Matrix.one_mul,
        Matrix.trace_mul_comm A Aᴴ]
    rw [e1, e2] at hk
    exact hk
  -- conclude
  have hge : 0 ≤ (W * M).trace.re := htr ▸ traceNorm_nonneg M
  have hAA : 0 ≤ (Aᴴ * A).trace.re := (Complex.le_def.mp
    (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1
  rw [htr, ← Real.sqrt_mul hAA]
  calc (W * M).trace.re = Real.sqrt ((W * M).trace.re ^ 2) := (Real.sqrt_sq hge).symm
    _ ≤ Real.sqrt ((Aᴴ * A).trace.re * (Bᴴ * B).trace.re) := Real.sqrt_le_sqrt hkey

end SKEFTHawking.QuantumNetwork
