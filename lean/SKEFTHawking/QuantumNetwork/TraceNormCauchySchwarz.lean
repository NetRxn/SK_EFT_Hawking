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

/-- **The shift `A + diagonal(c)` is invertible for cofinitely many `k`** (`c = (k+1)⁻¹`) — the
non-invertible shifts are roots of `(-A).charpoly` (via `Matrix.eval_charpoly`), a finite set, and
the shift sequence is injective. (Uses `diagonal` rather than `c•1` to keep the downstream
perturbation off the Frobenius-`NormedSpace` `smul`-whnf wall.) -/
theorem eventually_isUnit_perturb (A : Matrix ι ι ℂ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      IsUnit (A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹)) := by
  have hpne : (-A).charpoly ≠ 0 := (Matrix.charpoly_monic (-A)).ne_zero
  have hbad : {z : ℂ | (-A).charpoly.IsRoot z}.Finite := Polynomial.finite_setOf_isRoot hpne
  have hinj : Function.Injective (fun k : ℕ => ((k : ℂ) + 1)⁻¹) := by
    intro a b hab
    have h1 : (a : ℂ) + 1 = (b : ℂ) + 1 := inv_injective hab
    exact_mod_cast add_right_cancel h1
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite]
  refine Set.Finite.subset (hbad.preimage hinj.injOn) ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hk
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly, sub_neg_eq_add, Matrix.scalar_apply, add_comm]
  exact hk

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **Schatten-2 Cauchy–Schwarz (general)**: `traceNorm(A·B) ≤ √(tr AᴴA)·√(tr BᴴB)` for ALL
matrices — the invertible case extended to singular `A, B` by perturbing `A,B ↦ A+(1/k)•1` (each
invertible cofinitely) and taking `k → ∞`, using `continuous_traceNorm` + `le_of_tendsto_of_tendsto'`. -/
theorem traceNorm_mul_le (A B : Matrix ι ι ℂ) :
    traceNorm (A * B) ≤ Real.sqrt ((Aᴴ * A).trace.re) * Real.sqrt ((Bᴴ * B).trace.re) := by
  -- single-variable continuity (no product type, to stay off the Frobenius-instance whnf wall)
  have htr_re : Continuous fun X : Matrix ι ι ℂ => (Xᴴ * X).trace.re := by
    have h1 : Continuous fun X : Matrix ι ι ℂ => Xᴴ * X :=
      (continuous_id.matrix_conjTranspose).matrix_mul continuous_id
    exact Complex.continuous_re.comp h1.matrix_trace
  have hrootc : Continuous fun X : Matrix ι ι ℂ => Real.sqrt ((Xᴴ * X).trace.re) :=
    Real.continuous_sqrt.comp htr_re
  -- the perturbation `diagonal(cₖ) → 0` (no `smul`, to dodge the Frobenius-instance whnf wall)
  have hc : Filter.Tendsto (fun k : ℕ => ((k : ℂ) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    simp only [Function.comp_def, Complex.ofReal_zero] at h2
    exact Filter.Tendsto.congr (fun n => by push_cast; rw [one_div]) h2
  have hdiagc : Continuous fun z : ℂ => Matrix.diagonal (fun _ : ι => z) :=
    Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  have hc0 : Filter.Tendsto (fun k : ℕ => Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))
      Filter.atTop (nhds 0) := by
    have := (hdiagc.tendsto 0).comp hc
    simpa using this
  have hAk : Filter.Tendsto (fun k : ℕ => A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))
      Filter.atTop (nhds A) := by simpa using tendsto_const_nhds.add hc0
  have hBk : Filter.Tendsto (fun k : ℕ => B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))
      Filter.atTop (nhds B) := by simpa using tendsto_const_nhds.add hc0
  have hABk : Filter.Tendsto (fun k : ℕ => (A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))
      * (B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))) Filter.atTop (nhds (A * B)) :=
    hAk.mul hBk
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      traceNorm ((A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))
          * (B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹)))
        ≤ Real.sqrt (((A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))ᴴ
              * (A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))).trace.re)
          * Real.sqrt (((B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))ᴴ
              * (B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))).trace.re) := by
    filter_upwards [eventually_isUnit_perturb A, eventually_isUnit_perturb B] with k hUA hUB
    exact traceNorm_mul_le_of_isUnit hUA hUB
  have hLHS : Filter.Tendsto (fun k : ℕ =>
      traceNorm ((A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))
        * (B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹)))) Filter.atTop
      (nhds (traceNorm (A * B))) := (continuous_traceNorm.tendsto (A * B)).comp hABk
  have hRHS : Filter.Tendsto (fun k : ℕ =>
      Real.sqrt (((A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))ᴴ
            * (A + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))).trace.re)
        * Real.sqrt (((B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))ᴴ
            * (B + Matrix.diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹))).trace.re)) Filter.atTop
      (nhds (Real.sqrt ((Aᴴ * A).trace.re) * Real.sqrt ((Bᴴ * B).trace.re))) :=
    ((hrootc.tendsto A).comp hAk).mul ((hrootc.tendsto B).comp hBk)
  exact le_of_tendsto_of_tendsto hLHS hRHS hev

end SKEFTHawking.QuantumNetwork
