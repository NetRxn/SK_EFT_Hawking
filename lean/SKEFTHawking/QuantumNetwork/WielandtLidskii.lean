import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Wielandt min-max toward arbitrary-index Lidskii (Phase 6AL, Wave 4, item F1b core ∃P)

The genuine arbitrary-index Lidskii–Wielandt content underlying the trace-norm Mirsky inequality. The
top-level target (numerically validated, `mirsky_of_proj_exists` consumes it) is **single-frame existence**:
for every subset `S` there is a rank-`|S|` orthogonal projection simultaneously high for `A` and low for `B`.
We build toward it via the Courant–Fischer / Wielandt subspace machinery (Mathlib has only the *extreme*
eigenvalues via `hasEigenvalue_iSup/iInf`; the indexed min-max is absent).

This file starts with the **subspace-intersection dimension lemma** — the load-bearing technique for both the
single-eigenvalue Courant–Fischer "≤" direction and the Wielandt frame construction: two subspaces whose
dimensions sum past the ambient dimension meet in a nonzero vector.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- **Subspace-intersection dimension lemma.** Two finite-dimensional subspaces whose dimensions sum to
strictly more than the ambient dimension intersect in a nonzero vector. This is the core counting step of
the Courant–Fischer min-max (a candidate subspace meets a complementary eigenspace) and of the Wielandt
frame construction. -/
theorem exists_mem_inf_ne_zero {K : Type*} {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (s t : Submodule K V)
    (h : Module.finrank K V < Module.finrank K s + Module.finrank K t) :
    ∃ x ∈ s ⊓ t, x ≠ 0 := by
  have hsup : Module.finrank K (s ⊔ t : Submodule K V) ≤ Module.finrank K V := Submodule.finrank_le _
  have hkey : Module.finrank K (s ⊔ t : Submodule K V) + Module.finrank K (s ⊓ t : Submodule K V)
      = Module.finrank K s + Module.finrank K t := Submodule.finrank_sup_add_finrank_inf_eq s t
  have hpos : 0 < Module.finrank K (s ⊓ t : Submodule K V) := by omega
  have hnt : Nontrivial (s ⊓ t : Submodule K V) := Module.finrank_pos_iff.mp hpos
  obtain ⟨y, hy⟩ := exists_ne (0 : (s ⊓ t : Submodule K V))
  exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0)⟩

/-- **Quadratic-form spectral expansion.** For a symmetric operator `T`, the (complex) Rayleigh form
`⟪v, T v⟫` equals `∑ᵢ λᵢ · ‖cᵢ‖²` where `cᵢ = (eigenbasis).repr v i`. The diagonal action
`repr(Tv)ᵢ = λᵢ·repr(v)ᵢ` through the `repr` isometry gives it. -/
theorem isSymmetric_inner_self_eq_sum {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) :
    (inner 𝕜 v (T v) : 𝕜)
      = ∑ i, (hT.eigenvalues hn i : 𝕜) * ((‖(hT.eigenvectorBasis hn).repr v i‖ : 𝕜) ^ 2) := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map v (T v),
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have happly := hT.eigenvectorBasis_apply_self_apply hn v i
  rw [Pi.star_apply, happly, mul_assoc, RCLike.star_def, RCLike.mul_conj]

/-- Real Rayleigh form spectral expansion: `re ⟪v, T v⟫ = ∑ᵢ λᵢ ‖cᵢ‖²`. -/
theorem isSymmetric_re_inner_self_eq_sum {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) :
    RCLike.re (inner 𝕜 v (T v))
      = ∑ i, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 := by
  rw [isSymmetric_inner_self_eq_sum hT hn v, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- Parseval: `‖v‖² = ∑ᵢ ‖cᵢ‖²` in the eigenbasis coordinates. -/
theorem eigenvectorBasis_norm_sq_eq_sum {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map v, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]

/-- **Rayleigh lower bound on an eigenspace.** If every eigenbasis coordinate of `v` that is nonzero has
its eigenvalue `≥ c`, then the Rayleigh form `re ⟪v, T v⟫ ≥ c ‖v‖²`. (Take `v` in the span of eigenvectors
with eigenvalues `≥ c`.) -/
theorem isSymmetric_re_inner_ge {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) (c : ℝ)
    (hc : ∀ i, (hT.eigenvectorBasis hn).repr v i ≠ 0 → c ≤ hT.eigenvalues hn i) :
    c * ‖v‖ ^ 2 ≤ RCLike.re (inner 𝕜 v (T v)) := by
  rw [isSymmetric_re_inner_self_eq_sum hT hn v, eigenvectorBasis_norm_sq_eq_sum hT hn v,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rcases eq_or_ne ((hT.eigenvectorBasis hn).repr v i) 0 with h0 | h0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (hc i h0) (sq_nonneg _)

/-- **Rayleigh upper bound on an eigenspace.** Dual of `isSymmetric_re_inner_ge`. -/
theorem isSymmetric_re_inner_le {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) (c : ℝ)
    (hc : ∀ i, (hT.eigenvectorBasis hn).repr v i ≠ 0 → hT.eigenvalues hn i ≤ c) :
    RCLike.re (inner 𝕜 v (T v)) ≤ c * ‖v‖ ^ 2 := by
  rw [isSymmetric_re_inner_self_eq_sum hT hn v, eigenvectorBasis_norm_sq_eq_sum hT hn v,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rcases eq_or_ne ((hT.eigenvectorBasis hn).repr v i) 0 with h0 | h0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (hc i h0) (sq_nonneg _)

end SKEFTHawking.QuantumNetwork
