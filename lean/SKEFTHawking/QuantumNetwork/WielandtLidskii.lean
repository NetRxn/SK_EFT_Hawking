import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Spectrum
import SKEFTHawking.QuantumNetwork.SpectralMajorization

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

/-- A vector in the span of an eigenvector subset has vanishing coordinates outside the subset. -/
theorem repr_eq_zero_of_not_mem {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {s : Set (Fin n)} {v : E}
    (hv : v ∈ Submodule.span 𝕜 (⇑(hT.eigenvectorBasis hn) '' s)) {i : Fin n} (hi : i ∉ s) :
    (hT.eigenvectorBasis hn).repr v i = 0 := by
  set b := hT.eigenvectorBasis hn with hb
  rw [show (⇑b '' s) = (⇑b.toBasis '' s) by rw [OrthonormalBasis.coe_toBasis]] at hv
  have hsupp := Module.Basis.repr_support_subset_of_mem_span b.toBasis s hv
  have hni : (b.toBasis.repr v) i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (hsupp h))
  rwa [OrthonormalBasis.coe_toBasis_repr_apply] at hni

/-- The span of an eigenvector subset has dimension equal to the subset cardinality. -/
theorem finrank_eigenspace_span {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (s : Finset (Fin n)) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (⇑(hT.eigenvectorBasis hn) '' (s : Set (Fin n)))) = s.card := by
  set b := hT.eigenvectorBasis hn with hb
  have hli : LinearIndependent 𝕜 (fun i : (s : Set (Fin n)) => b i) :=
    (b.orthonormal.comp _ Subtype.val_injective).linearIndependent
  rw [Set.image_eq_range, finrank_span_eq_card hli, ← Set.toFinset_card]
  simp

/-- **Courant–Fischer, "≥" direction (single eigenvalue).** There is an `(m+1)`-dimensional subspace on
which the Rayleigh form is everywhere `≥ λ↓ₘ ‖·‖²` — namely the span of the top `m+1` eigenvectors. -/
theorem exists_subspace_re_inner_ge {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {m : ℕ} (hm : m < n) :
    ∃ V : Submodule 𝕜 E, Module.finrank 𝕜 V = m + 1 ∧
      ∀ v ∈ V, hT.eigenvalues hn ⟨m, hm⟩ * ‖v‖ ^ 2 ≤ RCLike.re (inner 𝕜 v (T v)) := by
  refine ⟨Submodule.span 𝕜 (⇑(hT.eigenvectorBasis hn) ''
    ((Finset.univ.filter (fun i : Fin n => (i : ℕ) < m + 1)) : Set (Fin n))), ?_, fun v hv => ?_⟩
  · rw [finrank_eigenspace_span, Fin.card_filter_val_lt]; omega
  · refine isSymmetric_re_inner_ge hT hn v (hT.eigenvalues hn ⟨m, hm⟩) (fun i hrepr => ?_)
    have hmem : i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m + 1) := by
      by_contra hi
      exact hrepr (repr_eq_zero_of_not_mem hT hn hv (Finset.mem_coe.not.mpr hi))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hT.eigenvalues_antitone hn (by rw [Fin.le_def]; exact Nat.lt_succ_iff.mp hmem)

/-- **Courant–Fischer, "≤" direction (single eigenvalue).** Every `(m+1)`-dimensional subspace contains a
nonzero vector with Rayleigh form `≤ λ↓ₘ ‖·‖²` — it meets the span of the bottom `n−m` eigenvectors. -/
theorem exists_mem_re_inner_le {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {m : ℕ} (hm : m < n)
    (V : Submodule 𝕜 E) (hV : Module.finrank 𝕜 V = m + 1) :
    ∃ v ∈ V, v ≠ 0 ∧ RCLike.re (inner 𝕜 v (T v)) ≤ hT.eigenvalues hn ⟨m, hm⟩ * ‖v‖ ^ 2 := by
  set Wbot := Submodule.span 𝕜 (⇑(hT.eigenvectorBasis hn) ''
    ((Finset.univ.filter (fun i : Fin n => m ≤ (i : ℕ))) : Set (Fin n))) with hWbot
  have hWdim : Module.finrank 𝕜 Wbot = n - m := by
    rw [hWbot, finrank_eigenspace_span]
    have h := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin n)))
      (p := fun i : Fin n => m ≤ (i : ℕ))
    rw [Finset.card_univ, Fintype.card_fin] at h
    have hneg : (Finset.univ.filter (fun i : Fin n => ¬ m ≤ (i : ℕ))).card = m := by
      have heq : (Finset.univ.filter (fun i : Fin n => ¬ m ≤ (i : ℕ)))
          = Finset.univ.filter (fun i : Fin n => (i : ℕ) < m) :=
        Finset.filter_congr (fun i _ => by simp [Nat.not_le])
      rw [heq, Fin.card_filter_val_lt]
      omega
    omega
  have hgt : Module.finrank 𝕜 E < Module.finrank 𝕜 V + Module.finrank 𝕜 Wbot := by
    rw [hV, hWdim, hn]; omega
  obtain ⟨x, hx, hx0⟩ := exists_mem_inf_ne_zero V Wbot hgt
  refine ⟨x, hx.1, hx0, ?_⟩
  refine isSymmetric_re_inner_le hT hn x (hT.eigenvalues hn ⟨m, hm⟩) (fun i hrepr => ?_)
  have hmem : i ∈ Finset.univ.filter (fun i : Fin n => m ≤ (i : ℕ)) := by
    by_contra hi
    exact hrepr (repr_eq_zero_of_not_mem hT hn hx.2 (Finset.mem_coe.not.mpr hi))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hT.eigenvalues_antitone hn (by rw [Fin.le_def]; exact hmem)

/-- **Ky Fan frame inequality (step 2).** For any orthonormal `k`-frame `{wᵣ}`, the Rayleigh sum
`∑ᵣ re⟪wᵣ, T wᵣ⟫ ≤ ∑_{j<k} λ↓ⱼ(T)` (sum of the `k` largest eigenvalues). Via the quadratic-form expansion,
the Bessel weights `pᵢ = ∑ᵣ ‖cᵢ(wᵣ)‖² ∈ [0,1]` (summing to `k`), and the shipped rearrangement
`sum_mul_le_sum_top`. -/
theorem isSymmetric_sum_re_inner_le_top {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {k : ℕ} {w : Fin k → E}
    (hw : Orthonormal 𝕜 w) :
    ∑ r, RCLike.re (inner 𝕜 (w r) (T (w r)))
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), hT.eigenvalues hn i := by
  set b := hT.eigenvectorBasis hn with hb
  have hexp : ∑ r, RCLike.re (inner 𝕜 (w r) (T (w r)))
      = ∑ i, hT.eigenvalues hn i * ∑ r, ‖b.repr (w r) i‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun r _ => isSymmetric_re_inner_self_eq_sum hT hn (w r)),
      Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
  rw [hexp]
  set p : Fin n → ℝ := fun i => ∑ r, ‖b.repr (w r) i‖ ^ 2 with hp
  have hp0 : ∀ i, 0 ≤ p i := fun i => Finset.sum_nonneg fun r _ => sq_nonneg _
  have hp1 : ∀ i, p i ≤ 1 := by
    intro i
    have hb1 : ‖b i‖ ^ 2 = 1 := by rw [b.orthonormal.1 i]; norm_num
    have hbes := hw.sum_inner_products_le (b i) (s := Finset.univ)
    rw [hb1] at hbes
    refine le_trans (le_of_eq ?_) hbes
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [b.repr_apply_apply, ← inner_conj_symm, RCLike.norm_conj]
  have hpsum : ∑ i, p i = (k : ℝ) := by
    rw [hp, Finset.sum_comm,
      Finset.sum_congr rfl (fun r _ => (eigenvectorBasis_norm_sq_eq_sum hT hn (w r)).symm)]
    simp [hw.1]
  exact sum_mul_le_sum_top (hT.eigenvalues hn) (hT.eigenvalues_antitone hn) p hp0 hp1 k hpsum

/-- **Flag Rayleigh lower bound (step 1).** For an orthonormal frame `{wᵣ}` with each `wᵣ` in the span of
the top `sᵣ+1` eigenvectors (A's eigen-flag), the Rayleigh sum is bounded below by the flag eigenvalues:
`∑ᵣ λ↓_{sᵣ}(T) ≤ ∑ᵣ re⟪wᵣ, T wᵣ⟫`. Each term is `isSymmetric_re_inner_ge` with `c = λ↓_{sᵣ}`. -/
theorem isSymmetric_sum_re_inner_ge_flag {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {k : ℕ} {s : Fin k → ℕ} (hs : ∀ r, s r < n)
    {w : Fin k → E} (hwn : ∀ r, ‖w r‖ = 1)
    (hw : ∀ r, w r ∈ Submodule.span 𝕜
      (⇑(hT.eigenvectorBasis hn) '' ({i : Fin n | (i : ℕ) ≤ s r} : Set (Fin n)))) :
    ∑ r, hT.eigenvalues hn ⟨s r, hs r⟩ ≤ ∑ r, RCLike.re (inner 𝕜 (w r) (T (w r))) := by
  refine Finset.sum_le_sum (fun r _ => ?_)
  have hge := isSymmetric_re_inner_ge hT hn (w r) (hT.eigenvalues hn ⟨s r, hs r⟩) (fun i hrepr => ?_)
  · rw [hwn r] at hge; simpa using hge
  · have hmem : (i : ℕ) ≤ s r := by
      by_contra hi
      exact hrepr (repr_eq_zero_of_not_mem hT hn (hw r) (by rw [Set.mem_setOf_eq]; exact hi))
    exact hT.eigenvalues_antitone hn (by rw [Fin.le_def]; exact hmem)

/-- **Weyl's single-eigenvalue perturbation bound (lower form):** `λ↓ᵢ(S+R) ≥ λ↓ᵢ(S) + λ↓ₙ₋₁(R)`, where
`λ↓ₙ₋₁(R)` is the smallest eigenvalue of `R`. Courant–Fischer "max–min": on `S`'s top-`(i+1)` eigenspace `V`
the Rayleigh quotient of `S+R` is `≥ λ↓ᵢ(S) + λ↓ₙ₋₁(R)` (since `⟪v,Sv⟫ ≥ λ↓ᵢ(S)‖v‖²` on `V` and
`⟪v,Rv⟫ ≥ λ↓ₙ₋₁(R)‖v‖²` everywhere), and any `(i+1)`-dim subspace contains a vector with `S+R`-Rayleigh
`≤ λ↓ᵢ(S+R)` (`exists_mem_re_inner_le`). Applying this twice (with `R ↦ −R`) yields the full Weyl two-sided
bound and the Lipschitz continuity `|λ↓ᵢ(A)−λ↓ᵢ(B)| ≤ ‖A−B‖`, the regularity input (P1) for the
eigenvalue-path proof of Lidskii. Reusable; absent from Mathlib. -/
theorem weyl_single_lower {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    {S R : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hR : R.IsSymmetric) {i : ℕ} (hi : i < n) :
    hS.eigenvalues hn ⟨i, hi⟩ + hR.eigenvalues hn ⟨n - 1, by omega⟩
      ≤ (hS.add hR).eigenvalues hn ⟨i, hi⟩ := by
  obtain ⟨V, hVdim, hVge⟩ := exists_subspace_re_inner_ge hS hn hi
  have hRge : ∀ v : E,
      hR.eigenvalues hn ⟨n - 1, by omega⟩ * ‖v‖ ^ 2 ≤ RCLike.re (inner 𝕜 v (R v)) := by
    intro v
    refine isSymmetric_re_inner_ge hR hn v _ (fun j _ => ?_)
    refine hR.eigenvalues_antitone hn ?_
    rw [Fin.le_def]; show (j : ℕ) ≤ n - 1; have := j.isLt; omega
  obtain ⟨v, hvV, hv0, hvle⟩ := exists_mem_re_inner_le (hS.add hR) hn hi V hVdim
  have h1 := hVge v hvV
  have h2 := hRge v
  have hadd : RCLike.re (inner 𝕜 v ((S + R) v))
      = RCLike.re (inner 𝕜 v (S v)) + RCLike.re (inner 𝕜 v (R v)) := by
    rw [LinearMap.add_apply, inner_add_right, map_add]
  rw [hadd] at hvle
  have hvnorm : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
  have hcomb : (hS.eigenvalues hn ⟨i, hi⟩ + hR.eigenvalues hn ⟨n - 1, by omega⟩) * ‖v‖ ^ 2
      ≤ (hS.add hR).eigenvalues hn ⟨i, hi⟩ * ‖v‖ ^ 2 := by rw [add_mul]; linarith
  exact le_of_mul_le_mul_right hcomb hvnorm

/-- **Weyl single-eigenvalue bound, general form** (`T = S + R` as a hypothesis, avoiding operator-congruence
at use sites — e.g. along a perturbation path `M(t) = M(s) + (t−s)C`): `λ↓ᵢ(T) ≥ λ↓ᵢ(S) + λ↓ₙ₋₁(R)`. Same
Courant–Fischer proof as `weyl_single_lower`, reading `⟪v,Tv⟫ = ⟪v,Sv⟫ + ⟪v,Rv⟫` through `T = S+R`. -/
theorem weyl_single_lower_of_eq {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    {T S R : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hR : R.IsSymmetric)
    (hTeq : T = S + R) {i : ℕ} (hi : i < n) :
    hS.eigenvalues hn ⟨i, hi⟩ + hR.eigenvalues hn ⟨n - 1, by omega⟩ ≤ hT.eigenvalues hn ⟨i, hi⟩ := by
  obtain ⟨V, hVdim, hVge⟩ := exists_subspace_re_inner_ge hS hn hi
  have hRge : ∀ v : E,
      hR.eigenvalues hn ⟨n - 1, by omega⟩ * ‖v‖ ^ 2 ≤ RCLike.re (inner 𝕜 v (R v)) := by
    intro v
    refine isSymmetric_re_inner_ge hR hn v _ (fun j _ => ?_)
    refine hR.eigenvalues_antitone hn ?_
    rw [Fin.le_def]; show (j : ℕ) ≤ n - 1; have := j.isLt; omega
  obtain ⟨v, hvV, hv0, hvle⟩ := exists_mem_re_inner_le hT hn hi V hVdim
  have hTv : RCLike.re (inner 𝕜 v (T v))
      = RCLike.re (inner 𝕜 v (S v)) + RCLike.re (inner 𝕜 v (R v)) := by
    rw [hTeq, LinearMap.add_apply, inner_add_right, map_add]
  rw [hTv] at hvle
  have h1 := hVge v hvV
  have h2 := hRge v
  have hvnorm : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
  have hcomb : (hS.eigenvalues hn ⟨i, hi⟩ + hR.eigenvalues hn ⟨n - 1, by omega⟩) * ‖v‖ ^ 2
      ≤ hT.eigenvalues hn ⟨i, hi⟩ * ‖v‖ ^ 2 := by rw [add_mul]; linarith
  exact le_of_mul_le_mul_right hcomb hvnorm

/-- **Max-min Lidskii–Wielandt, assembled (staging the frame-existence step (3)).** Given an orthonormal
frame `{wᵣ}` in `A`'s eigen-flag (`wᵣ ∈ span top sᵣ+1 A-eigenvectors`) with low `B`-Rayleigh-sum (hypothesis
`hB3` = step (3)), the arbitrary-subset Lidskii inequality follows:
`∑ᵣ λ↓_{sᵣ}(A) ≤ ∑ᵣ λ↓_{sᵣ}(B) + ∑_{j<k} λ↓ⱼ(A−B)`.
Proof: `∑λ↓_{sᵣ}(A) ≤ ∑⟨wᵣ,Awᵣ⟩` (step 1) `= ∑⟨wᵣ,Bwᵣ⟩ + ∑⟨wᵣ,(A−B)wᵣ⟩` (linearity) `≤ ∑λ↓_{sᵣ}(B) +
∑_{<k}λ↓(A−B)` (hypothesis hB3 + step 2 Ky Fan on `A−B`). Only the frame existence `hB3` remains to discharge. -/
theorem lidskii_of_frame {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n) {k : ℕ} {s : Fin k → ℕ}
    (hs : ∀ r, s r < n) {w : Fin k → E} (hw : Orthonormal 𝕜 w)
    (hwflag : ∀ r, w r ∈ Submodule.span 𝕜
      (⇑(hA.eigenvectorBasis hn) '' ({i : Fin n | (i : ℕ) ≤ s r} : Set (Fin n))))
    (hB3 : ∑ r, RCLike.re (inner 𝕜 (w r) (B (w r))) ≤ ∑ r, hB.eigenvalues hn ⟨s r, hs r⟩) :
    ∑ r, hA.eigenvalues hn ⟨s r, hs r⟩
      ≤ ∑ r, hB.eigenvalues hn ⟨s r, hs r⟩
        + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), (hA.sub hB).eigenvalues hn i := by
  have h1 := isSymmetric_sum_re_inner_ge_flag hA hn hs (fun r => hw.1 r) hwflag
  have h2 := isSymmetric_sum_re_inner_le_top (hA.sub hB) hn hw
  have hlin : ∑ r, RCLike.re (inner 𝕜 (w r) ((A - B) (w r)))
      = ∑ r, RCLike.re (inner 𝕜 (w r) (A (w r)))
        - ∑ r, RCLike.re (inner 𝕜 (w r) (B (w r))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [LinearMap.sub_apply, inner_sub_right, map_sub]
  linarith [h1, h2, hB3, hlin.symm.le, hlin.le]

end SKEFTHawking.QuantumNetwork
