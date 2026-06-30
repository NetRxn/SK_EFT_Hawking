import SKEFTHawking.LindbladSemigroup
import Mathlib.Analysis.Matrix.Normed

/-!
# GKSL CP-semigroup theorem (Phase 6BC Wave 5 / D10 Discharge W4) — discharge of `hreal`

`LindbladSemigroup.lean` proved trace-distance contractivity of the GKSL dynamical map
`Λ_t = e^{tℒ}` *conditionally* on a disclosed hypothesis `hreal`: that `Λ_t` is realized by a Kraus
channel (its complete positivity, the physical content of the GKSL theorem). This module discharges
`hreal` by **proving** that `Λ_t` is completely positive — hence (finite-dimensional Choi/Kraus
theorem) a Kraus channel — so the contraction becomes unconditional.

The route (Lie–Trotter): `ℒ = ℒ_jump + ℒ_drift` with `ℒ_jump` the dissipator (completely positive,
`lindblad_generator_CP`) and `ℒ_drift(ρ) = Gρ + ρG†` a conjugation generator (so `e^{sℒ_drift}` is
conjugation by `e^{sG}`, completely positive). Each Trotter factor `e^{(t/n)ℒ_drift} e^{(t/n)ℒ_jump}`
is CP; `e^{tℒ} = lim_n (e^{(t/n)ℒ_drift} e^{(t/n)ℒ_jump})^n` (matrix Lie–Trotter — built from scratch,
absent from Mathlib); CP is closed under limits (Choi matrix PSD, and the PSD cone is closed). Hence
`e^{tℒ}` is CP.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new axiom;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.OpenSystems

open scoped Matrix ComplexOrder Matrix.Norms.Operator
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- **The positive-semidefinite cone is closed.** A limit of positive-semidefinite matrices is
positive semidefinite — the topological input to "complete positivity is closed under limits". -/
lemma posSemidef_of_tendsto {A : ℕ → Matrix n n ℂ} {L : Matrix n n ℂ}
    (hA : Filter.Tendsto A Filter.atTop (nhds L)) (hpsd : ∀ k, (A k).PosSemidef) :
    L.PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · have hconj : Filter.Tendsto (fun k => (A k)ᴴ) Filter.atTop (nhds Lᴴ) :=
      (Continuous.tendsto (f := fun B : Matrix n n ℂ => Bᴴ) (by fun_prop) L).comp hA
    rw [show (fun k => (A k)ᴴ) = A from funext fun k => (hpsd k).1] at hconj
    exact tendsto_nhds_unique hconj hA
  · have hcont : Continuous (fun B : Matrix n n ℂ =>
        x.sum fun i xi => x.sum fun j xj => star xi * B i j * xj) := by
      simp only [Finsupp.sum]
      exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => by fun_prop
    exact ge_of_tendsto' ((hcont.tendsto L).comp hA) fun k => (hpsd k).2 x

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq B] in
/-- **Complete positivity is closed under limits.** If the Choi matrices of a sequence of completely
positive maps converge to the Choi matrix of `N`, then `N` is completely positive — via Choi's theorem
(CP ⟺ Choi PSD) and the closed PSD cone (`posSemidef_of_tendsto`). -/
lemma isCompletelyPositive_of_tendsto_choi {M : ℕ → MatrixMap A B ℂ} {N : MatrixMap A B ℂ}
    (hchoi : Filter.Tendsto (fun k => (M k).choi_matrix) Filter.atTop (nhds N.choi_matrix))
    (hcp : ∀ k, (M k).IsCompletelyPositive) :
    N.IsCompletelyPositive :=
  (MatrixMap.choi_PSD_iff_CP_map N).mpr
    (posSemidef_of_tendsto hchoi fun k => (MatrixMap.choi_PSD_iff_CP_map (M k)).mp (hcp k))

/-- **Powers of a completely positive endomorphism are completely positive** (the terms of the
exponential series). -/
lemma isCompletelyPositive_pow {M : MatrixMap A A ℂ} (hM : M.IsCompletelyPositive) :
    ∀ k : ℕ, (M ^ k).IsCompletelyPositive
  | 0 => by rw [pow_zero]; exact MatrixMap.IsCompletelyPositive.id
  | k + 1 => by rw [pow_succ]; exact hM.comp (isCompletelyPositive_pow hM k)

section ExpCP
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `Matrix.toLin` (same basis) carries matrix powers to endomorphism powers — it is the underlying
map of the algebra equivalence `Matrix.toLinAlgEquiv`. -/
lemma toLin_pow (b : Module.Basis (d × d) ℂ (Matrix d d ℂ)) (X : Matrix (d × d) (d × d) ℂ) (k : ℕ) :
    Matrix.toLin b b (X ^ k) = (Matrix.toLin b b X) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin_one]; rfl
  | succ k ih => rw [pow_succ, Matrix.toLin_mul b b b, ih, pow_succ]; rfl

/-- **The superoperator `e^{sℒ}` is completely positive when `ℒ` is completely positive and `s ≥ 0`**
— the exponential `toLin(exp(s • toMatrix M))` is a limit of the completely-positive partial sums
`∑_{n<N} (sⁿ/n!) Mⁿ` (each `Mⁿ` CP). The dissipator factor of the Lie–Trotter product. -/
lemma isCompletelyPositive_toLin_exp {M : MatrixMap d d ℂ} (hM : M.IsCompletelyPositive) {s : ℝ}
    (hs : 0 ≤ s) :
    MatrixMap.IsCompletelyPositive (Matrix.toLin (Matrix.stdBasis ℂ d d) (Matrix.stdBasis ℂ d d)
      (NormedSpace.exp ((s : ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ d d)
        (Matrix.stdBasis ℂ d d) M))) := by
  set b := Matrix.stdBasis ℂ d d
  set A : Matrix (d × d) (d × d) ℂ := (s : ℂ) • LinearMap.toMatrix b b M with hA_def
  have hterm : ∀ n : ℕ, Matrix.toLin b b (NormedSpace.expSeries ℂ (Matrix (d × d) (d × d) ℂ) n
      (fun _ => A)) = (((n.factorial : ℂ)⁻¹ * (s : ℂ) ^ n)) • M ^ n := by
    intro n
    rw [NormedSpace.expSeries_apply_eq, hA_def, smul_pow, map_smul, map_smul, toLin_pow,
      Matrix.toLin_toMatrix, smul_smul]
  refine isCompletelyPositive_of_tendsto_choi
    (M := fun N => Matrix.toLin b b
      (∑ n ∈ Finset.range N, NormedSpace.expSeries ℂ (Matrix (d × d) (d × d) ℂ) n (fun _ => A))) ?_ ?_
  · have hlin : (fun Y : Matrix (d × d) (d × d) ℂ => MatrixMap.choi_matrix (Matrix.toLin b b Y))
        = ⇑(MatrixMap.choi_equiv.toLinearMap ∘ₗ (Matrix.toLin b b).toLinearMap) := by
      ext Y; rfl
    have hcont : Continuous fun Y : Matrix (d × d) (d × d) ℂ =>
        MatrixMap.choi_matrix (Matrix.toLin b b Y) := by
      rw [hlin]; exact LinearMap.continuous_of_finiteDimensional _
    exact (hcont.tendsto _).comp (NormedSpace.expSeries_hasSum_exp A).tendsto_sum_nat
  · intro N
    dsimp only
    rw [map_sum]
    refine Finset.sum_induction _ _ (fun _ _ => MatrixMap.IsCompletelyPositive.add)
      (MatrixMap.IsCompletelyPositive.zero d d) (fun n _ => ?_)
    rw [hterm n]
    refine (isCompletelyPositive_pow hM n).smul ?_
    have : ((n.factorial : ℂ)⁻¹ * (s : ℂ) ^ n) = (((n.factorial : ℝ)⁻¹ * s ^ n : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    exact_mod_cast (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹ * s ^ n)

end ExpCP

section Drift
variable {d : Type*} [Fintype d] [DecidableEq d] {κ : Type*} [Fintype κ]

/-- The **drift generator** `A := −iH − ½∑ₖ Lₖ†Lₖ`. Its conjugation `ρ ↦ e^{sA} ρ e^{sA†}` is the
no-jump part of the GKSL dynamics. -/
noncomputable def driftMatrix (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) : Matrix d d ℂ :=
  -Complex.I • H - (2⁻¹ : ℂ) • ∑ k, (L k)ᴴ * L k

/-- The drift part `−i[H,·] − ½{∑Lₖ†Lₖ, ·}` of the GKSL generator equals `ρ ↦ Aρ + ρA†` for `A` the
drift generator, when `H` is Hermitian — a left-plus-right multiplication (the conjugation generator). -/
lemma lindbladDrift_eq (H : Matrix d d ℂ) (hH : H.IsHermitian) (L : κ → Matrix d d ℂ) :
    lindbladHamPart H + lindbladAnticommPart L
      = LinearMap.mulLeft ℂ (driftMatrix H L) + LinearMap.mulRight ℂ (driftMatrix H L)ᴴ := by
  have hAdj : (driftMatrix H L)ᴴ = Complex.I • H - (2⁻¹ : ℂ) • ∑ k, (L k)ᴴ * L k := by
    simp only [driftMatrix, conjTranspose_sub, conjTranspose_smul,
      conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, star_inv₀,
      Complex.star_def, map_neg, Complex.conj_I, neg_neg, star_ofNat]
  refine LinearMap.ext fun ρ => ?_
  rw [LinearMap.add_apply, lindbladHamPart_apply, lindbladAnticommPart_apply,
    LinearMap.add_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, hAdj, driftMatrix]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]; module

/-- **`exp` of the vectorized left-multiplication generator is left-multiplication by the matrix
exponential:** `toLin(exp(s • toMatrix(mulLeft A))) = mulLeft(exp(sA))`. Proof: `map_exp` on the
continuous algebra hom `toMatrixAlgEquiv ∘ Algebra.lmul`, then `toLin ∘ toMatrix = id`. -/
lemma toLin_exp_toMatrix_mulLeft (b : Module.Basis (d × d) ℂ (Matrix d d ℂ))
    (A : Matrix d d ℂ) (s : ℂ) :
    Matrix.toLin b b (NormedSpace.exp (s • LinearMap.toMatrix b b (LinearMap.mulLeft ℂ A)))
      = LinearMap.mulLeft ℂ (NormedSpace.exp (s • A)) := by
  set ψ : Matrix d d ℂ →ₐ[ℂ] Matrix (d × d) (d × d) ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul ℂ (Matrix d d ℂ)) with hψ
  have hψ_apply : ∀ x, ψ x = LinearMap.toMatrix b b (LinearMap.mulLeft ℂ x) := fun x => rfl
  have hcont : Continuous ψ := ψ.toLinearMap.continuous_of_finiteDimensional
  have key := NormedSpace.map_exp ψ hcont (s • A)
  rw [_root_.map_smul ψ, hψ_apply, hψ_apply] at key
  rw [← key, Matrix.toLin_toMatrix]

/-- Right-multiplication is left-multiplication by the transpose, conjugated by the transpose
involution `T`: `mulRight B = T ∘ mulLeft Bᵀ ∘ T` (since `ρB = (Bᵀ ρᵀ)ᵀ`). -/
lemma mulRight_eq_transpose_conj (B : Matrix d d ℂ) :
    LinearMap.mulRight ℂ B
      = (Matrix.transposeLinearEquiv d d ℂ ℂ).toLinearMap ∘ₗ LinearMap.mulLeft ℂ Bᵀ
          ∘ₗ (Matrix.transposeLinearEquiv d d ℂ ℂ).toLinearMap := by
  refine LinearMap.ext fun ρ => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  show ρ * B = (Bᵀ * ρᵀ)ᵀ
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]

/-- **`exp` of the vectorized right-multiplication generator is right-multiplication by the matrix
exponential:** `toLin(exp(s • toMatrix(mulRight B))) = mulRight(exp(sB))`. Via the transpose trick —
conjugate `mulLeft Bᵀ` by the transpose involution (`exp_units_conj`), reuse the left-mult lemma,
then `exp_transpose`. -/
lemma toLin_exp_toMatrix_mulRight (b : Module.Basis (d × d) ℂ (Matrix d d ℂ))
    (B : Matrix d d ℂ) (s : ℂ) :
    Matrix.toLin b b (NormedSpace.exp (s • LinearMap.toMatrix b b (LinearMap.mulRight ℂ B)))
      = LinearMap.mulRight ℂ (NormedSpace.exp (s • B)) := by
  set T : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ := (Matrix.transposeLinearEquiv d d ℂ ℂ).toLinearMap with hT
  have hTT : T ∘ₗ T = LinearMap.id := by
    refine LinearMap.ext fun ρ => ?_; show (ρᵀ)ᵀ = ρ; rw [Matrix.transpose_transpose]
  set P : Matrix (d × d) (d × d) ℂ := LinearMap.toMatrix b b T with hP
  have hPP : P * P = 1 := by
    rw [hP, ← LinearMap.toMatrix_comp b b b, hTT, LinearMap.toMatrix_id]
  set M : Matrix (d × d) (d × d) ℂ := LinearMap.toMatrix b b (LinearMap.mulLeft ℂ Bᵀ) with hMdef
  have hM : LinearMap.toMatrix b b (LinearMap.mulRight ℂ B) = P * M * P := by
    rw [mulRight_eq_transpose_conj, LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b,
      ← hT, ← hP, ← hMdef, mul_assoc]
  rw [hM]
  set U : (Matrix (d × d) (d × d) ℂ)ˣ := ⟨P, P, hPP, hPP⟩ with hU
  have hsmul : s • (P * M * P)
      = (U : Matrix (d × d) (d × d) ℂ) * (s • M) * (↑U⁻¹ : Matrix (d × d) (d × d) ℂ) := by
    show s • (P * M * P) = P * (s • M) * P
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hsmul, Matrix.exp_units_conj]
  show Matrix.toLin b b (P * NormedSpace.exp (s • M) * P) = LinearMap.mulRight ℂ (NormedSpace.exp (s • B))
  rw [Matrix.toLin_mul b b b, Matrix.toLin_mul b b b, hP, Matrix.toLin_toMatrix, hMdef,
    toLin_exp_toMatrix_mulLeft]
  have hBT : NormedSpace.exp (s • B) = (NormedSpace.exp (s • Bᵀ))ᵀ := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul, Matrix.transpose_transpose]
  rw [hBT, mulRight_eq_transpose_conj, Matrix.transpose_transpose, ← hT, LinearMap.comp_assoc]

/-- **The drift factor `e^{sℒ_drift}` is completely positive** — it is conjugation by `e^{sA}`
(`A = -iH - ½∑Lₖ†Lₖ`), hence CP by PhysLib's `congruence_CP`. The two commuting one-sided factors
exponentiate to `mulLeft(e^{sA})` and `mulRight(e^{sAᴴ}) = mulRight((e^{sA})ᴴ)`. -/
lemma isCompletelyPositive_toLin_exp_drift (H : Matrix d d ℂ) (hH : H.IsHermitian)
    (L : κ → Matrix d d ℂ) (s : ℝ) :
    MatrixMap.IsCompletelyPositive (Matrix.toLin (Matrix.stdBasis ℂ d d) (Matrix.stdBasis ℂ d d)
      (NormedSpace.exp ((s : ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ d d) (Matrix.stdBasis ℂ d d)
        (lindbladHamPart H + lindbladAnticommPart L)))) := by
  set b := Matrix.stdBasis ℂ d d
  set A := driftMatrix H L with hA
  have hcomm : Commute (LinearMap.toMatrix b b (LinearMap.mulLeft ℂ A))
      (LinearMap.toMatrix b b (LinearMap.mulRight ℂ Aᴴ)) :=
    (LinearMap.commute_mulLeft_right A Aᴴ).map (LinearMap.toMatrixAlgEquiv b)
  have heq : Matrix.toLin b b (NormedSpace.exp ((s : ℂ) • LinearMap.toMatrix b b
      (lindbladHamPart H + lindbladAnticommPart L)))
      = MatrixMap.conj (NormedSpace.exp ((s : ℂ) • A)) := by
    rw [lindbladDrift_eq H hH L, map_add, smul_add,
      Matrix.exp_add_of_commute _ _ ((hcomm.smul_left (s : ℂ)).smul_right (s : ℂ)),
      Matrix.toLin_mul b b b, toLin_exp_toMatrix_mulLeft, toLin_exp_toMatrix_mulRight]
    have hadj : NormedSpace.exp ((s : ℂ) • Aᴴ) = (NormedSpace.exp ((s : ℂ) • A))ᴴ := by
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal]
    rw [hadj]
    refine LinearMap.ext fun ρ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, MatrixMap.conj_apply, Matrix.mul_assoc]
  rw [heq]
  exact MatrixMap.congruence_CP _

end Drift

section Trotter

/-- **Noncommutative telescoping:** `aⁿ - bⁿ = ∑_{i<n} aⁱ (a - b) bⁿ⁻¹⁻ⁱ` in any ring (no
commutativity). The algebraic core of the Lie–Trotter product-formula norm estimate. -/
lemma pow_sub_pow_eq_telescope {R : Type*} [Ring R] (a b : R) (n : ℕ) :
    a ^ n - b ^ n = ∑ i ∈ Finset.range n, a ^ i * (a - b) * b ^ (n - 1 - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have hsplit : ∑ i ∈ Finset.range n, a ^ i * (a - b) * b ^ (n - i)
        = (∑ i ∈ Finset.range n, a ^ i * (a - b) * b ^ (n - 1 - i)) * b := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have hexp : n - i = n - 1 - i + 1 := by omega
      rw [hexp, pow_succ, ← mul_assoc]
    rw [hsplit, ← ih, pow_succ, pow_succ]
    noncomm_ring

end Trotter

end SKEFTHawking.OpenSystems
