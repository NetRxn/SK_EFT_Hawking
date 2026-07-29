import SKEFTHawking.LindbladSemigroup
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

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
  exact (congrArg (Matrix.toLin b b) key.symm).trans (Matrix.toLin_toMatrix b b _)

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

/-- **Norm estimate from the telescoping identity:** `‖aⁿ - bⁿ‖ ≤ n · Mⁿ⁻¹ · ‖a - b‖` for any
common norm bound `M ≥ ‖a‖, ‖b‖`. The Lipschitz-in-`a-b` control that makes the Trotter error
sum to `O(1/n)`. -/
lemma norm_pow_sub_pow_le {R : Type*} [NormedRing R] [NormOneClass R] (a b : R) {M : ℝ}
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * M ^ (n - 1) * ‖a - b‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg a) ha
  rw [pow_sub_pow_eq_telescope]
  calc ‖∑ i ∈ Finset.range n, a ^ i * (a - b) * b ^ (n - 1 - i)‖
      ≤ ∑ i ∈ Finset.range n, ‖a ^ i * (a - b) * b ^ (n - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, M ^ (n - 1) * ‖a - b‖ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < n := Finset.mem_range.mp hi
        calc ‖a ^ i * (a - b) * b ^ (n - 1 - i)‖
            ≤ ‖a ^ i‖ * ‖a - b‖ * ‖b ^ (n - 1 - i)‖ :=
              (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
          _ ≤ M ^ i * ‖a - b‖ * M ^ (n - 1 - i) := by
              gcongr
              · exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg a) ha _)
              · exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg b) hb _)
          _ = M ^ (n - 1) * ‖a - b‖ := by
              rw [mul_right_comm, ← pow_add, show i + (n - 1 - i) = n - 1 from by omega]
    _ = n * M ^ (n - 1) * ‖a - b‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Per-term bound for the exp tail: `‖((n+m)!)⁻¹ • Z^(n+m)‖ ≤ ‖Z‖ᵐ · (n!⁻¹ ‖Z‖ⁿ)`. -/
private lemma norm_expTermGen_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℂ 𝔸]
    (Z : 𝔸) (m n : ℕ) :
    ‖(((n + m).factorial : ℂ)⁻¹) • Z ^ (n + m)‖ ≤ ‖Z‖ ^ m * ((n.factorial : ℝ)⁻¹ * ‖Z‖ ^ n) := by
  calc ‖(((n + m).factorial : ℂ)⁻¹) • Z ^ (n + m)‖
      = ((n + m).factorial : ℝ)⁻¹ * ‖Z ^ (n + m)‖ := by
        rw [norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ ((n + m).factorial : ℝ)⁻¹ * ‖Z‖ ^ (n + m) := by gcongr; exact norm_pow_le _ _
    _ ≤ (n.factorial : ℝ)⁻¹ * ‖Z‖ ^ (n + m) := by
        have hpos2 : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
        have hpos1 : (0:ℝ) < (n + m).factorial := by exact_mod_cast (n + m).factorial_pos
        have hfle : (n.factorial : ℝ) ≤ (n + m).factorial := by
          exact_mod_cast Nat.factorial_le (show n ≤ n + m by omega)
        have : ((n + m).factorial : ℝ)⁻¹ ≤ (n.factorial : ℝ)⁻¹ :=
          (inv_le_inv₀ hpos1 hpos2).mpr hfle
        gcongr
    _ = ‖Z‖ ^ m * ((n.factorial : ℝ)⁻¹ * ‖Z‖ ^ n) := by rw [pow_add]; ring

/-- **General exp-Taylor remainder for a Banach algebra:** `‖exp Z - ∑_{k<m} (k!)⁻¹ Zᵏ‖ ≤ ‖Z‖ᵐ · exp‖Z‖`.
The matrix analogue of the scalar `Complex.norm_exp_sub_one_sub_id_le` family (absent from Mathlib for
general algebras); `m = 0,1,2` give the bounds the Lie–Trotter `O(1/n²)` step error needs. -/
lemma norm_exp_sub_sum_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] (Z : 𝔸) (m : ℕ) :
    ‖NormedSpace.exp Z - ∑ k ∈ Finset.range m, ((k.factorial : ℂ)⁻¹) • Z ^ k‖
      ≤ ‖Z‖ ^ m * Real.exp ‖Z‖ := by
  have hf : Summable (fun n => ((n.factorial : ℂ)⁻¹) • Z ^ n) := NormedSpace.expSeries_summable' Z
  have hsplit : NormedSpace.exp Z - ∑ k ∈ Finset.range m, ((k.factorial : ℂ)⁻¹) • Z ^ k
      = ∑' n, (((n + m).factorial : ℂ)⁻¹) • Z ^ (n + m) := by
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) Z, ← hf.sum_add_tsum_nat_add m]; abel
  rw [hsplit]
  have hsummN : Summable (fun n => ‖(((n + m).factorial : ℂ)⁻¹) • Z ^ (n + m)‖) :=
    (summable_nat_add_iff m).mpr (NormedSpace.norm_expSeries_summable' Z)
  have hsummR : Summable (fun n => ‖Z‖ ^ m * ((n.factorial : ℝ)⁻¹ * ‖Z‖ ^ n)) := by
    apply Summable.mul_left
    simpa [smul_eq_mul] using (NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖Z‖)
  have step1 : ‖∑' n, (((n + m).factorial : ℂ)⁻¹) • Z ^ (n + m)‖
      ≤ ∑' n, ‖(((n + m).factorial : ℂ)⁻¹) • Z ^ (n + m)‖ := norm_tsum_le_tsum_norm hsummN
  have step2 : ∑' n, ‖(((n + m).factorial : ℂ)⁻¹) • Z ^ (n + m)‖
      ≤ ∑' n, ‖Z‖ ^ m * ((n.factorial : ℝ)⁻¹ * ‖Z‖ ^ n) :=
    Summable.tsum_le_tsum (norm_expTermGen_le Z m) hsummN hsummR
  have step3 : ∑' n, ‖Z‖ ^ m * ((n.factorial : ℝ)⁻¹ * ‖Z‖ ^ n)
      = ‖Z‖ ^ m * ∑' n, (n.factorial : ℝ)⁻¹ * ‖Z‖ ^ n := tsum_mul_left
  have step4 : ∑' n, (n.factorial : ℝ)⁻¹ * ‖Z‖ ^ n = Real.exp ‖Z‖ := by
    rw [show Real.exp ‖Z‖ = NormedSpace.exp ‖Z‖ from congrFun Real.exp_eq_exp_ℝ _,
      NormedSpace.exp_eq_tsum ℝ]
    simp only [smul_eq_mul]
  exact le_of_le_of_eq (step1.trans step2) (step3.trans (by rw [step4]))

/-- `‖exp Z‖ ≤ exp‖Z‖` (the `m = 0` remainder). -/
lemma norm_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℂ 𝔸]
    [CompleteSpace 𝔸] (Z : 𝔸) : ‖NormedSpace.exp Z‖ ≤ Real.exp ‖Z‖ := by
  simpa using norm_exp_sub_sum_le Z 0

/-- `‖exp Z - 1‖ ≤ ‖Z‖ · exp‖Z‖` (the `m = 1` remainder). -/
lemma norm_exp_sub_one_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℂ 𝔸]
    [CompleteSpace 𝔸] (Z : 𝔸) : ‖NormedSpace.exp Z - 1‖ ≤ ‖Z‖ * Real.exp ‖Z‖ := by
  simpa [Finset.sum_range_one] using norm_exp_sub_sum_le Z 1

/-- **Quadratic exp-Taylor remainder:** `‖exp Z - 1 - Z‖ ≤ ‖Z‖² · exp‖Z‖` (the `m = 2` remainder). -/
lemma norm_exp_sub_one_sub_self_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] (Z : 𝔸) :
    ‖NormedSpace.exp Z - 1 - Z‖ ≤ ‖Z‖ ^ 2 * Real.exp ‖Z‖ := by
  have h := norm_exp_sub_sum_le Z 2
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  simp only [Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    pow_one] at h
  rw [show NormedSpace.exp Z - 1 - Z = NormedSpace.exp Z - (1 + Z) by abel]
  exact h

/-- **The Lie–Trotter one-step error is `O((‖X‖+‖Y‖)²)`:**
`‖eˣ·eʸ - e^{X+Y}‖ ≤ 4·(‖X‖+‖Y‖)²·exp(‖X‖+‖Y‖)`. From the identity
`eˣeʸ - 1 - (X+Y) = (eʸ-1-Y) + (eˣ-1-X)eʸ + X(eʸ-1)`, each summand `O(quadratic)` via the remainder
corollaries; the dominant term cancels against `e^{X+Y}-1-(X+Y)`. -/
lemma norm_exp_mul_exp_sub_exp_add_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] (X Y : 𝔸) :
    ‖NormedSpace.exp X * NormedSpace.exp Y - NormedSpace.exp (X + Y)‖
      ≤ 4 * (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by
  have hYP : ‖Y‖ ≤ ‖X‖ + ‖Y‖ := by linarith [norm_nonneg X]
  have hXP : ‖X‖ ≤ ‖X‖ + ‖Y‖ := by linarith [norm_nonneg Y]
  have hXYP : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le _ _
  -- the four summands, each ≤ (‖X‖+‖Y‖)² · exp(‖X‖+‖Y‖)
  have hb1 : ‖NormedSpace.exp Y - 1 - Y‖ ≤ (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) :=
    (norm_exp_sub_one_sub_self_le Y).trans (by gcongr)
  have hb2 : ‖(NormedSpace.exp X - 1 - X) * NormedSpace.exp Y‖
      ≤ (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖NormedSpace.exp X - 1 - X‖ * ‖NormedSpace.exp Y‖
        ≤ (‖X‖ ^ 2 * Real.exp ‖X‖) * Real.exp ‖Y‖ :=
          mul_le_mul (norm_exp_sub_one_sub_self_le X) (norm_exp_le Y) (norm_nonneg _) (by positivity)
      _ = ‖X‖ ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by rw [Real.exp_add]; ring
      _ ≤ (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by gcongr
  have hb3 : ‖X * (NormedSpace.exp Y - 1)‖ ≤ (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖X‖ * ‖NormedSpace.exp Y - 1‖
        ≤ ‖X‖ * (‖Y‖ * Real.exp ‖Y‖) := by gcongr; exact norm_exp_sub_one_le Y
      _ ≤ (‖X‖ + ‖Y‖) * ((‖X‖ + ‖Y‖) * Real.exp (‖X‖ + ‖Y‖)) := by gcongr
      _ = (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by ring
  have hb4 : ‖NormedSpace.exp (X + Y) - 1 - (X + Y)‖ ≤ (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) :=
    (norm_exp_sub_one_sub_self_le (X + Y)).trans (by gcongr)
  have hident : NormedSpace.exp X * NormedSpace.exp Y - NormedSpace.exp (X + Y)
      = ((NormedSpace.exp Y - 1 - Y) + (NormedSpace.exp X - 1 - X) * NormedSpace.exp Y
          + X * (NormedSpace.exp Y - 1)) - (NormedSpace.exp (X + Y) - 1 - (X + Y)) := by
    noncomm_ring
  rw [hident]
  calc ‖((NormedSpace.exp Y - 1 - Y) + (NormedSpace.exp X - 1 - X) * NormedSpace.exp Y
          + X * (NormedSpace.exp Y - 1)) - (NormedSpace.exp (X + Y) - 1 - (X + Y))‖
      ≤ ‖(NormedSpace.exp Y - 1 - Y) + (NormedSpace.exp X - 1 - X) * NormedSpace.exp Y
          + X * (NormedSpace.exp Y - 1)‖ + ‖NormedSpace.exp (X + Y) - 1 - (X + Y)‖ :=
        norm_sub_le _ _
    _ ≤ (‖NormedSpace.exp Y - 1 - Y‖ + ‖(NormedSpace.exp X - 1 - X) * NormedSpace.exp Y‖
          + ‖X * (NormedSpace.exp Y - 1)‖) + ‖NormedSpace.exp (X + Y) - 1 - (X + Y)‖ := by
        gcongr; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 4 * (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by linarith [hb1, hb2, hb3, hb4]

/-- `exp (n • W) = (exp W)ⁿ` over a complex Banach algebra — proven from `exp_add_of_commute_of_mem_ball`
(which needs only `CharZero ℂ`), avoiding Mathlib's `exp_nsmul` (gated on `[NormedAlgebra ℚ 𝔸]`, an
instance the matrix algebra does not carry). -/
private lemma exp_nsmul_eq_pow {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (W : 𝔸) : ∀ n : ℕ, NormedSpace.exp (n • W) = NormedSpace.exp W ^ n
  | 0 => by rw [zero_smul, pow_zero, NormedSpace.exp_zero]
  | k + 1 => by
      have hmem : ∀ z : 𝔸, z ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℂ 𝔸).radius :=
        fun z => (NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _
      rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball
        (Commute.smul_left (Commute.refl W) k) (hmem _) (hmem _), exp_nsmul_eq_pow W k, pow_succ]

/-- Per-step Lie–Trotter bound: `‖(e^{X/n}e^{Y/n})ⁿ - e^{X+Y}‖ ≤ 4(‖X‖+‖Y‖)²·exp(‖X‖+‖Y‖)/n`. -/
private lemma trotter_step_bound {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] (X Y : 𝔸) {n : ℕ} (hn : 1 ≤ n) :
    ‖(NormedSpace.exp ((n:ℝ)⁻¹ • X) * NormedSpace.exp ((n:ℝ)⁻¹ • Y)) ^ n - NormedSpace.exp (X + Y)‖
      ≤ 4 * (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) / n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  set s := ‖X‖ + ‖Y‖ with hs
  set a := NormedSpace.exp ((n:ℝ)⁻¹ • X) * NormedSpace.exp ((n:ℝ)⁻¹ • Y) with ha
  set b := NormedSpace.exp ((n:ℝ)⁻¹ • (X + Y)) with hb
  have hnX : ‖(n:ℝ)⁻¹ • X‖ = (n:ℝ)⁻¹ * ‖X‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnY : ‖(n:ℝ)⁻¹ • Y‖ = (n:ℝ)⁻¹ * ‖Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum : (n:ℝ)⁻¹ * ‖X‖ + (n:ℝ)⁻¹ * ‖Y‖ = (n:ℝ)⁻¹ * s := by rw [hs]; ring
  have hMa : ‖a‖ ≤ Real.exp ((n:ℝ)⁻¹ * s) := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖NormedSpace.exp ((n:ℝ)⁻¹ • X)‖ * ‖NormedSpace.exp ((n:ℝ)⁻¹ • Y)‖
        ≤ Real.exp ‖(n:ℝ)⁻¹ • X‖ * Real.exp ‖(n:ℝ)⁻¹ • Y‖ :=
          mul_le_mul (norm_exp_le _) (norm_exp_le _) (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((n:ℝ)⁻¹ * s) := by rw [← Real.exp_add, hnX, hnY, hsum]
  have hMb : ‖b‖ ≤ Real.exp ((n:ℝ)⁻¹ * s) := by
    refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr
    exact norm_add_le _ _
  have hbn : b ^ n = NormedSpace.exp (X + Y) := by
    rw [hb, ← exp_nsmul_eq_pow]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (ne_of_gt hn0), one_smul]
  have hab : ‖a - b‖ ≤ 4 * ((n:ℝ)⁻¹ * s) ^ 2 * Real.exp ((n:ℝ)⁻¹ * s) := by
    have h7c := norm_exp_mul_exp_sub_exp_add_le ((n:ℝ)⁻¹ • X) ((n:ℝ)⁻¹ • Y)
    rw [ha, hb, smul_add]
    refine h7c.trans (le_of_eq ?_)
    rw [hnX, hnY, hsum]
  have hexp_arg : (n:ℝ) * ((n:ℝ)⁻¹ * s) = s := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn0), one_mul]
  have hM : Real.exp ((n:ℝ)⁻¹ * s) ^ (n - 1) * Real.exp ((n:ℝ)⁻¹ * s) = Real.exp s := by
    rw [← pow_succ, Nat.sub_add_cancel hn, ← Real.exp_nat_mul, hexp_arg]
  rw [show NormedSpace.exp (X + Y) = b ^ n from hbn.symm]
  refine (norm_pow_sub_pow_le a b hMa hMb n).trans ?_
  calc (n:ℝ) * Real.exp ((n:ℝ)⁻¹ * s) ^ (n - 1) * ‖a - b‖
      ≤ (n:ℝ) * Real.exp ((n:ℝ)⁻¹ * s) ^ (n - 1)
          * (4 * ((n:ℝ)⁻¹ * s) ^ 2 * Real.exp ((n:ℝ)⁻¹ * s)) := by gcongr
    _ = 4 * ((n:ℝ) * ((n:ℝ)⁻¹ * s) ^ 2)
          * (Real.exp ((n:ℝ)⁻¹ * s) ^ (n - 1) * Real.exp ((n:ℝ)⁻¹ * s)) := by ring
    _ = 4 * s ^ 2 * Real.exp s / n := by rw [hM]; field_simp

/-- **The matrix Lie–Trotter product formula** (built from scratch — absent from Mathlib):
`(e^{X/n} e^{Y/n})ⁿ → e^{X+Y}`. The telescoping `‖aⁿ-bⁿ‖`-bound (7b) times the `O(1/n²)` one-step error
(7c′) gives `‖(e^{X/n}e^{Y/n})ⁿ - e^{X+Y}‖ ≤ C/n → 0`. -/
lemma tendsto_trotter {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] (X Y : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (NormedSpace.exp ((n:ℝ)⁻¹ • X) * NormedSpace.exp ((n:ℝ)⁻¹ • Y)) ^ n)
      Filter.atTop (nhds (NormedSpace.exp (X + Y))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
    (Filter.eventually_atTop.mpr ⟨1, fun n hn => trotter_step_bound X Y hn⟩) ?_
  have : Filter.Tendsto (fun n : ℕ => (4 * (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖)) / (n : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  simpa using this

end Trotter

section Propagator
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d] {κ : Type*} [Fintype κ]

omit [Fintype d] [DecidableEq d] [Nonempty d] in
/-- Compose a real scaling with a complex scaling: `r • ((t:ℂ) • M) = ↑(r·t) • M`. -/
private lemma real_smul_ofReal_smul (r t : ℝ) (M : Matrix (d × d) (d × d) ℂ) :
    r • ((t : ℂ) • M) = ((r * t : ℝ) : ℂ) • M := by
  rw [← smul_assoc, Complex.real_smul, ← Complex.ofReal_mul]

/-- **The GKSL propagator's action `Λ_t` is completely positive for `t ≥ 0`** (Hermitian `H`).
The Lie–Trotter product `(e^{(t/n)ℒ_drift} e^{(t/n)ℒ_jump})ⁿ` of completely-positive factors converges
(`tendsto_trotter`) to `Λ_t`, and complete positivity is closed under limits. This discharges `hreal`. -/
theorem isCompletelyPositive_lindbladPropagatorAction (H : Matrix d d ℂ) (hH : H.IsHermitian)
    (L : κ → Matrix d d ℂ) {t : ℝ} (ht : 0 ≤ t) :
    MatrixMap.IsCompletelyPositive (lindbladPropagatorAction H L t) := by
  set b := Matrix.stdBasis ℂ d d with hb
  set D := LinearMap.toMatrix b b (lindbladHamPart H + lindbladAnticommPart L) with hD
  set J := LinearMap.toMatrix b b (lindbladJump L) with hJ
  set X : Matrix (d × d) (d × d) ℂ := (t : ℂ) • D with hX
  set Y : Matrix (d × d) (d × d) ℂ := (t : ℂ) • J with hY
  -- the propagator's vectorized generator is X + Y
  have hgen : (t : ℂ) • lindbladLiouvillian H L = X + Y := by
    have hL : lindbladLiouvillian H L = LinearMap.toMatrix b b (lindbladGenerator H L) := rfl
    rw [hL, lindbladGenerator, hX, hY, hD, hJ, ← smul_add, ← map_add]
    congr 2
    abel
  -- each Trotter factor is CP, uniformly in n (n = 0 gives the identity)
  have hfac : ∀ n : ℕ, MatrixMap.IsCompletelyPositive (Matrix.toLin b b
      ((NormedSpace.exp ((n:ℝ)⁻¹ • X) * NormedSpace.exp ((n:ℝ)⁻¹ • Y)) ^ n)) := by
    intro n
    rw [toLin_pow, Matrix.toLin_mul b b b]
    refine isCompletelyPositive_pow (MatrixMap.IsCompletelyPositive.comp ?_ ?_) n
    · rw [hY, real_smul_ofReal_smul, hJ]
      exact isCompletelyPositive_toLin_exp (lindblad_generator_CP L)
        (mul_nonneg (by positivity) ht)
    · rw [hX, real_smul_ofReal_smul, hD]
      exact isCompletelyPositive_toLin_exp_drift H hH L ((n:ℝ)⁻¹ * t)
  -- choi-continuity of toLin
  have hcont : Continuous fun M : Matrix (d × d) (d × d) ℂ =>
      MatrixMap.choi_matrix (Matrix.toLin b b M) := by
    have hlin : (fun M : Matrix (d × d) (d × d) ℂ => MatrixMap.choi_matrix (Matrix.toLin b b M))
        = ⇑(MatrixMap.choi_equiv.toLinearMap ∘ₗ (Matrix.toLin b b).toLinearMap) := by ext M; rfl
    rw [hlin]; exact LinearMap.continuous_of_finiteDimensional _
  -- assemble: Λ_t = toLin(exp(X+Y)) = lim of CP approximants
  rw [lindbladPropagatorAction, lindbladPropagator, hgen]
  refine isCompletelyPositive_of_tendsto_choi (M := fun n =>
    Matrix.toLin b b ((NormedSpace.exp ((n:ℝ)⁻¹ • X) * NormedSpace.exp ((n:ℝ)⁻¹ • Y)) ^ n)) ?_ hfac
  exact (hcont.tendsto _).comp (tendsto_trotter X Y)

omit [Nonempty d] in
/-- **The GKSL generator is trace-annihilating:** `Tr(ℒρ) = 0`. The commutator part has zero trace,
and the jump term `Tr(∑ LₖρLₖ†) = Tr((∑Lₖ†Lₖ)ρ)` exactly cancels the anticommutator's
`−Tr((∑Lₖ†Lₖ)ρ)` (trace cyclicity). This is what makes `e^{tℒ}` trace-preserving (hence CPTP). -/
theorem lindblad_generator_traceZero (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    (lindbladGenerator H L ρ).trace = 0 := by
  rw [lindbladGenerator, LinearMap.add_apply, LinearMap.add_apply, lindbladHamPart_apply,
    lindbladJump_apply, lindbladAnticommPart_apply, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_mul_comm H ρ, sub_self, smul_zero, zero_add,
    Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_comm (L _ * ρ) (L _)ᴴ, ← Matrix.mul_assoc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, Matrix.trace_mul_comm ρ (∑ k, (L k)ᴴ * L k),
    smul_eq_mul]
  ring

omit [Nonempty d] in
/-- **The GKSL propagator is trace-preserving:** `Tr(Λ_t ρ) = Tr(ρ)`. Pushing the continuous-linear
functional `M ↦ Tr(toLin M ρ)` through the exponential series, only the `k = 0` term survives since
`Tr(ℒᵏρ) = 0` for `k ≥ 1` (trace-annihilation). Hence `Λ_t` is trace-preserving (CPTP). -/
theorem trace_lindbladPropagatorAction (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) (t : ℝ)
    (ρ : Matrix d d ℂ) :
    (lindbladPropagatorAction H L t ρ).trace = ρ.trace := by
  set b := Matrix.stdBasis ℂ d d with hb
  set A : Matrix (d × d) (d × d) ℂ := (t : ℂ) • lindbladLiouvillian H L with hA
  set ℒ := lindbladGenerator H L with hℒ
  let φ : Matrix (d × d) (d × d) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => (Matrix.toLin b b M ρ).trace
      map_add' := fun M N => by simp [map_add]
      map_smul' := fun c M => by simp [map_smul] }
  have hpow : ∀ k, Matrix.toLin b b ((lindbladLiouvillian H L) ^ k) = ℒ ^ k := fun k => by
    rw [toLin_pow, hℒ, lindbladLiouvillian, Matrix.toLin_toMatrix]
  have hterm : ∀ k : ℕ, φ (NormedSpace.expSeries ℂ (Matrix (d × d) (d × d) ℂ) k (fun _ => A))
      = ((k.factorial : ℂ)⁻¹ * (t : ℂ) ^ k) * ((ℒ ^ k) ρ).trace := by
    intro k
    show (Matrix.toLin b b (NormedSpace.expSeries ℂ _ k (fun _ => A)) ρ).trace = _
    rw [NormedSpace.expSeries_apply_eq, hA, smul_pow, map_smul, map_smul, hpow,
      LinearMap.smul_apply, LinearMap.smul_apply, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc]
  have hzero : ∀ k : ℕ, k ≠ 0 →
      φ (NormedSpace.expSeries ℂ (Matrix (d × d) (d × d) ℂ) k (fun _ => A)) = 0 := by
    intro k hk
    rw [hterm k]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ' ℒ j, Module.End.mul_apply, hℒ, lindblad_generator_traceZero, mul_zero]
  have hHasSum : HasSum
      (fun k => φ (NormedSpace.expSeries ℂ (Matrix (d × d) (d × d) ℂ) k (fun _ => A)))
      (φ (NormedSpace.exp A)) :=
    φ.toContinuousLinearMap.hasSum (NormedSpace.expSeries_hasSum_exp A)
  show φ (NormedSpace.exp A) = ρ.trace
  rw [← hHasSum.tsum_eq, tsum_eq_single 0 hzero, hterm 0]
  simp

open SKEFTHawking.QuantumNetwork in
/-- **Trace-distance contractivity of the GKSL dynamical map — UNCONDITIONAL.**
`D(Λ_t ρ, Λ_t σ) ≤ D(ρ, σ)` for Hermitian `H` and `t ≥ 0`, with **no disclosed realization
hypothesis**: `Λ_t` is proven completely positive (`isCompletelyPositive_lindbladPropagatorAction`)
and trace-preserving (`trace_lindbladPropagatorAction`), hence a Kraus channel, and the bound is the
CPTP data-processing inequality `traceDist_krausMap_le`. This discharges the former `hreal`. -/
theorem traceDist_lindblad_monotone (H : Matrix d d ℂ) (hH : H.IsHermitian) (L : κ → Matrix d d ℂ)
    {t : ℝ} (ht : 0 ≤ t) {ρ σ : Matrix d d ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    traceDist (lindbladPropagatorAction H L t ρ) (lindbladPropagatorAction H L t σ)
      ≤ traceDist ρ σ := by
  obtain ⟨K, hKeq⟩ := (isCompletelyPositive_lindbladPropagatorAction H hH L ht).exists_kraus
  set e := Fintype.equivFin (d × d) with he
  set K' : Fin (Fintype.card (d × d)) → Matrix d d ℂ := fun i => K (e.symm i) with hK'
  have hreal : ∀ x : Matrix d d ℂ, lindbladPropagatorAction H L t x = krausMap K' x := by
    intro x
    rw [hKeq]
    have hof : (MatrixMap.of_kraus K K) x = ∑ k : d × d, K k * x * (K k)ᴴ := by
      simp only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_mk,
        AddHom.coe_mk]
    rw [hof, krausMap]
    exact (Equiv.sum_comp e.symm (fun k => K k * x * (K k)ᴴ)).symm
  have hchannel : IsKrausChannel K' := by
    rw [IsKrausChannel, Matrix.ext_iff_trace_mul_right]
    intro x
    rw [one_mul]
    have htp := trace_lindbladPropagatorAction H L t x
    rw [hreal x, krausMap] at htp
    rw [← htp, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace_mul_comm (K' i * x) (K' i)ᴴ, ← Matrix.mul_assoc]
  rw [hreal ρ, hreal σ]
  exact traceDist_krausMap_le hchannel hρ hσ

end Propagator

end SKEFTHawking.OpenSystems