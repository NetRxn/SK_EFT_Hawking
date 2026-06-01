import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# General mixed-state certification layer (Phase 6AE-A, foundation)

The general density-matrix metrics the Bell-diagonal/Werner substrate (Phases
6AA–6AD) deliberately avoided, built concretely on `Matrix (Fin n) (Fin n) ℂ` using
Mathlib's spectral theorem and positive-semidefinite machinery (no abstract
C*-algebra detour, no Stinespring).

* `IsDensityOperator ρ` — positive semidefinite, unit trace.
* `traceNorm A = ∑ √eigenvalues(AᴴA)` — the Schatten-1 / nuclear norm `tr|A|`
  (sum of singular values).
* `traceDist ρ σ = ½‖ρ − σ‖₁` — the trace distance.

This increment establishes the definitions and their cleanly-provable structural
properties (nonnegativity, symmetry, vanishing on equality). The deep functional-
analytic theorems (trace-norm triangle inequality, CPTP contractivity, Uhlmann
fidelity / Fuchs–van de Graaf) are subsequent increments.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- A **density operator**: positive semidefinite with unit trace. -/
def IsDensityOperator (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Sum of singular values of a positive-semidefinite witness `∑ √eigenvalues(M)`.
Factored on the PSD witness (proof-irrelevant in `M`) so that trace-norm identities
reduce to matrix equalities. -/
noncomputable def traceNormOf {M : Matrix (Fin n) (Fin n) ℂ} (_hM : M.PosSemidef) : ℝ :=
  ∑ i, Real.sqrt (_hM.isHermitian.eigenvalues i)

/-- The trace-norm-of-witness depends only on the matrix, not the PSD proof. -/
theorem traceNormOf_congr {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef)
    (hM' : M'.PosSemidef) (h : M = M') : traceNormOf hM = traceNormOf hM' := by
  subst h; rfl

theorem traceNormOf_nonneg {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) :
    0 ≤ traceNormOf hM :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- **Trace norm** `‖A‖₁ = tr|A|`, as the sum of singular values
`∑ √eigenvalues(AᴴA)`. -/
noncomputable def traceNorm (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  traceNormOf (Matrix.posSemidef_conjTranspose_mul_self A)

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ traceNorm A :=
  traceNormOf_nonneg _

/-- The trace norm is invariant under negation (`AᴴA = (−A)ᴴ(−A)`). -/
theorem traceNorm_neg (A : Matrix (Fin n) (Fin n) ℂ) : traceNorm (-A) = traceNorm A :=
  traceNormOf_congr _ _ (by rw [conjTranspose_neg, neg_mul_neg])

/-- The trace norm of the zero matrix is zero. -/
@[simp] theorem traceNorm_zero : traceNorm (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have hz : Matrix.PosSemidef (0 : Matrix (Fin n) (Fin n) ℂ) := Matrix.PosSemidef.zero
  rw [traceNorm, traceNormOf_congr _ hz (by simp)]
  unfold traceNormOf
  have he : hz.isHermitian.eigenvalues = 0 :=
    (Matrix.IsHermitian.eigenvalues_eq_zero_iff _).mpr rfl
  simp [he]

/-- **Trace distance** `D(ρ,σ) = ½‖ρ − σ‖₁`. -/
noncomputable def traceDist (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (1 / 2) * traceNorm (ρ - σ)

/-- The trace distance is nonnegative. -/
theorem traceDist_nonneg (ρ σ : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ traceDist ρ σ := by
  unfold traceDist
  have := traceNorm_nonneg (ρ - σ)
  linarith

/-- **The trace distance is symmetric.** -/
theorem traceDist_comm (ρ σ : Matrix (Fin n) (Fin n) ℂ) : traceDist ρ σ = traceDist σ ρ := by
  unfold traceDist
  rw [← neg_sub ρ σ, traceNorm_neg]

/-- **The trace distance vanishes on equal states.** -/
@[simp] theorem traceDist_self (ρ : Matrix (Fin n) (Fin n) ℂ) : traceDist ρ ρ = 0 := by
  unfold traceDist
  rw [sub_self, traceNorm_zero, mul_zero]

/-! ### Bridge to the trace (step 1): trace norm of a density operator -/

/-- **Trace of a continuous-functional-calculus image** `tr(cfc f H) = ∑ f(λᵢ)`
(unitary conjugation preserves trace; the diagonal contributes `∑ f(eigenvalues)`). -/
theorem trace_cfc {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (hM.cfc f).trace = ∑ i, ((f (hM.eigenvalues i) : ℝ) : ℂ) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  simp [Function.comp]

/-- For Hermitian `A`, `A·A` is the continuous-functional-calculus image of squaring
(`A·A = cfc(·²)A`). Proven concretely via the spectral theorem and
`diagonal_mul_diagonal`, avoiding the generic CFC instance. -/
theorem isHermitian_mul_self_eq_cfc_sq {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    M * M = hM.cfc (fun x => x ^ 2) := by
  have hfun : (fun i => (RCLike.ofReal ∘ hM.eigenvalues) i * (RCLike.ofReal ∘ hM.eigenvalues) i)
      = (RCLike.ofReal ∘ (fun x => x ^ 2) ∘ hM.eigenvalues : Fin n → ℂ) := by
    funext i
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [Matrix.IsHermitian.cfc]
  conv_lhs => rw [hM.spectral_theorem]
  rw [← map_mul, diagonal_mul_diagonal, hfun]

/-- The eigenvalue multiset of `AᴴA` (Hermitian `A`) is the multiset of squared
eigenvalues of `A`, obtained by matching characteristic polynomials through the
cfc squaring identity (concrete; no CFC instance). -/
theorem map_eigenvalues_conjTranspose_mul_self {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    Multiset.map (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
        Finset.univ.val
      = Multiset.map (fun i => hA.eigenvalues i ^ 2) Finset.univ.val := by
  have hofReal : Function.Injective (RCLike.ofReal : ℝ → ℂ) := Complex.ofReal_injective
  apply Multiset.map_injective hofReal
  rw [Multiset.map_map, Multiset.map_map,
    ← (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.roots_charpoly_eq_eigenvalues,
    hA.eq, isHermitian_mul_self_eq_cfc_sq, ← hA.cfc_eq, hA.charpoly_cfc_eq,
    Finset.prod_eq_multiset_prod]
  rw [show (fun i => Polynomial.X - Polynomial.C (RCLike.ofReal (hA.eigenvalues i ^ 2) : ℂ))
        = (fun a => Polynomial.X - Polynomial.C a) ∘ fun i => (RCLike.ofReal (hA.eigenvalues i ^ 2) : ℂ)
      from rfl, ← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
  rfl
  · exact hA

/-- **Bridge (step 1, linchpin):** the trace norm of a positive-semidefinite matrix
equals its trace. In particular a density operator has trace norm `1`. -/
theorem traceNorm_posSemidef {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  have hms := map_eigenvalues_conjTranspose_mul_self hA.isHermitian
  have hsum : Multiset.map (fun i =>
        Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i))
          Finset.univ.val
      = Multiset.map hA.isHermitian.eigenvalues Finset.univ.val := by
    rw [show (fun i => Real.sqrt
          ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i))
        = Real.sqrt ∘ (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
      from rfl, ← Multiset.map_map, hms, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (hA.eigenvalues_nonneg i)
  have hr : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  unfold traceNorm traceNormOf
  rw [hr, Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, hsum]

/-- **A density operator has trace norm `1`** (step 2): `tr|ρ| = tr ρ = 1`. -/
theorem traceNorm_density_eq_one {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : IsDensityOperator ρ) :
    traceNorm ρ = 1 := by
  rw [traceNorm_posSemidef hρ.1, hρ.2, Complex.one_re]

/-- **Trace norm of a Hermitian matrix is the sum of `|eigenvalues|`** (Phase 6AF). The
abs-eigenvalue form every Hermitian trace-norm argument uses; via the shipped
`map_eigenvalues_conjTranspose_mul_self` + `Real.sqrt_sq_eq_abs`. -/
theorem traceNorm_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    traceNorm A = ∑ i, |hA.eigenvalues i| := by
  have hms := map_eigenvalues_conjTranspose_mul_self hA
  have hsum : Multiset.map (fun i =>
        Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i))
          Finset.univ.val
      = Multiset.map (fun i => |hA.eigenvalues i|) Finset.univ.val := by
    rw [show (fun i => Real.sqrt
          ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i))
        = Real.sqrt ∘ (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
      from rfl, ← Multiset.map_map, hms, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq_eq_abs _
  unfold traceNorm traceNormOf
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, hsum]

/-- Sum of the positive parts of the eigenvalues of a Hermitian matrix
(`∑ max(λᵢ, 0)`). The trace-norm triangle reduces to subadditivity of this. -/
noncomputable def eigPosSum {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, max (hA.eigenvalues i) 0

/-- **`‖H‖₁ = 2·(∑ positive eigenvalues) − tr H`** for Hermitian `H` (from
`|x| = 2·max(x,0) − x`). Reduces the trace-norm triangle to subadditivity of `eigPosSum`. -/
theorem traceNorm_hermitian_eq {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    traceNorm A = 2 * eigPosSum hA - A.trace.re := by
  have hr : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  rw [traceNorm_hermitian hA, hr, eigPosSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total 0 (hA.eigenvalues i) with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

/-- The matrix continuous functional calculus is identity on `id`: `cfc(x ↦ x) M = M`. -/
theorem cfc_id {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    hM.cfc (fun x => x) = M := by
  rw [Matrix.IsHermitian.cfc,
    show (RCLike.ofReal ∘ (fun x => x) ∘ hM.eigenvalues : Fin n → ℂ)
      = (RCLike.ofReal ∘ hM.eigenvalues) from rfl, ← hM.spectral_theorem]

/-- The matrix continuous functional calculus is multiplicative:
`cfc f M · cfc g M = cfc (f·g) M`. -/
theorem cfc_mul {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (f g : ℝ → ℝ) :
    hM.cfc f * hM.cfc g = hM.cfc (fun x => f x * g x) := by
  have hfun : (fun i => (RCLike.ofReal ∘ f ∘ hM.eigenvalues) i
        * (RCLike.ofReal ∘ g ∘ hM.eigenvalues) i)
      = (RCLike.ofReal ∘ (fun x => f x * g x) ∘ hM.eigenvalues : Fin n → ℂ) := by
    funext i; simp only [Function.comp_apply]; push_cast; ring
  rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, ← map_mul,
    diagonal_mul_diagonal, hfun]

/-- **Achievement:** `∑ positive eigenvalues = Re tr(P·H)` where `P = cfc(𝟙_{x>0})H`
is the positive-eigenvalue projection (since `𝟙_{x>0}(x)·x = max(x,0)` on the spectrum). -/
theorem eigPosSum_eq_re_trace_posProj {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    eigPosSum hM = (((hM.cfc fun x => if 0 < x then (1:ℝ) else 0) * M).trace).re := by
  have hPM : (hM.cfc fun x => if 0 < x then (1:ℝ) else 0) * M
      = hM.cfc (fun x => max x 0) := by
    have h1 : hM.cfc (fun x => max x 0)
        = (hM.cfc fun x => if 0 < x then (1:ℝ) else 0) * hM.cfc (fun x => x) := by
      rw [cfc_mul hM]
      congr 1
      funext x
      by_cases h : 0 < x
      · simp [h, max_eq_left h.le]
      · simp [h, max_eq_right (not_lt.mp h)]
    rw [h1, cfc_id hM]
  rw [hPM, trace_cfc, eigPosSum, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_re _).symm

/-- `cfc f M` is Hermitian for a real function `f` (real diagonal conjugated by a unitary). -/
theorem cfc_isHermitian {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (hM.cfc f).IsHermitian := by
  have hD : star (Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues : Fin n → ℂ))
      = Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues : Fin n → ℂ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    simp [Function.comp_def, Complex.conj_ofReal]
  rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, Matrix.IsHermitian.cfc, ← map_star, hD]

/-- `cfc f M` is positive-semidefinite when `f ≥ 0` on the spectrum (real diagonal of
nonnegative entries, conjugated by a unitary). -/
theorem cfc_posSemidef {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hM.eigenvalues i)) : (hM.cfc f).PosSemidef := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hd : (Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues : Fin n → ℂ)).PosSemidef := by
    refine Matrix.PosSemidef.diagonal fun i => ?_
    simp only [Pi.zero_apply, Function.comp_apply]
    exact Complex.zero_le_real.mpr (hf i)
  have h := hd.conjTranspose_mul_mul_same
    ((hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ)
  simpa [Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, mul_assoc] using h

/-- **Re tr(Q·S) ≥ 0** for a Hermitian idempotent (projection) `Q` and positive-
semidefinite `S`: `tr(Q·S) = tr(Qᴴ·S·Q)` (cyclic + `Q²=Q`), and `Qᴴ·S·Q` is PSD. -/
theorem re_trace_proj_mul_posSemidef_nonneg {Q S : Matrix (Fin n) (Fin n) ℂ}
    (hQh : Q.IsHermitian) (hQi : Q * Q = Q) (hS : S.PosSemidef) :
    0 ≤ (Q * S).trace.re := by
  have htr : (Qᴴ * S * Q).trace = (Q * S).trace := by
    rw [hQh.eq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQi]
  rw [← htr]
  exact (Complex.le_def.mp (hS.conjTranspose_mul_mul_same Q).trace_nonneg).1

/-- The matrix cfc is subtractive: `cfc f M − cfc g M = cfc (f−g) M`. -/
theorem cfc_sub {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (f g : ℝ → ℝ) :
    hM.cfc f - hM.cfc g = hM.cfc (fun x => f x - g x) := by
  have hfun : (fun i => (RCLike.ofReal ∘ f ∘ hM.eigenvalues) i
        - (RCLike.ofReal ∘ g ∘ hM.eigenvalues) i)
      = (RCLike.ofReal ∘ (fun x => f x - g x) ∘ hM.eigenvalues : Fin n → ℂ) := by
    funext i; simp only [Function.comp_apply]; push_cast; ring
  rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, ← map_sub,
    diagonal_sub, hfun]

/-- Positive part of a Hermitian matrix, `cfc(max(·,0))M` (positive-semidefinite). -/
noncomputable def posPart {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    Matrix (Fin n) (Fin n) ℂ := hM.cfc (fun x => max x 0)

/-- Negative part of a Hermitian matrix, `cfc(max(−·,0))M` (positive-semidefinite). -/
noncomputable def negPart {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    Matrix (Fin n) (Fin n) ℂ := hM.cfc (fun x => max (-x) 0)

theorem posPart_posSemidef {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    (posPart hM).PosSemidef := cfc_posSemidef hM fun _ => le_max_right _ _

theorem negPart_posSemidef {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    (negPart hM).PosSemidef := cfc_posSemidef hM fun _ => le_max_right _ _

/-- **`M = posPart M − negPart M`** (`max(x,0) − max(−x,0) = x`). -/
theorem self_eq_posPart_sub_negPart {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    M = posPart hM - negPart hM := by
  rw [posPart, negPart, cfc_sub]
  conv_lhs => rw [← cfc_id hM]
  congr 1
  funext x
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), sub_neg_eq_add, zero_add]

/-- `∑ positive eigenvalues = Re tr(posPart M)`. -/
theorem eigPosSum_eq_re_trace_posPart {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    eigPosSum hM = (posPart hM).trace.re := by
  rw [posPart, trace_cfc, eigPosSum, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_re _).symm

/-- Positive-eigenvalue projection `cfc(𝟙_{x>0})M`. -/
noncomputable def posProj {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    Matrix (Fin n) (Fin n) ℂ := hM.cfc (fun x => if 0 < x then (1:ℝ) else 0)

theorem posProj_isHermitian {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    (posProj hM).IsHermitian := cfc_isHermitian hM _

theorem posProj_idem {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    posProj hM * posProj hM = posProj hM := by
  rw [posProj, cfc_mul]
  congr 1
  funext x
  by_cases h : 0 < x <;> simp [h]

theorem one_sub_posProj_idem {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    (1 - posProj hM) * (1 - posProj hM) = 1 - posProj hM := by
  rw [sub_mul, one_mul, mul_sub, mul_one, posProj_idem, sub_self, sub_zero]

/-- **The projection bound:** `Re tr(P·A) ≤ ∑ positive eigenvalues(A)` for any projection
`P` and Hermitian `A`. The positive-eigenvalue projection maximizes `Re tr(P·A)`. -/
theorem re_trace_proj_mul_le_eigPosSum {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {P : Matrix (Fin n) (Fin n) ℂ} (hPh : P.IsHermitian) (hPi : P * P = P) :
    (P * A).trace.re ≤ eigPosSum hA := by
  rw [eigPosSum_eq_re_trace_posPart hA]
  have hPA : (P * A).trace.re
      = (P * posPart hA).trace.re - (P * negPart hA).trace.re := by
    rw [show P * A = P * posPart hA - P * negPart hA from by
        rw [← mul_sub, ← self_eq_posPart_sub_negPart hA], trace_sub, Complex.sub_re]
  have h1P_herm : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hPh
  have h1P_idem : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hPi, sub_self, sub_zero]
  have h1' : ((1 - P) * posPart hA).trace.re
      = (posPart hA).trace.re - (P * posPart hA).trace.re := by
    rw [sub_mul, one_mul, trace_sub, Complex.sub_re]
  have h1 := re_trace_proj_mul_posSemidef_nonneg h1P_herm h1P_idem (posPart_posSemidef hA)
  have h2 := re_trace_proj_mul_posSemidef_nonneg hPh hPi (negPart_posSemidef hA)
  rw [h1'] at h1
  linarith

/-- **Subadditivity of the positive-eigenvalue sum** (the Ky-Fan-style heart of the
trace-norm triangle): `eigPosSum(A+B) ≤ eigPosSum A + eigPosSum B`. -/
theorem eigPosSum_add_le {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (A + B).IsHermitian) :
    eigPosSum hAB ≤ eigPosSum hA + eigPosSum hB := by
  have hPh := posProj_isHermitian hAB
  have hPi := posProj_idem hAB
  have hach : eigPosSum hAB = (posProj hAB * (A + B)).trace.re :=
    eigPosSum_eq_re_trace_posProj hAB
  have hsplit : (posProj hAB * (A + B)).trace.re
      = (posProj hAB * A).trace.re + (posProj hAB * B).trace.re := by
    rw [mul_add, trace_add, Complex.add_re]
  rw [hach, hsplit]
  have bA := re_trace_proj_mul_le_eigPosSum hA hPh hPi
  have bB := re_trace_proj_mul_le_eigPosSum hB hPh hPi
  linarith

/-- **Trace-norm triangle inequality for Hermitian matrices** (6AF-1):
`‖A+B‖₁ ≤ ‖A‖₁ + ‖B‖₁`. -/
theorem traceNorm_hermitian_triangle {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  have hAB : (A + B).IsHermitian := hA.add hB
  rw [traceNorm_hermitian_eq hA, traceNorm_hermitian_eq hB, traceNorm_hermitian_eq hAB,
    Matrix.trace_add, Complex.add_re]
  have := eigPosSum_add_le hA hB hAB
  linarith

/-- **The trace distance satisfies the triangle inequality** — it is a genuine metric. -/
theorem traceDist_triangle (ρ σ τ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hτ : τ.IsHermitian) :
    traceDist ρ τ ≤ traceDist ρ σ + traceDist σ τ := by
  unfold traceDist
  have h := traceNorm_hermitian_triangle (hρ.sub hσ) (hσ.sub hτ)
  rw [show ρ - σ + (σ - τ) = ρ - τ by abel] at h
  linarith

/-- **The trace distance between density operators lies in `[0,1]`** (6AF-1, step 2 finish):
`0 ≤ D(ρ,σ) ≤ 1`, via the triangle inequality and `‖ρ‖₁ = ‖σ‖₁ = 1`. -/
theorem traceDist_mem_Icc {ρ σ : Matrix (Fin n) (Fin n) ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : traceDist ρ σ ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨traceDist_nonneg ρ σ, ?_⟩
  unfold traceDist
  have h := traceNorm_hermitian_triangle hρ.1.isHermitian hσ.1.isHermitian.neg
  rw [show ρ + -σ = ρ - σ by abel, traceNorm_neg, traceNorm_density_eq_one hρ,
    traceNorm_density_eq_one hσ] at h
  linarith

end SKEFTHawking.QuantumNetwork
