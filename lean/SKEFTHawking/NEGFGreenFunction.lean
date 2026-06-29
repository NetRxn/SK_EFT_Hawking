import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import SKEFTHawking.Basic

/-!
# NEGF Green's functions (Phase 6BA, Wave 1)

To our knowledge, the first machine-checked non-equilibrium Green's-function (NEGF) substrate: the
retarded / advanced Green's functions of a finite tight-binding device
Hamiltonian, the broadening (level-width) matrices `Γ`, and the spectral
function `A = i(G^R − G^A)` together with the two load-bearing structural
results — positivity `A ⪰ 0` and the spectral sum rule `∫ A dE / 2π = 1`.

## Substrate decision (Phase 6BA architecture, 2026-06-29)

NEGF transport is built on **finite-dimensional `Matrix m m ℂ`** (Mathlib's
nonsingular inverse), *not* on PhysLib's `LinearPMap.resolvent`. PhysLib's
`resolvent` (`…/Operators/SpectralTheory/Basic.lean`) is the resolvent of an
*unbounded* operator on an infinite-dimensional Hilbert space — it carries no
trace operation, and the headline transport observables built on this substrate
(transmission `T(E) = Tr[Γ_L G^R Γ_R G^A]` in `LandauerConductance.lean`,
conductance quantization `G = n·G₀` in `NEGFTransportCertificate.lean`) are
inherently finite-dimensional (a finite device region coupled to leads via
finite self-energy matrices). The finite-dim `Matrix` substrate is therefore the
physically correct home; PhysLib `resolvent` is a thematic spectral-identification
bridge, not load-bearing here. This matches the W1 brick list in
`docs/roadmaps/Phase6BA_Roadmap.md` ("finite-dim `Matrix`").

## Physical content

For a Hermitian device Hamiltonian `H` (a finite `m × m` complex matrix), an
energy `E ∈ ℝ`, and an infinitesimal broadening `η > 0`:

* `G^R(E) = ((E + iη)·1 − H)⁻¹`   — retarded Green's function
* `G^A(E) = ((E − iη)·1 − H)⁻¹ = (G^R)ᴴ`  — advanced Green's function
* `A(E)  = i(G^R − G^A)`           — spectral function

The resolvent algebra gives `A = 2η · G^R (G^R)ᴴ ⪰ 0`, and the spectral theorem
plus the Lorentzian (Cauchy) integral `∫ 2η/((E−λ)²+η²) dE = 2π` give the sum
rule `∫ A(E) dE / 2π = 1`.

## References

- Datta, *Electronic Transport in Mesoscopic Systems* (CUP 1995), Ch. 3 — NEGF.
- Datta, *Quantum Transport: Atom to Transistor* (CUP 2005), Ch. 9 — `Γ`, `A`.

Invariants (Phase 6BA): kernel-pure `{propext, Classical.choice, Quot.sound}`;
zero sorry; no project-local axioms; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.NEGF

open Matrix
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## Definitions -/

/-- The inverse retarded Green's function argument, `z(E,η)·1 − H` with
`z = E + iη`. `G^R` is its inverse. -/
noncomputable def retardedArg (H : Matrix m m ℂ) (E η : ℝ) : Matrix m m ℂ :=
  ((E : ℂ) + Complex.I * (η : ℂ)) • (1 : Matrix m m ℂ) - H

/-- The inverse advanced Green's function argument, `(E − iη)·1 − H`. -/
noncomputable def advancedArg (H : Matrix m m ℂ) (E η : ℝ) : Matrix m m ℂ :=
  ((E : ℂ) - Complex.I * (η : ℂ)) • (1 : Matrix m m ℂ) - H

/-- The retarded Green's function `G^R(E) = ((E + iη)·1 − H)⁻¹`. -/
noncomputable def gRetarded (H : Matrix m m ℂ) (E η : ℝ) : Matrix m m ℂ :=
  (retardedArg H E η)⁻¹

/-- The advanced Green's function `G^A(E) = ((E − iη)·1 − H)⁻¹`. Proven equal to
`(G^R)ᴴ` for Hermitian `H` in `gAdvanced_eq_conjTranspose`. -/
noncomputable def gAdvanced (H : Matrix m m ℂ) (E η : ℝ) : Matrix m m ℂ :=
  (advancedArg H E η)⁻¹

/-- The spectral function `A(E) = i(G^R − G^A)`. -/
noncomputable def spectralFn (H : Matrix m m ℂ) (E η : ℝ) : Matrix m m ℂ :=
  Complex.I • (gRetarded H E η - gAdvanced H E η)

/-! ## Invertibility of the resolvent argument

For `η > 0` and Hermitian `H`, the complex number `E + iη` is non-real and hence
not an eigenvalue of `H`, so `(E + iη)·1 − H` is invertible. The proof uses the
imaginary part of the quadratic form: `Im ⟪x, z x⟫ = η ‖x‖²`. -/

/-- For Hermitian `H` and `η > 0`, `retardedArg H E η` is a unit (invertible). -/
theorem retardedArg_isUnit (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) : IsUnit (retardedArg H E η) := by
  have hP : retardedArg H E η * advancedArg H E η
      = ((η : ℂ) ^ 2) • (1 : Matrix m m ℂ)
        + (H - (E : ℂ) • (1 : Matrix m m ℂ)) * (H - (E : ℂ) • (1 : Matrix m m ℂ)) := by
    simp only [retardedArg, advancedArg, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one]
    match_scalars <;> (try linear_combination (-(η : ℂ) ^ 2) * Complex.I_sq) <;> ring
  -- `B := H - E•1` is Hermitian, so `B * B` is positive semidefinite.
  have hBherm : (H - (E : ℂ) • (1 : Matrix m m ℂ)).IsHermitian := by
    refine hH.sub ?_
    refine (Matrix.isHermitian_one).smul ?_
    rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  have hBB : ((H - (E : ℂ) • (1 : Matrix m m ℂ)) *
      (H - (E : ℂ) • (1 : Matrix m m ℂ))).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (H - (E : ℂ) • (1 : Matrix m m ℂ))
    rwa [hBherm] at h
  -- `η²•1` is positive definite (η > 0).
  have hη1 : (((η : ℂ) ^ 2) • (1 : Matrix m m ℂ)).PosDef := by
    refine Matrix.PosDef.one.smul ?_
    have hpos : (0 : ℝ) < η ^ 2 := by positivity
    rw [show ((η : ℂ) ^ 2) = (((η ^ 2 : ℝ)) : ℂ) by push_cast; ring]
    exact_mod_cast hpos
  -- their sum is positive definite, hence a unit; transfer to `retardedArg` via determinants.
  have hpd : (((η : ℂ) ^ 2) • (1 : Matrix m m ℂ)
      + (H - (E : ℂ) • (1 : Matrix m m ℂ)) * (H - (E : ℂ) • (1 : Matrix m m ℂ))).PosDef :=
    hη1.add_posSemidef hBB
  rw [Matrix.isUnit_iff_isUnit_det]
  have hu : IsUnit ((retardedArg H E η * advancedArg H E η).det) := by
    rw [hP]; exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

/-! ## The advanced Green's function is the conjugate transpose -/

omit [Fintype m] in
/-- `advancedArg = (retardedArg)ᴴ` for Hermitian `H` — the inverse-GF arguments are
conjugate-transpose partners (since `E − iη = star (E + iη)` and `Hᴴ = H`). -/
theorem advancedArg_eq_conjTranspose (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ} :
    advancedArg H E η = (retardedArg H E η)ᴴ := by
  have hsc : ((E : ℂ) - Complex.I * (η : ℂ)) = star ((E : ℂ) + Complex.I * (η : ℂ)) := by
    simp [Complex.ext_iff]
  simp only [advancedArg, retardedArg, conjTranspose_sub, conjTranspose_smul,
    conjTranspose_one, hH.eq, ← hsc]

/-- For Hermitian `H` and `η > 0`, `advancedArg H E η` is a unit. -/
theorem advancedArg_isUnit (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) : IsUnit (advancedArg H E η) := by
  rw [advancedArg_eq_conjTranspose H hH E, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_conjTranspose]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (retardedArg_isUnit H hH E hη)).star

/-- `G^A = (G^R)ᴴ` for Hermitian `H` (any broadening `η`). -/
theorem gAdvanced_eq_conjTranspose (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ} :
    gAdvanced H E η = (gRetarded H E η)ᴴ := by
  simp only [gAdvanced, gRetarded, Matrix.conjTranspose_nonsing_inv,
    advancedArg_eq_conjTranspose H hH E]

/-! ## The spectral function as a manifestly positive form -/

/-- Resolvent identity: `A = i(G^R − G^A) = 2η · G^R (G^R)ᴴ`. -/
theorem spectralFn_eq_two_mul_eta (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) :
    spectralFn H E η = (2 * η : ℂ) • (gRetarded H E η * (gRetarded H E η)ᴴ) := by
  -- both resolvent arguments are units, so the inverse-difference identity applies.
  have hiff : IsUnit (retardedArg H E η) ↔ IsUnit (advancedArg H E η) :=
    iff_of_true (retardedArg_isUnit H hH E hη) (advancedArg_isUnit H hH E hη)
  have hdiff : gRetarded H E η - gAdvanced H E η
      = gRetarded H E η * (advancedArg H E η - retardedArg H E η) * gAdvanced H E η := by
    simp only [gRetarded, gAdvanced]
    exact Matrix.inv_sub_inv hiff
  have hBA : advancedArg H E η - retardedArg H E η
      = (-2 * Complex.I * (η : ℂ)) • (1 : Matrix m m ℂ) := by
    simp only [advancedArg, retardedArg]; match_scalars <;> ring
  unfold spectralFn
  rw [hdiff, hBA, gAdvanced_eq_conjTranspose H hH E, mul_smul_comm, smul_mul_assoc, mul_one,
    smul_smul]
  congr 1
  linear_combination (-2 * (η : ℂ)) * Complex.I_sq

/-- **`A ⪰ 0`** — the spectral function is positive semidefinite. -/
theorem spectralFn_posSemidef (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) : (spectralFn H E η).PosSemidef := by
  rw [spectralFn_eq_two_mul_eta H hH E hη]
  refine (Matrix.posSemidef_self_mul_conjTranspose (gRetarded H E η)).smul ?_
  have h2 : (0 : ℝ) ≤ 2 * η := by linarith
  rw [show (2 * η : ℂ) = (((2 * η : ℝ)) : ℂ) by push_cast; ring]
  exact_mod_cast h2

/-! ## Self-energy and broadening matrices

The lead self-energy `Σ` enters the retarded Green's function through the Dyson form
`G^R = (E·1 − H − Σ)⁻¹`; its anti-Hermitian part defines the broadening (level-width)
matrix `Γ = i(Σ − Σᴴ) = i(Σ^R − Σ^A)`. For the closed-system `iη` regularization used
here the effective self-energy is the constant `Σ = −iη·1`, whose broadening is `Γ = 2η·1`,
and the spectral function obeys the fundamental NEGF relation `A = G^R Γ G^A`. -/

/-- The constant self-energy realizing the `iη` broadening: `Σ = −iη·1`. With it,
`E·1 − H − Σ = (E + iη)·1 − H = retardedArg`. -/
noncomputable def selfEnergy (η : ℝ) : Matrix m m ℂ := (-Complex.I * (η : ℂ)) • (1 : Matrix m m ℂ)

/-- The broadening (level-width) matrix of a self-energy: `Γ(Σ) = i(Σ − Σᴴ) = i(Σ^R − Σ^A)`. -/
noncomputable def broadening (S : Matrix m m ℂ) : Matrix m m ℂ := Complex.I • (S - Sᴴ)

omit [Fintype m] in
/-- The Dyson form: `retardedArg = E·1 − H − Σ` for the `iη` self-energy. -/
theorem retardedArg_eq_sub_selfEnergy (H : Matrix m m ℂ) (E : ℝ) (η : ℝ) :
    retardedArg H E η = (E : ℂ) • (1 : Matrix m m ℂ) - H - selfEnergy η := by
  rw [retardedArg, selfEnergy]
  match_scalars <;> ring

omit [Fintype m] [DecidableEq m] in
/-- The broadening matrix `Γ(Σ)` is Hermitian. -/
theorem broadening_isHermitian (S : Matrix m m ℂ) : (broadening S).IsHermitian := by
  unfold broadening Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, Complex.star_def,
    Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

omit [Fintype m] in
/-- The `iη` self-energy has broadening `Γ = 2η·1`. -/
theorem selfEnergy_broadening (η : ℝ) :
    broadening (selfEnergy η) = (2 * (η : ℂ)) • (1 : Matrix m m ℂ) := by
  unfold broadening selfEnergy
  rw [conjTranspose_smul, conjTranspose_one]
  have hst : star (-Complex.I * (η : ℂ)) = Complex.I * (η : ℂ) := by simp
  rw [hst]
  match_scalars
  linear_combination (-2 * (η : ℂ)) * Complex.I_sq

/-- **The fundamental NEGF relation `A = G^R Γ G^A`** — the spectral function equals the
retarded Green's function dressed by the broadening of the (closed-system) self-energy. -/
theorem spectralFn_eq_gR_broadening_gA (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) :
    spectralFn H E η = gRetarded H E η * broadening (selfEnergy η) * gAdvanced H E η := by
  rw [spectralFn_eq_two_mul_eta H hH E hη, gAdvanced_eq_conjTranspose H hH E,
    selfEnergy_broadening, mul_smul_comm, mul_one, smul_mul_assoc]

/-! ## Spectral sum rule -/

open MeasureTheory in
/-- The Lorentzian (Cauchy) integral `∫ 1/((E−λ)² + η²) dE = π/η` over the whole line,
for `η > 0`. Derived from `∫ (1+x²)⁻¹ = π` by translation and rescaling. -/
theorem lorentzian_integral_inv (lam : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ E : ℝ, ((E - lam) ^ 2 + η ^ 2)⁻¹ = Real.pi / η := by
  have hηne : η ≠ 0 := ne_of_gt hη
  -- translate by `lam`
  have htr : (∫ E : ℝ, ((E - lam) ^ 2 + η ^ 2)⁻¹) = ∫ E : ℝ, (E ^ 2 + η ^ 2)⁻¹ :=
    integral_sub_right_eq_self (fun E => (E ^ 2 + η ^ 2)⁻¹) lam
  rw [htr]
  -- rescale: `(E² + η²)⁻¹ = η⁻² · (1 + (η⁻¹ E)²)⁻¹`
  have hpt : ∀ E : ℝ, (E ^ 2 + η ^ 2)⁻¹ = η⁻¹ ^ 2 * (1 + (η⁻¹ * E) ^ 2)⁻¹ := by
    intro E
    have h1 : (0 : ℝ) < E ^ 2 + η ^ 2 := by positivity
    have h2 : (0 : ℝ) < 1 + (η⁻¹ * E) ^ 2 := by positivity
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => (1 + x ^ 2)⁻¹) η⁻¹,
    integral_univ_inv_one_add_sq, inv_inv, abs_of_pos hη, smul_eq_mul]
  field_simp

/-- Diagonalization of the resolvent `(z·1 − H)⁻¹` of a Hermitian `H`, for any `z` that
avoids every eigenvalue: `(z·1 − H)⁻¹ = U · diag(1/(z − λₖ)) · Uᴴ`. -/
theorem resolvent_diag (H : Matrix m m ℂ) (hH : H.IsHermitian) (z : ℂ)
    (hz : ∀ k, z - (hH.eigenvalues k : ℂ) ≠ 0) :
    (z • (1 : Matrix m m ℂ) - H)⁻¹
    = (↑hH.eigenvectorUnitary : Matrix m m ℂ)
      * Matrix.diagonal (fun k => (z - (hH.eigenvalues k : ℂ))⁻¹)
      * star (↑hH.eigenvectorUnitary : Matrix m m ℂ) := by
  set U : Matrix m m ℂ := ↑hH.eigenvectorUnitary with hU
  set lam := hH.eigenvalues with hlam
  have hUs1 : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hUs2 : U * star U = 1 := mul_eq_one_comm.mp hUs1
  have hHdecomp : H = U * Matrix.diagonal (fun k => (lam k : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    congr 2
  -- a general conjugation-multiplies-through helper (uses `star U * U = 1`)
  have conj_mul : ∀ A B : Matrix m m ℂ,
      (U * A * star U) * (U * B * star U) = U * (A * B) * star U := by
    intro A B
    calc (U * A * star U) * (U * B * star U)
        = U * A * (star U * U) * B * star U := by simp only [Matrix.mul_assoc]
      _ = U * A * 1 * B * star U := by rw [hUs1]
      _ = U * (A * B) * star U := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hdiagsub : Matrix.diagonal (fun k => z - (lam k : ℂ))
      = z • (1 : Matrix m m ℂ) - Matrix.diagonal (fun k => (lam k : ℂ)) := by
    ext a b; by_cases h : a = b <;>
      simp [Matrix.smul_apply, Matrix.sub_apply, h]
  have hM : z • (1 : Matrix m m ℂ) - H
      = U * Matrix.diagonal (fun k => z - (lam k : ℂ)) * star U := by
    rw [hHdecomp, hdiagsub, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, mul_one,
      smul_mul_assoc, hUs2]
  have hDD : Matrix.diagonal (fun k => z - (lam k : ℂ))
      * Matrix.diagonal (fun k => (z - (lam k : ℂ))⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal,
      show (fun k => (z - (lam k : ℂ)) * (z - (lam k : ℂ))⁻¹) = (fun _ => (1 : ℂ)) from
        funext fun k => mul_inv_cancel₀ (hz k), Matrix.diagonal_one]
  have hrinv : (z • (1 : Matrix m m ℂ) - H)
      * (U * Matrix.diagonal (fun k => (z - (lam k : ℂ))⁻¹) * star U) = 1 := by
    rw [hM, conj_mul, hDD, Matrix.mul_one, hUs2]
  exact Matrix.inv_eq_right_inv hrinv

/-- `z − λₖ ≠ 0` whenever `z` has nonzero imaginary part — the resolvent-pole avoidance
condition specialized to `z = E ± iη` (the eigenvalues `λₖ` being real). -/
theorem sub_eigenvalue_ne_zero_of_im_ne (H : Matrix m m ℂ) (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (k : m) : z - (hH.eigenvalues k : ℂ) ≠ 0 := by
  intro h
  apply hz
  have : (z - (hH.eigenvalues k : ℂ)).im = z.im := by simp
  rw [h, Complex.zero_im] at this
  exact this.symm

/-- Diagonalization of `G^R`: `G^R(E) = U · diag(1/((E+iη) − λₖ)) · Uᴴ`. -/
theorem gRetarded_diag (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    gRetarded H E η
    = (↑hH.eigenvectorUnitary : Matrix m m ℂ)
      * Matrix.diagonal (fun k => ((E : ℂ) + Complex.I * (η : ℂ) - (hH.eigenvalues k : ℂ))⁻¹)
      * star (↑hH.eigenvectorUnitary : Matrix m m ℂ) := by
  rw [gRetarded, retardedArg]
  exact resolvent_diag H hH _
    (sub_eigenvalue_ne_zero_of_im_ne H hH (by simp [ne_of_gt hη]))

/-- Diagonalization of `G^A`: `G^A(E) = U · diag(1/((E−iη) − λₖ)) · Uᴴ`. -/
theorem gAdvanced_diag (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    gAdvanced H E η
    = (↑hH.eigenvectorUnitary : Matrix m m ℂ)
      * Matrix.diagonal (fun k => ((E : ℂ) - Complex.I * (η : ℂ) - (hH.eigenvalues k : ℂ))⁻¹)
      * star (↑hH.eigenvectorUnitary : Matrix m m ℂ) := by
  rw [gAdvanced, advancedArg]
  exact resolvent_diag H hH _
    (sub_eigenvalue_ne_zero_of_im_ne H hH (by simp [ne_of_gt hη]))

/-- Diagonalization of the spectral function: `A(E) = U · diag(2η/((E−λₖ)²+η²)) · Uᴴ`. -/
theorem spectralFn_diag (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    spectralFn H E η
    = (↑hH.eigenvectorUnitary : Matrix m m ℂ)
      * Matrix.diagonal (fun k => (2 * (η : ℂ)) / (((E : ℂ) - (hH.eigenvalues k : ℂ)) ^ 2 + (η : ℂ) ^ 2))
      * star (↑hH.eigenvectorUnitary : Matrix m m ℂ) := by
  set U : Matrix m m ℂ := ↑hH.eigenvectorUnitary with hU
  set lam := hH.eigenvalues with hlam
  rw [spectralFn, gRetarded_diag H hH E hη, gAdvanced_diag H hH E hη]
  -- factor `U · (-) · Uᴴ` out of the difference, then out of the `I•`
  rw [show (U * Matrix.diagonal (fun k => ((E : ℂ) + Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹) * star U)
        - (U * Matrix.diagonal (fun k => ((E : ℂ) - Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹) * star U)
      = U * (Matrix.diagonal (fun k => ((E : ℂ) + Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹)
            - Matrix.diagonal (fun k => ((E : ℂ) - Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹)) * star U
      from by rw [Matrix.mul_sub, Matrix.sub_mul]]
  rw [show Complex.I • (U * (Matrix.diagonal (fun k => ((E : ℂ) + Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹)
            - Matrix.diagonal (fun k => ((E : ℂ) - Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹)) * star U)
      = U * (Complex.I • (Matrix.diagonal (fun k => ((E : ℂ) + Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹)
            - Matrix.diagonal (fun k => ((E : ℂ) - Complex.I * (η : ℂ) - (lam k : ℂ))⁻¹))) * star U
      from by rw [mul_smul_comm, smul_mul_assoc]]
  congr 2
  -- reduce to the per-eigenvalue scalar identity
  ext a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    have hwR : (E : ℂ) + Complex.I * (η : ℂ) - (lam a : ℂ) ≠ 0 :=
      sub_eigenvalue_ne_zero_of_im_ne H hH (by simp [ne_of_gt hη]) a
    have hwA : (E : ℂ) - Complex.I * (η : ℂ) - (lam a : ℂ) ≠ 0 :=
      sub_eigenvalue_ne_zero_of_im_ne H hH (by simp [ne_of_gt hη]) a
    have hden : ((E : ℂ) - (lam a : ℂ)) ^ 2 + (η : ℂ) ^ 2 ≠ 0 := by
      rw [show ((E : ℂ) - (lam a : ℂ)) ^ 2 + (η : ℂ) ^ 2
          = (((E - lam a) ^ 2 + η ^ 2 : ℝ) : ℂ) from by push_cast; ring]
      exact_mod_cast ne_of_gt (by positivity)
    rw [inv_sub_inv hwR hwA]
    field_simp
    linear_combination (-2 * (η : ℂ) * ((E : ℂ) - (lam a : ℂ)) ^ 2) * Complex.I_sq
  · simp [Matrix.smul_apply, Matrix.diagonal_apply_ne, h]

open MeasureTheory in
/-- **`∫ A(E) dE / 2π = 1`** — the spectral sum rule, stated entrywise: every matrix
element of the spectral function integrates over all energies to `2π` times the
corresponding identity-matrix element (diagonal entries → `2π`, off-diagonal → `0`). -/
theorem negf_spectral_sum_rule (H : Matrix m m ℂ) (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η)
    (i j : m) :
    (∫ E : ℝ, (spectralFn H E η) i j) = 2 * (Real.pi : ℂ) * (1 : Matrix m m ℂ) i j := by
  set U : Matrix m m ℂ := ↑hH.eigenvectorUnitary with hU
  set lam := hH.eigenvalues with hlam
  have hUs2 : U * star U = 1 := mul_eq_one_comm.mp (Matrix.UnitaryGroup.star_mul_self _)
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hη
  -- (real) Lorentzian is integrable: scale `(1+x²)⁻¹`, then translate by `lk`.
  have hh : Integrable (fun x : ℝ => (x ^ 2 + η ^ 2)⁻¹) := by
    have key := ((integrable_comp_mul_left_iff (fun y : ℝ => (1 + y ^ 2)⁻¹)
      (inv_ne_zero (ne_of_gt hη))).2 integrable_inv_one_add_sq).const_mul (η⁻¹ ^ 2)
    rw [show (fun x : ℝ => (x ^ 2 + η ^ 2)⁻¹)
        = (fun x : ℝ => η⁻¹ ^ 2 * (1 + (η⁻¹ * x) ^ 2)⁻¹) from by
          funext x
          have h1 : (0 : ℝ) < x ^ 2 + η ^ 2 := by positivity
          have h2 : (0 : ℝ) < 1 + (η⁻¹ * x) ^ 2 := by positivity
          field_simp
          ring]
    exact key
  have hintR : ∀ lk : ℝ, Integrable (fun E : ℝ => (2 * η) * ((E - lk) ^ 2 + η ^ 2)⁻¹) := by
    intro lk
    exact (hh.comp_sub_right lk).const_mul (2 * η)
  -- complex Lorentzian = `↑(real)`; integrable and integrates to `2π`.
  have hcastfun : ∀ lk : ℝ, (fun E : ℝ => (2 * (η : ℂ)) / (((E : ℂ) - (lk : ℂ)) ^ 2 + (η : ℂ) ^ 2))
      = (fun E : ℝ => (((2 * η) * ((E - lk) ^ 2 + η ^ 2)⁻¹ : ℝ) : ℂ)) := by
    intro lk; funext E; push_cast; rw [div_eq_mul_inv]
  have hcL : ∀ lk : ℝ, Integrable (fun E : ℝ =>
      (2 * (η : ℂ)) / (((E : ℂ) - (lk : ℂ)) ^ 2 + (η : ℂ) ^ 2)) := by
    intro lk; rw [hcastfun lk]; exact (hintR lk).ofReal
  have hLor : ∀ lk : ℝ, (∫ E : ℝ, (2 * (η : ℂ)) / (((E : ℂ) - (lk : ℂ)) ^ 2 + (η : ℂ) ^ 2))
      = 2 * (Real.pi : ℂ) := by
    intro lk
    rw [hcastfun lk, integral_complex_ofReal, integral_const_mul, lorentzian_integral_inv lk hη]
    push_cast
    field_simp
  -- entry of `A` as a finite sum of constant-coefficient Lorentzians
  have hentry : ∀ E : ℝ, (spectralFn H E η) i j
      = ∑ k, (U i k * (star U) k j)
          * ((2 * (η : ℂ)) / (((E : ℂ) - (lam k : ℂ)) ^ 2 + (η : ℂ) ^ 2)) := by
    intro E
    rw [spectralFn_diag H hH E hη, Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hterm : ∀ k : m, (∫ (a : ℝ), U i k * (star U) k j
        * (2 * (η : ℂ) / (((a : ℂ) - (lam k : ℂ)) ^ 2 + (η : ℂ) ^ 2)))
      = U i k * (star U) k j * (2 * (Real.pi : ℂ)) := by
    intro k
    exact (integral_const_mul (U i k * (star U) k j) _).trans
      (congrArg (fun t => U i k * (star U) k j * t) (hLor (lam k)))
  simp_rw [hentry]
  rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hcL (lam k)).const_mul _),
    Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul,
    show (∑ k, U i k * (star U) k j) = (U * star U) i j from (Matrix.mul_apply ..).symm, hUs2]
  ring

end SKEFTHawking.NEGF
