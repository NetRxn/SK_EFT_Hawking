import Mathlib
import SKEFTHawking.KummerRP3Covering

/-!
# The antipodal map of `S³ ⊂ ℂ²` is homotopic to the identity — `τ_* = 1` on `H₊(S³;ℤ)`

The pinned antipodal involution `negS3 : (a,b) ↦ (−a,−b)` is complex multiplication by `−1 = e^{iπ}`
in both coordinates, so the **phase rotation** `H((a,b), s) = (e^{iπs}a, e^{iπs}b)` is a free
homotopy from the identity (`s = 0`) to `negS3` (`s = 1`) *through* `S³` (`|e^{iπs}| = 1` preserves
the defining norm). By integral homotopy invariance the homology deck action is trivial in every
positive degree:

* `tauHomS3_eq_id : τ_* = 1` on `Hₙ₊₁(S³;ℤ)` — hence
* `normHom_S3_eq_two_smul : N_* = 2` and `diffHom_S3_eq_zero : D_* = 0`.

This is the odd-sphere degree fact (`deg(antipodal) = (−1)⁴ = +1`) obtained *without* degree
theory — the ℂ²-carrier's phase rotation replaces it. It feeds the Smith-sequence solve of
`H_*(ℝP³;ℤ)`: on the covering sphere the norm sequence's `D`-map dies and the `N`-map doubles.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (S3top negS3C tauHomS3 tauHom normHom diffHom)
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularHomotopyInvariance (slice)

namespace SKEFTHawking.KummerRP3TauHomotopy

noncomputable section

/-- The unit-norm rotation phase `e^{iπs}`. -/
def phase (s : unitInterval) : ℂ := Complex.exp ((Real.pi * (s : ℝ) : ℝ) * Complex.I)

theorem norm_phase (s : unitInterval) : ‖phase s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase_zero : phase 0 = 1 := by
  simp [phase]

theorem phase_one : phase 1 = -1 := by
  simp [phase, Complex.exp_pi_mul_I]

theorem continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

/-- **The phase-rotation homotopy** `H((a,b), s) = (e^{iπs}a, e^{iπs}b)` from the identity to the
antipodal map, through `S³`. -/
def tauHomotopy : C(↑S3top × unitInterval, ↑S3top) :=
  ⟨fun p => ⟨(phase p.2 * p.1.1.1, phase p.2 * p.1.1.2), by
      simpa [norm_mul, norm_phase p.2] using p.1.2⟩,
    by
      apply Continuous.subtype_mk
      exact ((continuous_phase.comp continuous_snd).mul
          ((continuous_subtype_val.comp continuous_fst).fst)).prodMk
        ((continuous_phase.comp continuous_snd).mul
          ((continuous_subtype_val.comp continuous_fst).snd))⟩

theorem slice_tauHomotopy_zero : slice tauHomotopy 0 = ContinuousMap.id ↑S3top := by
  ext x
  apply Subtype.ext
  show (phase 0 * x.1.1, phase 0 * x.1.2) = x.1
  rw [phase_zero]
  simp

theorem slice_tauHomotopy_one : slice tauHomotopy 1 = negS3C := by
  ext x
  apply Subtype.ext
  show (phase 1 * x.1.1, phase 1 * x.1.2) = (negS3 x).1
  rw [phase_one]
  apply Prod.ext <;> simp [negS3]

/-- **The homology deck action is trivial in positive degrees**: `τ_* = 1` on `Hₙ₊₁(S³;ℤ)`. -/
theorem tauHomS3_eq_id (n : ℕ) : tauHomS3 (n + 1) = LinearMap.id := by
  have h := SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_eq_of_homotopic
    (f := ContinuousMap.id ↑S3top) (g := negS3C) tauHomotopy
    slice_tauHomotopy_zero slice_tauHomotopy_one n
  rw [tauHomS3, tauHom, h, SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_id]

/-- **`N_* = 2` on `Hₙ₊₁(S³;ℤ)`**: the homology norm operator of the antipodal action doubles. -/
theorem normHom_S3_eq_two_smul (n : ℕ) (h : Homology S3top (n + 1)) :
    normHom negS3C (n + 1) h = 2 • h := by
  have htau : Homology.mapInt negS3C (n + 1) h = h := by
    have := congrArg (fun f => f h) (tauHomS3_eq_id n)
    simpa [tauHomS3, tauHom] using this
  show (LinearMap.id + Homology.mapInt negS3C (n + 1) :
    Homology S3top (n + 1) →ₗ[ℤ] Homology S3top (n + 1)) h = 2 • h
  rw [LinearMap.add_apply, LinearMap.id_apply, htau, two_smul]

/-- **`D_* = 0` on `Hₙ₊₁(S³;ℤ)`**: the homology difference operator of the antipodal action
vanishes. -/
theorem diffHom_S3_eq_zero (n : ℕ) (h : Homology S3top (n + 1)) :
    diffHom negS3C (n + 1) h = 0 := by
  have htau : Homology.mapInt negS3C (n + 1) h = h := by
    have := congrArg (fun f => f h) (tauHomS3_eq_id n)
    simpa [tauHomS3, tauHom] using this
  show (LinearMap.id - Homology.mapInt negS3C (n + 1) :
    Homology S3top (n + 1) →ₗ[ℤ] Homology S3top (n + 1)) h = 0
  rw [LinearMap.sub_apply, LinearMap.id_apply, htau, sub_self]

end

end SKEFTHawking.KummerRP3TauHomotopy
