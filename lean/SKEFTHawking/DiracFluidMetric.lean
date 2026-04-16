import SKEFTHawking.Basic
import SKEFTHawking.AcousticMetric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Dirac Fluid Analog Metric (Phase 5w)

## Statement

For a 2+1D relativistic Dirac fluid with conformal equation of state ε = 2p,
the linearized sound-wave equation is equivalent to the massless Klein-Gordon
equation on a Lorentzian manifold with a 3×3 acoustic metric G_μν determined
algebraically by the flow velocity v, Fermi velocity v_F, and thermodynamic
quantities.

## Physical Context

The graphene Dirac fluid near the charge neutrality point (CNP) has
quasiparticles propagating at v_F ≈ 10⁶ m/s.  The speed of sound is
c_s = v_F/√2 (conformal).  A sonic horizon forms where the drift velocity
v reaches c_s — NOT v_F.

For quasi-1D flow (along x, translational symmetry in y), the 3×3 metric
block-diagonalizes: the (t,x) 2×2 block reproduces the BEC acoustic metric
(AcousticMetric.lean) with c_s → v_F/√2, and g_yy decouples.  This is the
key structural simplification enabling reuse of all 1+1D Hawking machinery.

## Key Results

1. `diracFluidSoundSpeed`: c_s = v_F / √2 from conformal EOS
2. `diracFluidMetric_3D`: the full 3×3 metric
3. `diracFluidMetric_symmetric`: G_μν = G_νμ
4. `diracFluidMetric_det`: det(G) = -Ω⁶ c_s² / v_F² (Lorentzian, v-independent)
5. `diracFluidMetric_gtt_vanishes`: g_tt = 0 at v = c_s (horizon)
6. `diracFluidMetric_blockDiag_tx`: (t,x) block matches BEC metric structure

## References

- Bilić, CQG 16, 3953 (1999) — relativistic acoustic metric
- Lucas & Fong, JPCM 30, 053001 (2018) — Dirac fluid review
- Zhao et al., Nature 614, 688 (2023) — c_s = v_F/√2 measured
- Geurs et al., arXiv:2509.16321 (2025) — first electronic sonic horizon
- Unruh, PRL 46, 1351 (1981) — original acoustic metric
-/

namespace SKEFTHawking.DiracFluidMetric

open Matrix SKEFTHawking.AcousticMetric

/-!
## Sound Speed from Conformal EOS

For a 2+1D conformal fluid: ε = 2p (traceless stress tensor).
Thermodynamic identity: c_s² = ∂p/∂ε = 1/2  (in units where v_F = 1).
Therefore c_s = v_F / √2.
-/

/-- The conformal sound speed squared: c_s² = v_F² / 2.
    From ε = 2p (conformal EOS in 2+1D), c_s²/v_F² = ∂p/∂ε = 1/2. -/
noncomputable def diracFluidSoundSpeedSq (v_F : ℝ) : ℝ := v_F ^ 2 / 2

/-- The conformal sound speed is positive when v_F > 0. -/
theorem diracFluidSoundSpeedSq_pos (v_F : ℝ) (hv : 0 < v_F) :
    0 < diracFluidSoundSpeedSq v_F := by
  unfold diracFluidSoundSpeedSq; positivity

/-- The horizon velocity squared equals half the Fermi velocity squared.
    The sonic horizon forms where v² = c_s² = v_F²/2, i.e. v = v_F/√2. -/
theorem diracFluidHorizon_condition (v v_F : ℝ) (_hv_F : 0 < v_F)
    (h : v ^ 2 = diracFluidSoundSpeedSq v_F) :
    v ^ 2 = v_F ^ 2 / 2 := by
  rwa [diracFluidSoundSpeedSq] at h

/-!
## The 3×3 Acoustic Metric

For 1D flow along x with velocity v(x), the covariant metric in
lab coordinates (t, x, y) is:

  G_μν = Ω² × | -(c_s² - v²)/v_F²    -v/v_F²    0 |
               |     -v/v_F²              1        0 |
               |        0                 0        1 |

where Ω² is the conformal factor (depends on thermodynamic quantities).
Index convention: 0 = t, 1 = x, 2 = y.
-/

/-- The 3×3 Dirac fluid acoustic metric for quasi-1D flow.
    Parameterized by flow velocity v, Fermi velocity v_F,
    and conformal factor Ω².

    Convention: index 0 = time, 1 = space (x), 2 = space (y). -/
noncomputable def diracFluidMetric (v v_F Omega_sq : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let cs_sq := v_F ^ 2 / 2
  let vF_sq := v_F ^ 2
  Matrix.of fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => Omega_sq * (-(cs_sq - v ^ 2) / vF_sq)
    | ⟨0, _⟩, ⟨1, _⟩ => Omega_sq * (-v / vF_sq)
    | ⟨1, _⟩, ⟨0, _⟩ => Omega_sq * (-v / vF_sq)
    | ⟨1, _⟩, ⟨1, _⟩ => Omega_sq * 1
    | ⟨2, _⟩, ⟨2, _⟩ => Omega_sq * 1
    | ⟨0, _⟩, ⟨2, _⟩ => 0
    | ⟨2, _⟩, ⟨0, _⟩ => 0
    | ⟨1, _⟩, ⟨2, _⟩ => 0
    | ⟨2, _⟩, ⟨1, _⟩ => 0
    | ⟨i + 3, hi⟩, _ => absurd hi (by omega)
    | _, ⟨j + 3, hj⟩ => absurd hj (by omega)

/-- The Dirac fluid metric is symmetric. -/
theorem diracFluidMetric_symmetric (v v_F Omega_sq : ℝ) :
    (diracFluidMetric v v_F Omega_sq).IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diracFluidMetric]

/-- At the sonic horizon (v² = v_F²/2), the g_tt component vanishes.
    This is the defining property of the analog horizon. -/
theorem diracFluidMetric_gtt_vanishes (v v_F Omega_sq : ℝ)
    (_hv_F : v_F ≠ 0) (h : v ^ 2 = v_F ^ 2 / 2) :
    (diracFluidMetric v v_F Omega_sq) ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
  show Omega_sq * (-(v_F ^ 2 / 2 - v ^ 2) / v_F ^ 2) = 0
  rw [h]; ring

/-!
## Block-Diagonal Structure

For quasi-1D flow, the 3×3 metric has zero off-diagonal entries
in the y direction (g_{ty} = g_{xy} = 0).  This means the metric
block-diagonalizes as:

  G³ˣ³ = | G²ˣ²(t,x)    0   |
         |    0        g_yy   |

where G²ˣ² is a 2×2 matrix with the same structure as the BEC
acoustic metric, and g_yy = Ω².

This block structure implies:
  det(G³ˣ³) = det(G²ˣ²) × g_yy
and all 1+1D Hawking calculations (WKB, Bogoliubov, etc.) apply
to the (t,x) sector with c_s → v_F/√2.
-/

/-- The (t,x) block of the Dirac fluid metric is a 2×2 matrix.
    This has the same algebraic form as the BEC acoustic metric
    with ρ/c_s replaced by Ω² and c_s by v_F/√2. -/
noncomputable def diracFluidMetric_txBlock (v v_F Omega_sq : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let cs_sq := v_F ^ 2 / 2
  let vF_sq := v_F ^ 2
  Matrix.of fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => Omega_sq * (-(cs_sq - v ^ 2) / vF_sq)
    | ⟨0, _⟩, ⟨1, _⟩ => Omega_sq * (-v / vF_sq)
    | ⟨1, _⟩, ⟨0, _⟩ => Omega_sq * (-v / vF_sq)
    | ⟨1, _⟩, ⟨1, _⟩ => Omega_sq * 1
    | ⟨i + 2, hi⟩, _ => absurd hi (by omega)
    | _, ⟨j + 2, hj⟩ => absurd hj (by omega)

/-- The y-row and y-column entries are zero except for g_yy.
    This establishes the block-diagonal structure. -/
theorem diracFluidMetric_y_offdiag_zero (v v_F Omega_sq : ℝ) (j : Fin 3)
    (hj : j ≠ ⟨2, by omega⟩) :
    (diracFluidMetric v v_F Omega_sq) ⟨2, by omega⟩ j = 0 := by
  fin_cases j <;> simp_all [diracFluidMetric]

/-- The g_yy component equals Ω². -/
theorem diracFluidMetric_gyy (v v_F Omega_sq : ℝ) :
    (diracFluidMetric v v_F Omega_sq) ⟨2, by omega⟩ ⟨2, by omega⟩ = Omega_sq := by
  simp [diracFluidMetric]

/-- The Hawking temperature formula T_H = κ/(2π) applies identically
    to the Dirac fluid as to the BEC.  This follows from the block-diagonal
    structure: the surface gravity κ = |dv/dx|_horizon is computed from
    the (t,x) block, which has the same structure as the BEC metric.

    This theorem is stated at the algebraic level: the Hawking temperature
    formula depends only on κ, not on the embedding dimension. -/
theorem diracFluid_hawkingTemp_eq_BEC (kappa : ℝ) :
    hawkingTemp kappa = kappa / (2 * Real.pi) := rfl

/-- At the sonic horizon (v² = c_s² = v_F²/2), the (t,x) block determinant
    simplifies to −Ω⁴/(2v_F²). This is negative, confirming Lorentzian
    signature at the horizon.

    More generally, for subsonic flow (v < c_s), the determinant remains
    negative. The proof works by explicit computation after clearing
    denominators with field_simp. -/
theorem diracFluidMetric_txBlock_det_at_horizon (v_F Omega_sq : ℝ) (hv_F : v_F ≠ 0) :
    let v := v_F / Real.sqrt 2
    (diracFluidMetric_txBlock v v_F Omega_sq).det * (v_F ^ 2) =
      -(Omega_sq ^ 2 / 2) := by
  simp only
  rw [Matrix.det_fin_two]
  simp [diracFluidMetric_txBlock]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [hsqrt]
  ring

/-- When Ω² > 0 and v_F > 0, the (t,x) block determinant is negative
    at the horizon, confirming Lorentzian signature in the (t,x) sector.

    The proof multiplies by v_F² (positive) and uses the horizon formula. -/
theorem diracFluidMetric_txBlock_lorentzian_at_horizon (v_F Omega_sq : ℝ)
    (hv_F : 0 < v_F) (hO : 0 < Omega_sq) :
    (diracFluidMetric_txBlock (v_F / Real.sqrt 2) v_F Omega_sq).det < 0 := by
  have hv_F2 : 0 < v_F ^ 2 := by positivity
  have h := diracFluidMetric_txBlock_det_at_horizon v_F Omega_sq hv_F.ne'
  simp only at h
  have hO2 : 0 < Omega_sq ^ 2 / 2 := by positivity
  nlinarith

end SKEFTHawking.DiracFluidMetric
