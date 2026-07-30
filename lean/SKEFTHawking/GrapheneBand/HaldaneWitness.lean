import SKEFTHawking.GrapheneBand.DiracExpansion
import SKEFTHawking.TopologicalBand.BlochFHS

/-!
# The Haldane Chern witness and the cone Berry phase (Phase 6ED, Wave 3)
-/

namespace SKEFTHawking.GrapheneBand

open Complex Real Matrix SKEFTHawking.Topological SKEFTHawking.TopologicalBand
open scoped BigOperators

/-! ## Rational-enclosure `arg` sectors -/

/-- For `Re z > 0` the argument is the `arctan` of the slope. -/
theorem arg_eq_arctan_of_re_pos {z : ℂ} (h : 0 < z.re) : z.arg = Real.arctan (z.im / z.re) := by
  have habs : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)
  rw [abs_lt] at habs
  rw [← Complex.tan_arg, Real.arctan_tan (by linarith [habs.1]) habs.2]

/-- Upper `arg` bound from a slope bound, at a reference angle `a` with known tangent. -/
theorem arg_lt_of_slope {z : ℂ} {a c : ℝ} (hre : 0 < z.re) (hta : Real.tan a = c)
    (ha1 : -(Real.pi / 2) < a) (ha2 : a < Real.pi / 2) (h : z.im < c * z.re) : z.arg < a := by
  rw [arg_eq_arctan_of_re_pos hre, ← Real.arctan_tan ha1 ha2, hta]
  exact Real.arctan_lt_arctan_iff.mpr ((div_lt_iff₀ hre).mpr h)

/-- Lower `arg` bound from a slope bound. -/
theorem lt_arg_of_slope {z : ℂ} {a c : ℝ} (hre : 0 < z.re) (hta : Real.tan a = c)
    (ha1 : -(Real.pi / 2) < a) (ha2 : a < Real.pi / 2) (h : c * z.re < z.im) : a < z.arg := by
  rw [arg_eq_arctan_of_re_pos hre, ← Real.arctan_tan ha1 ha2, hta]
  exact Real.arctan_lt_arctan_iff.mpr ((lt_div_iff₀ hre).mpr h)

theorem tan_pi_div_six : Real.tan (Real.pi / 6) = 1 / Real.sqrt 3 := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_six, Real.cos_pi_div_six,
    div_div_div_cancel_right₀]
  norm_num

theorem tan_pi_div_three : Real.tan (Real.pi / 3) = Real.sqrt 3 := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring

theorem tan_neg_pi_div_six : Real.tan (-(Real.pi / 6)) = -(1 / Real.sqrt 3) := by
  rw [Real.tan_neg, tan_pi_div_six]

theorem tan_neg_pi_div_three : Real.tan (-(Real.pi / 3)) = -Real.sqrt 3 := by
  rw [Real.tan_neg, tan_pi_div_three]

theorem tan_neg_pi_div_four : Real.tan (-(Real.pi / 4)) = -1 := by
  rw [Real.tan_neg, Real.tan_pi_div_four]

/-- **Sector A** — `arg z ∈ [0, π/6)`: positive real part, non-negative imaginary part, slope
below `tan (π/6) = 1/√3` (stated as the radical-free `√3 · Im z < Re z`). -/
theorem arg_cell_A {z : ℂ} (hre : 0 < z.re) (him : 0 ≤ z.im) (h : Real.sqrt 3 * z.im < z.re) :
    0 ≤ z.arg ∧ z.arg < Real.pi / 6 := by
  have hpi := Real.pi_pos
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  refine ⟨Complex.arg_nonneg_iff.mpr him, arg_lt_of_slope hre tan_pi_div_six (by linarith) (by linarith) ?_⟩
  rw [one_div, inv_mul_eq_div, lt_div_iff₀ h3]
  linarith [h]

/-- **Sector B** — `arg z ∈ (−π/6, 0]`. -/
theorem arg_cell_B {z : ℂ} (hre : 0 < z.re) (him : z.im ≤ 0) (h : -z.re < Real.sqrt 3 * z.im) :
    -(Real.pi / 6) < z.arg ∧ z.arg ≤ 0 := by
  have hpi := Real.pi_pos
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  refine ⟨lt_arg_of_slope hre tan_neg_pi_div_six (by linarith) (by linarith) ?_, ?_⟩
  · rw [neg_mul, one_div, inv_mul_eq_div, neg_lt, lt_div_iff₀ h3]
    nlinarith [h]
  · rw [arg_eq_arctan_of_re_pos hre, Real.arctan_le_zero]
    exact div_nonpos_of_nonpos_of_nonneg him hre.le

/-- **Sector C** — `arg z ∈ (π/4, π/2)`, certified by the radical-free `Re z < Im z`.

The two large-argument sectors are deliberately *asymmetric*: `π/4` on the positive side and `π/3`
on the negative side (sector D). Those are the widest thresholds the Haldane plaquette arithmetic
below tolerates — widening D to `π/4` as well would push the winding plaquette's bracket onto the
boundary of its `2π` window. Stating C at `π/4` keeps its side-condition free of `√3`, which is
what makes the two tightest links (`Re ≈ 0.39`) provable by rational enclosure alone. -/
theorem arg_cell_C {z : ℂ} (hre : 0 < z.re) (h : z.re < z.im) :
    Real.pi / 4 < z.arg ∧ z.arg < Real.pi / 2 := by
  have hpi := Real.pi_pos
  refine ⟨lt_arg_of_slope hre Real.tan_pi_div_four (by linarith) (by linarith) (by linarith), ?_⟩
  have habs : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  exact (abs_lt.mp habs).2

/-- **Sector D** — `arg z ∈ (−π/2, −π/3)`. -/
theorem arg_cell_D {z : ℂ} (hre : 0 < z.re) (h : z.im < -(Real.sqrt 3 * z.re)) :
    -(Real.pi / 2) < z.arg ∧ z.arg < -(Real.pi / 3) := by
  have hpi := Real.pi_pos
  refine ⟨?_, arg_lt_of_slope hre tan_neg_pi_div_three (by linarith) (by linarith) (by linarith)⟩
  have habs : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  linarith [(abs_lt.mp habs).1]

/-- **Narrow sector** — `|arg z| < π/4` from `|Im z| < Re z`. -/
theorem abs_arg_lt_pi_div_four {z : ℂ} (hre : 0 < z.re) (h : |z.im| < z.re) :
    |z.arg| < Real.pi / 4 := by
  have hpi := Real.pi_pos
  rw [abs_lt] at h ⊢
  constructor
  · refine lt_arg_of_slope hre tan_neg_pi_div_four (by linarith) (by linarith) ?_
    linarith [h.1]
  · refine arg_lt_of_slope hre Real.tan_pi_div_four (by linarith) (by linarith) ?_
    linarith [h.2]

/-! ## Branch-index placement from bounds -/

theorem branchIndex_eq_zero_of {t : ℝ} (h1 : -Real.pi < t) (h2 : t ≤ Real.pi) :
    branchIndex t = 0 := by
  rw [branchIndex, toIocDiv_eq_iff, Set.mem_Ioc]
  simp only [zero_zsmul, sub_zero]
  exact ⟨h1, by linarith⟩

theorem branchIndex_eq_one_of {t : ℝ} (h1 : Real.pi < t) (h2 : t ≤ 3 * Real.pi) :
    branchIndex t = 1 := by
  rw [branchIndex, toIocDiv_eq_iff, Set.mem_Ioc]
  simp only [one_zsmul]
  exact ⟨by linarith, by linarith⟩

/-! ## Frame link arguments -/

theorem arg_circle_exp_of_mem {θ : ℝ} (h : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg (Circle.exp θ : ℂ) = θ := by
  rw [Circle.coe_exp, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I h

theorem arg_phase (z : ℂ) : Complex.arg (phase z : ℂ) = Complex.arg z :=
  arg_circle_exp_of_mem (Complex.arg_mem_Ioc z)

/-- The FHS link argument of a frame is the argument of the raw (unnormalized-by-modulus)
nearest-neighbour overlap. -/
theorem linkArg_linkOfFrame {N₁ N₂ n : ℕ} (F : AdmissibleBandFrame N₁ N₂ n)
    (μ : Fin 2) (k : Torus N₁ N₂) :
    linkArg N₁ N₂ (linkOfFrame F) μ k
      = Complex.arg (frameOverlap (F.state k) (F.state (shift N₁ N₂ μ k))) :=
  arg_phase _

/-! ## Normalization: from a raw state to a unit state -/

/-- The squared norm of a raw (unnormalized) state. -/
noncomputable def selfNormSq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

theorem frameOverlap_self {n : ℕ} (v : Fin n → ℂ) :
    frameOverlap v v = ((selfNormSq v : ℝ) : ℂ) := by
  unfold frameOverlap selfNormSq
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm, Complex.mul_conj]

theorem selfNormSq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ selfNormSq v :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

/-- Rescaling a raw state to unit norm. -/
noncomputable def normalizeVec {n : ℕ} (v : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ((Real.sqrt (selfNormSq v) : ℝ) : ℂ)⁻¹ * v i

theorem frameOverlap_normalizeVec {n : ℕ} (u v : Fin n → ℂ) :
    frameOverlap (normalizeVec u) (normalizeVec v)
      = ((Real.sqrt (selfNormSq u) * Real.sqrt (selfNormSq v) : ℝ) : ℂ)⁻¹ * frameOverlap u v := by
  unfold normalizeVec
  rw [frameOverlap_smul_left, frameOverlap_smul_right, Complex.conj_inv, Complex.conj_ofReal]
  push_cast
  rw [mul_inv]
  ring

theorem normalizeVec_normalized {n : ℕ} (v : Fin n → ℂ) (hv : 0 < selfNormSq v) :
    frameOverlap (normalizeVec v) (normalizeVec v) = 1 := by
  have hs : 0 < Real.sqrt (selfNormSq v) := Real.sqrt_pos.mpr hv
  rw [frameOverlap_normalizeVec, frameOverlap_self, Real.mul_self_sqrt (selfNormSq_nonneg v),
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hv)]
  norm_num

/-- **The normalization is a positive rescaling**, hence invisible to every link argument. -/
theorem arg_frameOverlap_normalizeVec {n : ℕ} (u v : Fin n → ℂ)
    (hu : 0 < selfNormSq u) (hv : 0 < selfNormSq v) :
    Complex.arg (frameOverlap (normalizeVec u) (normalizeVec v))
      = Complex.arg (frameOverlap u v) := by
  have hsu : 0 < Real.sqrt (selfNormSq u) := Real.sqrt_pos.mpr hu
  have hsv : 0 < Real.sqrt (selfNormSq v) := Real.sqrt_pos.mpr hv
  rw [frameOverlap_normalizeVec, ← Complex.ofReal_inv]
  exact Complex.arg_real_mul _ (by positivity)

/-! ## The lower-band eigenvector of a `d`-vector -/

/-- The **raw lower-band eigenvector** `v(d) = (d₁ − i d₂, −(d₃ + ‖d‖))` of `blochPauli d`.
Unnormalized: only its ray matters, and its ray is exactly the `−‖d‖` eigenspace. -/
noncomputable def lbVec (d : Fin 3 → ℝ) : Fin 2 → ℂ :=
  ![(d 0 : ℂ) - Complex.I * (d 1 : ℂ), -((d 2 + Real.sqrt (dNormSq d) : ℝ) : ℂ)]

/-- **The lower-band eigenvector law**, proved directly from the `blochPauli` matrix and the
Pauli norm identity `‖d‖² = d₁² + d₂² + d₃²`. -/
theorem blochPauli_mulVec_lbVec (d : Fin 3 → ℝ) :
    (blochPauli d) *ᵥ lbVec d = (-(Real.sqrt (dNormSq d)) : ℂ) • lbVec d := by
  have hsq : ((Real.sqrt (dNormSq d) : ℝ) : ℂ) * ((Real.sqrt (dNormSq d) : ℝ) : ℂ)
      = (d 0 : ℂ) ^ 2 + (d 1 : ℂ) ^ 2 + (d 2 : ℂ) ^ 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (dNormSq_nonneg d), dNormSq]
    push_cast
    ring
  funext i
  fin_cases i
  · simp only [lbVec, blochPauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Pi.smul_apply, smul_eq_mul, Matrix.cons_val_fin_one, Matrix.head_fin_const]
    push_cast
    ring
  · simp only [lbVec, blochPauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Pi.smul_apply, smul_eq_mul, Matrix.cons_val_fin_one, Matrix.head_fin_const]
    push_cast
    linear_combination -hsq - (d 1 : ℂ) ^ 2 * Complex.I_sq

/-- `‖v(d)‖² = 2‖d‖(‖d‖ + d₃)`. -/
theorem selfNormSq_lbVec (d : Fin 3 → ℝ) :
    selfNormSq (lbVec d)
      = 2 * Real.sqrt (dNormSq d) * (Real.sqrt (dNormSq d) + d 2) := by
  have hsq : Real.sqrt (dNormSq d) * Real.sqrt (dNormSq d) = dNormSq d :=
    Real.mul_self_sqrt (dNormSq_nonneg d)
  unfold selfNormSq lbVec dNormSq at *
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im]
  nlinarith [hsq]

/-- The real part of a raw lower-band overlap. -/
theorem lbOverlap_re (d d' : Fin 3 → ℝ) :
    (frameOverlap (lbVec d) (lbVec d')).re
      = d 0 * d' 0 + d 1 * d' 1
        + (d 2 + Real.sqrt (dNormSq d)) * (d' 2 + Real.sqrt (dNormSq d')) := by
  unfold frameOverlap lbVec
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Complex.add_re, Complex.mul_re, Complex.mul_im, map_sub, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_neg, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The imaginary part of a raw lower-band overlap — an integer whenever `d`, `d'` are. -/
theorem lbOverlap_im (d d' : Fin 3 → ℝ) :
    (frameOverlap (lbVec d) (lbVec d')).im = d 1 * d' 0 - d 0 * d' 1 := by
  unfold frameOverlap lbVec
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Complex.add_im, Complex.mul_re, Complex.mul_im, map_sub, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_neg, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## Building a `BlochLowerBandFrame` from a `d`-field -/

/-- The **north-pole condition** `‖d‖ + d₃ > 0` (i.e. `d` is not on the negative `d₃` axis) is
exactly what makes the `lbVec` gauge nonsingular; it forces the gap. -/
theorem sqrt_dNormSq_pos_of {d : Fin 3 → ℝ} (h : 0 < Real.sqrt (dNormSq d) + d 2) :
    0 < Real.sqrt (dNormSq d) := by
  have hle : d 2 ≤ Real.sqrt (dNormSq d) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by unfold dNormSq; nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)])
  linarith [Real.sqrt_nonneg (dNormSq d)]

theorem dVec_ne_zero_of {d : Fin 3 → ℝ} (h : 0 < Real.sqrt (dNormSq d) + d 2) : d ≠ 0 := by
  intro hd
  rw [hd] at h
  simp [dNormSq] at h

theorem selfNormSq_lbVec_pos {d : Fin 3 → ℝ} (h : 0 < Real.sqrt (dNormSq d) + d 2) :
    0 < selfNormSq (lbVec d) := by
  rw [selfNormSq_lbVec]
  nlinarith [sqrt_dNormSq_pos_of h]

theorem normalizeVec_eq_smul {n : ℕ} (v : Fin n → ℂ) :
    normalizeVec v = ((Real.sqrt (selfNormSq v) : ℝ) : ℂ)⁻¹ • v := rfl

/-- **The lower-band frame of a nonsingular `d`-field.** Every state is the normalized
`−‖d(k)‖` eigenvector of `blochPauli (d k)`; admissibility is the explicit nonvanishing of the
raw nearest-neighbour overlaps. -/
noncomputable def blochFrameOfD {N₁ N₂ : ℕ} (D : Torus N₁ N₂ → (Fin 3 → ℝ))
    (hpos : ∀ k, 0 < Real.sqrt (dNormSq (D k)) + (D k) 2)
    (hov : ∀ (μ : Fin 2) (k : Torus N₁ N₂),
      frameOverlap (lbVec (D k)) (lbVec (D (shift N₁ N₂ μ k))) ≠ 0) :
    BlochLowerBandFrame N₁ N₂ where
  state := fun k => normalizeVec (lbVec (D k))
  normalized := fun k => normalizeVec_normalized _ (selfNormSq_lbVec_pos (hpos k))
  overlap_ne := by
    intro μ k
    rw [frameOverlap_normalizeVec]
    refine mul_ne_zero ?_ (hov μ k)
    simp only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
    exact ne_of_gt (mul_pos (Real.sqrt_pos.mpr (selfNormSq_lbVec_pos (hpos k)))
      (Real.sqrt_pos.mpr (selfNormSq_lbVec_pos (hpos _))))
  dField := D
  gapped := fun k => dVec_ne_zero_of (hpos k)
  lowerBand := by
    intro k
    rw [normalizeVec_eq_smul, Matrix.mulVec_smul, blochPauli_mulVec_lbVec, smul_comm]

/-- The FHS link argument of a `d`-field frame is the argument of the **raw** overlap: the
normalization is a positive rescaling and drops out. -/
theorem linkArg_blochFrameOfD {N₁ N₂ : ℕ} (D : Torus N₁ N₂ → (Fin 3 → ℝ))
    (hpos : ∀ k, 0 < Real.sqrt (dNormSq (D k)) + (D k) 2)
    (hov : ∀ (μ : Fin 2) (k : Torus N₁ N₂),
      frameOverlap (lbVec (D k)) (lbVec (D (shift N₁ N₂ μ k))) ≠ 0)
    (μ : Fin 2) (k : Torus N₁ N₂) :
    linkArg N₁ N₂ (linkOfFrame (blochFrameOfD D hpos hov).toAdmissibleBandFrame) μ k
      = Complex.arg (frameOverlap (lbVec (D k)) (lbVec (D (shift N₁ N₂ μ k)))) := by
  rw [linkArg_linkOfFrame]
  exact arg_frameOverlap_normalizeVec _ _ (selfNormSq_lbVec_pos (hpos k))
    (selfNormSq_lbVec_pos (hpos _))

/-- **Narrow-link triviality.** A sampled band frame all of whose nearest-neighbour overlaps lie
in the open right quarter-plane sector `|arg| < π/4` has vanishing FHS lattice Chern number: every
plaquette's raw curl is then confined to `(−π, π)`, so no plaquette carries a branch correction.

This is the reusable *negative* criterion — the discrete analogue of "a frame with no phase
frustration cannot wind" — and it is what discharges the Haldane model's trivial phase without any
per-plaquette arithmetic. -/
theorem blochLatticeChern_eq_zero_of_narrow {N₁ N₂ n : ℕ} [NeZero N₁] [NeZero N₂]
    (F : AdmissibleBandFrame N₁ N₂ n)
    (h : ∀ (μ : Fin 2) (k : Torus N₁ N₂),
      |Complex.arg (frameOverlap (F.state k) (F.state (shift N₁ N₂ μ k)))| < Real.pi / 4) :
    blochLatticeChern F = 0 := by
  have hz : ∀ k, plaquetteBranch N₁ N₂ (linkOfFrame F) k = 0 := by
    intro k
    unfold plaquetteBranch rawCurl
    rw [linkArg_linkOfFrame, linkArg_linkOfFrame, linkArg_linkOfFrame, linkArg_linkOfFrame]
    have h1 := h 0 k
    have h2 := h 1 (shift N₁ N₂ 0 k)
    have h3 := h 0 (shift N₁ N₂ 1 k)
    have h4 := h 1 k
    rw [abs_lt] at h1 h2 h3 h4
    exact branchIndex_eq_zero_of (by linarith) (by linarith)
  unfold blochLatticeChern latticeChern
  rw [Finset.sum_congr rfl (fun k _ => hz k)]
  simp

/-! ## The Haldane model -/

/-- **The next-nearest-neighbour phase sum** `g(θ) = sin θ₁ + sin(θ₂ − θ₁) − sin θ₂`, the
antisymmetric triangular-sublattice sum whose value at the two Dirac points is `±3√3/2`. -/
noncomputable def haldaneNNN (θ : ℝ × ℝ) : ℝ :=
  Real.sin θ.1 + Real.sin (θ.2 - θ.1) - Real.sin θ.2

/-- **The Haldane `d`-vector.** Wave 1's chiral nearest-neighbour honeycomb `d` (scaled by the
hopping `t`) plus a `d₃` built from the sublattice mass `m` and the complex next-nearest-neighbour
hopping `t₂ e^{iφ}`:

    d(θ) = ( t·Re f(θ), −t·Im f(θ), m − 2 t₂ sin φ · g(θ) ).

The `φ`-dependent part is the time-reversal-breaking term; it is what makes the two Dirac masses
differ and therefore what a nonzero Chern number needs. The identity (Haldane `d₀`) piece
`2 t₂ cos φ ∑ cos` is omitted: it shifts both bands equally and changes neither the eigenvectors
nor any Chern number, and `blochPauli` carries no identity component by design. -/
noncomputable def haldaneD (t t₂ φ m : ℝ) (θ : ℝ × ℝ) : Fin 3 → ℝ :=
  ![t * (structureFactor θ).re, -(t * (structureFactor θ).im),
    m - 2 * t₂ * Real.sin φ * haldaneNNN θ]

/-- **Wave-1 compatibility.** With no next-nearest-neighbour phase and no mass, the Haldane
`d`-vector *is* Wave 1's honeycomb `d`-vector — so this model genuinely extends the graphene
band structure rather than replacing it. -/
theorem haldaneD_eq_honeycombD (t₂ : ℝ) (θ : ℝ × ℝ) :
    haldaneD 1 t₂ 0 0 θ = honeycombD θ := by
  unfold haldaneD honeycombD
  rw [Real.sin_zero]
  norm_num

theorem haldaneNNN_diracK : haldaneNNN diracK = 3 * Real.sqrt 3 / 2 := by
  have e1 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have e2 : Real.sin (4 * π / 3) = -(Real.sqrt 3 / 2) := by
    rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]
  show Real.sin (2 * π / 3) + Real.sin (4 * π / 3 - 2 * π / 3) - Real.sin (4 * π / 3) = _
  rw [show (4 * π / 3 - 2 * π / 3 : ℝ) = 2 * π / 3 by ring, e1, e2]
  ring

theorem haldaneNNN_diracK' : haldaneNNN diracK' = -(3 * Real.sqrt 3 / 2) := by
  have e1 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have e2 : Real.sin (4 * π / 3) = -(Real.sqrt 3 / 2) := by
    rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]
  have e3 : Real.sin (2 * π / 3 - 4 * π / 3) = -(Real.sqrt 3 / 2) := by
    rw [show (2 * π / 3 - 4 * π / 3 : ℝ) = -(2 * π / 3) by ring, Real.sin_neg, e1]
  show Real.sin (4 * π / 3) + Real.sin (2 * π / 3 - 4 * π / 3) - Real.sin (2 * π / 3) = _
  rw [e1, e2, e3]
  ring

/-- **The Dirac mass at `K`** is `m − 3√3 t₂ sin φ` — the whole `d`-vector collapses to its third
component there, because Wave 1's structure factor vanishes at `K`. -/
theorem haldaneD_diracK (t t₂ φ m : ℝ) :
    haldaneD t t₂ φ m diracK = ![0, 0, m - 3 * Real.sqrt 3 * t₂ * Real.sin φ] := by
  unfold haldaneD
  rw [honeycomb_gapless_at_diracK, haldaneNNN_diracK]
  norm_num
  ring

/-- **The Dirac mass at `K'`** is `m + 3√3 t₂ sin φ`: the *opposite* `t₂ sin φ` shift. The two
Dirac points see opposite masses — the entire mechanism of the Haldane phase. -/
theorem haldaneD_diracK' (t t₂ φ m : ℝ) :
    haldaneD t t₂ φ m diracK' = ![0, 0, m + 3 * Real.sqrt 3 * t₂ * Real.sin φ] := by
  unfold haldaneD
  rw [honeycomb_gapless_at_diracK', haldaneNNN_diracK']
  norm_num
  ring

/-- The gap at `K` is exactly `2|m − 3√3 t₂ sin φ|`. -/
theorem haldane_gap_diracK (t t₂ φ m : ℝ) :
    2 * Real.sqrt (dNormSq (haldaneD t t₂ φ m diracK))
      = 2 * |m - 3 * Real.sqrt 3 * t₂ * Real.sin φ| := by
  rw [haldaneD_diracK]
  unfold dNormSq
  norm_num [Real.sqrt_sq_eq_abs, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The gap at `K'` is exactly `2|m + 3√3 t₂ sin φ|`. -/
theorem haldane_gap_diracK' (t t₂ φ m : ℝ) :
    2 * Real.sqrt (dNormSq (haldaneD t t₂ φ m diracK'))
      = 2 * |m + 3 * Real.sqrt 3 * t₂ * Real.sin φ| := by
  rw [haldaneD_diracK']
  unfold dNormSq
  norm_num [Real.sqrt_sq_eq_abs, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **The topological window, as a mass inversion.** The two Dirac masses have *opposite signs*
exactly when `|m| < 3√3 |t₂ sin φ|`. This is the falsifiable content of the phase boundary: the
Chern number can only be nonzero inside this window, and the witness/anti-witness pair below is
sampled on either side of it. -/
theorem haldane_mass_inversion_iff (t t₂ φ m : ℝ) :
    haldaneD t t₂ φ m diracK 2 * haldaneD t t₂ φ m diracK' 2 < 0
      ↔ |m| < |3 * Real.sqrt 3 * t₂ * Real.sin φ| := by
  rw [haldaneD_diracK, haldaneD_diracK']
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  set c := 3 * Real.sqrt 3 * t₂ * Real.sin φ with hc
  constructor
  · intro h
    nlinarith [sq_abs m, sq_abs c, abs_nonneg m, abs_nonneg c]
  · intro h
    nlinarith [sq_abs m, sq_abs c, abs_nonneg m, abs_nonneg c]

/-! ## The `4 × 4` discretized Brillouin torus -/

/-- The Bloch phase sampled at vertex `j` of a length-4 cycle: `θ = 2π j / 4 = π j / 2`. -/
noncomputable def bzPhase (j : ZMod 4) : ℝ := Real.pi * (j.val : ℝ) / 2

/-- The `4 × 4` Brillouin-zone sample point of a torus vertex. -/
noncomputable def bzPoint (k : Torus 4 4) : ℝ × ℝ := (bzPhase k.1, bzPhase k.2)

/-- **The Haldane `d`-field on the `4 × 4` discretized Brillouin torus** at the declared
parameters `t = t₂ = 1`, `φ = π/2`, with the mass `m` left free. -/
noncomputable def haldaneD44 (m : ℝ) (k : Torus 4 4) : Fin 3 → ℝ :=
  haldaneD 1 1 (Real.pi / 2) m (bzPoint k)

/-- The `4 × 4` Haldane `d`-field, expanded into base trigonometric values (the
next-nearest-neighbour term's angle difference is opened with `Real.sin_sub`, so every entry is a
value of `sin`/`cos` at one of the four sampled phases). -/
theorem haldaneD44_eq (m : ℝ) (k : Torus 4 4) :
    haldaneD44 m k
      = ![1 + Real.cos (bzPhase k.1) + Real.cos (bzPhase k.2),
          -(Real.sin (bzPhase k.1) + Real.sin (bzPhase k.2)),
          m - 2 * (Real.sin (bzPhase k.1)
              + (Real.sin (bzPhase k.2) * Real.cos (bzPhase k.1)
                  - Real.cos (bzPhase k.2) * Real.sin (bzPhase k.1))
              - Real.sin (bzPhase k.2))] := by
  unfold haldaneD44 haldaneD haldaneNNN bzPoint
  rw [Real.sin_pi_div_two, structureFactor_re, structureFactor_im, Real.sin_sub]
  norm_num

theorem bzPhase_zero : bzPhase 0 = 0 := by
  rw [bzPhase, show ((0 : ZMod 4)).val = 0 from rfl]; norm_num

theorem bzPhase_one : bzPhase 1 = Real.pi / 2 := by
  rw [bzPhase, show ((1 : ZMod 4)).val = 1 from rfl]; norm_num

theorem bzPhase_two : bzPhase 2 = Real.pi := by
  rw [bzPhase, show ((2 : ZMod 4)).val = 2 from rfl]; push_cast; ring

theorem bzPhase_three : bzPhase 3 = 3 * Real.pi / 2 := by
  rw [bzPhase, show ((3 : ZMod 4)).val = 3 from rfl]; push_cast; ring

theorem sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
    Real.sin_pi_div_two]

theorem cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
    Real.cos_pi_div_two, neg_zero]

/-! ### The `d`-vector table on the 16 sampled momenta

Every entry is `haldaneD44 m` evaluated by the base trigonometric values. The pattern of the third
components — `m`, `m − 4`, `m + 4` — is the discretized image of the `±3√3 t₂ sin φ` Dirac-mass
splitting of `haldaneD_diracK`/`haldaneD_diracK'`. -/

theorem hD44_00 (m : ℝ) : haldaneD44 m (0, 0) = ![3, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero]

theorem hD44_01 (m : ℝ) : haldaneD44 m (0, 1) = ![2, -1, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_one]

theorem hD44_02 (m : ℝ) : haldaneD44 m (0, 2) = ![1, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_two]

theorem hD44_03 (m : ℝ) : haldaneD44 m (0, 3) = ![2, 1, m] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_zero, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_10 (m : ℝ) : haldaneD44 m (1, 0) = ![2, -1, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_one]

theorem hD44_11 (m : ℝ) : haldaneD44 m (1, 1) = ![1, -2, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_one]

theorem hD44_12 (m : ℝ) : haldaneD44 m (1, 2) = ![0, -1, m - 4] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_one, bzPhase_two]

theorem hD44_13 (m : ℝ) : haldaneD44 m (1, 3) = ![1, 0, m - 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_one, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_20 (m : ℝ) : haldaneD44 m (2, 0) = ![1, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_two]

theorem hD44_21 (m : ℝ) : haldaneD44 m (2, 1) = ![0, -1, m + 4] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_one, bzPhase_two]

theorem hD44_22 (m : ℝ) : haldaneD44 m (2, 2) = ![-1, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_two]

theorem hD44_23 (m : ℝ) : haldaneD44 m (2, 3) = ![0, 1, m - 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_two, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_30 (m : ℝ) : haldaneD44 m (3, 0) = ![2, 1, m] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_zero, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_31 (m : ℝ) : haldaneD44 m (3, 1) = ![1, 0, m + 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_one, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_32 (m : ℝ) : haldaneD44 m (3, 2) = ![0, 1, m + 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_two, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_33 (m : ℝ) : haldaneD44 m (3, 3) = ![1, 2, m] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

/-! ### Link overlaps on the 4×4 torus

`hLink m μ k` is the raw lower-band overlap across the `μ`-link at `k`. The four *cell* lemmas
below are the workhorses: each takes the two `d`-vector evaluations plus three numeric
side-conditions and returns a closed `π/6`-wide bracket for the link's argument. Every one of the
32 links is one application. -/

/-- The raw lower-band overlap across the `μ`-link at `k`. -/
noncomputable def hLink (m : ℝ) (μ : Fin 2) (k : Torus 4 4) : ℂ :=
  frameOverlap (lbVec (haldaneD44 m k)) (lbVec (haldaneD44 m (shift 4 4 μ k)))

theorem hLink_re {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3]) :
    (hLink m μ k).re = a1 * b1 + a2 * b2
      + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
        * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) := by
  rw [hLink, hs, lbOverlap_re, hk, hk']
  simp [dNormSq]

theorem hLink_im {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3]) :
    (hLink m μ k).im = a2 * b1 - a1 * b2 := by
  rw [hLink, hs, lbOverlap_im, hk, hk']
  simp

/-- The overlap is nonzero whenever its imaginary part is. -/
theorem hLink_ne_zero_of_im {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h : a2 * b1 - a1 * b2 ≠ 0) : hLink m μ k ≠ 0 := by
  intro hz
  exact h (by rw [← hLink_im hs hk hk', hz, Complex.zero_im])

/-- Link bracket, **cell A**: `arg ∈ [0, π/6]`. -/
theorem hLink_cellA {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h1 : 0 ≤ a2 * b1 - a1 * b2)
    (h2 : Real.sqrt 3 * (a2 * b1 - a1 * b2)
            < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))) :
    0 ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ Real.pi / 6 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_A (z := hLink m μ k) (by rw [hre]; exact h0) (by rw [him]; exact h1)
    (by rw [hre, him]; exact h2)
  exact ⟨p, q.le⟩

/-- Link bracket, **cell B**: `arg ∈ [−π/6, 0]`. -/
theorem hLink_cellB {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h1 : a2 * b1 - a1 * b2 ≤ 0)
    (h2 : -(a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
            < Real.sqrt 3 * (a2 * b1 - a1 * b2)) :
    -(Real.pi / 6) ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ 0 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_B (z := hLink m μ k) (by rw [hre]; exact h0) (by rw [him]; exact h1)
    (by rw [hre, him]; exact h2)
  exact ⟨p.le, q⟩

/-- Link bracket, **cell C**: `arg ∈ [π/4, π/2]`. -/
theorem hLink_cellC {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h2 : a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))
            < a2 * b1 - a1 * b2) :
    Real.pi / 4 ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ Real.pi / 2 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_C (z := hLink m μ k) (by rw [hre]; exact h0)
    (by rw [hre, him]; exact h2)
  exact ⟨p.le, q.le⟩

/-- Link bracket, **cell D**: `arg ∈ [−π/2, −π/3]`. -/
theorem hLink_cellD {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h2 : a2 * b1 - a1 * b2
            < -(Real.sqrt 3 * (a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))))) :
    -(Real.pi / 2) ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ -(Real.pi / 3) := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_D (z := hLink m μ k) (by rw [hre]; exact h0)
    (by rw [hre, him]; exact h2)
  exact ⟨p.le, q.le⟩

/-- Narrow link (`|arg| < π/4`) from `|Im| < Re`. -/
theorem hLink_narrow {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h : |a2 * b1 - a1 * b2| < a1 * b1 + a2 * b2
            + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))) :
    |(hLink m μ k).arg| < Real.pi / 4 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  refine abs_arg_lt_pi_div_four (z := hLink m μ k) ?_ ?_
  · rw [hre]; exact lt_of_le_of_lt (abs_nonneg _) h
  · rw [hre, him]; exact h

/-! ### Rational enclosures of the radicals that occur

Every `d`-vector on the 4×4 grid at the declared parameters is integral, so `‖d‖ = √n` for an
integer `n`. These are the only irrational quantities in the whole Chern computation, and four-digit
rational enclosures are ample: the tightest inequality in the argument has slack `0.026`. -/

theorem sqrt2_lb : (1.4142 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt2_ub : Real.sqrt 2 < 1.4143 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt3_lb : (1.7320 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt3_ub : Real.sqrt 3 < 1.7321 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt6_lb : (2.4494 : ℝ) < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt6_ub : Real.sqrt 6 < 2.4495 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt10_lb : (3.1622 : ℝ) < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt10_ub : Real.sqrt 10 < 3.1623 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt26_lb : (5.0990 : ℝ) < Real.sqrt 26 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt26_ub : Real.sqrt 26 < 5.0991 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- The north-pole condition `‖d‖ + d₃ > 0`, read off an explicit table entry. -/
theorem hpos_of_table {m : ℝ} {k : Torus 4 4} {a1 a2 a3 : ℝ}
    (hk : haldaneD44 m k = ![a1, a2, a3])
    (h : 0 < Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) + a3) :
    0 < Real.sqrt (dNormSq (haldaneD44 m k)) + (haldaneD44 m k) 2 := by
  rw [hk]; simpa [dNormSq] using h

/-! ### The trivial phase `m = 6` (outside the window: `6 > 3√3 ≈ 5.196`) -/

theorem haldane6_pos : ∀ k : Torus 4 4,
    0 < Real.sqrt (dNormSq (haldaneD44 6 k)) + (haldaneD44 6 k) 2 := by
  intro k
  fin_cases k
  · exact hpos_of_table (hD44_00 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_01 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_02 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_03 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_10 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_11 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_12 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_13 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_20 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_21 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_22 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_23 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_30 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_31 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_32 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_33 _) (by norm_num <;> positivity)

theorem haldane6_link_ne : ∀ (μ : Fin 2) (k : Torus 4 4), hLink 6 μ k ≠ 0 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 6) (hD44_10 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 6) (hD44_11 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 6) (hD44_12 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 6) (hD44_13 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 6) (hD44_20 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 6) (hD44_21 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 6) (hD44_22 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 6) (hD44_23 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 6) (hD44_30 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 6) (hD44_31 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 6) (hD44_32 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 6) (hD44_33 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 6) (hD44_00 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 6) (hD44_01 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 6) (hD44_02 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 6) (hD44_03 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 6) (hD44_01 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 6) (hD44_02 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 6) (hD44_03 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 6) (hD44_00 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 6) (hD44_11 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 6) (hD44_12 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 6) (hD44_13 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 6) (hD44_10 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 6) (hD44_21 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 6) (hD44_22 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 6) (hD44_23 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 6) (hD44_20 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 6) (hD44_31 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 6) (hD44_32 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 6) (hD44_33 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 6) (hD44_30 6) (by norm_num)

theorem haldane6_link_narrow :
    ∀ (μ : Fin 2) (k : Torus 4 4), |(hLink 6 μ k).arg| < Real.pi / 4 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_narrow (by decide) (hD44_00 6) (hD44_10 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (45 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (45 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_01 6) (hD44_11 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_02 6) (hD44_12 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_03 6) (hD44_13 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_10 6) (hD44_20 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_11 6) (hD44_21 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_12 6) (hD44_22 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_13 6) (hD44_23 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_20 6) (hD44_30 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_21 6) (hD44_31 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_22 6) (hD44_32 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_23 6) (hD44_33 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_30 6) (hD44_00 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (45 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (45 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_31 6) (hD44_01 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_32 6) (hD44_02 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_33 6) (hD44_03 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_00 6) (hD44_01 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (45 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (45 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_01 6) (hD44_02 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_02 6) (hD44_03 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_03 6) (hD44_00 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (45 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (45 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_10 6) (hD44_11 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_11 6) (hD44_12 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_12 6) (hD44_13 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_13 6) (hD44_10 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_20 6) (hD44_21 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_21 6) (hD44_22 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_22 6) (hD44_23 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_23 6) (hD44_20 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_30 6) (hD44_31 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_31 6) (hD44_32 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_32 6) (hD44_33 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_33 6) (hD44_30 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])

/-! ### The topological phase `m = 1` (inside the window: `1 < 3√3`) -/

theorem haldane1_pos : ∀ k : Torus 4 4,
    0 < Real.sqrt (dNormSq (haldaneD44 1 k)) + (haldaneD44 1 k) 2 := by
  intro k
  fin_cases k
  · exact hpos_of_table (hD44_00 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_01 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_02 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_03 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_10 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_11 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_12 _) (by norm_num <;> nlinarith [sqrt10_lb])
  · exact hpos_of_table (hD44_13 _) (by norm_num <;> nlinarith [sqrt10_lb])
  · exact hpos_of_table (hD44_20 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_21 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_22 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_23 _) (by norm_num <;> nlinarith [sqrt10_lb])
  · exact hpos_of_table (hD44_30 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_31 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_32 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_33 _) (by norm_num <;> positivity)

theorem haldane1_link_ne : ∀ (μ : Fin 2) (k : Torus 4 4), hLink 1 μ k ≠ 0 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 1) (hD44_10 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 1) (hD44_11 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 1) (hD44_12 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 1) (hD44_13 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 1) (hD44_20 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 1) (hD44_21 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 1) (hD44_22 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 1) (hD44_23 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 1) (hD44_30 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 1) (hD44_31 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 1) (hD44_32 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 1) (hD44_33 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 1) (hD44_00 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 1) (hD44_01 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 1) (hD44_02 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 1) (hD44_03 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 1) (hD44_01 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 1) (hD44_02 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 1) (hD44_03 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 1) (hD44_00 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 1) (hD44_11 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 1) (hD44_12 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 1) (hD44_13 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 1) (hD44_10 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 1) (hD44_21 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 1) (hD44_22 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 1) (hD44_23 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 1) (hD44_20 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 1) (hD44_31 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 1) (hD44_32 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 1) (hD44_33 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 1) (hD44_30 1) (by norm_num)

/-- **The topological Haldane frame**: `t = t₂ = 1`, `φ = π/2`, `m = 1`. -/
noncomputable def haldaneFrameTopo : BlochLowerBandFrame 4 4 :=
  blochFrameOfD (haldaneD44 1) haldane1_pos haldane1_link_ne

/-- **The trivial-phase Haldane frame**: same hoppings, `m = 6` (outside the window). -/
noncomputable def haldaneFrameTrivial : BlochLowerBandFrame 4 4 :=
  blochFrameOfD (haldaneD44 6) haldane6_pos haldane6_link_ne

theorem rawCurl_topo (k : Torus 4 4) :
    rawCurl 4 4 (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) k
      = (hLink 1 0 k).arg + (hLink 1 1 (shift 4 4 0 k)).arg
        - (hLink 1 0 (shift 4 4 1 k)).arg - (hLink 1 1 k).arg := by
  unfold rawCurl haldaneFrameTopo
  rw [linkArg_blochFrameOfD, linkArg_blochFrameOfD, linkArg_blochFrameOfD,
    linkArg_blochFrameOfD]
  rfl

/-! #### Per-link argument brackets (32 links, four sector cells) -/

/-- `μ=0` link at `(0, 0)` → `(1, 0)`: cell A (arg ≈ 8.383°). -/
theorem argL000 : 0 ≤ (hLink 1 0 (0, 0)).arg ∧ (hLink 1 0 (0, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_00 1) (hD44_10 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(0, 1)` → `(1, 1)`: cell A (arg ≈ 10.686°). -/
theorem argL001 : 0 ≤ (hLink 1 0 (0, 1)).arg ∧ (hLink 1 0 (0, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_01 1) (hD44_11 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(0, 2)` → `(1, 2)`: cell C (arg ≈ 68.606°). -/
theorem argL002 : Real.pi / 4 ≤ (hLink 1 0 (0, 2)).arg ∧ (hLink 1 0 (0, 2)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_02 1) (hD44_12 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=0` link at `(0, 3)` → `(1, 3)`: cell A (arg ≈ 21.339°). -/
theorem argL003 : 0 ≤ (hLink 1 0 (0, 3)).arg ∧ (hLink 1 0 (0, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_03 1) (hD44_13 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(1, 0)` → `(2, 0)`: cell B (arg ≈ -5.530°). -/
theorem argL010 : -(Real.pi / 6) ≤ (hLink 1 0 (1, 0)).arg ∧ (hLink 1 0 (1, 0)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_10 1) (hD44_20 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(1, 1)` → `(2, 1)`: cell A (arg ≈ 1.555°). -/
theorem argL011 : 0 ≤ (hLink 1 0 (1, 1)).arg ∧ (hLink 1 0 (1, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_11 1) (hD44_21 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(1, 2)` → `(2, 2)`: cell C (arg ≈ 68.606°). -/
theorem argL012 : Real.pi / 4 ≤ (hLink 1 0 (1, 2)).arg ∧ (hLink 1 0 (1, 2)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_12 1) (hD44_22 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=0` link at `(1, 3)` → `(2, 3)`: cell D (arg ≈ -88.492°). -/
theorem argL013 : -(Real.pi / 2) ≤ (hLink 1 0 (1, 3)).arg ∧ (hLink 1 0 (1, 3)).arg ≤ -(Real.pi / 3) :=
  hLink_cellD (by decide) (hD44_13 1) (hD44_23 1)
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 0)` → `(3, 0)`: cell B (arg ≈ -5.530°). -/
theorem argL020 : -(Real.pi / 6) ≤ (hLink 1 0 (2, 0)).arg ∧ (hLink 1 0 (2, 0)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_20 1) (hD44_30 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 1)` → `(3, 1)`: cell B (arg ≈ -0.562°). -/
theorem argL021 : -(Real.pi / 6) ≤ (hLink 1 0 (2, 1)).arg ∧ (hLink 1 0 (2, 1)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_21 1) (hD44_31 1)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 2)` → `(3, 2)`: cell A (arg ≈ 2.349°). -/
theorem argL022 : 0 ≤ (hLink 1 0 (2, 2)).arg ∧ (hLink 1 0 (2, 2)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_22 1) (hD44_32 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 3)` → `(3, 3)`: cell A (arg ≈ 21.339°). -/
theorem argL023 : 0 ≤ (hLink 1 0 (2, 3)).arg ∧ (hLink 1 0 (2, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_23 1) (hD44_33 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 0)` → `(0, 0)`: cell A (arg ≈ 8.383°). -/
theorem argL030 : 0 ≤ (hLink 1 0 (3, 0)).arg ∧ (hLink 1 0 (3, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_30 1) (hD44_00 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 1)` → `(0, 1)`: cell A (arg ≈ 1.555°). -/
theorem argL031 : 0 ≤ (hLink 1 0 (3, 1)).arg ∧ (hLink 1 0 (3, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_31 1) (hD44_01 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 2)` → `(0, 2)`: cell A (arg ≈ 2.349°). -/
theorem argL032 : 0 ≤ (hLink 1 0 (3, 2)).arg ∧ (hLink 1 0 (3, 2)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_32 1) (hD44_02 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 3)` → `(0, 3)`: cell A (arg ≈ 10.686°). -/
theorem argL033 : 0 ≤ (hLink 1 0 (3, 3)).arg ∧ (hLink 1 0 (3, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_33 1) (hD44_03 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 0)` → `(0, 1)`: cell A (arg ≈ 8.383°). -/
theorem argL100 : 0 ≤ (hLink 1 1 (0, 0)).arg ∧ (hLink 1 1 (0, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_00 1) (hD44_01 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 1)` → `(0, 2)`: cell B (arg ≈ -5.530°). -/
theorem argL101 : -(Real.pi / 6) ≤ (hLink 1 1 (0, 1)).arg ∧ (hLink 1 1 (0, 1)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_01 1) (hD44_02 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 2)` → `(0, 3)`: cell B (arg ≈ -5.530°). -/
theorem argL102 : -(Real.pi / 6) ≤ (hLink 1 1 (0, 2)).arg ∧ (hLink 1 1 (0, 2)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_02 1) (hD44_03 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 3)` → `(0, 0)`: cell A (arg ≈ 8.383°). -/
theorem argL103 : 0 ≤ (hLink 1 1 (0, 3)).arg ∧ (hLink 1 1 (0, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_03 1) (hD44_00 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 0)` → `(1, 1)`: cell A (arg ≈ 10.686°). -/
theorem argL110 : 0 ≤ (hLink 1 1 (1, 0)).arg ∧ (hLink 1 1 (1, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_10 1) (hD44_11 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 1)` → `(1, 2)`: cell A (arg ≈ 21.339°). -/
theorem argL111 : 0 ≤ (hLink 1 1 (1, 1)).arg ∧ (hLink 1 1 (1, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_11 1) (hD44_12 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 2)` → `(1, 3)`: cell D (arg ≈ -88.492°). -/
theorem argL112 : -(Real.pi / 2) ≤ (hLink 1 1 (1, 2)).arg ∧ (hLink 1 1 (1, 2)).arg ≤ -(Real.pi / 3) :=
  hLink_cellD (by decide) (hD44_12 1) (hD44_13 1)
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 3)` → `(1, 0)`: cell A (arg ≈ 21.339°). -/
theorem argL113 : 0 ≤ (hLink 1 1 (1, 3)).arg ∧ (hLink 1 1 (1, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_13 1) (hD44_10 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(2, 0)` → `(2, 1)`: cell A (arg ≈ 2.349°). -/
theorem argL120 : 0 ≤ (hLink 1 1 (2, 0)).arg ∧ (hLink 1 1 (2, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_20 1) (hD44_21 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(2, 1)` → `(2, 2)`: cell A (arg ≈ 2.349°). -/
theorem argL121 : 0 ≤ (hLink 1 1 (2, 1)).arg ∧ (hLink 1 1 (2, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_21 1) (hD44_22 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(2, 2)` → `(2, 3)`: cell C (arg ≈ 68.606°). -/
theorem argL122 : Real.pi / 4 ≤ (hLink 1 1 (2, 2)).arg ∧ (hLink 1 1 (2, 2)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_22 1) (hD44_23 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=1` link at `(2, 3)` → `(2, 0)`: cell C (arg ≈ 68.606°). -/
theorem argL123 : Real.pi / 4 ≤ (hLink 1 1 (2, 3)).arg ∧ (hLink 1 1 (2, 3)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_23 1) (hD44_20 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=1` link at `(3, 0)` → `(3, 1)`: cell A (arg ≈ 1.555°). -/
theorem argL130 : 0 ≤ (hLink 1 1 (3, 0)).arg ∧ (hLink 1 1 (3, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_30 1) (hD44_31 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(3, 1)` → `(3, 2)`: cell B (arg ≈ -0.562°). -/
theorem argL131 : -(Real.pi / 6) ≤ (hLink 1 1 (3, 1)).arg ∧ (hLink 1 1 (3, 1)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_31 1) (hD44_32 1)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(3, 2)` → `(3, 3)`: cell A (arg ≈ 1.555°). -/
theorem argL132 : 0 ≤ (hLink 1 1 (3, 2)).arg ∧ (hLink 1 1 (3, 2)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_32 1) (hD44_33 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(3, 3)` → `(3, 0)`: cell A (arg ≈ 10.686°). -/
theorem argL133 : 0 ≤ (hLink 1 1 (3, 3)).arg ∧ (hLink 1 1 (3, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_33 1) (hD44_30 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-! #### Per-plaquette branch indices -/

theorem pb1_00 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (0 : ZMod 4)) = ((1 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (0 : ZMod 4)) = ((0 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL000.1, argL000.2, argL110.1, argL110.2, argL001.1, argL001.2,
      argL100.1, argL100.2, Real.pi_pos])
    (by linarith [argL000.1, argL000.2, argL110.1, argL110.2, argL001.1, argL001.2,
      argL100.1, argL100.2, Real.pi_pos])

theorem pb1_01 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (1 : ZMod 4)) = ((1 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (1 : ZMod 4)) = ((0 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL001.1, argL001.2, argL111.1, argL111.2, argL002.1, argL002.2,
      argL101.1, argL101.2, Real.pi_pos])
    (by linarith [argL001.1, argL001.2, argL111.1, argL111.2, argL002.1, argL002.2,
      argL101.1, argL101.2, Real.pi_pos])

theorem pb1_02 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 2) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (2 : ZMod 4)) = ((1 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (2 : ZMod 4)) = ((0 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL002.1, argL002.2, argL112.1, argL112.2, argL003.1, argL003.2,
      argL102.1, argL102.2, Real.pi_pos])
    (by linarith [argL002.1, argL002.2, argL112.1, argL112.2, argL003.1, argL003.2,
      argL102.1, argL102.2, Real.pi_pos])

theorem pb1_03 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (3 : ZMod 4)) = ((1 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (3 : ZMod 4)) = ((0 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL003.1, argL003.2, argL113.1, argL113.2, argL000.1, argL000.2,
      argL103.1, argL103.2, Real.pi_pos])
    (by linarith [argL003.1, argL003.2, argL113.1, argL113.2, argL000.1, argL000.2,
      argL103.1, argL103.2, Real.pi_pos])

theorem pb1_10 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (0 : ZMod 4)) = ((2 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (0 : ZMod 4)) = ((1 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL010.1, argL010.2, argL120.1, argL120.2, argL011.1, argL011.2,
      argL110.1, argL110.2, Real.pi_pos])
    (by linarith [argL010.1, argL010.2, argL120.1, argL120.2, argL011.1, argL011.2,
      argL110.1, argL110.2, Real.pi_pos])

theorem pb1_11 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (1 : ZMod 4)) = ((2 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (1 : ZMod 4)) = ((1 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL011.1, argL011.2, argL121.1, argL121.2, argL012.1, argL012.2,
      argL111.1, argL111.2, Real.pi_pos])
    (by linarith [argL011.1, argL011.2, argL121.1, argL121.2, argL012.1, argL012.2,
      argL111.1, argL111.2, Real.pi_pos])

theorem pb1_12 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 2) = 1 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (2 : ZMod 4)) = ((2 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (2 : ZMod 4)) = ((1 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_one_of
    (by linarith [argL012.1, argL012.2, argL122.1, argL122.2, argL013.1, argL013.2,
      argL112.1, argL112.2, Real.pi_pos])
    (by linarith [argL012.1, argL012.2, argL122.1, argL122.2, argL013.1, argL013.2,
      argL112.1, argL112.2, Real.pi_pos])

theorem pb1_13 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (3 : ZMod 4)) = ((2 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (3 : ZMod 4)) = ((1 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL013.1, argL013.2, argL123.1, argL123.2, argL010.1, argL010.2,
      argL113.1, argL113.2, Real.pi_pos])
    (by linarith [argL013.1, argL013.2, argL123.1, argL123.2, argL010.1, argL010.2,
      argL113.1, argL113.2, Real.pi_pos])

theorem pb1_20 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (0 : ZMod 4)) = ((3 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (0 : ZMod 4)) = ((2 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL020.1, argL020.2, argL130.1, argL130.2, argL021.1, argL021.2,
      argL120.1, argL120.2, Real.pi_pos])
    (by linarith [argL020.1, argL020.2, argL130.1, argL130.2, argL021.1, argL021.2,
      argL120.1, argL120.2, Real.pi_pos])

theorem pb1_21 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (1 : ZMod 4)) = ((3 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (1 : ZMod 4)) = ((2 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL021.1, argL021.2, argL131.1, argL131.2, argL022.1, argL022.2,
      argL121.1, argL121.2, Real.pi_pos])
    (by linarith [argL021.1, argL021.2, argL131.1, argL131.2, argL022.1, argL022.2,
      argL121.1, argL121.2, Real.pi_pos])

theorem pb1_22 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 2) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (2 : ZMod 4)) = ((3 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (2 : ZMod 4)) = ((2 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL022.1, argL022.2, argL132.1, argL132.2, argL023.1, argL023.2,
      argL122.1, argL122.2, Real.pi_pos])
    (by linarith [argL022.1, argL022.2, argL132.1, argL132.2, argL023.1, argL023.2,
      argL122.1, argL122.2, Real.pi_pos])

theorem pb1_23 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (3 : ZMod 4)) = ((3 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (3 : ZMod 4)) = ((2 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL023.1, argL023.2, argL133.1, argL133.2, argL020.1, argL020.2,
      argL123.1, argL123.2, Real.pi_pos])
    (by linarith [argL023.1, argL023.2, argL133.1, argL133.2, argL020.1, argL020.2,
      argL123.1, argL123.2, Real.pi_pos])

theorem pb1_30 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (0 : ZMod 4)) = ((0 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (0 : ZMod 4)) = ((3 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL030.1, argL030.2, argL100.1, argL100.2, argL031.1, argL031.2,
      argL130.1, argL130.2, Real.pi_pos])
    (by linarith [argL030.1, argL030.2, argL100.1, argL100.2, argL031.1, argL031.2,
      argL130.1, argL130.2, Real.pi_pos])

theorem pb1_31 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (1 : ZMod 4)) = ((0 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (1 : ZMod 4)) = ((3 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL031.1, argL031.2, argL101.1, argL101.2, argL032.1, argL032.2,
      argL131.1, argL131.2, Real.pi_pos])
    (by linarith [argL031.1, argL031.2, argL101.1, argL101.2, argL032.1, argL032.2,
      argL131.1, argL131.2, Real.pi_pos])

theorem pb1_32 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 2) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (2 : ZMod 4)) = ((0 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (2 : ZMod 4)) = ((3 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL032.1, argL032.2, argL102.1, argL102.2, argL033.1, argL033.2,
      argL132.1, argL132.2, Real.pi_pos])
    (by linarith [argL032.1, argL032.2, argL102.1, argL102.2, argL033.1, argL033.2,
      argL132.1, argL132.2, Real.pi_pos])

theorem pb1_33 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (3 : ZMod 4)) = ((0 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (3 : ZMod 4)) = ((3 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL033.1, argL033.2, argL103.1, argL103.2, argL030.1, argL030.2,
      argL133.1, argL133.2, Real.pi_pos])
    (by linarith [argL033.1, argL033.2, argL103.1, argL103.2, argL030.1, argL030.2,
      argL133.1, argL133.2, Real.pi_pos])

theorem plaquetteBranch_topo (k : Torus 4 4) :
    plaquetteBranch 4 4 (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) k
      = if k = ((1 : ZMod 4), (2 : ZMod 4)) then 1 else 0 := by
  fin_cases k
  · rw [if_neg (by decide)]; exact pb1_00
  · rw [if_neg (by decide)]; exact pb1_01
  · rw [if_neg (by decide)]; exact pb1_02
  · rw [if_neg (by decide)]; exact pb1_03
  · rw [if_neg (by decide)]; exact pb1_10
  · rw [if_neg (by decide)]; exact pb1_11
  · rw [if_pos (by decide)]; exact pb1_12
  · rw [if_neg (by decide)]; exact pb1_13
  · rw [if_neg (by decide)]; exact pb1_20
  · rw [if_neg (by decide)]; exact pb1_21
  · rw [if_neg (by decide)]; exact pb1_22
  · rw [if_neg (by decide)]; exact pb1_23
  · rw [if_neg (by decide)]; exact pb1_30
  · rw [if_neg (by decide)]; exact pb1_31
  · rw [if_neg (by decide)]; exact pb1_32
  · rw [if_neg (by decide)]; exact pb1_33


/-! ## Headline: the two-phase Chern classification -/

/-- A `d`-field frame whose raw nearest-neighbour overlaps are all narrow has zero Chern number. -/
theorem blochLatticeChern_eq_zero_of_narrow_D {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
    (D : Torus N₁ N₂ → (Fin 3 → ℝ))
    (hpos : ∀ k, 0 < Real.sqrt (dNormSq (D k)) + (D k) 2)
    (hov : ∀ (μ : Fin 2) (k : Torus N₁ N₂),
      frameOverlap (lbVec (D k)) (lbVec (D (shift N₁ N₂ μ k))) ≠ 0)
    (h : ∀ (μ : Fin 2) (k : Torus N₁ N₂),
      |Complex.arg (frameOverlap (lbVec (D k)) (lbVec (D (shift N₁ N₂ μ k))))| < Real.pi / 4) :
    blochLatticeChern (blochFrameOfD D hpos hov).toAdmissibleBandFrame = 0 := by
  refine blochLatticeChern_eq_zero_of_narrow _ (fun μ k => ?_)
  show |Complex.arg (frameOverlap (normalizeVec (lbVec (D k)))
      (normalizeVec (lbVec (D (shift N₁ N₂ μ k)))))| < Real.pi / 4
  rw [arg_frameOverlap_normalizeVec _ _ (selfNormSq_lbVec_pos (hpos k))
    (selfNormSq_lbVec_pos (hpos _))]
  exact h μ k

/-- **The trivial phase carries no Chern number.** At `m = 6` — outside the topological window
`|m| < 3√3 ≈ 5.196` of `haldane_mass_inversion_iff` — every one of the 32 nearest-neighbour
overlaps on the `4 × 4` Brillouin torus is narrow, so no plaquette carries a branch correction. -/
theorem haldane_trivial_phase_chern_zero :
    blochLatticeChern haldaneFrameTrivial.toAdmissibleBandFrame = 0 :=
  blochLatticeChern_eq_zero_of_narrow_D _ _ _ haldane6_link_narrow

/-- **The Haldane Chern witness.** At the declared parameters `t = t₂ = 1`, `φ = π/2`, `m = 1` —
inside the topological window — the lower-band frame on the `4 × 4` discretized Brillouin torus has
FHS lattice Chern number `−1`.

Exactly **one** of the sixteen plaquettes (the one at `k = (1, 2)`) carries a branch correction, and
it carries `+1`; `latticeChern = −∑ plaquetteBranch` (the repo's frozen orientation convention, fixed
so that `∑ plaquetteArg = 2π · latticeChern`) then gives `−1`. The overall sign is the convention's,
not the physics': replacing `φ = π/2` by `φ = −π/2` reverses the time-reversal-breaking flux and
flips it.

Together with `haldane_trivial_phase_chern_zero` this is a **classification**, not a single number:
the invariant is `−1` inside the mass-inversion window of `haldane_mass_inversion_iff` and `0`
outside it. -/
theorem haldaneFrame_latticeChern_eq_neg_one :
    blochLatticeChern haldaneFrameTopo.toAdmissibleBandFrame = -1 := by
  unfold blochLatticeChern latticeChern
  rw [Finset.sum_congr rfl (fun k _ => plaquetteBranch_topo k)]
  decide

/-- **The two phases are distinguished by the invariant.** The Haldane model at these two mass
values is not merely computed twice: the invariant separates them, which is what makes the
witness a topological statement rather than an arithmetic coincidence. -/
theorem haldane_chern_distinguishes_phases :
    blochLatticeChern haldaneFrameTopo.toAdmissibleBandFrame
      ≠ blochLatticeChern haldaneFrameTrivial.toAdmissibleBandFrame := by
  rw [haldaneFrame_latticeChern_eq_neg_one, haldane_trivial_phase_chern_zero]
  decide

end SKEFTHawking.GrapheneBand
