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

/-- **Sector C** — `arg z ∈ (π/3, π/2)`. -/
theorem arg_cell_C {z : ℂ} (hre : 0 < z.re) (h : Real.sqrt 3 * z.re < z.im) :
    Real.pi / 3 < z.arg ∧ z.arg < Real.pi / 2 := by
  have hpi := Real.pi_pos
  refine ⟨lt_arg_of_slope hre tan_pi_div_three (by linarith) (by linarith) h, ?_⟩
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

end SKEFTHawking.GrapheneBand
