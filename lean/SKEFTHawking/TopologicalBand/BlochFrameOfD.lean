import SKEFTHawking.TopologicalBand.BlochFHS
import SKEFTHawking.TopologicalBand.ArgSectors

/-!
# Lower-band frames from a `d`-field (Phase 6ED, Wave 3 — promoted)

The model-independent adapter turning **any** nonsingular `d`-field on a finite Brillouin torus
into a `BlochLowerBandFrame`, together with the link-argument and narrow-link machinery a concrete
Chern computation needs.

* `selfNormSq` / `normalizeVec` — raw states and their unit rescaling, with
  `arg_frameOverlap_normalizeVec`: normalization is a **positive** rescaling, hence invisible to
  every link argument. This is what lets a computation work with raw, integer-valued overlaps.
* `lbVec d = (d₁ − i d₂, −(d₃ + ‖d‖))` — the raw lower-band eigenvector, with the eigenvector law
  `blochPauli_mulVec_lbVec` proved directly from `BlochBundle`'s Pauli identity, and the overlap's
  real and imaginary parts in closed form (`lbOverlap_re`, `lbOverlap_im`).
* `blochFrameOfD` — the frame itself, under the **north-pole condition** `‖d‖ + d₃ > 0`
  (`lbVec` degenerates to `0` exactly on the negative `d₃` axis, so this is not cosmetic) plus
  explicit overlap nonvanishing.
* `blochLatticeChern_eq_zero_of_narrow` and its `d`-field form `_of_narrow_D` — the reusable
  *negative* criterion: all nearest-neighbour overlaps within `|arg| < π/4` forces `C = 0`.

**Promoted out of `GrapheneBand.HaldaneWitness` on 2026-07-29.** Every declaration here is stated
for an arbitrary `D : Torus N₁ N₂ → (Fin 3 → ℝ)`; none mentions graphene. A later square-lattice
(QWZ) spike reuses this adapter rather than rebuilding it, and does so without importing a
graphene module.
-/

namespace SKEFTHawking.TopologicalBand

open Complex Real Matrix SKEFTHawking.Topological
open scoped BigOperators

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
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

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

Unnormalized: where it is nonzero, only its ray matters, and that ray is exactly the `−‖d‖`
eigenspace. **It is not everywhere nonzero.** On the negative `d₃` axis the formula degenerates —
`lbVec ![0, 0, -1] = ![0, 0]` — which is the standard south-pole coordinate singularity of this
gauge, not a defect in the eigenvector law (`blochPauli_mulVec_lbVec` still holds there, vacuously).
Every consumer therefore carries the **north-pole condition** `0 < ‖d‖ + d₃`, which
`selfNormSq_lbVec_pos` converts into the nonvanishing the frame construction needs. -/
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
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Pi.smul_apply, smul_eq_mul, Matrix.cons_val_fin_one]
    push_cast
    ring
  · simp only [lbVec, blochPauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Pi.smul_apply, smul_eq_mul, Matrix.cons_val_fin_one]
    push_cast
    linear_combination -hsq - (d 1 : ℂ) ^ 2 * Complex.I_sq

/-- `‖v(d)‖² = 2‖d‖(‖d‖ + d₃)`. -/
theorem selfNormSq_lbVec (d : Fin 3 → ℝ) :
    selfNormSq (lbVec d)
      = 2 * Real.sqrt (dNormSq d) * (Real.sqrt (dNormSq d) + d 2) := by
  have hsq : Real.sqrt (dNormSq d) * Real.sqrt (dNormSq d) = dNormSq d :=
    Real.mul_self_sqrt (dNormSq_nonneg d)
  unfold selfNormSq lbVec dNormSq at *
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
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
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.add_re, Complex.mul_re, Complex.mul_im, map_sub, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_neg, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The imaginary part of a raw lower-band overlap — an integer whenever `d`, `d'` are. -/
theorem lbOverlap_im (d d' : Fin 3 → ℝ) :
    (frameOverlap (lbVec d) (lbVec d')).im = d 1 * d' 0 - d 0 * d' 1 := by
  unfold frameOverlap lbVec
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
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

end SKEFTHawking.TopologicalBand
