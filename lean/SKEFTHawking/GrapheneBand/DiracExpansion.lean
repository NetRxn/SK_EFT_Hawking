import SKEFTHawking.GrapheneBand.Honeycomb
import Mathlib.Analysis.Complex.Exponential

/-!
# Linear dispersion at the Dirac point, and the Dirac mass (Phase 6ED, Wave 2)

Wave 1 located the Dirac points as the exact zero set of the structure factor. This wave supplies
the property every downstream consumer actually cites — that the dispersion is **linear** near
those points — as an inequality with an *explicit* remainder constant, never as `O(|q|²)`.

## The linear form, and the AC's `(3/2)‖q‖`

Working (as Wave 1 does) in Bloch-phase coordinates, the exact first-order form at `K` is

    L(q) = i·(ω·q₁ + ω²·q₂),   ω = exp(2πi/3),   so   ‖L(q)‖ = √(q₁² − q₁q₂ + q₂²)

(`linearForm_norm`). The roadmap's AC wrote this as `(3/2)·‖q‖`. That is its value **after** the
phase offsets are read against a physical lattice — and this file now performs that conversion
rather than describing it:

* `quadForm_of_chart` — for an `IsHoneycombChart` pair `(a₁, a₂)` (Wave 1) and `qᵢ = ⟨p, aᵢ⟩`,
  `q₁² − q₁q₂ + q₂² = (3/4)‖a₁‖²‖p‖²`. **This is what "isotropic in the physical frame" means, and
  it is now a theorem.** The claim is *chart-specific*: for a 120° pair the same expression sweeps
  a factor of 3 across directions, so the isotropy is not a property of `q ↦ q₁² − q₁q₂ + q₂²`.
* `dispersion_slope_of_neighbours` — for a bond geometry of nearest-neighbour distance `a_CC`,
  `‖L‖ = (3/2)·a_CC·‖p‖`.

**Units warning (the `√3`).** The `3/2` multiplies the **nearest-neighbour distance** `a_CC`, not
the lattice constant. Since `‖a₁‖ = √3·a_CC` (`chart_len_sq_of_neighbours`), the same slope is
`(√3/2)·a_lattice`. Writing "`(3/2)a` for a lattice constant `a`" is wrong by a factor `√3`.

`fermiVelocity t a_CC ℏ = 3·t·a_CC/(2ℏ)` is shipped **parametrized** — it bakes in no coordinate
choice and no unit contract — and is made load-bearing by
`dispersion_slope_eq_hbar_fermiVelocity` (`E = ℏ·v_F·‖p‖`). Note the `t = 1` normalization of
`structureFactor`: the hopping-carrying family is Wave 1's `structureFactorT`/`honeycombDT`.

## UNKNOWN-1, resolved — and the validity ball, removed

Route chosen: a **`Complex.exp` Taylor bound**, applied once per hopping term, remainder constant
`C = 1`. The two rejected alternatives (two-variable `Real.cos`/`sin` expansion; a direct
polynomial sandwich) would both have rebuilt remainder control that already exists.

The first version of this wave took that bound from Mathlib's
`Complex.norm_exp_sub_one_sub_id_le`, inheriting its `‖z‖ ≤ 1` hypothesis as a validity ball, while
arguing *in prose* that the ball was an artifact of the lemma rather than of the mathematics — and
using that argument to decline an AC item. Having it both ways was the defect. The argument is now
**discharged**: `norm_exp_mul_I_sub_one_sub_id_le` proves `‖e^{ix} − 1 − ix‖ ≤ x²` for every real
`x` (mean-value inequality on `F(t) = e^{it} − 1 − it`, whose derivative has norm
`2|sin(t/2)| ≤ |t|`), so `structureFactor_linear_expansion_global` carries **no ball at all**. The
ball-shaped corollary that discarded its own hypotheses was deleted on 2026-07-29: it had no
consumers anywhere in the repo, and the global form is strictly stronger.

Consequently the AC's "witness that the bound fails outside the ball" is genuinely unsatisfiable —
there is no outside. The non-vacuity content that replaces it is stated at cone scale:
`dispersion_linear_not_exact_in_ball` exhibits `q = (1,1)`, with
`‖f(K+q)‖ = 2sin(1/2) ≠ 1 = ‖L(q)‖`. (`dispersion_linear_not_exact`, at `|qᵢ| ≈ 2.09`, is kept as
the companion witness for the global form; on its own it said nothing about the ball.)

`dispersion_linear_enclosure` supplies the AC's second Wave-2 item, the two-sided rational
enclosure `7/10 − ‖q‖ ≤ E(K+q)/‖q‖ ≤ 63/50 + ‖q‖` — the statement that actually asserts linearity
with bounded slope, rather than bounding a difference.

**⚠ Guardrail (inherited).** Statements are about the stated tight-binding model; identification of
`t`, `a_CC`, or a measured `v_F` with a physical sample is consumer-side.

**Publication target:** bundle **D11**.
-/

namespace SKEFTHawking.GrapheneBand

open Complex Real SKEFTHawking.Topological

/-! ## The linear form at `K` -/

/-- The exact first-order form of `f` at the `K` point, `L(q) = i·(ω·q₁ + ω²·q₂)` with
`ω = exp(2πi/3)`, written through Wave 1's `diracK` phases so the two files cannot drift apart. -/
noncomputable def linearForm (q : ℝ × ℝ) : ℂ :=
  Complex.I * (Complex.exp (diracK.1 * Complex.I) * q.1
             + Complex.exp (diracK.2 * Complex.I) * q.2)

/-- **The structure factor's exact decomposition at `K`.**

    f(K + q) = ω·(e^{iq₁} − 1) + ω²·(e^{iq₂} − 1)

The constant terms cancel because `1 + ω + ω² = 0` — which is exactly Wave 1's
`honeycomb_gapless_at_diracK`, consumed here rather than re-derived. Everything below is a
statement about this decomposition. -/
theorem structureFactor_diracK_add (q : ℝ × ℝ) :
    structureFactor (diracK.1 + q.1, diracK.2 + q.2)
      = Complex.exp (diracK.1 * Complex.I) * (Complex.exp (q.1 * Complex.I) - 1)
        + Complex.exp (diracK.2 * Complex.I) * (Complex.exp (q.2 * Complex.I) - 1) := by
  have hzero : structureFactor diracK = 0 := honeycomb_gapless_at_diracK
  unfold structureFactor at hzero ⊢
  rw [show ((diracK.1 + q.1 : ℝ) : ℂ) * Complex.I = diracK.1 * Complex.I + q.1 * Complex.I by
        push_cast; ring,
      show ((diracK.2 + q.2 : ℝ) : ℂ) * Complex.I = diracK.2 * Complex.I + q.2 * Complex.I by
        push_cast; ring,
      Complex.exp_add, Complex.exp_add]
  linear_combination hzero

/-! ## The global Taylor bound

Mathlib's `Complex.norm_exp_sub_one_sub_id_le` carries the hypothesis `‖z‖ ≤ 1`. On the imaginary
axis that hypothesis is an artifact of the lemma's proof, not of the mathematics, so we discharge
it once and for all here: the bound `‖e^{ix} − 1 − ix‖ ≤ x²` holds for **every** real `x`.

Route: the mean-value inequality applied to `F(t) = e^{it} − 1 − it`, whose derivative
`i(e^{it} − 1)` has norm `2|sin(t/2)| ≤ |t| ≤ |x|` on the segment from `0` to `x`. -/

/-- `‖e^{it} − 1‖ ≤ |t|` for real `t` — the chord of the unit circle is at most its arc.
Computed from `‖e^{it} − 1‖² = 2 − 2cos t = 4 sin²(t/2)`. -/
theorem norm_exp_mul_I_sub_one_le (t : ℝ) :
    ‖Complex.exp ((t : ℝ) * Complex.I) - 1‖ ≤ |t| := by
  have hsq : ‖Complex.exp ((t : ℝ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.exp_mul_I, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hhalf : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h := Real.cos_two_mul' (t / 2)
    have hp := Real.sin_sq_add_cos_sq (t / 2)
    rw [show (2 * (t / 2) : ℝ) = t by ring] at h
    linarith
  have hs : |Real.sin (t / 2)| ≤ |t / 2| := Real.abs_sin_le_abs
  have hs2 : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
    nlinarith [hs, abs_nonneg (Real.sin (t / 2)), abs_nonneg (t / 2),
      sq_abs (Real.sin (t / 2)), sq_abs (t / 2)]
  nlinarith [norm_nonneg (Complex.exp ((t : ℝ) * Complex.I) - 1), abs_nonneg t, sq_abs t]

/-- **The Taylor bound, globally.** `‖e^{ix} − 1 − ix‖ ≤ x²` for every real `x` — no validity ball.

The file previously argued in prose that the `‖z‖ ≤ 1` ball inherited from Mathlib's
`Complex.norm_exp_sub_one_sub_id_le` was an artifact of that lemma rather than of the mathematics,
and used that argument to decline an AC item. This theorem is that argument, discharged. -/
theorem norm_exp_mul_I_sub_one_sub_id_le (x : ℝ) :
    ‖Complex.exp ((x : ℝ) * Complex.I) - 1 - (x : ℝ) * Complex.I‖ ≤ x ^ 2 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Complex.exp ((s : ℝ) * Complex.I) - 1 - (s : ℝ) * Complex.I)
        (Complex.exp ((t : ℝ) * Complex.I) * Complex.I - Complex.I) t := by
    intro t
    have hre : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) * Complex.I) Complex.I t := by
      simpa using hre.mul_const Complex.I
    exact (hlin.cexp.sub_const 1).sub hlin
  have hbound : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      ‖Complex.exp ((t : ℝ) * Complex.I) * Complex.I - Complex.I‖ ≤ |x| := by
    intro t ht
    have hfac : Complex.exp ((t : ℝ) * Complex.I) * Complex.I - Complex.I
        = (Complex.exp ((t : ℝ) * Complex.I) - 1) * Complex.I := by ring
    have htx : |t| ≤ |x| := by
      rcases Set.mem_uIcc.mp ht with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · rw [abs_of_nonneg hl]; exact le_trans hr (le_abs_self x)
      · rw [abs_of_nonpos hr]; exact le_trans (neg_le_neg hl) (neg_le_abs x)
    rw [hfac, norm_mul, Complex.norm_I, mul_one]
    exact le_trans (norm_exp_mul_I_sub_one_le t) htx
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => Complex.exp ((s : ℝ) * Complex.I) - 1 - (s : ℝ) * Complex.I)
    (f' := fun t : ℝ => Complex.exp ((t : ℝ) * Complex.I) * Complex.I - Complex.I)
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound (convex_uIcc 0 x)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero] at hmvt
  calc ‖Complex.exp ((x : ℝ) * Complex.I) - 1 - (x : ℝ) * Complex.I‖
      ≤ |x| * ‖x‖ := hmvt
    _ = x ^ 2 := by rw [Real.norm_eq_abs, ← sq_abs]; ring

/-- **The linear form's modulus is the triangular-lattice quadratic form:**
`‖L(q)‖ = √(q₁² − q₁q₂ + q₂²)`. This is the `(3/2)‖q‖` of the AC, in coordinate-free form. -/
theorem linearForm_norm (q : ℝ × ℝ) :
    ‖linearForm q‖ = Real.sqrt (q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2) := by
  have hK1 : Real.cos diracK.1 = -(1/2) ∧ Real.sin diracK.1 = Real.sqrt 3 / 2 := by
    constructor
    · show Real.cos (2 * π / 3) = -(1/2)
      rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    · show Real.sin (2 * π / 3) = Real.sqrt 3 / 2
      rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hK2 : Real.cos diracK.2 = -(1/2) ∧ Real.sin diracK.2 = -(Real.sqrt 3 / 2) := by
    constructor
    · show Real.cos (4 * π / 3) = -(1/2)
      rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]
    · show Real.sin (4 * π / 3) = -(Real.sqrt 3 / 2)
      rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  unfold linearForm
  simp only [Complex.exp_mul_I, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  rw [hK1.1, hK1.2, hK2.1, hK2.2]
  nlinarith [hs3]

/-! ## The linear-dispersion theorem -/

/-- **Linear dispersion at the Dirac point, with an explicit remainder — globally.**

    | ‖f(K + q)‖ − √(q₁² − q₁q₂ + q₂²) |  ≤  q₁² + q₂²    for every `q ∈ ℝ²`.

No validity ball. The ball that the first shipped version carried came from Mathlib's
`Complex.norm_exp_sub_one_sub_id_le`, whose `‖z‖ ≤ 1` hypothesis is an artifact of its proof; the
file argued exactly that in prose while still shipping the gated statement, and used the argument
to decline an AC item. `norm_exp_mul_I_sub_one_sub_id_le` discharges the argument, and this is the
result.

Proof: the exact decomposition (`structureFactor_diracK_add`), the reverse triangle inequality, and
one application of the global Taylor bound per hopping term (each phase has unit modulus). -/
theorem structureFactor_linear_expansion_global {q : ℝ × ℝ} :
    |‖structureFactor (diracK.1 + q.1, diracK.2 + q.2)‖ - ‖linearForm q‖|
      ≤ q.1 ^ 2 + q.2 ^ 2 := by
  have hdiff : structureFactor (diracK.1 + q.1, diracK.2 + q.2) - linearForm q
      = Complex.exp (diracK.1 * Complex.I) *
          (Complex.exp (q.1 * Complex.I) - 1 - q.1 * Complex.I)
        + Complex.exp (diracK.2 * Complex.I) *
          (Complex.exp (q.2 * Complex.I) - 1 - q.2 * Complex.I) := by
    rw [structureFactor_diracK_add]
    unfold linearForm
    ring
  have hb : ∀ x : ℝ, ‖Complex.exp ((x : ℝ) * Complex.I) - 1 - (x : ℝ) * Complex.I‖ ≤ x ^ 2 :=
    norm_exp_mul_I_sub_one_sub_id_le
  calc |‖structureFactor (diracK.1 + q.1, diracK.2 + q.2)‖ - ‖linearForm q‖|
      ≤ ‖structureFactor (diracK.1 + q.1, diracK.2 + q.2) - linearForm q‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖Complex.exp (diracK.1 * Complex.I) *
            (Complex.exp (q.1 * Complex.I) - 1 - q.1 * Complex.I)
          + Complex.exp (diracK.2 * Complex.I) *
            (Complex.exp (q.2 * Complex.I) - 1 - q.2 * Complex.I)‖ := by rw [hdiff]
    _ ≤ ‖Complex.exp (diracK.1 * Complex.I) *
            (Complex.exp (q.1 * Complex.I) - 1 - q.1 * Complex.I)‖
          + ‖Complex.exp (diracK.2 * Complex.I) *
            (Complex.exp (q.2 * Complex.I) - 1 - q.2 * Complex.I)‖ := norm_add_le _ _
    _ = ‖Complex.exp (q.1 * Complex.I) - 1 - q.1 * Complex.I‖
          + ‖Complex.exp (q.2 * Complex.I) - 1 - q.2 * Complex.I‖ := by
        rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
          one_mul, one_mul]
    _ ≤ q.1 ^ 2 + q.2 ^ 2 := add_le_add (hb q.1) (hb q.2)

/-- **The remainder term is genuinely needed, at cone scale.**

At `q = (1, 1)` the two sides of `structureFactor_linear_expansion_global` differ:

    f(K + (1,1)) = (ω + ω²)(e^{i} − 1) = −(e^{i} − 1),   so ‖f‖ = 2 sin(1/2) ≈ 0.959,

while `‖L(1,1)‖ = √(1 − 1 + 1) = 1`. So the expansion is a genuine inequality, not a disguised
equality.

Kept alongside `dispersion_linear_not_exact` because the two witness strictness at physically
**different scales**: this one at `|qᵢ| = 1`, inside the cone region where the expansion is
actually used, and that one at the `K → K'` offset `|qᵢ| = 2π/3 ≈ 2.09`, where the true structure
factor vanishes outright. Neither subsumes the other. *(Until 2026-07-29 the distinction was
stated as "one for the ball form, one for the global form"; the ball-shaped forwarder has since
been deleted, so the honest distinction is the scale.)* -/
theorem dispersion_linear_not_exact_in_ball :
    ‖structureFactor (diracK.1 + (1 : ℝ), diracK.2 + (1 : ℝ))‖ ≠ ‖linearForm ((1 : ℝ), (1 : ℝ))‖ := by
  have hsum : Complex.exp ((diracK.1 : ℝ) * Complex.I)
      + Complex.exp ((diracK.2 : ℝ) * Complex.I) = -1 := by
    have h0 := honeycomb_gapless_at_diracK
    unfold structureFactor at h0
    linear_combination h0
  have hfac : structureFactor (diracK.1 + (1 : ℝ), diracK.2 + (1 : ℝ))
      = -(Complex.exp (((1 : ℝ)) * Complex.I) - 1) := by
    rw [structureFactor_diracK_add ((1 : ℝ), (1 : ℝ))]
    linear_combination (Complex.exp (((1 : ℝ)) * Complex.I) - 1) * hsum
  have hL : ‖linearForm ((1 : ℝ), (1 : ℝ))‖ = 1 := by
    rw [linearForm_norm]; norm_num
  rw [hfac, hL, norm_neg]
  -- `‖e^{i} − 1‖² = 2 − 2 cos 1 = 4 sin²(1/2) < 1`
  have hnsq : ‖Complex.exp (((1 : ℝ)) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.exp_mul_I, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    nlinarith [Real.sin_sq_add_cos_sq (1 : ℝ)]
  have hhalf : Real.cos 1 = 1 - 2 * Real.sin (1/2) ^ 2 := by
    have h := Real.cos_two_mul' (1/2 : ℝ)
    have hp := Real.sin_sq_add_cos_sq (1/2 : ℝ)
    rw [show (2 * (1/2 : ℝ)) = 1 by norm_num] at h
    linarith
  have hs : Real.sin (1/2 : ℝ) < 1/2 := Real.sin_lt (by norm_num)
  have hspos : 0 < Real.sin (1/2 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by nlinarith [Real.pi_gt_three])
  intro hEq
  rw [hEq] at hnsq
  nlinarith [hnsq, hhalf, hs, hspos]

/-- **The remainder term is genuinely needed — the global witness.**

At the offset carrying `K` to the *other* Dirac point `K'` — `q = (2π/3, −2π/3)` — the true
structure factor **vanishes** (it is a Dirac point, Wave 1) while the linear form does not:
`‖L(q)‖ = √(4π²/3) > 0`.

This offset sits at `|qᵢ| = 2π/3 ≈ 2.09`, well beyond cone scale; the companion witness
`dispersion_linear_not_exact_in_ball` de-trivializes the same global theorem at `|qᵢ| = 1`, inside
the region where the expansion is actually used. -/
theorem dispersion_linear_not_exact :
    ‖structureFactor (diracK.1 + 2 * π / 3, diracK.2 + (-(2 * π / 3)))‖
      ≠ ‖linearForm (2 * π / 3, -(2 * π / 3))‖ := by
  have hK' : (diracK.1 + 2 * π / 3, diracK.2 + (-(2 * π / 3))) = diracK' := by
    unfold diracK diracK'
    simp only [Prod.mk.injEq]
    constructor <;> ring
  rw [hK', honeycomb_gapless_at_diracK', norm_zero, linearForm_norm]
  have hpi : 0 < π := Real.pi_pos
  have : 0 < (2 * π / 3) ^ 2 - (2 * π / 3) * -(2 * π / 3) + (-(2 * π / 3)) ^ 2 := by nlinarith
  exact ne_of_lt (Real.sqrt_pos.mpr this)

/-! ## The physical frame: isotropy, `(3/2)·a_CC`, and the Fermi velocity

The coordinate-free quadratic form `q₁² − q₁q₂ + q₂²` is *not* isotropic as a function of `q`; it
is isotropic once `q` is read as the phase offsets of a physical momentum against an
`IsHoneycombChart` pair. That is a theorem, not a remark, and this section proves it — which is
also what supplies the missing units in the AC's `(3/2)‖q‖`. -/

/-- **The chart makes the triangular form isotropic.** For an `IsHoneycombChart` pair `(a₁, a₂)`
and any plane momentum `p`, with `qᵢ = ⟨p, aᵢ⟩`,

    q₁² − q₁q₂ + q₂²  =  (3/4)·‖a₁‖²·‖p‖²

— depending on `p` only through `‖p‖`. Proof: the chart conditions force `a₂` to be `a₁` rotated by
`±60°`, i.e. `S·a₂ = (S/2)·a₁ ± c·a₁^⊥` with `c² = (3/4)S²` (from Lagrange's identity); substituting
collapses the cross terms. -/
private lemma quad_key (S c A B D : ℝ) (hc2 : c ^ 2 = 3/4 * S ^ 2)
    (e1 : S * D = S/2 * A + c * B) :
    S ^ 2 * (A ^ 2 - A * D + D ^ 2) = 3/4 * S ^ 2 * (A ^ 2 + B ^ 2) := by
  linear_combination (c * B + S * D - S/2 * A) * e1 + B ^ 2 * hc2

theorem quadForm_of_chart {a₁ a₂ : ℝ × ℝ} (h : IsHoneycombChart a₁ a₂) (p : ℝ × ℝ) :
    (planeDot p a₁) ^ 2 - (planeDot p a₁) * (planeDot p a₂) + (planeDot p a₂) ^ 2
      = 3/4 * planeDot a₁ a₁ * planeDot p p := by
  obtain ⟨hne, hlen, hang⟩ := h
  have hS : 0 < planeDot a₁ a₁ := planeDot_self_pos hne
  simp only [planeDot] at hlen hang hS ⊢
  -- Lagrange's identity plus the two chart conditions pin the cross product `c`.
  have hc2 : (a₁.1 * a₂.2 - a₂.1 * a₁.2) ^ 2 = 3/4 * (a₁.1 * a₁.1 + a₁.2 * a₁.2) ^ 2 := by
    linear_combination (a₁.1 * a₁.1 + a₁.2 * a₁.2) * hlen
      - (1/2) * ((a₁.1 * a₁.1 + a₁.2 * a₁.2)/2 + (a₁.1 * a₂.1 + a₁.2 * a₂.2)) * hang
  -- `a₂` resolved along `a₁` and its perpendicular
  have e1 : (a₁.1 * a₁.1 + a₁.2 * a₁.2) * (p.1 * a₂.1 + p.2 * a₂.2)
      = (a₁.1 * a₁.1 + a₁.2 * a₁.2)/2 * (p.1 * a₁.1 + p.2 * a₁.2)
        + (a₁.1 * a₂.2 - a₂.1 * a₁.2) * (p.2 * a₁.1 - p.1 * a₁.2) := by
    linear_combination ((p.1 * a₁.1 + p.2 * a₁.2)/2) * hang
  have hkey := quad_key (a₁.1 * a₁.1 + a₁.2 * a₁.2) (a₁.1 * a₂.2 - a₂.1 * a₁.2)
    (p.1 * a₁.1 + p.2 * a₁.2) (p.2 * a₁.1 - p.1 * a₁.2) (p.1 * a₂.1 + p.2 * a₂.2) hc2 e1
  refine mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hS)) ?_
  rw [hkey]
  ring

/-- **`‖L(q)‖ = (√3/2)·‖a₁‖·‖p‖` in the physical frame** — the linear form's modulus is isotropic,
proportional to `‖p‖` alone. This is the theorem behind the phrase "isotropic in the physical
frame". -/
theorem linearForm_norm_of_chart {a₁ a₂ : ℝ × ℝ} (h : IsHoneycombChart a₁ a₂) (p : ℝ × ℝ) :
    ‖linearForm (planeDot p a₁, planeDot p a₂)‖
      = Real.sqrt 3 / 2 * Real.sqrt (planeDot a₁ a₁) * Real.sqrt (planeDot p p) := by
  have h34 : Real.sqrt (3/4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [show (3/4 : ℝ) = 3 * (1/2) ^ 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
    ring
  rw [linearForm_norm]
  rw [quadForm_of_chart h p,
    show (3/4 * planeDot a₁ a₁ * planeDot p p : ℝ)
      = 3 / 4 * (planeDot a₁ a₁ * planeDot p p) by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_mul (planeDot_self_nonneg a₁), h34]
  ring

/-- **The AC's `(3/2)·a_CC·‖p‖`, with the units it was missing.**

For the chart derived from a physical honeycomb bond geometry of nearest-neighbour distance
`a_CC = ‖δ‖`, the first-order band energy at hopping `t = 1` is exactly `(3/2)·a_CC·‖p‖`.

The `3/2` multiplies the **nearest-neighbour distance**, not the lattice constant: since
`‖a₁‖ = √3·a_CC` (`chart_len_sq_of_neighbours`), the same slope reads `(√3/2)·a_lattice`. Prose
that writes "`(3/2)a` for a lattice constant `a`" is wrong by a factor `√3`. -/
theorem dispersion_slope_of_neighbours {δ : Fin 3 → ℝ × ℝ} (h : IsHoneycombNeighbours δ)
    (p : ℝ × ℝ) :
    ‖linearForm (planeDot p (δ 0 - δ 2), planeDot p (δ 1 - δ 2))‖
      = 3/2 * Real.sqrt (planeDot (δ 0) (δ 0)) * Real.sqrt (planeDot p p) := by
  rw [linearForm_norm_of_chart (isHoneycombChart_of_neighbours h) p, chart_len_sq_of_neighbours h,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination
    (Real.sqrt (planeDot (δ 0) (δ 0)) * Real.sqrt (planeDot p p) / 2) * hs3

/-- **The Fermi velocity of the tight-binding model**, `v_F = 3·t·a_CC / (2ℏ)`.

Parametrized in the hopping `t`, the nearest-neighbour distance `a_CC` and `ℏ`, so it bakes in no
coordinate choice and no unit contract — the caller supplies all three. Its content is
`dispersion_slope_eq_hbar_fermiVelocity`; on its own this is only a name for a quotient. -/
noncomputable def fermiVelocity (t a_CC hbar : ℝ) : ℝ := 3 * t * a_CC / (2 * hbar)

/-- **`E = ℏ·v_F·‖p‖` for the tight-binding model.**

The first-order band energy at hopping `t` in the physical frame equals `ℏ·v_F·‖p‖` with
`v_F = 3·t·a_CC/(2ℏ)`. This is what makes `fermiVelocity` load-bearing rather than a definition:
the geometric content is `dispersion_slope_of_neighbours` (the `3/2` and the `a_CC`), and `ℏ`
merely cancels. -/
theorem dispersion_slope_eq_hbar_fermiVelocity {δ : Fin 3 → ℝ × ℝ} (h : IsHoneycombNeighbours δ)
    (p : ℝ × ℝ) (t hbar : ℝ) (hbar_ne : hbar ≠ 0) :
    t * ‖linearForm (planeDot p (δ 0 - δ 2), planeDot p (δ 1 - δ 2))‖
      = hbar * fermiVelocity t (Real.sqrt (planeDot (δ 0) (δ 0))) hbar
          * Real.sqrt (planeDot p p) := by
  rw [dispersion_slope_of_neighbours h p, fermiVelocity]
  field_simp

/-! ## The two-sided slope enclosure -/

/-- **The dispersion is linear with a bounded, rationally-enclosed slope.**

    7/10 − ‖q‖  ≤  E(K + q) / ‖q‖  ≤  63/50 + ‖q‖        (`q ≠ 0`, `‖q‖ = √(q₁² + q₂²)`)

where `E(K + q) = ‖f(K + q)‖` is the upper band energy. This is the AC's
`dispersion_linear_enclosure` — the statement that actually *says* the dispersion is linear, as
opposed to bounding a difference: it pins the slope `E/‖q‖` into a rational band that closes onto
`[√½, √3⁄2] ≈ [0.707, 1.225]` as `q → 0`.

Two ingredients: the anisotropy of the triangular quadratic form is bounded,
`½‖q‖² ≤ q₁² − q₁q₂ + q₂² ≤ 3⁄2‖q‖²` (the extremes are the `q₁ = ±q₂` directions), and the
remainder is controlled by `structureFactor_linear_expansion_global`. The rational endpoints
`7/10 < √½` and `63/50 > √3⁄2` keep the statement `norm_num`-checkable.

The lower bound is informative exactly when `‖q‖ < 7/10`; beyond that it degrades to the trivial
`E ≥ 0`, which is honest — the expansion has no content at large `q`. -/
theorem dispersion_linear_enclosure {q : ℝ × ℝ} (hq : q ≠ (0, 0)) :
    7/10 - Real.sqrt (q.1 ^ 2 + q.2 ^ 2)
        ≤ ‖structureFactor (diracK.1 + q.1, diracK.2 + q.2)‖ / Real.sqrt (q.1 ^ 2 + q.2 ^ 2) ∧
      ‖structureFactor (diracK.1 + q.1, diracK.2 + q.2)‖ / Real.sqrt (q.1 ^ 2 + q.2 ^ 2)
        ≤ 63/50 + Real.sqrt (q.1 ^ 2 + q.2 ^ 2) := by
  have hP : 0 < q.1 ^ 2 + q.2 ^ 2 := by
    by_contra hc
    rw [not_lt] at hc
    have hs1 : q.1 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg q.2]) (sq_nonneg q.1)
    have hs2 : q.2 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg q.1]) (sq_nonneg q.2)
    exact hq (Prod.ext (pow_eq_zero_iff (by norm_num) |>.mp hs1)
      (pow_eq_zero_iff (by norm_num) |>.mp hs2))
  set nq := Real.sqrt (q.1 ^ 2 + q.2 ^ 2) with hnq_def
  have hnq : 0 < nq := Real.sqrt_pos.mpr hP
  have hnq2 : nq ^ 2 = q.1 ^ 2 + q.2 ^ 2 := Real.sq_sqrt hP.le
  have hQnn : (0 : ℝ) ≤ q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2 := by nlinarith [sq_nonneg (q.1 - q.2)]
  -- the anisotropy band of the triangular quadratic form
  have hQlow : (7/10 * nq) ^ 2 ≤ q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2 := by
    nlinarith [hnq2, sq_nonneg (q.1 - q.2), sq_nonneg q.1, sq_nonneg q.2]
  have hQup : q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2 ≤ (63/50 * nq) ^ 2 := by
    nlinarith [hnq2, sq_nonneg (q.1 + q.2), sq_nonneg q.1, sq_nonneg q.2]
  have hlow : 7/10 * nq ≤ ‖linearForm q‖ := by
    rw [linearForm_norm]
    calc 7/10 * nq = Real.sqrt ((7/10 * nq) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hQlow
  have hup : ‖linearForm q‖ ≤ 63/50 * nq := by
    rw [linearForm_norm]
    calc Real.sqrt (q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2) ≤ Real.sqrt ((63/50 * nq) ^ 2) :=
          Real.sqrt_le_sqrt hQup
      _ = 63/50 * nq := Real.sqrt_sq (by positivity)
  have hexp := abs_le.mp (structureFactor_linear_expansion_global (q := q))
  rw [← hnq2] at hexp
  constructor
  · rw [le_div_iff₀ hnq]
    nlinarith [hexp.1, hlow]
  · rw [div_le_iff₀ hnq]
    nlinarith [hexp.2, hup]

/-! ## The gapped Dirac model -/

/-- **The gapped honeycomb `d`-vector**: Wave 1's chiral `d` with a sublattice-staggering mass `m`
in the third slot. `m ≠ 0` breaks the sublattice symmetry and opens a gap at the Dirac points. -/
noncomputable def gappedHoneycombD (θ : ℝ × ℝ) (m : ℝ) : Fin 3 → ℝ :=
  ![(structureFactor θ).re, -(structureFactor θ).im, m]

/-- `‖d‖² = |f|² + m²` for the gapped model. -/
theorem dNormSq_gappedHoneycombD (θ : ℝ × ℝ) (m : ℝ) :
    dNormSq (gappedHoneycombD θ m) = Complex.normSq (structureFactor θ) + m ^ 2 := by
  unfold dNormSq gappedHoneycombD Complex.normSq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  ring

/-- **The gap at the Dirac point is exactly `2|m|`.** Not an approximation: at `K` the structure
factor vanishes (Wave 1), so `‖d‖ = |m|` and the band separation `2‖d‖` is `2|m|` on the nose. -/
theorem gapped_dirac_gap_eq (m : ℝ) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD diracK m)) = 2 * |m| := by
  rw [dNormSq_gappedHoneycombD, honeycomb_gapless_at_diracK]
  simp [Real.sqrt_sq_eq_abs]

/-- **The gapped honeycomb Bloch Hamiltonian** as a `blochPauli` instance, so the gapped model gets
the same 2×2 spectral core the massless one does rather than only a `‖d‖` formula. -/
noncomputable def gappedHoneycombBloch (θ : ℝ × ℝ) (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  blochPauli (gappedHoneycombD θ m)

/-- **The gapped bands are `±√(|f(θ)|² + m²)`** as eigenvalues — the gapped analogue of
`honeycomb_band_secular`, again by citing `blochPauli_band_secular`. This is what makes the gap
statements below statements about a *spectrum* rather than about a norm. -/
theorem gappedHoneycomb_band_secular (θ : ℝ × ℝ) (m : ℝ) :
    (gappedHoneycombBloch θ m
        - ((Real.sqrt (Complex.normSq (structureFactor θ) + m ^ 2) : ℝ) : ℂ) • 1).det = 0 ∧
      (gappedHoneycombBloch θ m
        - ((-Real.sqrt (Complex.normSq (structureFactor θ) + m ^ 2) : ℝ) : ℂ) • 1).det = 0 := by
  have h := blochPauli_band_secular (gappedHoneycombD θ m)
  rw [dNormSq_gappedHoneycombD] at h
  exact h

/-- **The gap is strictly monotone in the mass, at every phase** — not only at the Dirac point,
where the claim would reduce to `2|m| < 2|m'|`. Here the comparison is between two square roots of
`|f(θ)|² + m²`, so the statement has content at every `θ`: `m` is a genuine tuning parameter of the
whole band structure, and a reported gap that does not track `|m|` refutes the model. -/
theorem gapped_gap_strictMono_in_mass (θ : ℝ × ℝ) {m m' : ℝ} (h : |m| < |m'|) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD θ m))
      < 2 * Real.sqrt (dNormSq (gappedHoneycombD θ m')) := by
  rw [dNormSq_gappedHoneycombD, dNormSq_gappedHoneycombD]
  have hm : m ^ 2 < m' ^ 2 := by
    nlinarith [abs_nonneg m, abs_nonneg m', sq_abs m, sq_abs m']
  have hlt : Complex.normSq (structureFactor θ) + m ^ 2
      < Complex.normSq (structureFactor θ) + m' ^ 2 := by linarith
  have := Real.sqrt_lt_sqrt (add_nonneg (Complex.normSq_nonneg _) (sq_nonneg m)) hlt
  linarith

/-- **The gap closes exactly at a massless Dirac phase**: `gap(θ, m) = 0 ↔ f θ = 0 ∧ m = 0`. Both
conjuncts are needed, which is the substantive form — at the Dirac point it specializes to
`gapped_dirac_gapless_iff_massless`, but away from it the `f θ = 0` conjunct is the binding one. -/
theorem gapped_gapless_iff (θ : ℝ × ℝ) (m : ℝ) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD θ m)) = 0 ↔ structureFactor θ = 0 ∧ m = 0 := by
  rw [dNormSq_gappedHoneycombD]
  constructor
  · intro h
    have hs : Real.sqrt (Complex.normSq (structureFactor θ) + m ^ 2) = 0 := by linarith
    have h0 : Complex.normSq (structureFactor θ) + m ^ 2 = 0 :=
      (Real.sqrt_eq_zero (add_nonneg (Complex.normSq_nonneg _) (sq_nonneg m))).mp hs
    have hf : Complex.normSq (structureFactor θ) = 0 := by
      nlinarith [Complex.normSq_nonneg (structureFactor θ), sq_nonneg m]
    have hm : m = 0 := by nlinarith [Complex.normSq_nonneg (structureFactor θ), sq_nonneg m]
    exact ⟨Complex.normSq_eq_zero.mp hf, hm⟩
  · rintro ⟨hf, hm⟩
    rw [hf, hm]
    simp

/-- **The Dirac points minimize the gap.** For every phase `θ`, the gapped band separation is at
least its value `2|m|` at `K` — so `gapped_dirac_gap_eq` reports the *minimum* gap of the model,
which is the quantity a spectroscopy experiment measures, not merely its value at one point. -/
theorem gapped_gap_ge_dirac (θ : ℝ × ℝ) (m : ℝ) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD diracK m))
      ≤ 2 * Real.sqrt (dNormSq (gappedHoneycombD θ m)) := by
  rw [dNormSq_gappedHoneycombD, dNormSq_gappedHoneycombD, honeycomb_gapless_at_diracK]
  have := Real.sqrt_le_sqrt
    (show Complex.normSq (0 : ℂ) + m ^ 2 ≤ Complex.normSq (structureFactor θ) + m ^ 2 by
      simp only [map_zero]
      nlinarith [Complex.normSq_nonneg (structureFactor θ)])
  linarith

/-- **…and they are the only minimizers.** Equality with the `K`-point gap holds exactly on the
Dirac set. Together with `gapped_gap_ge_dirac` this makes the pair a genuine characterization of
the band minimum rather than a single evaluation. -/
theorem gapped_gap_eq_dirac_iff (θ : ℝ × ℝ) (m : ℝ) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD θ m))
        = 2 * Real.sqrt (dNormSq (gappedHoneycombD diracK m)) ↔ structureFactor θ = 0 := by
  rw [dNormSq_gappedHoneycombD, dNormSq_gappedHoneycombD, honeycomb_gapless_at_diracK]
  simp only [map_zero, zero_add]
  constructor
  · intro h
    have hsq : Real.sqrt (Complex.normSq (structureFactor θ) + m ^ 2) = Real.sqrt (m ^ 2) := by
      linarith
    have := congrArg (fun x : ℝ => x ^ 2) hsq
    simp only [Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg (structureFactor θ)) (sq_nonneg m)),
      Real.sq_sqrt (sq_nonneg m)] at this
    exact Complex.normSq_eq_zero.mp (by linarith)
  · intro h; rw [h]; simp

/-- **The mass hypothesis is load-bearing:** at `m = 0` the gap closes at `K`, recovering Wave 1's
gapless cone. The specialization of `gapped_gapless_iff` to `θ = K`, where the `f θ = 0` conjunct
is discharged by `honeycomb_gapless_at_diracK`. -/
theorem gapped_dirac_gapless_iff_massless (m : ℝ) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD diracK m)) = 0 ↔ m = 0 := by
  rw [gapped_dirac_gap_eq]
  constructor
  · intro h; exact abs_eq_zero.mp (by linarith)
  · intro h; rw [h]; simp

end SKEFTHawking.GrapheneBand
