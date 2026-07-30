import SKEFTHawking.GrapheneBand.Honeycomb
import Mathlib.Analysis.Complex.Exponential

/-!
# Linear dispersion at the Dirac point, and the Dirac mass (Phase 6ED, Wave 2)

Wave 1 located the Dirac points as the exact zero set of the structure factor. This wave supplies
the property every downstream consumer actually cites — that the dispersion is **linear** near
those points — as an inequality with an *explicit* remainder constant and an *explicit* validity
ball, never as `O(|q|²)`.

## The linear form, and the AC's `(3/2)‖q‖`

Working (as Wave 1 does) in Bloch-phase coordinates, the exact first-order form at `K` is

    L(q) = i·(ω·q₁ + ω²·q₂),   ω = exp(2πi/3),   so   ‖L(q)‖ = √(q₁² − q₁q₂ + q₂²)

(`linearForm_norm`). The roadmap's AC wrote this as `(3/2)·‖q‖`, which is its value **after**
converting phase offsets to Cartesian momentum against a lattice constant `a` — the `3/2` (and the
Fermi velocity `v_F = 3ta/2ℏ` built from it) is a coordinate-and-units artifact, not part of the
model. What ships is therefore the coordinate-free quadratic form `q₁² − q₁q₂ + q₂²`, which is the
triangular lattice's reciprocal metric and is *isotropic in the physical frame*; a consumer that
fixes primitive vectors recovers `(3/2)a‖q‖` from it. This is the same strengthening Wave 1 made,
for the same reason.

## UNKNOWN-1, resolved

Route chosen: **`Complex.exp` Taylor bound**, `Complex.norm_exp_sub_one_sub_id_le`, applied once
per hopping term. It gives remainder constant `C = 1` on the ball `|q₁| ≤ 1 ∧ |q₂| ≤ 1`. The two
rejected alternatives (two-variable `Real.cos`/`sin` expansion; a direct polynomial sandwich) would
both have required rebuilding the remainder control this lemma already provides.

**Honest note on the validity ball.** The ball is an artifact of the *Mathlib lemma*, not of the
mathematics: the sharp bound `‖e^{iq} − 1 − iq‖ ≤ q²/2` holds for every real `q`, so the shipped
bound (constant `1`) is in fact true globally. The roadmap's AC asked for a witness that the bound
**fails** outside the ball; that request rests on a false premise and **cannot be satisfied**, so
it is not faked. What *is* shipped instead is the honest non-vacuity content:
`dispersion_linear_not_exact` exhibits a concrete offset at which `‖f(K+q)‖ ≠ ‖L(q)‖`, proving the
remainder term is genuinely needed rather than the inequality being a disguised equality.

**⚠ Guardrail (inherited).** Statements are about the stated tight-binding model; identification of
`t`, `a`, or a measured `v_F` with a physical sample is consumer-side.

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
  simp only []
  rw [show ((diracK.1 + q.1 : ℝ) : ℂ) * Complex.I = diracK.1 * Complex.I + q.1 * Complex.I by
        push_cast; ring,
      show ((diracK.2 + q.2 : ℝ) : ℂ) * Complex.I = diracK.2 * Complex.I + q.2 * Complex.I by
        push_cast; ring,
      Complex.exp_add, Complex.exp_add]
  linear_combination hzero

/-- The two cube-root-of-unity phases have unit modulus. -/
theorem norm_exp_diracK_phase (x : ℝ) : ‖Complex.exp ((x : ℝ) * Complex.I)‖ = 1 := by
  rw [show ((x : ℝ) : ℂ) * Complex.I = (x : ℂ) * Complex.I from rfl]
  simp

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

/-- **Linear dispersion at the Dirac point, with an explicit remainder.**

    | ‖f(K + q)‖ − √(q₁² − q₁q₂ + q₂²) |  ≤  q₁² + q₂²    for  |q₁| ≤ 1, |q₂| ≤ 1.

The remainder constant is `1` and the validity ball is stated, so this is a *usable bound* rather
than an `O(|q|²)` assertion — which is the entire point of the wave. Proof: the exact
decomposition (`structureFactor_diracK_add`), the reverse triangle inequality, and one application
of `Complex.norm_exp_sub_one_sub_id_le` per hopping term (each phase has unit modulus). -/
theorem structureFactor_linear_expansion {q : ℝ × ℝ}
    (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) :
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
  have hb : ∀ x : ℝ, |x| ≤ 1 →
      ‖Complex.exp ((x : ℝ) * Complex.I) - 1 - (x : ℝ) * Complex.I‖ ≤ x ^ 2 := by
    intro x hx
    have hnorm : ‖((x : ℝ) : ℂ) * Complex.I‖ = |x| := by
      simp
    have := Complex.norm_exp_sub_one_sub_id_le (x := ((x : ℝ) : ℂ) * Complex.I)
      (by rw [hnorm]; exact hx)
    rw [hnorm] at this
    calc ‖Complex.exp ((x : ℝ) * Complex.I) - 1 - (x : ℝ) * Complex.I‖ ≤ |x| ^ 2 := this
      _ = x ^ 2 := by rw [sq_abs]
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
        rw [norm_mul, norm_mul, norm_exp_diracK_phase, norm_exp_diracK_phase, one_mul, one_mul]
    _ ≤ q.1 ^ 2 + q.2 ^ 2 := add_le_add (hb q.1 h1) (hb q.2 h2)

/-- **The remainder term is genuinely needed: the linear form is not exact.**

At the offset carrying `K` to the *other* Dirac point `K'` — `q = (2π/3, −2π/3)` — the true
structure factor **vanishes** (it is a Dirac point, Wave 1) while the linear form does not:
`‖L(q)‖ = √(4π²/3) > 0`. So `structureFactor_linear_expansion` is a genuine inequality and not a
disguised equality, which is the non-vacuity content the AC's (unsatisfiable) "fails outside the
ball" request was reaching for. -/
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
  simp only []
  exact ne_of_lt (Real.sqrt_pos.mpr this)

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

/-- **The gap is strictly monotone in the mass** — so `m` is a genuine tuning parameter, and a
reported gap that does not track `|m|` refutes the model rather than the measurement. -/
theorem gap_vs_mass_strictMono {m m' : ℝ} (h : |m| < |m'|) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD diracK m))
      < 2 * Real.sqrt (dNormSq (gappedHoneycombD diracK m')) := by
  rw [gapped_dirac_gap_eq, gapped_dirac_gap_eq]
  linarith

/-- **The mass hypothesis is load-bearing:** at `m = 0` the gap closes, recovering Wave 1's gapless
cone. Together with `gap_vs_mass_strictMono` this makes the gapped model a one-parameter family
rather than a restatement. -/
theorem gapped_dirac_gapless_iff_massless (m : ℝ) :
    2 * Real.sqrt (dNormSq (gappedHoneycombD diracK m)) = 0 ↔ m = 0 := by
  rw [gapped_dirac_gap_eq]
  constructor
  · intro h; exact abs_eq_zero.mp (by linarith)
  · intro h; rw [h]; simp

end SKEFTHawking.GrapheneBand
