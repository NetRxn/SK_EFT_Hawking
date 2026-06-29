import SKEFTHawking.NEGFGreenFunction

/-!
# Landauer–Büttiker conductance (Phase 6BA, Wave 2)

The headline mesoscopic-transport observable, built on the Wave-1 NEGF substrate
(`NEGFGreenFunction.lean`): the Caroli / Meir–Wingreen **transmission function**

    T(E) = Tr[Γ_L · G^R(E) · Γ_R · G^A(E)]

(`Γ_{L,R}` the left/right lead broadening matrices, `G^{R/A}` the retarded/advanced
device Green's functions), and the linear-response Landauer conductance

    G = (2e²/h) ∫ T(E) (−∂f/∂E) dE .

## Results

* `transmission` — the trace formula, generic in `Γ_L, Γ_R` and the retarded GF.
* `transmission_eq_gAdvanced` — ties it to the actual advanced GF `G^A = (G^R)ᴴ`.
* `transmission_isReal` — `T(E)` is real (Hermitian leads): a genuine observable.
* `transmission_nonneg` — `T(E) ≥ 0` (positive-semidefinite leads): a transmission
  *probability*, via the spectral factorization `posSemidef_exists_mul_conjTranspose`.
* `posSemidef_exists_mul_conjTranspose` — reusable: every PSD matrix is `B·Bᴴ` (spectral √).
* `transmissionReal` + `transmissionReal_ofReal` — the real transmission `Re Tr[…]` and its
  bridge to the matrix `transmission` (so the scalar `T : ℝ → ℝ` below is grounded).
* `landauerConductance` + `landauer_conductance_def` — the conductance functional.
* `fermiWindow_integral_eq_one` — `∫ (−∂f/∂E) dE = 1` (β>0), the improper-FTC normalization.
* `landauerConductance_const_transmission` (Fermi-window normalization as hypothesis) and the
  **unconditional** `landauerConductance_const_transmission'` (β>0) — the linear-response limit
  `G = (2e²/h)·T₀` for energy-independent transmission; the precursor of W3's `G = n·G₀`.

## References

- Caroli, Combescot, Nozières, Saint-James, J. Phys. C 4, 916 (1971) — NEGF transmission.
- Meir & Wingreen, PRL 68, 2512 (1992) — interacting-region current formula.
- Datta, *Electronic Transport in Mesoscopic Systems* (CUP 1995), Ch. 2–3.

Invariants (Phase 6BA): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero sorry;
no project-local axioms; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.NEGF

open Matrix
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## The transmission function -/

/-- The Caroli / Meir–Wingreen transmission `T = Tr[Γ_L · G^R · Γ_R · (G^R)ᴴ]`. Generic in
the lead broadenings `Γ_L, Γ_R` and the retarded Green's function `gR` (the advanced GF is
`(gR)ᴴ`; see `transmission_eq_gAdvanced` for the tie to `gAdvanced`). -/
noncomputable def transmission (ΓL ΓR gR : Matrix m m ℂ) : ℂ :=
  (ΓL * gR * ΓR * gRᴴ).trace

/-- `T(E) = Tr[Γ_L · G^R(E) · Γ_R · G^A(E)]` with the genuine advanced Green's function
`G^A = (G^R)ᴴ` (for Hermitian `H`). -/
theorem transmission_eq_gAdvanced (H : Matrix m m ℂ) (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (ΓL ΓR : Matrix m m ℂ) :
    (ΓL * gRetarded H E η * ΓR * gAdvanced H E η).trace = transmission ΓL ΓR (gRetarded H E η) := by
  rw [transmission, gAdvanced_eq_conjTranspose H hH E]

omit [DecidableEq m] in
/-- **`T(E)` is real** — for Hermitian lead broadenings the transmission is a genuine
real observable (`conj T = T`). -/
theorem transmission_isReal (ΓL ΓR : Matrix m m ℂ) (hL : ΓL.IsHermitian) (hR : ΓR.IsHermitian)
    (gR : Matrix m m ℂ) :
    (starRingEnd ℂ) (transmission ΓL ΓR gR) = transmission ΓL ΓR gR := by
  unfold transmission
  rw [starRingEnd_apply, ← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL.eq, hR.eq]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (gR * ΓR * gRᴴ) ΓL]
  simp only [← Matrix.mul_assoc]

/-- The **real transmission** `T(E) = Re Tr[Γ_L G^R Γ_R G^A]` — the scalar fed to
`landauerConductance` below. -/
noncomputable def transmissionReal (ΓL ΓR gR : Matrix m m ℂ) : ℝ := (transmission ΓL ΓR gR).re

omit [DecidableEq m] in
/-- **Bridge: `↑(transmissionReal) = transmission`** for Hermitian leads — the scalar real
transmission carries the full (real) matrix transmission value, grounding the `T : ℝ → ℝ`
argument of `landauerConductance` in the NEGF trace `Tr[Γ_L G^R Γ_R G^A]`. -/
theorem transmissionReal_ofReal (ΓL ΓR gR : Matrix m m ℂ) (hL : ΓL.IsHermitian)
    (hR : ΓR.IsHermitian) :
    (transmissionReal ΓL ΓR gR : ℂ) = transmission ΓL ΓR gR := by
  have him : (transmission ΓL ΓR gR).im = 0 := by
    have h := transmission_isReal ΓL ΓR hL hR gR
    rwa [Complex.conj_eq_iff_im] at h
  apply Complex.ext <;> simp [transmissionReal, him]

/-! ## Linear-response Landauer conductance -/

open MeasureTheory

/-- The Fermi–Dirac distribution `f(E) = 1/(1 + exp(β(E−μ)))` (β = 1/k_BT, μ the chemical
potential). -/
noncomputable def fermi (μ β E : ℝ) : ℝ := (1 + Real.exp (β * (E - μ)))⁻¹

/-- The Fermi window (thermal weight) `w(E) = −∂f/∂E` — the energy window, of width ~k_BT
about μ, that carries the linear-response current. -/
noncomputable def fermiWindow (μ β E : ℝ) : ℝ := -deriv (fermi μ β) E

/-- **The linear-response Landauer conductance** `G = (2e²/h) ∫ T(E)(−∂f/∂E) dE`, with `G₀`
the conductance quantum `2e²/h` and `T : ℝ → ℝ` the (real) transmission function
`T(E) = Re Tr[Γ_L G^R Γ_R G^A]` (see `transmission`/`transmission_isReal`). -/
noncomputable def landauerConductance (G₀ : ℝ) (T : ℝ → ℝ) (μ β : ℝ) : ℝ :=
  G₀ * ∫ E, T E * fermiWindow μ β E

/-- `landauer_conductance_def` — the conductance is the conductance quantum times the
Fermi-window-weighted transmission integral. -/
theorem landauer_conductance_def (G₀ : ℝ) (T : ℝ → ℝ) (μ β : ℝ) :
    landauerConductance G₀ T μ β = G₀ * ∫ E, T E * fermiWindow μ β E := rfl

/-- **Linear-response limit** — for an energy-independent transmission `T₀` (the wide-band /
low-bias regime), the conductance collapses to `G = G₀ · T₀`, because the Fermi window is a
normalized weight (`∫ (−∂f/∂E) dE = 1`). This is the precursor of the W3 conductance
quantization `G = n·G₀`. The normalization `hw` is the standard Fermi-window identity
(`fermiWindow_integral_eq_one`, the improper FTC `∫_ℝ −f' = f(−∞) − f(+∞) = 1`). -/
theorem landauerConductance_const_transmission (G₀ T₀ μ β : ℝ)
    (hw : ∫ E, fermiWindow μ β E = 1) :
    landauerConductance G₀ (fun _ => T₀) μ β = G₀ * T₀ := by
  rw [landauerConductance, integral_const_mul, hw, mul_one]

open Filter Topology in
/-- **The Fermi window integrates to one**, `∫ (−∂f/∂E) dE = 1` for `β > 0` — the standard
normalization. Improper FTC: `∫_ℝ f' = f(+∞) − f(−∞) = 0 − 1 = −1`, so `∫ (−f') = 1`. -/
theorem fermiWindow_integral_eq_one {β : ℝ} (hβ : 0 < β) (μ : ℝ) :
    ∫ E, fermiWindow μ β E = 1 := by
  set g : ℝ → ℝ := fun E => Real.exp (β * (E - μ)) with hg
  set d : ℝ → ℝ := fun E => -(g E * β) / (1 + g E) ^ 2 with hd
  have hden : ∀ E, (0 : ℝ) < 1 + g E := fun E => by positivity
  have hderiv : ∀ E, HasDerivAt (fermi μ β) (d E) E := by
    intro E
    have hlin : HasDerivAt (fun E => β * (E - μ)) β E := by
      simpa using ((hasDerivAt_id E).sub_const μ).const_mul β
    have hgd : HasDerivAt g (g E * β) E := by
      simpa [hg] using (Real.hasDerivAt_exp (β * (E - μ))).comp E hlin
    have hdend : HasDerivAt (fun E => 1 + g E) (g E * β) E := by simpa using hgd.const_add 1
    simpa [fermi, hd] using hdend.inv (ne_of_gt (hden E))
  have hwin : (fun E => fermiWindow μ β E) = fun E => -d E := by
    funext E; rw [fermiWindow, (hderiv E).deriv]
  -- limits of `fermi` at ±∞
  have hsubtop : Tendsto (fun E : ℝ => E - μ) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-μ) tendsto_id
  have hsubbot : Tendsto (fun E : ℝ => E - μ) atBot atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-μ) tendsto_id
  have hgtop : Tendsto g atTop atTop :=
    Real.tendsto_exp_atTop.comp (hsubtop.const_mul_atTop hβ)
  have hgbot : Tendsto g atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hsubbot.const_mul_atBot hβ)
  have hftop : Tendsto (fermi μ β) atTop (𝓝 0) := by
    have h1 : Tendsto (fun E => 1 + g E) atTop atTop := tendsto_atTop_add_const_left _ 1 hgtop
    simpa [fermi] using tendsto_inv_atTop_zero.comp h1
  have hfbot : Tendsto (fermi μ β) atBot (𝓝 1) := by
    have h1 : Tendsto (fun E => 1 + g E) atBot (𝓝 (1 + 0)) := tendsto_const_nhds.add hgbot
    simpa [fermi] using h1.inv₀ (by norm_num)
  -- continuity + positivity of the derivative (for measurability + the domination bound)
  have hgpos : ∀ E, (0 : ℝ) < g E := fun E => by rw [hg]; positivity
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hdcont : Continuous d := by
    simp only [hd]
    exact ((hgc.mul continuous_const).neg).div
      ((continuous_const.add hgc).pow 2) (fun E => by positivity)
  have habs : ∀ E, ‖d E‖ = g E * β / (1 + g E) ^ 2 := by
    intro E
    rw [Real.norm_eq_abs, hd, abs_div, abs_neg, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
  -- integrability of the derivative on each half-line (exp-dominated)
  have hint_iic : MeasureTheory.IntegrableOn d (Set.Iic μ) := by
    have hdom : MeasureTheory.IntegrableOn (fun E => β * g E) (Set.Iic μ) := by
      refine MeasureTheory.IntegrableOn.congr_fun
        ((integrableOn_exp_mul_Iic hβ μ).const_mul (β * Real.exp (-(β * μ))))
        (fun E _ => ?_) measurableSet_Iic
      simp only [hg]
      rw [mul_assoc, ← Real.exp_add, show -(β * μ) + β * E = β * (E - μ) from by ring]
    refine MeasureTheory.Integrable.mono' hdom hdcont.aestronglyMeasurable ?_
    filter_upwards with E
    rw [habs, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ (1 + g E) ^ 2 := by nlinarith [hgpos E]
    nlinarith [mul_pos hβ (hgpos E), h1]
  have hint_ioi : MeasureTheory.IntegrableOn d (Set.Ioi μ) := by
    have hdom : MeasureTheory.IntegrableOn (fun E => β * Real.exp (-(β * (E - μ)))) (Set.Ioi μ) := by
      refine MeasureTheory.IntegrableOn.congr_fun
        ((integrableOn_exp_mul_Ioi (show (-β : ℝ) < 0 by linarith) μ).const_mul
          (β * Real.exp (β * μ))) (fun E _ => ?_) measurableSet_Ioi
      rw [mul_assoc, ← Real.exp_add, show β * μ + -β * E = -(β * (E - μ)) from by ring]
    refine MeasureTheory.Integrable.mono' hdom hdcont.aestronglyMeasurable ?_
    filter_upwards with E
    rw [habs, show β * Real.exp (-(β * (E - μ))) = β / g E from by
      rw [hg, Real.exp_neg]; ring, div_le_div_iff₀ (by positivity) (hgpos E)]
    nlinarith [hgpos E, hβ, mul_pos hβ (hgpos E)]
  -- FTC-2 on each half-line
  have hIic : ∫ E in Set.Iic μ, d E = fermi μ β μ - 1 :=
    integral_Iic_of_hasDerivAt_of_tendsto' (fun E _ => hderiv E) hint_iic hfbot
  have hIoi : ∫ E in Set.Ioi μ, d E = 0 - fermi μ β μ :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun E _ => hderiv E) hint_ioi hftop
  have hintegrable : MeasureTheory.Integrable d := by
    rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi (a := μ)]
    exact hint_iic.union hint_ioi
  have hsplit : ∫ E, d E = (fermi μ β μ - 1) + (0 - fermi μ β μ) := by
    rw [← MeasureTheory.integral_add_compl (measurableSet_Iic) hintegrable, Set.compl_Iic, hIic,
      hIoi]
  rw [hwin, MeasureTheory.integral_neg, hsplit]
  ring

/-- **Unconditional linear-response limit** — for `β > 0` (positive temperature) a constant
transmission `T₀` gives exactly `G = G₀·T₀`. Combines `landauerConductance_const_transmission`
with the now-discharged Fermi-window normalization `fermiWindow_integral_eq_one`. -/
theorem landauerConductance_const_transmission' (G₀ T₀ μ : ℝ) {β : ℝ} (hβ : 0 < β) :
    landauerConductance G₀ (fun _ => T₀) μ β = G₀ * T₀ :=
  landauerConductance_const_transmission G₀ T₀ μ β (fermiWindow_integral_eq_one hβ μ)

/-! ## Transmission non-negativity (`T ≥ 0`) -/

/-- **Every positive-semidefinite matrix factors as `M = B·Bᴴ`** — the symmetric spectral
square root `B = U·diag(√λ)·Uᴴ` built by hand from `IsHermitian.spectral_theorem` (the matrix
`CFC.sqrt` is unavailable here without the C⋆-operator-norm instance, which diamonds with the
entrywise matrix norms). -/
theorem posSemidef_exists_mul_conjTranspose {M : Matrix m m ℂ} (hM : M.PosSemidef) :
    ∃ B : Matrix m m ℂ, M = B * Bᴴ := by
  set U : Matrix m m ℂ := ↑hM.1.eigenvectorUnitary with hU
  set lam := hM.1.eigenvalues with hlam
  have hUs1 : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self _
  have conj_mul : ∀ A C : Matrix m m ℂ,
      (U * A * star U) * (U * C * star U) = U * (A * C) * star U := by
    intro A C
    calc (U * A * star U) * (U * C * star U)
        = U * A * (star U * U) * C * star U := by simp only [Matrix.mul_assoc]
      _ = U * A * 1 * C * star U := by rw [hUs1]
      _ = U * (A * C) * star U := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hMdecomp : M = U * Matrix.diagonal (fun i => (lam i : ℂ)) * star U := by
    conv_lhs => rw [hM.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    congr 2
  have hsq : (fun i => (Real.sqrt (lam i) : ℂ) * (Real.sqrt (lam i) : ℂ))
      = (fun i => (lam i : ℂ)) := by
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]
  have hDherm : (Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ)))ᴴ
      = Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose]
  refine ⟨U * Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ)) * star U, ?_⟩
  have hBconj : (U * Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ)) * star U)ᴴ
      = U * Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ)) * star U := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hDherm, Matrix.mul_assoc]
  rw [hBconj, hMdecomp, conj_mul, Matrix.diagonal_mul_diagonal, hsq]

open scoped MatrixOrder in
/-- **`T(E) ≥ 0`** — for positive-semidefinite lead broadenings the transmission is a genuine
probability (a non-negative real). With `Γ_R = B·Bᴴ`, `T = Tr[(G^R B)ᴴ · Γ_L · (G^R B)] ≥ 0`
by positive-semidefinite congruence of `Γ_L`. -/
theorem transmission_nonneg (ΓL ΓR : Matrix m m ℂ) (hL : ΓL.PosSemidef) (hR : ΓR.PosSemidef)
    (gR : Matrix m m ℂ) : 0 ≤ transmission ΓL ΓR gR := by
  obtain ⟨B, hB⟩ := posSemidef_exists_mul_conjTranspose hR
  have hT : transmission ΓL ΓR gR = ((gR * B)ᴴ * ΓL * (gR * B)).trace := by
    unfold transmission
    rw [hB, Matrix.conjTranspose_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (ΓL * gR * B) Bᴴ gRᴴ, Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
  rw [hT]
  exact (hL.conjTranspose_mul_mul_same (gR * B)).trace_nonneg

end SKEFTHawking.NEGF
