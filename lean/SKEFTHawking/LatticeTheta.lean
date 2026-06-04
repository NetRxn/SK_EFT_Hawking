/-
Phase 5q.B frontier build (route C), sub-wave C3 substrate: lattice theta groundwork.

This module begins the analytic substrate for the zero-axiom van der Blij route chosen by the user
(2026-06-03): prove `IsEvenUnimodular M → 8 ∣ latticeSig M` via the theta / Poisson-summation /
modular argument, with NO project-local axiom. See
`docs/roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md` ("Build sub-waves (frontier (C))").

The lattice theta function `Θ_L(τ) = ∑_{v ∈ ℤᵈ} exp(iπτ · vᵀGv)` (G the Gram matrix, Im τ > 0) is
well-defined because the summand decays like a Gaussian. The convergence is controlled by dominating
the general quadratic form by a multiple of `‖v‖²` (positive-definite case) and then by the
*diagonal* Gaussian `∏ᵢ exp(-c·vᵢ²)`, which factors over the coordinates. This module supplies the
factorisation engine: **summability of a coordinatewise product over `ℤᵈ` from per-coordinate
summability** — the base brick every theta-convergence argument routes through.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound`), default heartbeats, no
`native_decide`. Reusable beyond this project (genuine Mathlib-gap infrastructure: there is no
multivariate Poisson summation / lattice theta in Mathlib as of 2026-06-03).
-/

import Mathlib
import SKEFTHawking.EvenLatticeForm

namespace SKEFTHawking

open Complex Real Matrix

/-- **Coordinatewise-product summability over `ℤᵈ`.** If each coordinate factor `g i : ℤ → ℂ` is
absolutely summable, then the product `v ↦ ∏ᵢ ‖g i (v i)‖` is summable over `v : Fin d → ℤ`. Proved
by induction on `d` via the `Fin.consEquiv` splitting `ℤ × (Fin d → ℤ) ≃ (Fin (d+1) → ℤ)` and the
binary product-summability `Summable.mul_of_nonneg`. -/
theorem summable_normprod_pi {d : ℕ} (g : Fin d → ℤ → ℂ)
    (hg : ∀ i, Summable (fun n => ‖g i n‖)) :
    Summable (fun v : Fin d → ℤ => ∏ i, ‖g i (v i)‖) := by
  induction d with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ d ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
      have hf : Summable (fun n => ‖g 0 n‖) := hg 0
      have hgg : Summable (fun w : Fin d → ℤ => ∏ i, ‖g i.succ (w i)‖) :=
        ih (fun i => g i.succ) (fun i => hg i.succ)
      have hmul := hf.mul_of_nonneg hgg (fun n => norm_nonneg _)
        (fun w => Finset.prod_nonneg fun i _ => norm_nonneg _)
      refine hmul.congr ?_
      intro p
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ]

/-- **Coordinatewise-product summability (ℂ-valued form).** The product `v ↦ ∏ᵢ g i (v i)` is
(absolutely) summable over `ℤᵈ` when each coordinate factor is absolutely summable — obtained from
`summable_normprod_pi` since `‖∏ᵢ g i (v i)‖ = ∏ᵢ ‖g i (v i)‖`. This is the form the diagonal Gaussian
theta sum uses (`g i n = cexp (π * I * τ * n²)`, summable for `0 < τ.im` by `jacobiTheta₂`). -/
theorem summable_prod_pi {d : ℕ} (g : Fin d → ℤ → ℂ)
    (hg : ∀ i, Summable (fun n => ‖g i n‖)) :
    Summable (fun v : Fin d → ℤ => ∏ i, g i (v i)) := by
  apply Summable.of_norm
  refine (summable_normprod_pi g hg).congr ?_
  intro v
  rw [norm_prod]

/-! ## The diagonal lattice theta sum converges

The single-coordinate Gaussian term `n ↦ exp(iπ n² τ)` is absolutely summable for `Im τ > 0` (it is
the `z = 0` Jacobi theta term, `summable_jacobiTheta₂_term_iff`). Feeding this into `summable_prod_pi`
gives convergence of the *diagonal* `d`-dimensional theta sum `∑_{v ∈ ℤᵈ} exp(iπτ ∑ᵢ vᵢ²)`. This is
both the standard-lattice theta and the dominating series for the general (Gram-matrix) theta. -/

/-- **Single-coordinate Gaussian absolute summability** for `Im τ > 0` (the `z = 0` Jacobi theta term). -/
theorem summable_gaussian_coord (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖cexp (π * I * (n : ℂ) ^ 2 * τ)‖) := by
  have h := (summable_jacobiTheta₂_term_iff (0 : ℂ) τ).mpr hτ
  rw [← summable_norm_iff] at h
  refine h.congr (fun n => ?_)
  simp [jacobiTheta₂_term]

/-- **The diagonal lattice theta sum converges** for `Im τ > 0`:
`∑_{v ∈ ℤᵈ} exp(iπτ · ∑ᵢ vᵢ²)` is summable. The convergence engine for the lattice theta function. -/
theorem summable_diagonal_gaussian {d : ℕ} (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun v : Fin d → ℤ => cexp (π * I * τ * ∑ i, ((v i : ℂ)) ^ 2)) := by
  have key := summable_prod_pi (fun _ : Fin d => fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * τ))
    (fun _ => summable_gaussian_coord τ hτ)
  refine key.congr (fun v => ?_)
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## Positive-definite coercivity

To pass from the *diagonal* Gaussian to the general Gram-matrix theta `∑_{v ∈ ℤᵈ} exp(iπτ · vᵀGv)`,
the form `vᵀGv` must dominate `λ·‖v‖²` for some `λ > 0` (so that the general summand is dominated by a
diagonal Gaussian). This is the coercivity of a positive-definite form, proved here from first
principles: the continuous form attains a positive minimum `λ` on the compact unit "sphere"
`{x | ∑ᵢ xᵢ² = 1}`, and homogeneity (`Q(t·x) = t²·Q(x)`) propagates the bound to all `x`. Reusable;
no Mathlib equivalent as of 2026-06-03. -/

/-- **Coercivity of a positive-definite form:** there is `λ > 0` with `λ · ∑ᵢ xᵢ² ≤ xᵀGx` for all `x`.
`λ` is the minimum of the Rayleigh quotient (the smallest eigenvalue), obtained by compactness. -/
theorem posDef_coercive {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x : Fin d → ℝ, lam * (∑ i, (x i) ^ 2) ≤ x ⬝ᵥ G *ᵥ x := by
  have hQcont : Continuous (fun x : Fin d → ℝ => x ⬝ᵥ G *ᵥ x) := by fun_prop
  have hrcont : Continuous (fun x : Fin d → ℝ => ∑ i, (x i) ^ 2) := by fun_prop
  have hpos : ∀ x : Fin d → ℝ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x := by
    intro x hx; simpa using hG.dotProduct_mulVec_pos hx
  have hhom : ∀ (t : ℝ) (x : Fin d → ℝ), (t • x) ⬝ᵥ G *ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ G *ᵥ x) := by
    intro t x; rw [mulVec_smul, dotProduct_smul, smul_dotProduct]; simp only [smul_eq_mul]; ring
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; exact ⟨1, one_pos, fun x => by simp⟩
  · set S : Set (Fin d → ℝ) := {x | ∑ i, (x i) ^ 2 = 1} with hSdef
    have hScompact : IsCompact S := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_eq hrcont continuous_const
      · rw [Metric.isBounded_iff_subset_closedBall 0]
        refine ⟨1, fun x hx => ?_⟩
        simp only [hSdef, Set.mem_setOf_eq] at hx
        rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
        intro i
        have hle : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        rw [hx] at hle; rw [Real.norm_eq_abs]; nlinarith [sq_abs (x i), abs_nonneg (x i)]
    have hSne : S.Nonempty := by
      obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hd
      refine ⟨Pi.single i₀ 1, ?_⟩
      simp only [hSdef, Set.mem_setOf_eq]
      rw [Finset.sum_eq_single i₀] <;> simp +contextual
    obtain ⟨x₀, hx₀S, hx₀min⟩ := hScompact.exists_isMinOn hSne hQcont.continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h; rw [h] at hx₀S; simp only [hSdef, Set.mem_setOf_eq] at hx₀S; simp at hx₀S
    refine ⟨x₀ ⬝ᵥ G *ᵥ x₀, hpos x₀ hx₀ne, fun x => ?_⟩
    rcases eq_or_ne (∑ i, (x i) ^ 2) 0 with hx0 | hx0
    · have hxz : x = 0 := by
        have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp hx0
        funext i; have h2 := hall i (Finset.mem_univ i); simpa using h2
      rw [hxz]; simp
    · have hs : 0 < ∑ i, (x i) ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hx0)
      set s := ∑ i, (x i) ^ 2 with hsdef
      set y := (Real.sqrt s)⁻¹ • x with hydef
      have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
      have hyS : y ∈ S := by
        simp only [hSdef, Set.mem_setOf_eq, hydef, Pi.smul_apply, smul_eq_mul, mul_pow]
        rw [← Finset.mul_sum, ← hsdef, inv_pow, Real.sq_sqrt hs.le]; field_simp
      have hxy : x = Real.sqrt s • y := by
        rw [hydef, smul_smul, mul_inv_cancel₀ (ne_of_gt hsqrt), one_smul]
      have hxx : x ⬝ᵥ G *ᵥ x = s * (y ⬝ᵥ G *ᵥ y) := by
        conv_lhs => rw [hxy]
        rw [hhom (Real.sqrt s) y, Real.sq_sqrt hs.le]
      rw [hxx]
      have hmin : x₀ ⬝ᵥ G *ᵥ x₀ ≤ y ⬝ᵥ G *ᵥ y := hx₀min hyS
      nlinarith [hmin, hs]

/-! ## The general (Gram-matrix) lattice theta sum converges

Combining coercivity (`posDef_coercive`) with the diagonal Gaussian convergence engine, the general
lattice theta sum `∑_{v ∈ ℤᵈ} exp(iπτ · vᵀGv)` converges for any **positive-definite** real Gram
matrix `G` and `Im τ > 0`. The summand norm `exp(-π·Im τ·vᵀGv)` is dominated, via `vᵀGv ≥ λ·∑vᵢ²`, by
the diagonal Gaussian `∏ᵢ exp(-π·λ·Im τ·vᵢ²)`, which is summable by `summable_normprod_pi`. This is
the convergence theorem for `Θ_G` in the **definite** case (the indefinite case requires the
Siegel–Narain majorant — frontier sub-wave C5). -/

/-- **The general Gram-matrix lattice theta sum converges** for positive-definite `G` and `Im τ > 0`:
`∑_{v ∈ ℤᵈ} exp(iπτ · vᵀGv)` is summable. (Dominated by a diagonal Gaussian via `posDef_coercive`.) -/
theorem summable_gram_gaussian {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun v : Fin d → ℤ =>
      cexp (π * I * τ * ((((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))) : ℝ) : ℂ))) := by
  obtain ⟨lam, hlam, hcoe⟩ := posDef_coercive G hG
  set c : ℝ := lam * τ.im with hc
  have hcim : 0 < (I * (c : ℂ)).im := by simp [hc]; positivity
  have hdom : Summable (fun v : Fin d → ℤ =>
      ∏ i, ‖cexp (π * I * ((v i : ℤ) : ℂ) ^ 2 * (I * (c : ℂ)))‖) :=
    summable_normprod_pi (fun _ : Fin d => fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * (I * (c : ℂ))))
      (fun _ => summable_gaussian_coord (I * (c : ℂ)) hcim)
  refine Summable.of_norm_bounded hdom (fun v => ?_)
  have hnf : ‖cexp (π * I * τ * ((((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))) : ℝ) : ℂ))‖
      = Real.exp (-(π * τ.im * ((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))))) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have hprod : (∏ i, ‖cexp (π * I * ((v i : ℤ) : ℂ) ^ 2 * (I * (c : ℂ)))‖)
      = Real.exp (∑ i, -(π * c * (v i : ℝ) ^ 2)) := by
    rw [Real.exp_sum]; apply Finset.prod_congr rfl; intro i _
    have harg : (π : ℂ) * I * ((v i : ℤ) : ℂ) ^ 2 * (I * (c : ℂ))
        = (((-(π * c * (v i : ℝ) ^ 2)) : ℝ) : ℂ) := by
      rw [show (π : ℂ) * I * ((v i : ℤ) : ℂ) ^ 2 * (I * (c : ℂ))
            = ((π : ℂ) * ((v i : ℤ) : ℂ) ^ 2 * (c : ℂ)) * (I * I) by ring, Complex.I_mul_I]
      push_cast; ring
    rw [Complex.norm_exp, harg, Complex.ofReal_re]
  rw [hnf, hprod, Real.exp_le_exp]
  have hco := hcoe (fun i => (v i : ℝ))
  have hsum : (∑ i, -(π * c * (v i : ℝ) ^ 2)) = -(π * c * ∑ i, (v i : ℝ) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hsum, hc]
  have hpt : (0 : ℝ) ≤ π * τ.im := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hco hpt]

/-! ## The lattice theta function and its T-transformation (period 1)

The lattice theta function `Θ_G(τ) := ∑_{v ∈ ℤᵈ} exp(iπτ · vᵀGv)`. For an **even** lattice (the
quadratic form `vᵀGv` is always an even integer), the theta function is invariant under `τ ↦ τ + 1`
— the first (easy) half of its modularity, the T-transformation. This is a purely *termwise* identity
(`exp(iπ·1·vᵀGv) = exp(2πi·m) = 1`), needing neither positive-definiteness nor summability. The
even-integer condition is supplied (with no dangling hypothesis) by `even_lattice_heven`, which routes
through `EvenLattice.redBilin_self_eq_zero` (the mod-2 reduction of an even symmetric form vanishes on
the diagonal). The S-transformation (the hard half, via Poisson summation — sub-wave C2) is next. -/

/-- The **lattice theta function** `Θ_G(τ) = ∑_{v ∈ ℤᵈ} exp(iπτ · vᵀGv)`. -/
noncomputable def latticeTheta {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (τ : ℂ) : ℂ :=
  ∑' v : Fin d → ℤ,
    cexp (π * I * τ * ((((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))) : ℝ) : ℂ))

/-- **T-transformation (period 1)** for an even lattice: `Θ_G(τ + 1) = Θ_G(τ)` whenever every value
`vᵀGv` of the quadratic form is an even integer. Purely termwise (no summability needed). -/
theorem latticeTheta_T {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (heven : ∀ v : Fin d → ℤ,
      ∃ m : ℤ, ((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))) = 2 * (m : ℝ))
    (τ : ℂ) : latticeTheta G (τ + 1) = latticeTheta G τ := by
  unfold latticeTheta
  apply tsum_congr
  intro v
  obtain ⟨m, hm⟩ := heven v
  rw [hm,
    show (π : ℂ) * I * (τ + 1) * (((2 * (m : ℝ)) : ℝ) : ℂ)
        = π * I * τ * (((2 * (m : ℝ)) : ℝ) : ℂ) + (m : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The even-lattice condition holds for any even symmetric integer matrix.** For `A` symmetric with
even diagonal, every value `vᵀAv` of the (real-cast) quadratic form is an even integer. Routes through
`EvenLattice.redBilin_self_eq_zero`. This discharges the hypothesis of `latticeTheta_T`. -/
theorem even_lattice_heven {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hsymm : A.transpose = A) (heven : ∀ i, 2 ∣ A i i) (v : Fin d → ℤ) :
    ∃ m : ℤ, ((fun i => (v i : ℝ)) ⬝ᵥ (A.map (Int.cast)) *ᵥ (fun i => (v i : ℝ))) = 2 * (m : ℝ) := by
  have hint : 2 ∣ ∑ i, ∑ j, v i * A i j * v j := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp ?_
    push_cast
    rw [← EvenLattice.redBilin_self_eq_zero hsymm heven (fun i => (v i : ZMod 2))]
    unfold EvenLattice.redBilin
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  obtain ⟨m, hm⟩ := hint
  refine ⟨m, ?_⟩
  have hL : (fun i => (v i : ℝ)) ⬝ᵥ (A.map (Int.cast)) *ᵥ (fun i => (v i : ℝ))
      = ∑ i, ∑ j, (v i : ℝ) * ((A i j : ℝ) * (v j : ℝ)) := by
    rw [dotProduct]; apply Finset.sum_congr rfl; intro i _
    rw [mulVec, dotProduct, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    rw [Matrix.map_apply]
  rw [hL]
  have hcast : ((∑ i, ∑ j, v i * A i j * v j : ℤ) : ℝ)
      = ∑ i, ∑ j, (v i : ℝ) * ((A i j : ℝ) * (v j : ℝ)) := by
    push_cast; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [← hcast, hm]; push_cast; ring

/-- **T-transformation for an even symmetric integer lattice:** `Θ_A(τ + 1) = Θ_A(τ)` (fully grounded,
no hypothesis beyond even + symmetric). -/
theorem latticeTheta_T_int {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hsymm : A.transpose = A) (heven : ∀ i, 2 ∣ A i i) (τ : ℂ) :
    latticeTheta (A.map (Int.cast)) (τ + 1) = latticeTheta (A.map (Int.cast)) τ :=
  latticeTheta_T (A.map (Int.cast)) (fun v => even_lattice_heven A hsymm heven v) τ

/-- **The lattice theta is the convergent sum of its terms** (positive-definite case): for `G` PD and
`Im τ > 0`, the defining series `HasSum`s to `latticeTheta G τ`. The analytic handle for all further
manipulation (S-transformation, value at `i∞`, etc.). -/
theorem hasSum_latticeTheta {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun v : Fin d → ℤ =>
        cexp (π * I * τ * ((((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))) : ℝ) : ℂ)))
      (latticeTheta G τ) :=
  (summable_gram_gaussian G hG τ hτ).hasSum

/-- **The theta has constant term 1** (the cusp normalization): for `G` PD and `Im τ > 0`,
`Θ_G(τ) = 1 + ∑_{v ≠ 0} exp(iπτ·vᵀGv)`. The `v = 0` term is `exp(0) = 1`; the remaining sum is the
"positive-frequency" part vanishing as `Im τ → ∞`. This is the `q`-expansion constant term that makes
`Θ_G` a *nonzero* modular form (the input the C4 weight-mod-8 argument needs). -/
theorem latticeTheta_eq_one_add {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    latticeTheta G τ = 1 + ∑' v : Fin d → ℤ,
      (if v = 0 then 0 else
        cexp (π * I * τ * ((((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))) : ℝ) : ℂ))) := by
  rw [latticeTheta, (summable_gram_gaussian G hG τ hτ).tsum_eq_add_tsum_ite 0]
  congr 1
  simp

/-! ## T²-invariance for any integral lattice

For an *integral* lattice (every value `vᵀGv` is an integer — e.g. any integer Gram matrix, even or
odd), the theta is invariant under `τ ↦ τ + 2`: `Θ_G(τ + 2) = Θ_G(τ)`. (For *even* lattices this
sharpens to period 1, `latticeTheta_T`.) This is the T²-modularity that holds on the theta group
`Γ_θ`, covering odd unimodular lattices (e.g. the standard `ℤᵈ`) where period 1 fails. Purely termwise. -/

/-- **T²-invariance (period 2)** for an integral lattice: `Θ_G(τ + 2) = Θ_G(τ)` whenever every value
`vᵀGv` of the quadratic form is an integer. -/
theorem latticeTheta_period_two {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (hint : ∀ v : Fin d → ℤ,
      ∃ m : ℤ, ((fun i => (v i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (v i : ℝ))) = (m : ℝ))
    (τ : ℂ) : latticeTheta G (τ + 2) = latticeTheta G τ := by
  unfold latticeTheta
  apply tsum_congr
  intro v
  obtain ⟨m, hm⟩ := hint v
  rw [hm,
    show (π : ℂ) * I * (τ + 2) * ((m : ℝ) : ℂ)
        = π * I * τ * ((m : ℝ) : ℂ) + (m : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The integral-valued condition holds for any integer Gram matrix.** Every value `vᵀAv` of the
(real-cast) form of an integer matrix `A` is an integer — discharges the hypothesis of
`latticeTheta_period_two` for integer lattices (no evenness needed). -/
theorem int_lattice_intValued {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (v : Fin d → ℤ) :
    ∃ m : ℤ, ((fun i => (v i : ℝ)) ⬝ᵥ (A.map (Int.cast)) *ᵥ (fun i => (v i : ℝ))) = (m : ℝ) := by
  refine ⟨∑ i, ∑ j, v i * A i j * v j, ?_⟩
  rw [dotProduct]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.map_apply]; ring

/-- **T²-invariance for an integer Gram matrix**, fully grounded. -/
theorem latticeTheta_period_two_int {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (τ : ℂ) :
    latticeTheta (A.map (Int.cast)) (τ + 2) = latticeTheta (A.map (Int.cast)) τ :=
  latticeTheta_period_two (A.map (Int.cast)) (fun v => int_lattice_intValued A v) τ

/-! ## Congruence invariance: the theta is a lattice-class invariant

The lattice theta depends only on the **isometry class** of the form: congruent Gram matrices
`G` and `PᵀGP` (for `P ∈ GL_d(ℤ)`, i.e. an integer matrix with unit determinant) give the same
theta. This is the reindexing `v ↦ P·v` of the summation lattice `ℤᵈ` (a bijection since `P` is
unimodular), with the quadratic-form identity `vᵀ(PᵀGP)v = (Pv)ᵀG(Pv)`. Purely a reindex of the sum
(`Equiv.tsum_eq`) — needs neither positive-definiteness nor summability. Class-invariance is exactly
what lets the modular argument work with the form up to integral change of basis. -/

/-- The reindexing bijection `v ↦ P · v` of `ℤᵈ` induced by a unimodular integer matrix `P`. -/
noncomputable def reindexEquiv {d : ℕ} (P : Matrix (Fin d) (Fin d) ℤ) (hP : IsUnit P.det) :
    (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun v := P *ᵥ v
  invFun v := P⁻¹ *ᵥ v
  left_inv v := by
    show P⁻¹ *ᵥ (P *ᵥ v) = v
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul P hP, one_mulVec]
  right_inv v := by
    show P *ᵥ (P⁻¹ *ᵥ v) = v
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv P hP, one_mulVec]

/-- **Congruence invariance:** `Θ_{PᵀGP}(τ) = Θ_G(τ)` for any unimodular integer `P`. The theta is an
invariant of the lattice's integral isometry class. -/
theorem latticeTheta_congr {d : ℕ} (P : Matrix (Fin d) (Fin d) ℤ) (hP : IsUnit P.det)
    (G : Matrix (Fin d) (Fin d) ℝ) (τ : ℂ) :
    latticeTheta ((P.map (Int.cast))ᵀ * G * (P.map (Int.cast))) τ = latticeTheta G τ := by
  unfold latticeTheta
  rw [← (reindexEquiv P hP).tsum_eq
    (fun w : Fin d → ℤ => cexp (π * I * τ *
      ((((fun i => (w i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (w i : ℝ))) : ℝ) : ℂ)))]
  apply tsum_congr; intro v
  have hcast : (P.map (Int.cast)) *ᵥ (fun i => (v i : ℝ))
      = (fun i => (((reindexEquiv P hP) v) i : ℝ)) := by
    funext i
    show (P.map (Int.cast) *ᵥ fun i => (v i : ℝ)) i = ((P *ᵥ v) i : ℝ)
    rw [mulVec, dotProduct, mulVec, dotProduct]; push_cast
    apply Finset.sum_congr rfl; intro j _; rw [Matrix.map_apply]
  have hQ : (fun i => (v i : ℝ)) ⬝ᵥ ((P.map (Int.cast))ᵀ * G * (P.map (Int.cast))) *ᵥ
        (fun i => (v i : ℝ))
      = (fun i => (((reindexEquiv P hP) v) i : ℝ)) ⬝ᵥ G *ᵥ
        (fun i => (((reindexEquiv P hP) v) i : ℝ)) := by
    rw [mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hcast]
  rw [hQ]

/-! ## Fubini index split (scaffolding for multivariate Poisson summation, C2)

The summation lattice `ℤᵈ⁺¹` splits as `ℤ × ℤᵈ` via `Fin.consEquiv`, so a summable family over
`ℤᵈ⁺¹` resums as an iterated sum over the first coordinate and the rest. This is the structural
skeleton of the coordinate-by-coordinate Poisson-summation argument (C2): each iteration peels off one
coordinate to apply the 1-dimensional Poisson formula. Pure resummation (`Equiv.tsum_eq` +
`Summable.tsum_prod`). -/

/-- **Fubini split over `ℤᵈ⁺¹`**: `∑_{v ∈ ℤᵈ⁺¹} f v = ∑_{n ∈ ℤ} ∑_{w ∈ ℤᵈ} f(cons n w)` for summable
`f`. The index recursion underlying iterated multivariate Poisson summation. -/
theorem tsum_fin_succ {d : ℕ} (f : (Fin (d + 1) → ℤ) → ℂ) (hf : Summable f) :
    ∑' v : Fin (d + 1) → ℤ, f v = ∑' (n : ℤ), ∑' (w : Fin d → ℤ), f (Fin.cons n w) := by
  have hf' : Summable (f ∘ (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ))) :=
    (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff.mpr hf
  calc ∑' v : Fin (d + 1) → ℤ, f v
      = ∑' p : ℤ × (Fin d → ℤ), (f ∘ (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ))) p :=
        ((Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).tsum_eq f).symm
    _ = ∑' (n : ℤ) (w : Fin d → ℤ), (f ∘ (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ))) (n, w) :=
        hf'.tsum_prod
    _ = ∑' (n : ℤ) (w : Fin d → ℤ), f (Fin.cons n w) := by
        apply tsum_congr; intro n; apply tsum_congr; intro w
        simp only [Function.comp_apply]; congr 1

/-- **Product–tsum factorization over `ℤᵈ`**: for a coordinatewise-separable summand, the sum over the
lattice factors as a product of one-dimensional sums, `∑_{v ∈ ℤᵈ} ∏ᵢ gᵢ(vᵢ) = ∏ᵢ ∑_{n ∈ ℤ} gᵢ(n)`.
This is the multivariate Fubini that makes a *diagonal* lattice theta factor as a product of
one-variable Jacobi thetas — the separable special case of multivariate Poisson, and the bridge from
Mathlib's 1-dimensional `jacobiTheta` to the multidimensional theta. Proved by induction via the
Fubini split (`tsum_fin_succ`) and `tsum_mul_left`/`tsum_mul_right`. -/
theorem tsum_pi_eq_prod_tsum {d : ℕ} (g : Fin d → ℤ → ℂ)
    (hg : ∀ i, Summable (fun n => ‖g i n‖)) :
    ∑' v : Fin d → ℤ, ∏ i, g i (v i) = ∏ i, ∑' n : ℤ, g i n := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [tsum_fin_succ _ (summable_prod_pi g hg)]
      have hstep : ∀ n : ℤ, (∑' w : Fin d → ℤ, ∏ i, g i ((Fin.cons n w : Fin (d + 1) → ℤ) i))
          = g 0 n * ∏ i : Fin d, ∑' m : ℤ, g i.succ m := by
        intro n
        have hfun : (fun w : Fin d → ℤ => ∏ i, g i ((Fin.cons n w : Fin (d + 1) → ℤ) i))
            = (fun w : Fin d → ℤ => g 0 n * ∏ i : Fin d, g i.succ (w i)) := by
          funext w; simp [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [hfun, tsum_mul_left, ih (fun i => g i.succ) (fun i => hg i.succ)]
      rw [tsum_congr hstep, tsum_mul_right, Fin.prod_univ_succ]

/-! ## The standard lattice theta is `jacobiTheta ^ d`

For the identity Gram matrix `1` (the standard lattice `ℤᵈ` with `vᵀv = ∑vᵢ²`), the lattice theta
factors — via `tsum_pi_eq_prod_tsum` — as the `d`-th power of Mathlib's one-variable Jacobi theta:
`Θ_1(τ) = (jacobiTheta τ)ᵈ`. This connects the multidimensional theta to Mathlib's `jacobiTheta`
machinery, whose modular S-transformation (`jacobiTheta_S_smul`) then gives the S-transformation of the
*separable/diagonal* lattice theta. (The standard lattice is odd unimodular; the even-unimodular case
needs the genuinely non-separable multivariate Poisson, the remaining C2 work.) -/

/-- **The standard (identity-form) lattice theta equals `(jacobiTheta τ)ᵈ`** for `Im τ > 0`. -/
theorem latticeTheta_one_eq_jacobiTheta_pow {d : ℕ} (τ : ℂ) (hτ : 0 < τ.im) :
    latticeTheta (1 : Matrix (Fin d) (Fin d) ℝ) τ = (jacobiTheta τ) ^ d := by
  unfold latticeTheta
  have hsummand : ∀ v : Fin d → ℤ,
      cexp (π * I * τ * ((((fun i => (v i : ℝ)) ⬝ᵥ (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ
          (fun i => (v i : ℝ))) : ℝ) : ℂ))
      = ∏ i, cexp (π * I * τ * (((v i : ℝ) ^ 2 : ℝ) : ℂ)) := by
    intro v
    rw [Matrix.one_mulVec, dotProduct]; push_cast
    rw [← Complex.exp_sum]; congr 1
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [tsum_congr hsummand,
      tsum_pi_eq_prod_tsum (fun _ => fun n => cexp (π * I * τ * (((n : ℝ) ^ 2 : ℝ) : ℂ)))
        (fun _ => ?_)]
  · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [jacobiTheta]
    apply tsum_congr; intro n
    have harg : (π * I * τ * (((n : ℝ) ^ 2 : ℝ) : ℂ)) = (π * I * (n : ℂ) ^ 2 * τ) := by
      push_cast; ring
    rw [harg]
  · refine (summable_gaussian_coord τ hτ).congr (fun n => ?_)
    have harg : (π * I * (n : ℂ) ^ 2 * τ) = (π * I * τ * (((n : ℝ) ^ 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [harg]

/-- **S-transformation of the standard lattice theta** (the diagonal/separable case): under the
modular `S : τ ↦ -1/τ`, `Θ_1(S•τ) = ((-iτ)^{1/2})ᵈ · Θ_1(τ)`. Obtained by raising Mathlib's
one-variable Jacobi-theta S-transformation (`jacobiTheta_S_smul`) to the `d`-th power through
`latticeTheta_one_eq_jacobiTheta_pow`. This is the modular S-transform for the standard (odd
unimodular) lattice; the multiplier `((-iτ)^{1/2})ᵈ = (-iτ)^{d/2}` is the weight-`d/2` automorphy
factor. (The even-unimodular case requires the genuinely non-separable multivariate Poisson, C2.) -/
theorem latticeTheta_one_S_smul {d : ℕ} (τ : UpperHalfPlane) :
    latticeTheta (1 : Matrix (Fin d) (Fin d) ℝ) ↑(ModularGroup.S • τ)
      = ((-I * ↑τ) ^ (1/2 : ℂ)) ^ d * latticeTheta (1 : Matrix (Fin d) (Fin d) ℝ) ↑τ := by
  rw [latticeTheta_one_eq_jacobiTheta_pow _ (ModularGroup.S • τ).im_pos,
      latticeTheta_one_eq_jacobiTheta_pow _ τ.im_pos,
      jacobiTheta_S_smul, mul_pow]

/-- **Diagonal lattice theta as a product of scaled Jacobi thetas**: for a diagonal Gram matrix
`diagonal a` (the orthogonal direct sum of rank-one forms `aᵢ`), the theta factors as
`Θ_{diag a}(τ) = ∏ᵢ jacobiTheta(τ·aᵢ)`, valid where each scaled argument lies in the upper half plane
(`0 < (τ·aᵢ).im`). Generalises `latticeTheta_one_eq_jacobiTheta_pow` (the `aᵢ = 1` case) and exhibits
the multiplicativity of the theta over an orthogonal sum of one-dimensional lattices. -/
theorem latticeTheta_diagonal {d : ℕ} (a : Fin d → ℝ) (τ : ℂ) (ha : ∀ i, 0 < (τ * (a i : ℂ)).im) :
    latticeTheta (Matrix.diagonal a) τ = ∏ i, jacobiTheta (τ * (a i : ℂ)) := by
  unfold latticeTheta
  have hsummand : ∀ v : Fin d → ℤ,
      cexp (π * I * τ * ((((fun i => (v i : ℝ)) ⬝ᵥ (Matrix.diagonal a) *ᵥ
          (fun i => (v i : ℝ))) : ℝ) : ℂ))
      = ∏ i, cexp (π * I * (((v i : ℝ) ^ 2 : ℝ) : ℂ) * (τ * (a i : ℂ))) := by
    intro v
    have hquad : (fun i => (v i : ℝ)) ⬝ᵥ (Matrix.diagonal a) *ᵥ (fun i => (v i : ℝ))
        = ∑ i, a i * (v i : ℝ) ^ 2 := by
      rw [dotProduct]; apply Finset.sum_congr rfl; intro i _; rw [Matrix.mulVec_diagonal]; ring
    rw [hquad]; push_cast; rw [← Complex.exp_sum, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [tsum_congr hsummand,
      tsum_pi_eq_prod_tsum (fun i => fun n => cexp (π * I * (((n : ℝ) ^ 2 : ℝ) : ℂ) * (τ * (a i : ℂ))))
        (fun i => ?_)]
  · apply Finset.prod_congr rfl; intro i _
    rw [jacobiTheta]; apply tsum_congr; intro n
    have harg : (π * I * (((n : ℝ) ^ 2 : ℝ) : ℂ) * (τ * (a i : ℂ)))
        = (π * I * (n : ℂ) ^ 2 * (τ * (a i : ℂ))) := by push_cast; ring
    rw [harg]
  · refine (summable_gaussian_coord (τ * (a i : ℂ)) (ha i)).congr (fun n => ?_)
    have harg : (π * I * (n : ℂ) ^ 2 * (τ * (a i : ℂ)))
        = (π * I * (((n : ℝ) ^ 2 : ℝ) : ℂ) * (τ * (a i : ℂ))) := by push_cast; ring
    rw [harg]

/-! ## The Gaussian-with-linear-term slice is `jacobiTheta₂` (C2 partial-Poisson building block)

When the multivariate lattice sum is peeled one coordinate at a time (via `tsum_fin_succ`), each inner
sum over a single coordinate `n` of the Gaussian `exp(iπτ·vᵀGv)` is a **one-dimensional Gaussian with
a linear term** `∑_n exp(iπτ·n² + 2πi·z·n)` — where the elliptic variable `z` carries the cross-terms
coupling that coordinate to the others. This is exactly Mathlib's two-variable `jacobiTheta₂ z τ`,
whose functional equation (`jacobiTheta₂_functional_equation`) supplies the partial-Poisson transform
in that coordinate. This lemma records the identification, the reusable building block for the
non-separable multivariate Poisson summation (C2). -/

/-- **The Gaussian-with-linear-term sum is `jacobiTheta₂`**:
`jacobiTheta₂ z τ = ∑_{n ∈ ℤ} exp(iπτ·n² + 2πi·z·n)`. The one-dimensional coordinate slice of the
lattice Gaussian (with `z` the cross-term), whose `jacobiTheta₂_functional_equation` is the
partial-Poisson step for iterated multivariate Poisson summation. -/
theorem jacobiTheta₂_eq_tsum_gaussian (z τ : ℂ) :
    jacobiTheta₂ z τ = ∑' n : ℤ, cexp (π * I * τ * (n : ℂ) ^ 2 + 2 * π * I * z * n) := by
  rw [jacobiTheta₂]
  apply tsum_congr; intro n
  rw [jacobiTheta₂_term]
  congr 1
  ring

end SKEFTHawking
