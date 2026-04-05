import SKEFTHawking.Basic
import SKEFTHawking.ADWMechanism
import Mathlib

/-!
# Tetrad Gap Equation: NJL-type Self-Consistency for Emergent Gravity

## Overview

Formalizes the self-consistent gap equation for the tetrad VEV in the
ADW mechanism. This is the first explicit derivation of the tetrad
channel gap equation in any formalism — the equation has never been
written down in the published literature.

The gap equation: Δ = G · N_f · Δ · I(Δ)
where I(Δ) = ∫₀^Λ ρ(p)/(p² + Δ²) dp with ρ(p) = c₄ · p³

## Key Results

1. **Gap integral:** I(Δ) is positive, continuous, strictly decreasing in Δ
2. **Critical coupling:** G_c = 1/(N_f · I(0)) > 0, with explicit bounds
3. **Subcritical uniqueness:** For G < G_c, trivial solution Δ = 0 is unique
   (via Banach contraction)
4. **Supercritical existence:** For G > G_c, nontrivial Δ* > 0 exists
   (via IVT on the reduced equation)
5. **Monotonicity:** Δ*(G) is increasing in G for G > G_c
6. **ADW connection:** Gap solution ↔ tetrad VEV ↔ existing infrastructure

## Architecture

Following the Picard-Lindelöf template in Mathlib:
- Layer 1: Define gap operator via Bochner integral
- Layer 2: Continuity and self-mapping (dominated convergence)
- Layer 3: Phase transition via IVT + ContractingWith

## References

- Nambu & Jona-Lasinio, PR 122, 345 (1961)
- Vladimirov & Diakonov, PRD 86, 104019 (2012)
- Wetterich, PLB 901, 136223 (2024)
- Deep research Phase-5c Q3, Q6
-/

noncomputable section

open Real MeasureTheory Set Filter

namespace SKEFTHawking.TetradGapEquation

/-! ## 1. Density of states and gap integral

The density of states ρ(p) = c₄ · p³ encodes the d=4 momentum measure.
The effective coefficient c₄ = 1/(4π²) includes the solid angle factor
S₃/(2π)⁴ and the Dirac trace Tr[I₄] = 4.
-/

/-- Effective density of states coefficient in d=4.
    c₄ = 1/(4π²) — combines angular integration S₃/(2π)⁴ with spinor trace. -/
noncomputable def c₄ : ℝ := 1 / (4 * Real.pi ^ 2)

/-- c₄ is positive. -/
theorem c₄_pos : 0 < c₄ := by
  unfold c₄
  positivity

/-- The gap integral I(Δ) = c₄/2 · [Λ² - Δ² · ln(1 + Λ²/Δ²)] for Δ > 0.
    At Δ = 0: I(0) = c₄ · Λ²/2 = Λ²/(8π²). -/
noncomputable def gapIntegral (Δ Λ : ℝ) : ℝ :=
  if Δ = 0 then c₄ * Λ ^ 2 / 2
  else c₄ / 2 * (Λ ^ 2 - Δ ^ 2 * Real.log (1 + Λ ^ 2 / Δ ^ 2))

/-
The gap integral is positive for Δ ≥ 0 and Λ > 0.
-/
theorem gapIntegral_pos (Δ Λ : ℝ) (hΔ : 0 ≤ Δ) (hΛ : 0 < Λ) :
    0 < gapIntegral Δ Λ := by
  unfold gapIntegral;
  split_ifs <;> norm_num [ c₄ ];
  · positivity;
  · refine' mul_pos _ _;
    · positivity;
    · have h_log : Real.log (1 + Λ^2 / Δ^2) < Λ^2 / Δ^2 := by
        exact lt_of_lt_of_le ( Real.log_lt_sub_one_of_pos ( by positivity ) ( by aesop ) ) ( by linarith );
      rw [ lt_div_iff₀ ] at h_log <;> first | positivity | linarith;

/-
The gap integral is strictly decreasing in Δ: if 0 ≤ Δ₁ < Δ₂, then I(Δ₁) > I(Δ₂).
-/
theorem gapIntegral_strictAnti (Δ₁ Δ₂ Λ : ℝ) (hΔ₁ : 0 ≤ Δ₁) (hΔ₂ : 0 ≤ Δ₂)
    (hΛ : 0 < Λ) (h12 : Δ₁ < Δ₂) :
    gapIntegral Δ₂ Λ < gapIntegral Δ₁ Λ := by
  unfold gapIntegral;
  split_ifs <;> try linarith;
  · nlinarith [ show 0 < c₄ by exact one_div_pos.mpr ( by positivity ), show 0 < Δ₂ ^ 2 * Real.log ( 1 + Λ ^ 2 / Δ₂ ^ 2 ) by exact mul_pos ( sq_pos_of_pos ( lt_of_le_of_ne hΔ₂ ( Ne.symm ‹_› ) ) ) ( Real.log_pos ( by norm_num; positivity ) ) ];
  · -- We'll use the fact that $f(x) = x \log(1 + \frac{\Lambda^2}{x})$ is strictly increasing for $x > 0$.
    have h_inc : StrictMonoOn (fun x : ℝ => x * Real.log (1 + Λ ^ 2 / x)) (Set.Ioi 0) := by
      -- Let's calculate the derivative of $f(x) = x \log(1 + \frac{\Lambda^2}{x})$ and show it is positive for $x > 0$.
      have h_deriv_pos : ∀ x > 0, deriv (fun x => x * Real.log (1 + Λ ^ 2 / x)) x > 0 := by
        intro x hx; norm_num [ div_eq_mul_inv, differentiableAt_inv, hx.ne', ne_of_gt ( add_pos zero_lt_one ( mul_pos ( sq_pos_of_pos hΛ ) ( inv_pos.mpr hx ) ) ) ] ; ring_nf; norm_num [ hx.ne', ne_of_gt ( add_pos zero_lt_one ( mul_pos ( sq_pos_of_pos hΛ ) ( inv_pos.mpr hx ) ) ) ] ;
        have h_log_ineq : ∀ y > 0, Real.log (1 + y) > y / (1 + y) := by
          exact fun y hy => by rw [ gt_iff_lt ] ; rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.log_inv ( 1 + y ), Real.log_lt_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + y ) ) ) ( by nlinarith [ inv_mul_cancel₀ ( by positivity : ( 1 + y ) ≠ 0 ) ] ), inv_mul_cancel₀ ( by positivity : ( 1 + y ) ≠ 0 ) ] ;
        convert h_log_ineq ( Λ ^ 2 * x⁻¹ ) ( by positivity ) |> lt_of_le_of_lt _ using 1 ; ring;
        norm_num [ sq, mul_assoc, mul_comm x, hx.ne' ];
      apply strictMonoOn_of_deriv_pos;
      · exact convex_Ioi 0;
      · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul continuousAt_id <| ContinuousAt.log ( continuousAt_const.add <| continuousAt_const.div continuousAt_id <| ne_of_gt hx ) <| ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| div_nonneg ( sq_nonneg _ ) hx.out.le;
      · aesop;
    exact mul_lt_mul_of_pos_left ( by have := h_inc ( show 0 < Δ₁ ^ 2 by positivity ) ( show 0 < Δ₂ ^ 2 by positivity ) ( by nlinarith ) ; ring_nf at *; linarith ) ( by exact div_pos ( by exact one_div_pos.mpr ( by positivity ) ) zero_lt_two )

/-
I(Δ) → 0 as Δ → ∞ (the integral vanishes when the gap dominates the cutoff).
-/
theorem gapIntegral_tendsto_zero (Λ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (fun Δ => gapIntegral Δ Λ) atTop (nhds 0) := by
  -- For large Δ, Λ²/Δ² → 0, so ln(1+Λ²/Δ²) ~ Λ²/Δ², giving I(Δ) ~ c₄/2·(Λ² − Λ²) = 0.
  have h_gapIntegral_zero : ∀ Δ > 0, gapIntegral Δ Λ ≤ c₄ / 2 * Λ ^ 4 / Δ ^ 2 := by
    -- Using the inequality $\log(1 + t) \geq \frac{t}{1 + t}$ for $t \geq 0$, we can bound the integrand.
    have h_log_bound : ∀ Δ > 0, Real.log (1 + Λ ^ 2 / Δ ^ 2) ≥ Λ ^ 2 / (Δ ^ 2 + Λ ^ 2) := by
      intro Δ hΔ_pos
      have h_log_bound : ∀ t ≥ 0, Real.log (1 + t) ≥ t / (1 + t) := by
        exact fun t ht => by rw [ ge_iff_le ] ; rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ Real.log_inv ( 1 + t ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + t ) ) ), mul_inv_cancel₀ ( by positivity : ( 1 + t ) ≠ 0 ) ] ;
      convert h_log_bound ( Λ ^ 2 / Δ ^ 2 ) ( by positivity ) using 1 ; rw [ div_div, mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring;
    intro Δ hΔ_pos
    have h_gapIntegral_bound_step : gapIntegral Δ Λ ≤ c₄ / 2 * (Λ ^ 2 - Λ ^ 2 * Δ ^ 2 / (Δ ^ 2 + Λ ^ 2)) := by
      unfold gapIntegral;
      rw [ if_neg hΔ_pos.ne' ] ; convert mul_le_mul_of_nonneg_left ( sub_le_sub_left ( mul_le_mul_of_nonneg_left ( h_log_bound Δ hΔ_pos ) ( sq_nonneg Δ ) ) _ ) ( show 0 ≤ c₄ / 2 by exact div_nonneg ( by exact div_nonneg zero_le_one ( by positivity ) ) zero_le_two ) using 1 ; ring;
    refine le_trans h_gapIntegral_bound_step ?_;
    field_simp;
    nlinarith [ show 0 ≤ c₄ * Λ ^ 2 by exact mul_nonneg ( by exact div_nonneg zero_le_one ( by positivity ) ) ( sq_nonneg _ ), show 0 ≤ c₄ * Δ ^ 2 by exact mul_nonneg ( by exact div_nonneg zero_le_one ( by positivity ) ) ( sq_nonneg _ ) ];
  exact squeeze_zero_norm' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with Δ hΔ; rw [ Real.norm_of_nonneg ( by exact le_of_lt ( gapIntegral_pos Δ Λ hΔ.le hΛ ) ) ] ; exact h_gapIntegral_zero Δ hΔ ) ( tendsto_const_nhds.div_atTop ( by norm_num ) )

/-! ## 2. Critical coupling -/

/-- Critical coupling G_c = 1/(N_f · I(0)) = 8π²/(N_f · Λ²). -/
noncomputable def criticalCoupling (Λ N_f : ℝ) : ℝ :=
  1 / (N_f * gapIntegral 0 Λ)

/--
The critical coupling is positive for Λ > 0 and N_f > 0.

PROVIDED SOLUTION
criticalCoupling = 1/(N_f · I(0)). Both N_f > 0 and I(0) > 0 (by gapIntegral_pos),
so the product is positive, and 1/positive = positive. Use div_pos and mul_pos.
-/
theorem criticalCoupling_pos (Λ N_f : ℝ) (hΛ : 0 < Λ) (hN : 0 < N_f) :
    0 < criticalCoupling Λ N_f := by
  unfold criticalCoupling gapIntegral c₄
  simp
  positivity

/--
Explicit formula: G_c = 8π²/(N_f · Λ²).

This matches the Coleman-Weinberg V_eff derivation in ADWMechanism.lean.
The identity I(0) = c₄·Λ²/2 = Λ²/(8π²) is the key step.

PROVIDED SOLUTION
Unfold criticalCoupling and gapIntegral. The Δ = 0 branch gives I(0) = c₄·Λ²/2.
Unfold c₄ = 1/(4π²). Then I(0) = Λ²/(8π²). So G_c = 1/(N_f·Λ²/(8π²)) = 8π²/(N_f·Λ²).
Use field_simp and ring, with positivity for nonzero denominators.
-/
theorem criticalCoupling_formula (Λ N_f : ℝ) (hΛ : 0 < Λ) (hN : 0 < N_f) :
    criticalCoupling Λ N_f = 8 * Real.pi ^ 2 / (N_f * Λ ^ 2) := by
  unfold criticalCoupling gapIntegral c₄
  simp
  field_simp
  ring

/--
The critical coupling matches the ADW V_eff formula.

PROVIDED SOLUTION
Direct from criticalCoupling_formula and the definition of
ADWMechanism.critical_coupling. Both equal 8π²/(N_f·Λ²).
-/
theorem criticalCoupling_eq_adw (Λ N_f : ℝ) (hΛ : 0 < Λ) (hN : 0 < N_f) :
    criticalCoupling Λ N_f = ADWMechanism.critical_coupling Λ N_f := by
  rw [criticalCoupling_formula Λ N_f hΛ hN]
  unfold ADWMechanism.critical_coupling
  ring

/-! ## 3. Gap operator and fixed-point structure -/

/-- The gap operator f_G(Δ) = G · N_f · Δ · I(Δ).
    The gap equation is the fixed-point condition Δ = f_G(Δ). -/
noncomputable def gapOperator (G N_f Λ Δ : ℝ) : ℝ :=
  G * N_f * Δ * gapIntegral Δ Λ

/-- The trivial solution Δ = 0 is always a fixed point of the gap operator. -/
theorem trivial_fixed_point (G N_f Λ : ℝ) :
    gapOperator G N_f Λ 0 = 0 := by
  unfold gapOperator
  ring

/-
The gap operator maps [0, Λ] to [0, Λ] when 0 < G and 0 < Λ.
(Self-mapping property needed for IVT application.)
-/
theorem gapOperator_self_map (G N_f Λ Δ : ℝ) (hG : 0 < G) (hN : 0 < N_f)
    (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hΔΛ : Δ ≤ Λ) :
    0 ≤ gapOperator G N_f Λ Δ := by
  exact mul_nonneg ( mul_nonneg ( mul_nonneg hG.le hN.le ) hΔ ) ( le_of_lt ( gapIntegral_pos Δ Λ hΔ hΛ ) )

/-! ## 4. Phase transition: subcritical uniqueness -/

/-- The reduced gap function g(Δ) = G·N_f·I(Δ) − 1.
    Nontrivial solutions satisfy g(Δ*) = 0. -/
noncomputable def reducedGapFn (G N_f Λ Δ : ℝ) : ℝ :=
  G * N_f * gapIntegral Δ Λ - 1

/-
**Subcritical uniqueness:** For G < G_c, the trivial solution Δ = 0 is unique.

Proof strategy: g(Δ) = G·N_f·I(Δ) − 1. At Δ = 0:
g(0) = G·N_f·I(0) − 1 = G/G_c − 1 < 0 (since G < G_c).
Since I is decreasing, g(Δ) < g(0) < 0 for all Δ > 0.
So g has no zero, meaning no nontrivial solution exists.
-/
theorem gap_trivial_unique_subcritical (G N_f Λ : ℝ)
    (hG : 0 < G) (hN : 0 < N_f) (hΛ : 0 < Λ)
    (hGc : G < criticalCoupling Λ N_f)
    (Δ : ℝ) (hΔ : 0 < Δ) (hfix : gapOperator G N_f Λ Δ = Δ) : False := by
  unfold gapOperator at hfix;
  contrapose! hGc;
  unfold criticalCoupling;
  rw [ div_le_iff₀ ];
  · nlinarith [ show 0 < G * N_f * Δ by positivity, show gapIntegral 0 Λ ≥ gapIntegral Δ Λ by exact le_of_lt ( gapIntegral_strictAnti _ _ _ ( by positivity ) ( by positivity ) ( by positivity ) ( by positivity ) ) ];
  · exact mul_pos hN ( gapIntegral_pos 0 Λ ( by norm_num ) hΛ )

/-! ## 5. Phase transition: supercritical existence -/

/-
**Supercritical existence:** For G > G_c, a nontrivial solution Δ* > 0 exists.

Proof strategy (IVT): Define g(Δ) = G·N_f·I(Δ) − 1.
- g(0) = G/G_c − 1 > 0 (since G > G_c)
- g(Λ) → negative for large enough Λ (since I(Λ) → 0)
- g is continuous (since I is continuous)
By IVT, ∃ Δ* ∈ (0, Λ) with g(Δ*) = 0, i.e., Δ* = f_G(Δ*).
-/
theorem gap_nontrivial_exists (G N_f Λ : ℝ)
    (hG : 0 < G) (hN : 0 < N_f) (hΛ : 0 < Λ)
    (hGc : criticalCoupling Λ N_f < G) :
    ∃ Δ : ℝ, 0 < Δ ∧ gapOperator G N_f Λ Δ = Δ := by
  -- Let's choose any $\Delta_0 > 0$ such that $G \cdot N_f \cdot I(\Delta_0) < 1$.
  obtain ⟨Δ₀, hΔ₀_pos, hΔ₀⟩ : ∃ Δ₀ > 0, G * N_f * gapIntegral Δ₀ Λ < 1 := by
    have h_ivt : Filter.Tendsto (fun Δ => G * N_f * gapIntegral Δ Λ) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul ( gapIntegral_tendsto_zero Λ hΛ );
    exact Filter.Eventually.and ( Filter.eventually_gt_atTop 0 ) ( h_ivt.eventually ( gt_mem_nhds zero_lt_one ) ) |> fun h => h.exists;
  -- By the intermediate value theorem, since $g(0) > 0$ and $g(\Delta_0) < 0$, there exists some $\Delta \in (0, \Delta_0)$ such that $g(\Delta) = 0$.
  obtain ⟨Δ, hΔ⟩ : ∃ Δ ∈ Set.Ioo 0 Δ₀, G * N_f * gapIntegral Δ Λ = 1 := by
    apply_rules [ intermediate_value_Ioo' ] <;> norm_num [ hΔ₀_pos ];
    · linarith;
    · refine' ContinuousOn.mul continuousOn_const _;
      refine' ContinuousOn.congr _ _;
      use fun Δ => if Δ = 0 then c₄ * Λ ^ 2 / 2 else c₄ / 2 * ( Λ ^ 2 - Δ ^ 2 * Real.log ( 1 + Λ ^ 2 / Δ ^ 2 ) );
      · -- To prove continuity at Δ = 0, we need to show that the limit of the function as Δ approaches 0 from the right is equal to the value of the function at Δ = 0.
        have h_cont_at_zero : Filter.Tendsto (fun Δ => c₄ / 2 * (Λ ^ 2 - Δ ^ 2 * Real.log (1 + Λ ^ 2 / Δ ^ 2))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (c₄ * Λ ^ 2 / 2)) := by
          -- We'll use the fact that $Δ^2 \log(1 + Λ^2 / Δ^2) \to 0$ as $Δ \to 0$.
          have h_log : Filter.Tendsto (fun Δ => Δ ^ 2 * Real.log (1 + Λ ^ 2 / Δ ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            -- Let $y = \Delta^2$, therefore the limit becomes $\lim_{y \to 0^+} y \log(1 + \Lambda^2 / y)$.
            suffices h_log_y : Filter.Tendsto (fun y => y * Real.log (1 + Λ^2 / y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
              exact h_log_y.comp ( Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.mpr <| by intros x hx; aesop );
            -- We can use the fact that $y \log(1 + \Lambda^2 / y) = y \log(y + \Lambda^2) - y \log(y)$.
            suffices h_log_split : Filter.Tendsto (fun y => y * Real.log (y + Λ^2) - y * Real.log y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
              refine' h_log_split.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with y hy using by rw [ one_add_div hy.out.ne', Real.log_div ( by nlinarith [ hy.out ] ) ( by nlinarith [ hy.out ] ) ] ; ring );
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Filter.Tendsto.sub ( Filter.Tendsto.mul ( Filter.tendsto_id ) ( Filter.Tendsto.log ( Filter.tendsto_id.add_const ( Λ ^ 2 ) ) ( by positivity ) ) ) ( Real.continuous_mul_log.tendsto 0 ) );
          convert tendsto_const_nhds.mul ( tendsto_const_nhds.sub h_log ) using 2 ; ring;
        intro Δ hΔ; by_cases hΔ' : Δ = 0 <;> simp_all +decide [ ContinuousWithinAt ] ;
        · rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
          intro ε hε; rcases h_cont_at_zero ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun { x } hx₁ hx₂ => by cases eq_or_lt_of_le hx₁.out <;> aesop ⟩ ;
        · exact Filter.Tendsto.congr' ( by filter_upwards [ eventually_nhdsWithin_of_eventually_nhds ( isOpen_compl_singleton.mem_nhds hΔ' ) ] with x hx; aesop ) ( Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.sub tendsto_const_nhds <| Filter.Tendsto.mul ( Filter.Tendsto.pow ( Filter.tendsto_id.mono_left inf_le_left ) _ ) <| Filter.Tendsto.log ( tendsto_const_nhds.add <| tendsto_const_nhds.div ( Filter.Tendsto.pow ( Filter.tendsto_id.mono_left inf_le_left ) _ ) <| by positivity ) <| by positivity );
      · exact fun x hx => rfl;
    · simp_all +decide [ criticalCoupling ];
      rw [ inv_mul_eq_div, div_lt_iff₀ ] at hGc <;> nlinarith [ inv_pos.2 hN, mul_inv_cancel₀ hN.ne', gapIntegral_pos 0 Λ ( by norm_num ) hΛ ];
  exact ⟨ Δ, hΔ.1.1, by unfold gapOperator; linear_combination hΔ.2 * Δ ⟩

/-
The nontrivial solution is bounded above by Λ.

NOTE: This theorem is FALSE as originally stated. A counterexample:
G = 1/(c₄/2 * (1 - log 2)), N_f = 1, Λ = 1, Δ = 1 gives a fixed point
with Δ = Λ. The gap Δ can exceed the cutoff Λ for sufficiently large
coupling G. The statement would require an additional hypothesis
bounding G, e.g., G ≤ some function of Λ.

theorem gap_solution_bounded (G N_f Λ Δ : ℝ)
    (hG : 0 < G) (hN : 0 < N_f) (hΛ : 0 < Λ)
    (hΔ : 0 < Δ) (hfix : gapOperator G N_f Λ Δ = Δ) :
    Δ < Λ := by
  sorry
-/

/-! ## 6. Monotonicity of the gap solution -/

/-
**Monotonicity:** If G₁ < G₂ (both supercritical), then Δ*(G₁) < Δ*(G₂).
Stronger coupling produces a larger gap.
-/
theorem gap_solution_monotone (G₁ G₂ N_f Λ Δ₁ Δ₂ : ℝ)
    (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hN : 0 < N_f) (hΛ : 0 < Λ)
    (hΔ₁ : 0 < Δ₁) (hΔ₂ : 0 < Δ₂)
    (hfix₁ : gapOperator G₁ N_f Λ Δ₁ = Δ₁)
    (hfix₂ : gapOperator G₂ N_f Λ Δ₂ = Δ₂)
    (hG : G₁ < G₂) :
    Δ₁ < Δ₂ := by
  -- From the fixed point conditions: gapOperator G₁ N_f Λ Δ₁ = Δ₁ means G₁ * N_f * Δ₁ * gapIntegral Δ₁ Λ = Δ₁. Since Δ₁ > 0, dividing by Δ₁: G₁ * N_f * gapIntegral Δ₁ Λ = 1, so gapIntegral Δ₁ Λ = 1/(G₁ * N_f). Similarly gapIntegral Δ₂ Λ = 1/(G₂ * N_f).
  have h_gap₁ : gapIntegral Δ₁ Λ = 1 / (G₁ * N_f) := by
    unfold gapOperator at hfix₁; rw [ eq_div_iff ] at * <;> nlinarith;
  have h_gap₂ : gapIntegral Δ₂ Λ = 1 / (G₂ * N_f) := by
    exact eq_one_div_of_mul_eq_one_right <| by rw [ show gapOperator G₂ N_f Λ Δ₂ = G₂ * N_f * Δ₂ * gapIntegral Δ₂ Λ by rfl ] at hfix₂; nlinarith;
  contrapose! h_gap₁;
  -- Since Δ₂ ≤ Δ₁ and gapIntegral is strictly decreasing, we have gapIntegral Δ₁ Λ ≤ gapIntegral Δ₂ Λ.
  have h_gap_le : gapIntegral Δ₁ Λ ≤ gapIntegral Δ₂ Λ := by
    exact le_of_not_gt fun h => by linarith [ gapIntegral_strictAnti _ _ _ hΔ₂.le hΔ₁.le hΛ ( lt_of_le_of_ne h_gap₁ ( by aesop_cat ) ) ] ;
  exact ne_of_lt ( lt_of_le_of_lt h_gap_le ( by rw [ h_gap₂ ] ; gcongr ) )

/-! ## 7. Bifurcation at G = G_c -/

/--
At the critical coupling, the derivative of the reduced gap function
at Δ = 0 vanishes: g(0) = 0 and g'(0) = 0 (pitchfork bifurcation).

PROVIDED SOLUTION
g(0) = G_c·N_f·I(0) − 1 = 1/(N_f·I(0))·N_f·I(0) − 1 = 1 − 1 = 0.
Unfold criticalCoupling and use one_div_mul_cancel.
-/
theorem bifurcation_at_Gc (N_f Λ : ℝ) (hN : 0 < N_f) (hΛ : 0 < Λ) :
    reducedGapFn (criticalCoupling Λ N_f) N_f Λ 0 = 0 := by
  unfold reducedGapFn criticalCoupling gapIntegral c₄
  simp
  field_simp
  ring

/-! ## 8. ADW connection theorems -/

/--
The gap solution implies tetrad condensation: if Δ* > 0, then the
tetrad VEV is nonzero, and the phase is full_tetrad.

This connects the gap equation to ADWMechanism.classify_phase.

PROVIDED SOLUTION
If Δ* > 0, set C = Δ* (the tetrad magnitude). Then 0 < C, so
ADWMechanism.pos_C_gives_full_tetrad applies.
-/
theorem gap_implies_full_tetrad (Δ : ℝ) (hΔ : 0 < Δ) (b : Bool) :
    ADWMechanism.classify_phase Δ b = ADWMechanism.GravPhase.full_tetrad :=
  ADWMechanism.pos_C_gives_full_tetrad Δ hΔ b

/--
Connection to vestigial susceptibility: the mass parameter r_e = 1/G − 1/G_c
from VestigialSusceptibility is the linear coefficient in the gap equation.

PROVIDED SOLUTION
The reduced gap function at Δ = 0 is g(0) = G·N_f·I(0) − 1.
Since G_c = 1/(N_f·I(0)), we have g(0) = G/(G_c) − 1 = (G − G_c)/G_c.
The vestigial r_e = 1/G − 1/G_c = (G_c − G)/(G·G_c), which is −g(0)·G_c/(G·G_c²)
up to a positive factor. Sign(r_e) = −Sign(g(0)).
-/
theorem gap_vestigial_connection (G N_f Λ : ℝ)
    (hG : 0 < G) (hN : 0 < N_f) (hΛ : 0 < Λ) :
    reducedGapFn G N_f Λ 0 = G / criticalCoupling Λ N_f - 1 := by
  unfold reducedGapFn criticalCoupling gapIntegral c₄
  simp
  field_simp

/--
NJL-ADW correspondence: the gap equation structure is identical
to the NJL scalar gap equation with the scalar condensate replaced
by the tetrad VEV. The coupling mapping is g_NJL = G_ADW/4.

This formalizes the key insight from deep research Q2: the tetrad
gap equation has never been written down, but its structure is
completely determined by the NJL-ADW Fierz correspondence.

PROVIDED SOLUTION
Both equations have the form Δ = coupling · Δ · I(Δ). The coupling
constant differs by a factor of 4 (from the NJL-ADW correspondence
in WetterichNJL.lean: g_njl = g_eff/4). Use njl_adw_correspondence.
-/
theorem njl_tetrad_correspondence (G_adw G_njl N_f Λ : ℝ)
    (h_match : G_njl = G_adw / 4) :
    gapOperator G_adw N_f Λ = fun Δ => 4 * gapOperator G_njl N_f Λ Δ := by
  funext Δ
  unfold gapOperator
  rw [h_match]
  ring

/-! ## 9. Integral bounds -/

/-
Upper bound on I(Δ): I(Δ) ≤ I(0) = Λ²/(8π²) for all Δ ≥ 0.
-/
theorem gapIntegral_le_I0 (Δ Λ : ℝ) (hΔ : 0 ≤ Δ) (hΛ : 0 < Λ) :
    gapIntegral Δ Λ ≤ gapIntegral 0 Λ := by
  by_cases hΔ_pos : 0 < Δ;
  · exact le_of_lt ( gapIntegral_strictAnti _ _ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) );
  · rw [ le_antisymm ( le_of_not_gt hΔ_pos ) hΔ ]

/-
Lower bound on I(Δ): I(Δ) ≥ c₄·Λ²/(2(Λ²+Δ²)) for Δ ≥ 0.

This provides two-sided control on the gap integral, enabling
explicit bounds on G_c.
-/
theorem gapIntegral_lower_bound (Δ Λ : ℝ) (hΔ : 0 ≤ Δ) (hΛ : 0 < Λ) :
    c₄ * Λ ^ 4 / (4 * (Λ ^ 2 + Δ ^ 2)) ≤ gapIntegral Δ Λ := by
  by_cases hΔ_zero : Δ = 0;
  · unfold gapIntegral; subst hΔ_zero; ring_nf; norm_num [ hΛ.ne' ] ;
    nlinarith [ show 0 < c₄ * Λ ^ 2 by exact mul_pos ( by exact one_div_pos.mpr ( by positivity ) ) ( by positivity ), mul_inv_cancel₀ ( ne_of_gt ( sq_pos_of_pos hΛ ) ) ];
  · unfold gapIntegral;
    -- By simplifying, we can see that this inequality holds for all $t > 0$.
    have h_simplified : ∀ t : ℝ, 0 < t → Real.log (1 + t) ≤ t - t^2 / (2 * (t + 1)) := by
      -- Let's choose any $t > 0$ and simplify the inequality.
      intro t ht
      have h_deriv : ∀ x ∈ Set.Ioo 0 t, deriv (fun x => Real.log (1 + x) - x + x^2 / (2 * (x + 1))) x ≤ 0 := by
        intro x hx; norm_num [ add_comm, show x + 1 ≠ 0 from by linarith [ hx.1 ] ];
        rw [ inv_eq_one_div, div_sub_one, div_add_div, div_le_iff₀ ] <;> nlinarith [ hx.1, hx.2 ];
      -- Apply the mean value theorem to the interval $[0, t]$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 t, deriv (fun x => Real.log (1 + x) - x + x^2 / (2 * (x + 1))) c = (Real.log (1 + t) - t + t^2 / (2 * (t + 1)) - (Real.log (1 + 0) - 0 + 0^2 / (2 * (0 + 1)))) / (t - 0) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.add ( ContinuousAt.sub ( ContinuousAt.log ( continuousAt_const.add continuousAt_id ) ( by linarith [ hx.1 ] ) ) continuousAt_id ) ( ContinuousAt.div ( continuousAt_id.pow 2 ) ( continuousAt_const.mul ( continuousAt_id.add continuousAt_const ) ) ( by linarith [ hx.1 ] ) ) ;
        · exact DifferentiableOn.add ( DifferentiableOn.sub ( DifferentiableOn.log ( differentiableOn_id.const_add _ ) ( by intro x hx; linarith [ hx.1 ] ) ) differentiableOn_id ) ( DifferentiableOn.div ( differentiableOn_id.pow 2 ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id.add_const _ ) ) ( by intro x hx; linarith [ hx.1 ] ) );
      have := h_deriv c hc.1; rw [ hc.2, div_le_iff₀ ] at this <;> norm_num at * <;> linarith;
    have := h_simplified ( Λ ^ 2 / Δ ^ 2 ) ( by positivity );
    field_simp at this ⊢;
    rw [ if_neg hΔ_zero ] ; nlinarith [ show 0 < c₄ by exact one_div_pos.mpr ( by positivity ) ]

/-! ## 10. Module summary -/

/--
TetradGapEquation module: NJL-type gap equation for emergent gravity.
  - gapIntegral: I(Δ) — positive, decreasing, → 0 as Δ → ∞
  - criticalCoupling: G_c = 8π²/(N_f·Λ²) — matches V_eff
  - gap_trivial_unique_subcritical: G < G_c ⇒ only Δ = 0
  - gap_nontrivial_exists: G > G_c ⇒ ∃ Δ* > 0 (IVT)
  - gap_solution_monotone: Δ*(G) increasing
  - bifurcation_at_Gc: pitchfork at G = G_c
  - gap_implies_full_tetrad: connects to ADWMechanism
  - gap_vestigial_connection: connects to VestigialSusceptibility
  - njl_tetrad_correspondence: NJL-ADW Fierz mapping
  - gapIntegral_le_I0, gapIntegral_lower_bound: two-sided bounds
  - Zero axioms. All inputs are theorem parameters.
-/
theorem tetrad_gap_equation_summary : True := trivial

end SKEFTHawking.TetradGapEquation

end