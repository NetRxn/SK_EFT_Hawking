/-
Phase 6EE Wave 1 substrate: first-order averaging in a Banach algebra.

This module exists for two reasons, one mathematical and one mechanical.

MATHEMATICAL. The estimate that controls a rotating-wave reduction is not special to `2×2`
matrices: it is the statement that when a propagator discrepancy is driven by a generator with a
BOUNDED ANTIDERIVATIVE, integration by parts converts "integrand is `O(ε)`, so the integral is
`O(εT)`" into "the integral is `O(ε) + O(ε·T·‖generators‖)". Stated over a Banach algebra it is
reusable substrate rather than a one-off.

MECHANICAL. On concrete `Matrix n n ℂ` the same construction is blocked by an instance diamond:
`HasDerivAt.mul` and a `HasDerivAt` appearing in a structure field reach `AddCommGroup` by
different paths (`Matrix.addCommGroup` vs `Matrix.linftyOpNormedRing.toAddCommGroup`), so the two
will not unify. Over an abstract `[NormedRing A] [NormedAlgebra ℝ A]` the instances are coherent by
construction and the problem does not arise. Concrete matrices enter only at instantiation.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.Control

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-! ## 1. The triple product rule -/

/-- Product rule for three factors in a Banach algebra. Order is preserved throughout: `A` is not
assumed commutative, and for the propagator application it genuinely is not. -/
theorem hasDerivAt_mul₃ {f g h : ℝ → A} {f' g' h' : A} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) (hh : HasDerivAt h h' s) :
    HasDerivAt (fun r => f r * g r * h r)
      (f' * g s * h s + f s * g' * h s + f s * g s * h') s := by
  have h1 := (hf.mul hg).mul hh
  have heq : (f' * g s + f s * g') * h s + (f * g) s * h'
      = f' * g s * h s + f s * g' * h s + f s * g s * h' := by
    show (f' * g s + f s * g') * h s + f s * g s * h' = _
    noncomm_ring
  rw [heq] at h1
  exact h1

/-! ## 2. The averaging identity

`W = L·S·U` differentiates to `L·P·S·U + L·G·U + L·S·Q·U`, so integrating and applying the
fundamental theorem of calculus expresses `∫ L·G·U` — the object we want to bound — in terms of a
BOUNDARY term plus two terms carrying `S` rather than `G`. When `S` (the antiderivative of `G`) is
small even though `G` is not, that is exactly the trade that produces a Bloch–Siegert-scale bound. -/

variable {S L U P Q G : ℝ → A}

/-- The integrand of the averaging identity is the derivative of `L·S·U`. -/
theorem hasDerivAt_averaging (hS : ∀ s, HasDerivAt S (G s) s)
    (hL : ∀ s, HasDerivAt L (L s * P s) s) (hU : ∀ s, HasDerivAt U (Q s * U s) s) (s : ℝ) :
    HasDerivAt (fun r => L r * S r * U r)
      (L s * P s * S s * U s + L s * G s * U s + L s * S s * (Q s * U s)) s :=
  hasDerivAt_mul₃ (hL s) (hS s) (hU s)

/-- **First-order averaging identity** (FTC applied to `L·S·U`). -/
theorem integral_averaging [CompleteSpace A] (hS : ∀ s, HasDerivAt S (G s) s)
    (hL : ∀ s, HasDerivAt L (L s * P s) s) (hU : ∀ s, HasDerivAt U (Q s * U s) s)
    (hcont : Continuous fun s =>
      L s * P s * S s * U s + L s * G s * U s + L s * S s * (Q s * U s))
    (T : ℝ) :
    (∫ s in (0 : ℝ)..T,
        (L s * P s * S s * U s + L s * G s * U s + L s * S s * (Q s * U s)))
      = L T * S T * U T - L 0 * S 0 * U 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_averaging hS hL hU s) (hcont.intervalIntegrable 0 T)

/-! ## 3. The averaging bound

The payoff. `∫₀ᵀ L·G·U` is bounded using only a bound `B` on the ANTIDERIVATIVE `S`, never on `G`
itself. A pointwise bound on `G` would give `O(‖G‖·T)`; this gives `B·(1 + T(Kp+Kq))`, and when `G`
oscillates fast `B` is small even though `‖G‖` is not. That is the whole mechanism behind the
Bloch–Siegert scale. -/

/-- **The first-order averaging bound.**

The factor bounds `KL`, `KU` are ARBITRARY, not pinned to `1`. That matters concretely: at the
`ℓ^∞` operator norm a generic `2×2` unitary has norm `> 1` (the co-rotating propagator
`exp(-iθσ_x)` has row sums `|cos θ| + |sin θ|`, reaching `√2`), so a hypothesis `‖L s‖ ≤ 1` would
exclude essentially every rotation — i.e. exactly the propagators this machinery exists to bound.
Carrying general bounds keeps the theorem applicable to the intended objects in any norm. -/
theorem norm_integral_mul_mul_le [CompleteSpace A] {B KL KU Kp Kq T : ℝ}
    (hS : ∀ s, HasDerivAt S (G s) s)
    (hL : ∀ s, HasDerivAt L (L s * P s) s) (hU : ∀ s, HasDerivAt U (Q s * U s) s)
    (hSc : Continuous S) (hLc : Continuous L) (hUc : Continuous U)
    (hPc : Continuous P) (hQc : Continuous Q) (hGc : Continuous G)
    (hS0 : S 0 = 0)
    (hLb : ∀ s, ‖L s‖ ≤ KL) (hUb : ∀ s, ‖U s‖ ≤ KU) (hSb : ∀ s, ‖S s‖ ≤ B)
    (hPb : ∀ s, ‖P s‖ ≤ Kp) (hQb : ∀ s, ‖Q s‖ ≤ Kq)
    (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ‖∫ s in (0 : ℝ)..T, L s * G s * U s‖ ≤ KL * KU * B * (1 + T * (Kp + Kq)) := by
  have hKp : 0 ≤ Kp := le_trans (norm_nonneg _) (hPb 0)
  have hKq : 0 ≤ Kq := le_trans (norm_nonneg _) (hQb 0)
  have hKL : 0 ≤ KL := le_trans (norm_nonneg _) (hLb 0)
  have hKU : 0 ≤ KU := le_trans (norm_nonneg _) (hUb 0)
  -- The three summands are continuous, hence interval-integrable.
  have iA : IntervalIntegrable (fun s => L s * P s * S s * U s) MeasureTheory.volume 0 T :=
    (((hLc.mul hPc).mul hSc).mul hUc).intervalIntegrable 0 T
  have iB : IntervalIntegrable (fun s => L s * G s * U s) MeasureTheory.volume 0 T :=
    ((hLc.mul hGc).mul hUc).intervalIntegrable 0 T
  have iC : IntervalIntegrable (fun s => L s * S s * (Q s * U s)) MeasureTheory.volume 0 T :=
    ((hLc.mul hSc).mul (hQc.mul hUc)).intervalIntegrable 0 T
  have hid := integral_averaging hS hL hU
    (by fun_prop : Continuous fun s =>
      L s * P s * S s * U s + L s * G s * U s + L s * S s * (Q s * U s)) T
  rw [intervalIntegral.integral_add (iA.add iB) iC,
    intervalIntegral.integral_add iA iB] at hid
  have hW0 : L 0 * S 0 * U 0 = 0 := by rw [hS0]; simp
  rw [hW0, sub_zero] at hid
  -- Isolate the integral of interest.
  have hsplit : (∫ s in (0 : ℝ)..T, L s * G s * U s)
      = L T * S T * U T - (∫ s in (0 : ℝ)..T, L s * P s * S s * U s)
        - ∫ s in (0 : ℝ)..T, L s * S s * (Q s * U s) := by
    rw [← hid]; abel
  rw [hsplit]
  -- Bound the boundary term and the two integrals.
  -- Pointwise bound on a triple product `‖L · X · U‖ ≤ KL · KX · KU`.
  have htriple : ∀ (X : A) (KX : ℝ), 0 ≤ KX → ‖X‖ ≤ KX → ∀ s : ℝ,
      ‖L s * X * U s‖ ≤ KL * KX * KU := by
    intro X KX hKX hX s
    refine le_trans (norm_mul_le _ _) ?_
    have h1 : ‖L s * X‖ ≤ KL * KX :=
      le_trans (norm_mul_le _ _) (mul_le_mul (hLb s) hX (norm_nonneg _) hKL)
    exact mul_le_mul h1 (hUb s) (norm_nonneg _) (by positivity)
  have hbdry : ‖L T * S T * U T‖ ≤ KL * B * KU := htriple (S T) B hB (hSb T) T
  have hIA : ‖∫ s in (0 : ℝ)..T, L s * P s * S s * U s‖ ≤ (KL * (Kp * B) * KU) * T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := KL * (Kp * B) * KU) (f := fun s => L s * P s * S s * U s) (a := 0) (b := T) ?_
    · simpa [abs_of_nonneg hT] using this
    · intro s _
      have hPS : ‖P s * S s‖ ≤ Kp * B :=
        le_trans (norm_mul_le _ _) (mul_le_mul (hPb s) (hSb s) (norm_nonneg _) hKp)
      have := htriple (P s * S s) (Kp * B) (by positivity) hPS s
      calc ‖L s * P s * S s * U s‖ = ‖L s * (P s * S s) * U s‖ := by congr 1; noncomm_ring
        _ ≤ KL * (Kp * B) * KU := this
  have hIC : ‖∫ s in (0 : ℝ)..T, L s * S s * (Q s * U s)‖ ≤ (KL * (B * Kq) * KU) * T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := KL * (B * Kq) * KU) (f := fun s => L s * S s * (Q s * U s)) (a := 0) (b := T) ?_
    · simpa [abs_of_nonneg hT] using this
    · intro s _
      have hSQ : ‖S s * Q s‖ ≤ B * Kq :=
        le_trans (norm_mul_le _ _) (mul_le_mul (hSb s) (hQb s) (norm_nonneg _) hB)
      have := htriple (S s * Q s) (B * Kq) (by positivity) hSQ s
      calc ‖L s * S s * (Q s * U s)‖ = ‖L s * (S s * Q s) * U s‖ := by
            congr 1; noncomm_ring
        _ ≤ KL * (B * Kq) * KU := this
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_sub_le _ _) le_rfl) ?_
  nlinarith [hbdry, hIA, hIC, hB, hKp, hKq, hKL, hKU, hT,
    mul_nonneg (mul_nonneg hKL hKU) hB, mul_nonneg hKL hKU]

/-! ## 4. From the averaging bound to a genuine propagator difference

Two links. First, the product of two ODE solutions `L' = L·P`, `U' = Q·U` is itself an ODE solution
with generator `P + Q`, so FTC turns `∫₀ᵀ L·(P+Q)·U` into the boundary value `L T·U T − L 0·U 0` —
this is the discrepancy identity. Second, when `L` is a left inverse of a third propagator `Ur`, the
difference `U − Ur` factors as `Ur·(L·U − 1)`, transferring the bound off the conjugated quantity
and onto the literal difference. -/

/-- The product of two ODE solutions solves the ODE with the SUMMED generator. -/
theorem hasDerivAt_mul_ode (hL : ∀ s, HasDerivAt L (L s * P s) s)
    (hU : ∀ s, HasDerivAt U (Q s * U s) s) (s : ℝ) :
    HasDerivAt (fun r => L r * U r) (L s * (P s + Q s) * U s) s := by
  have h := (hL s).mul (hU s)
  have heq : L s * P s * U s + L s * (Q s * U s) = L s * (P s + Q s) * U s := by
    noncomm_ring
  rw [heq] at h
  exact h

/-- **The discrepancy identity.** -/
theorem integral_mul_ode [CompleteSpace A] (hL : ∀ s, HasDerivAt L (L s * P s) s)
    (hU : ∀ s, HasDerivAt U (Q s * U s) s)
    (hcont : Continuous fun s => L s * (P s + Q s) * U s) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, L s * (P s + Q s) * U s) = L T * U T - L 0 * U 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_mul_ode hL hU s) (hcont.intervalIntegrable 0 T)

omit [NormedAlgebra ℝ A] in
/-- **The unitarity transfer.** If `Ur` has right inverse `Vr` and `‖Ur‖ ≤ KUr`, a bound on the
CONJUGATED discrepancy `Vr·Ue − 1` transfers to the literal difference `Ue − Ur`. -/
theorem norm_sub_le_norm_mul_sub_one {Ue Ur Vr : A} {KUr : ℝ} (hinv : Ur * Vr = 1)
    (hUr : ‖Ur‖ ≤ KUr) :
    ‖Ue - Ur‖ ≤ KUr * ‖Vr * Ue - 1‖ := by
  have hfac : Ue - Ur = Ur * (Vr * Ue - 1) := by
    rw [mul_sub, ← mul_assoc, hinv, one_mul, mul_one]
  rw [hfac]
  exact le_trans (norm_mul_le _ _)
    (mul_le_mul_of_nonneg_right hUr (norm_nonneg _))

/-- **The propagator difference bound.** The capstone: the difference between the exact propagator
`U` and the reduced propagator `Ur` is bounded by `B·(1 + T·(Kp+Kq))`, where `B` bounds the
ANTIDERIVATIVE of the discrepancy generator `P + Q`.

Nothing here asserts the reduction as an equality; the conclusion is an inequality whose constant is
explicit in every parameter. -/
theorem norm_propagator_sub_le [CompleteSpace A] {B KL KU KUr Kp Kq T : ℝ} {Ur : A}
    (hS : ∀ s, HasDerivAt S (P s + Q s) s)
    (hL : ∀ s, HasDerivAt L (L s * P s) s) (hU : ∀ s, HasDerivAt U (Q s * U s) s)
    (hSc : Continuous S) (hLc : Continuous L) (hUc : Continuous U)
    (hPc : Continuous P) (hQc : Continuous Q)
    (hS0 : S 0 = 0) (hL0U0 : L 0 * U 0 = 1)
    (hLb : ∀ s, ‖L s‖ ≤ KL) (hUb : ∀ s, ‖U s‖ ≤ KU) (hSb : ∀ s, ‖S s‖ ≤ B)
    (hPb : ∀ s, ‖P s‖ ≤ Kp) (hQb : ∀ s, ‖Q s‖ ≤ Kq) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hinv : Ur * L T = 1) (hUrb : ‖Ur‖ ≤ KUr) :
    ‖U T - Ur‖ ≤ KUr * (KL * KU * B * (1 + T * (Kp + Kq))) := by
  -- Transfer to the conjugated discrepancy.
  refine le_trans (norm_sub_le_norm_mul_sub_one hinv hUrb) ?_
  have hKUr : 0 ≤ KUr := le_trans (norm_nonneg _) hUrb
  refine mul_le_mul_of_nonneg_left ?_ hKUr
  -- The conjugated discrepancy IS the integral of `L·(P+Q)·U`.
  have hid := integral_mul_ode hL hU (by fun_prop) T
  rw [hL0U0] at hid
  rw [← hid]
  -- ... which the averaging bound controls, with `G := P + Q`.
  exact norm_integral_mul_mul_le hS hL hU hSc hLc hUc hPc hQc (hPc.add hQc)
    hS0 hLb hUb hSb hPb hQb hB hT

end

end SKEFTHawking.Control
