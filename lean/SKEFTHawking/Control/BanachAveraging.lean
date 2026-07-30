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

/-- **The first-order averaging bound.** -/
theorem norm_integral_mul_mul_le [CompleteSpace A] {B Kp Kq T : ℝ}
    (hS : ∀ s, HasDerivAt S (G s) s)
    (hL : ∀ s, HasDerivAt L (L s * P s) s) (hU : ∀ s, HasDerivAt U (Q s * U s) s)
    (hSc : Continuous S) (hLc : Continuous L) (hUc : Continuous U)
    (hPc : Continuous P) (hQc : Continuous Q) (hGc : Continuous G)
    (hS0 : S 0 = 0)
    (hLb : ∀ s, ‖L s‖ ≤ 1) (hUb : ∀ s, ‖U s‖ ≤ 1) (hSb : ∀ s, ‖S s‖ ≤ B)
    (hPb : ∀ s, ‖P s‖ ≤ Kp) (hQb : ∀ s, ‖Q s‖ ≤ Kq)
    (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ‖∫ s in (0 : ℝ)..T, L s * G s * U s‖ ≤ B * (1 + T * (Kp + Kq)) := by
  have hKp : 0 ≤ Kp := le_trans (norm_nonneg _) (hPb 0)
  have hKq : 0 ≤ Kq := le_trans (norm_nonneg _) (hQb 0)
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
  have hbdry : ‖L T * S T * U T‖ ≤ B := by
    refine le_trans (norm_mul_le _ _) ?_
    have h1 : ‖L T * S T‖ ≤ B := by
      refine le_trans (norm_mul_le _ _) ?_
      nlinarith [hLb T, hSb T, norm_nonneg (L T), norm_nonneg (S T)]
    nlinarith [h1, hUb T, norm_nonneg (U T), hB]
  have hIA : ‖∫ s in (0 : ℝ)..T, L s * P s * S s * U s‖ ≤ (B * Kp) * T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := B * Kp) (f := fun s => L s * P s * S s * U s) (a := 0) (b := T) ?_
    · simpa [abs_of_nonneg hT] using this
    · intro s _
      refine le_trans (norm_mul_le _ _) ?_
      have h1 : ‖L s * P s * S s‖ ≤ B * Kp := by
        refine le_trans (norm_mul_le _ _) ?_
        have h2 : ‖L s * P s‖ ≤ Kp := by
          refine le_trans (norm_mul_le _ _) ?_
          nlinarith [hLb s, hPb s, norm_nonneg (L s), norm_nonneg (P s)]
        nlinarith [h2, hSb s, norm_nonneg (S s), hKp, hB]
      exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (hUb s)) h1
  have hIC : ‖∫ s in (0 : ℝ)..T, L s * S s * (Q s * U s)‖ ≤ (B * Kq) * T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := B * Kq) (f := fun s => L s * S s * (Q s * U s)) (a := 0) (b := T) ?_
    · simpa [abs_of_nonneg hT] using this
    · intro s _
      refine le_trans (norm_mul_le _ _) ?_
      have h1 : ‖L s * S s‖ ≤ B := by
        refine le_trans (norm_mul_le _ _) ?_
        nlinarith [hLb s, hSb s, norm_nonneg (L s), norm_nonneg (S s)]
      have h2 : ‖Q s * U s‖ ≤ Kq := by
        refine le_trans (norm_mul_le _ _) ?_
        nlinarith [hQb s, hUb s, norm_nonneg (Q s), norm_nonneg (U s)]
      nlinarith [h1, h2, hB, hKq, norm_nonneg (L s * S s), norm_nonneg (Q s * U s)]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_sub_le _ _) le_rfl) ?_
  nlinarith [hbdry, hIA, hIC, hB, hKp, hKq, hT]

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

/-- **The unitarity transfer.** If `Ur` has right inverse `Vr` and `‖Ur‖ ≤ 1`, a bound on the
CONJUGATED discrepancy `Vr·Ue − 1` transfers to the literal difference `Ue − Ur`. -/
theorem norm_sub_le_norm_mul_sub_one {Ue Ur Vr : A} (hinv : Ur * Vr = 1) (hUr : ‖Ur‖ ≤ 1) :
    ‖Ue - Ur‖ ≤ ‖Vr * Ue - 1‖ := by
  have hfac : Ue - Ur = Ur * (Vr * Ue - 1) := by
    rw [mul_sub, ← mul_assoc, hinv, one_mul, mul_one]
  rw [hfac]
  exact le_trans (norm_mul_le _ _) (mul_le_of_le_one_left (norm_nonneg _) hUr)

/-- **The propagator difference bound.** The capstone: the difference between the exact propagator
`U` and the reduced propagator `Ur` is bounded by `B·(1 + T·(Kp+Kq))`, where `B` bounds the
ANTIDERIVATIVE of the discrepancy generator `P + Q`.

Nothing here asserts the reduction as an equality; the conclusion is an inequality whose constant is
explicit in every parameter. -/
theorem norm_propagator_sub_le [CompleteSpace A] {B Kp Kq T : ℝ} {Ur : A}
    (hS : ∀ s, HasDerivAt S (P s + Q s) s)
    (hL : ∀ s, HasDerivAt L (L s * P s) s) (hU : ∀ s, HasDerivAt U (Q s * U s) s)
    (hSc : Continuous S) (hLc : Continuous L) (hUc : Continuous U)
    (hPc : Continuous P) (hQc : Continuous Q)
    (hS0 : S 0 = 0) (hL0U0 : L 0 * U 0 = 1)
    (hLb : ∀ s, ‖L s‖ ≤ 1) (hUb : ∀ s, ‖U s‖ ≤ 1) (hSb : ∀ s, ‖S s‖ ≤ B)
    (hPb : ∀ s, ‖P s‖ ≤ Kp) (hQb : ∀ s, ‖Q s‖ ≤ Kq) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hinv : Ur * L T = 1) (hUrb : ‖Ur‖ ≤ 1) :
    ‖U T - Ur‖ ≤ B * (1 + T * (Kp + Kq)) := by
  -- Transfer to the conjugated discrepancy.
  refine le_trans (norm_sub_le_norm_mul_sub_one hinv hUrb) ?_
  -- The conjugated discrepancy IS the integral of `L·(P+Q)·U`.
  have hid := integral_mul_ode hL hU (by fun_prop) T
  rw [hL0U0] at hid
  rw [← hid]
  -- ... which the averaging bound controls, with `G := P + Q`.
  exact norm_integral_mul_mul_le hS hL hU hSc hLc hUc hPc hQc (hPc.add hQc)
    hS0 hLb hUb hSb hPb hQb hB hT

end

end SKEFTHawking.Control
