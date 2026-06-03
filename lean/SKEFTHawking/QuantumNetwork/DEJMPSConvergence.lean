import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Distillation

/-!
# DEJMPS general-Bell-diagonal map: structure and sub-basin convergence (Phase 6AD / Bucket 3.3)

Extends the shipped Werner-restriction result (`dejmps_werner_fidelity_increase`,
`Distillation.lean`) to the **general Bell-diagonal** DEJMPS map (Dür–Briegel review
Eq. (19); exact-formulas DR §2b), in the corrected diagonal `(00,11)=(I,Y)` pairing:

`A' = (A²+D²)/N`, `B' = (B²+C²)/N`, `C' = 2AD/N`, `D' = 2BC/N`, `N = (A+D)²+(B+C)²`.

## What is and isn't provable (verified directly, against the literature)

The convergence-basin claim sometimes paraphrased as "every Bell-diagonal state with
`λ₀₀ > 1/2` converges to `|Φ⁺⟩`" (Macchiavello, Phys. Lett. A 246, 385 (1998)) is an
**asymptotic** statement whose orbit is **not monotone**: direct iteration of
`(3/5, 0, 0, 2/5)` (with `λ₀₀ = 3/5 > 1/2`) *decreases* on the first step
(`3/5 → 13/25`) before climbing to `1`. We therefore make precise:

* the map's **structural invariants** — normalization (`dejmps_normalization`),
  nonnegativity, the pure-target fixed point (`dejmps_fixed_point`);
* a **clean sub-basin with monotone single-step increase** — the phase-flip-only
  family `D = 0` (`dejmps_increase_phaseFlipOnly`), complementing the shipped Werner
  sub-basin;
* the **non-monotonicity witness** `dejmps_single_step_can_decrease`, showing
  `λ₀₀ > 1/2` does NOT guarantee a single-step increase.

The full asymptotic convergence on the entire `λ₀₀ > 1/2` basin rests on Macchiavello's
non-monotone (Lyapunov-style) argument and is cited, not formalized.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- DEJMPS output `B' = (B²+C²)/N`. -/
noncomputable def dejmpsOutB (A B C D : ℝ) : ℝ := (B ^ 2 + C ^ 2) / dejmpsNorm A B C D

/-- DEJMPS output `C' = 2AD/N` (cross term). -/
noncomputable def dejmpsOutC (A B C D : ℝ) : ℝ := (2 * A * D) / dejmpsNorm A B C D

/-- DEJMPS output `D' = 2BC/N` (cross term). -/
noncomputable def dejmpsOutD (A B C D : ℝ) : ℝ := (2 * B * C) / dejmpsNorm A B C D

/-- **The DEJMPS map preserves normalization** (state → state): the four outputs sum
to `1` whenever the normalizer is nonzero. -/
theorem dejmps_normalization (A B C D : ℝ) (hN : dejmpsNorm A B C D ≠ 0) :
    dejmpsOutA A B C D + dejmpsOutB A B C D + dejmpsOutC A B C D + dejmpsOutD A B C D = 1 := by
  unfold dejmpsOutA dejmpsOutB dejmpsOutC dejmpsOutD dejmpsNorm at *
  field_simp at hN ⊢
  ring

/-- The target-fidelity output is nonnegative (the numerator `A²+D²` and the
normalizer are both nonnegative). -/
theorem dejmpsOutA_nonneg (A B C D : ℝ) : 0 ≤ dejmpsOutA A B C D := by
  unfold dejmpsOutA dejmpsNorm
  positivity

/-- The cross output `C' = 2AD/N` is nonnegative for a physical (nonnegative) input. -/
theorem dejmpsOutC_nonneg {A B C D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ dejmpsOutC A B C D := by
  unfold dejmpsOutC dejmpsNorm
  positivity

/-- **The pure target `|Φ⁺⟩` is a fixed point** of the DEJMPS map. -/
theorem dejmps_fixed_point :
    dejmpsOutA 1 0 0 0 = 1 ∧ dejmpsOutB 1 0 0 0 = 0
      ∧ dejmpsOutC 1 0 0 0 = 0 ∧ dejmpsOutD 1 0 0 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [dejmpsOutA, dejmpsOutB, dejmpsOutC, dejmpsOutD, dejmpsNorm]

/-- **Monotone single-step increase on the phase-flip-only sub-basin** `D = 0`: for a
Bell-diagonal state with no `Y`-error and `λ₀₀ = A ∈ (1/2, 1)`, DEJMPS strictly
increases the target fidelity. (Complements the shipped Werner sub-basin.) -/
theorem dejmps_increase_phaseFlipOnly {A B C : ℝ} (hsum : A + B + C = 1)
    (hA : 1 / 2 < A) (hA1 : A < 1) : A < dejmpsOutA A B C 0 := by
  have hBC : B + C = 1 - A := by linarith
  have hN : 0 < dejmpsNorm A B C 0 := by
    unfold dejmpsNorm; rw [hBC]; nlinarith [hA, hA1]
  unfold dejmpsOutA dejmpsNorm at *
  rw [lt_div_iff₀ hN, hBC]
  nlinarith [mul_pos (mul_pos (show (0:ℝ) < A by linarith) (show (0:ℝ) < 2 * A - 1 by linarith))
    (show (0:ℝ) < 1 - A by linarith)]

/-- **Non-monotonicity witness:** `λ₀₀ = 3/5 > 1/2` does NOT guarantee a single-step
increase — DEJMPS sends `(3/5, 0, 0, 2/5)` to `λ₀₀' = 13/25 < 3/5`. (The orbit still
converges to `1` asymptotically; the single step is not monotone.) -/
theorem dejmps_single_step_can_decrease : dejmpsOutA (3 / 5) 0 0 (2 / 5) < 3 / 5 := by
  simp only [dejmpsOutA, dejmpsNorm]
  norm_num

/-! ## The diagonal-pairing correction is load-bearing (Wave 6AH.6)

The shipped DEJMPS theorems use the symmetric **Werner** input `(F, (1−F)/3, (1−F)/3, (1−F)/3)`,
on which `B = D` so the corrected diagonal pairing `A²+D²` and the naive adjacent pairing `A²+B²`
*coincide* — no theorem there witnesses the correction. The lemmas below close that gap on an
**asymmetric** Bell-diagonal input where `B ≠ D`. -/

/-- The *naive* (incorrect) adjacent-pairing target output `(A²+B²)/N`, for contrast with the
corrected diagonal pairing `dejmpsOutA = (A²+D²)/N`. -/
noncomputable def dejmpsOutA_naive (A B C D : ℝ) : ℝ := (A ^ 2 + B ^ 2) / dejmpsNorm A B C D

/-- **The two pairings differ on an asymmetric input.** On `(1/2, 3/10, 1/10, 1/10)` — a normalized
Bell-diagonal state (`1/2+3/10+1/10+1/10 = 1`) with `B = 3/10 ≠ 1/10 = D`, so *not* Werner — the
corrected diagonal pairing gives `A' = 1/2` while the naive adjacent pairing gives `17/26 ≠ 1/2`.
The `(00,11)=(I,Y)` pairing choice is therefore load-bearing, not a vacuous relabeling. -/
theorem dejmps_diagonal_pairing_distinguishes :
    dejmpsOutA (1 / 2) (3 / 10) (1 / 10) (1 / 10) = 1 / 2
      ∧ dejmpsOutA_naive (1 / 2) (3 / 10) (1 / 10) (1 / 10) = 17 / 26 := by
  constructor <;> simp only [dejmpsOutA, dejmpsOutA_naive, dejmpsNorm] <;> norm_num

/-- **Only the diagonal pairing yields a valid state.** On the same asymmetric input the four DEJMPS
outputs with the corrected diagonal pairing sum to `1` (a normalized Bell-diagonal state), whereas
substituting the naive adjacent pairing breaks normalization (the sum `≠ 1`). This is the physical
reason the diagonal pairing is the correct one: the recurrence must map states to states. -/
theorem dejmps_naive_pairing_breaks_normalization :
    dejmpsOutA (1 / 2) (3 / 10) (1 / 10) (1 / 10) + dejmpsOutB (1 / 2) (3 / 10) (1 / 10) (1 / 10)
        + dejmpsOutC (1 / 2) (3 / 10) (1 / 10) (1 / 10) + dejmpsOutD (1 / 2) (3 / 10) (1 / 10) (1 / 10)
        = 1
      ∧ dejmpsOutA_naive (1 / 2) (3 / 10) (1 / 10) (1 / 10)
          + dejmpsOutB (1 / 2) (3 / 10) (1 / 10) (1 / 10)
          + dejmpsOutC (1 / 2) (3 / 10) (1 / 10) (1 / 10)
          + dejmpsOutD (1 / 2) (3 / 10) (1 / 10) (1 / 10) ≠ 1 := by
  constructor <;>
    simp only [dejmpsOutA, dejmpsOutA_naive, dejmpsOutB, dejmpsOutC, dejmpsOutD, dejmpsNorm] <;>
    norm_num

end SKEFTHawking.QuantumNetwork
