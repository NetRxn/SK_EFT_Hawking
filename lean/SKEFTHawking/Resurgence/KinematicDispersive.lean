/-
Phase 6n Wave 1a.3 Path A — Stage 3 Lean lift (Session 12, 2026-05-05).

Closed-form kinematic-dispersive coefficient sequence and the geometric-rate
1/4 theorem. Lifts the Python Stage-3 result
(`src/resurgence/bdg_self_energy.py:gamma_n_kinematic_dispersive_closed_form`)
to Lean.

**Substantive content.**

The kinematic NLO+ dispersive coefficient sequence at T = 0 is

  γ_n^(kin-disp) / γ_1 = (-1)^(n-1) · C(2(n-1), n-1) / 16^(n-1)

derived from evaluating the LO Beliaev rate Γ_Bel = γ_1 · c_s · ξ⁴ · k⁵
against the full Bogoliubov dispersion ω_Bog = c_s k √(1+(ξk/2)²) instead
of the linear approximation. The ratio sequence
  ρ_k := γ_{k+1}^(kin-disp) / γ_1 = (-1)^k · C(2k, k) / 16^k
has the **central binomial bound** |C(2k, k)| ≤ 4^k (Mathlib
`Nat.choose_le_two_pow` specialized to `n = 2k`), giving
|ρ_k| ≤ 4^k / 16^k = 1/4^k.

The kinematic-dispersive sequence is therefore **`IsGeometric ρ 1 (1/4)`**
— geometric with rate 1/4 and convergence radius 4 in the gradient
variable g = (ξk)², equivalently radius ξk = 2 (i.e., k = 2 c_s/ξ =
2 · Λ_UV).

This is the load-bearing Lean-level closure of Path B's qualitative
"geometric not Gevrey-1" verdict (Session 5) into a precise
quantitative theorem on the kinematic piece. The full γ_n verdict
includes loop-piece contributions (Beliaev-Galitskii 1959 2-loop
self-energy at order (ξk)^6) deferred to Stage 4.

**Cross-references:**
- Python Stage 3: `src/resurgence/bdg_self_energy.py` (Session 11).
- Path B verdict: `temporary/working-docs/phase6n/6n_alpha_3_VERDICT.md`.
- Stage 3 close: `temporary/working-docs/phase6n/wave_1a_3_path_A_stage3_close.md`.
- Phase 6n roadmap Wave 1a sub-wave status (Stage 3 SHIPPED Session 11).

**Discipline notes (preemptive-strengthening checklist applied):**
- Bundle redundancy (P2): each theorem expresses a distinct fact
  (closed-form values vs central-binomial bound vs geometric-rate
  conclusion vs cross-bridge to Borel infrastructure).
- Quantitative connection: `kinDispRatio_abs_le_quarter_pow` ties the
  closed-form coefficient ratio to the load-bearing 1/4 numerical bound.
- Cross-module bridge (P6): `kinDispSeq_isGeometric` and
  `kinDispSeq_isGevrey1_trivially` invoke `IsGeometric` and `IsGevrey1`
  (Basic.lean) respectively, in proof bodies.
- Trivial-discharge check (P3-P5): `kinDispRatio_abs_le_quarter_pow`
  uses `Nat.choose_le_two_pow` substantively; the geometric-bound
  conclusion is not vacuously true.
- Defining-the-conclusion check: `kinDispRatio` is the closed-form
  ratio (substantively defined; not engineered to make the geometric
  bound trivial).
-/
import SKEFTHawking.Resurgence.Basic
import SKEFTHawking.Resurgence.BorelAction
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace SKEFTHawking.Resurgence

/--
**Closed-form ratio `γ_{k+1}^(kin-disp) / γ_1 = (-1)^k · C(2k, k) / 16^k`**
in ℚ.

Indexed from `k = 0`; `kinDispRatio 0 = 1` (LO Beliaev = γ_1 itself);
`kinDispRatio 1 = -1/8`; `kinDispRatio 2 = 3/128`; etc.

Derivation: Bogoliubov inverse-dispersion expansion
  [1 + (ξk/2)²]^(-1/2) = Σ_{k≥0} (-1)^k · C(2k, k) / 16^k · (ξk)^(2k)
combined with `Γ/ω = γ_1 (ξk)^4 · (ω_lin/ω_Bog)`. See Python
`gamma_n_kinematic_dispersive_closed_form` for cross-validation.
-/
def kinDispRatio (k : ℕ) : ℚ :=
  ((-1 : ℤ) ^ k * (Nat.choose (2 * k) k : ℤ) : ℚ) / (16 : ℚ) ^ k

/--
**Real-valued kinematic-dispersive ratio sequence.**

The float counterpart for use in `IsGeometric` and `IsGevrey1`.
-/
noncomputable def kinDispSeq : ℕ → ℝ :=
  fun k => (kinDispRatio k : ℝ)

/-- Sanity: `kinDispRatio 0 = 1`. -/
@[simp] theorem kinDispRatio_zero : kinDispRatio 0 = 1 := by
  unfold kinDispRatio; simp

/-- Sanity: `kinDispRatio 1 = -1/8` (the Stage-3 anchor γ_2/γ_1). -/
theorem kinDispRatio_one : kinDispRatio 1 = -1 / 8 := by
  unfold kinDispRatio
  norm_num [Nat.choose]

/-- Sanity: `kinDispRatio 2 = 3/128`. -/
theorem kinDispRatio_two : kinDispRatio 2 = 3 / 128 := by
  unfold kinDispRatio
  norm_num [Nat.choose]

/-- Sanity: `kinDispRatio 3 = -5/1024`. -/
theorem kinDispRatio_three : kinDispRatio 3 = -5 / 1024 := by
  unfold kinDispRatio
  norm_num [Nat.choose]

/--
**Auxiliary: the central binomial bound `C(2k, k) ≤ 4^k` in ℕ.**

Direct specialization of `Nat.choose_le_two_pow` to `n := 2k` plus
the identity `2^(2k) = 4^k`. Substantive use in
`kinDispRatio_abs_le_quarter_pow`.
-/
theorem central_binomial_le_four_pow (k : ℕ) :
    Nat.choose (2 * k) k ≤ 4 ^ k := by
  have h := Nat.choose_le_two_pow (n := 2 * k) (k := k)
  -- h : Nat.choose (2 * k) k ≤ 2 ^ (2 * k)
  have h_pow_eq : (2 : ℕ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]; norm_num
  rw [h_pow_eq] at h
  exact h

/--
**Central binomial bound on the kinematic-dispersive ratio:
`|kinDispRatio k| ≤ (1/4)^k` in ℝ.**

Substantive content: uses the central binomial coefficient bound
`C(2k, k) ≤ 4^k` (Mathlib `Nat.choose_le_two_pow` via the auxiliary
`central_binomial_le_four_pow`), combined with the |(-1)^k| = 1 sign
factor and the 16^k denominator.

This is the load-bearing inequality establishing geometric convergence
of the kinematic-dispersive sequence with rate 1/4.
-/
theorem kinDispRatio_abs_le_quarter_pow (k : ℕ) :
    |(kinDispRatio k : ℝ)| ≤ (1 / 4) ^ k := by
  unfold kinDispRatio
  push_cast
  -- Goal: |(-1)^k * (C(2k,k) : ℝ) / 16^k| ≤ (1/4)^k
  have h16_pos : (0 : ℝ) < (16 : ℝ) ^ k := by positivity
  have h4_pos : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  rw [abs_div, abs_of_pos h16_pos]
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by exact_mod_cast Nat.zero_le _ :
        (0 : ℝ) ≤ (Nat.choose (2 * k) k : ℝ))]
  -- Goal: (C(2k,k) : ℝ) / 16^k ≤ (1/4)^k
  have h_choose_le : (Nat.choose (2 * k) k : ℝ) ≤ (4 : ℝ) ^ k := by
    exact_mod_cast central_binomial_le_four_pow k
  -- (1/4)^k = 1/4^k
  rw [div_pow, one_pow]
  rw [div_le_div_iff₀ h16_pos h4_pos]
  rw [one_mul]
  -- Goal: (C(2k,k) : ℝ) * 4^k ≤ 16^k
  have h16_eq : (16 : ℝ) ^ k = (4 : ℝ) ^ k * (4 : ℝ) ^ k := by
    have h16 : (16 : ℝ) = 4 * 4 := by norm_num
    rw [h16, mul_pow]
  rw [h16_eq]
  exact mul_le_mul_of_nonneg_right h_choose_le h4_pos.le

/--
**The kinematic-dispersive sequence is geometric with rate 1/4.**

Substantive structural theorem: `kinDispSeq` (the real-valued
kinematic-dispersive ratio sequence γ_{k+1}^(kin-disp) / γ_1) satisfies
`IsGeometric kinDispSeq 1 (1/4)` — i.e., `|kinDispSeq k| ≤ 1 · (1/4)^k`
for all `k`, with rate `r = 1/4 ∈ (0, 1)`.

This is the **load-bearing closure** of Path B's qualitative
"geometric not Gevrey-1" verdict (Session 5) into a precise
quantitative result on the kinematic piece. The convergence radius
in the gradient variable g = (ξk)² is 1/r = 4, equivalently ξk = 2,
i.e., k = 2 · Λ_UV. The full γ_n verdict pending Stage 4 loop-piece
contributions.
-/
theorem kinDispSeq_isGeometric :
    IsGeometric kinDispSeq 1 (1 / 4) := by
  refine ⟨zero_le_one, by norm_num, by norm_num, ?_⟩
  intro k
  unfold kinDispSeq
  rw [one_mul]
  exact kinDispRatio_abs_le_quarter_pow k

/--
**The kinematic-dispersive sequence's Borel transform is bounded by
`(1/4)^k / k!`.**

Direct consequence of `borelTransform_bounded_of_isGeometric` applied to
`kinDispSeq_isGeometric`: the Borel transform decays super-geometrically.
The Borel-plane series for `kinDispSeq` is therefore *entire* (no Borel
singularity at any finite distance), confirming that the kinematic
piece carries **no resurgence-theoretic transseries content** — the
sequence is Borel-summable and the perturbative gradient expansion
captures all the kinematic-dispersive content without non-perturbative
corrections from the kinematic side.

Loop-piece transseries content (Stage 4) remains an open question.
-/
theorem kinDispSeq_borelTransform_bounded :
    ∀ k : ℕ, |borelTransform kinDispSeq k| ≤ 1 * (1 / 4) ^ k / k.factorial :=
  borelTransform_bounded_of_isGeometric kinDispSeq_isGeometric

/--
**Cross-bridge: the kinematic-dispersive sequence is also Gevrey-1
with Borel action `A = 1` (degenerate / trivial Gevrey-1 witness).**

A geometric sequence with rate `r ∈ (0, 1)` is bounded by `1`, hence
also bounded by `n!/A^n` for any `A > 0` (since `n!/A^n ≥ 1` for `n ≥ 0`
when `A ≤ 1`, and the bound becomes loose at large `n`). We witness
this with `A = 1` to encode the structural distinction:

The kinematic piece is geometric (Borel transform entire), but a
*degenerate* Gevrey-1 witness still applies — emphasizing that the full
γ_n verdict (kinematic + loop pieces) requires the loop-piece (Stage 4)
contribution to determine whether the *full* sequence has finite Borel
action (genuine Gevrey-1 with transseries content) or remains geometric
(no transseries content from the loop side either).
-/
theorem kinDispSeq_isGevrey1_trivially :
    IsGevrey1 kinDispSeq 1 := by
  refine ⟨one_pos, ?_⟩
  intro k
  -- |kinDispSeq k| ≤ (1/4)^k ≤ 1 ≤ k! / 1^k = k!
  have h1 : |kinDispSeq k| ≤ (1 / 4) ^ k := by
    have h := kinDispSeq_isGeometric.bound k
    rwa [one_mul] at h
  have h2 : ((1 : ℝ) / 4) ^ k ≤ 1 :=
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 : ℝ) / 4 ≤ 1)
  have h3 : (1 : ℝ) ≤ (k.factorial : ℝ) / 1 ^ k := by
    rw [one_pow, div_one]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_pos k).ne'
  linarith

/--
**Closure summary theorem (Stage 3 Lean lift, Session 12).**

Bundles the four substantive load-bearing facts about the
kinematic-dispersive coefficient sequence:

  1. Closed-form value at k = 0: `kinDispRatio 0 = 1` (LO Beliaev anchor).
  2. Closed-form value at k = 1: `kinDispRatio 1 = -1/8` (Stage-3 NLO anchor).
  3. Geometric-rate-1/4 bound: `IsGeometric kinDispSeq 1 (1/4)`.
  4. Borel-transform bound (decays super-geometrically;
     equivalently, the Borel transform of the kinematic sequence
     is entire — no resurgence content from the kinematic piece).

This is the Lean-level closure of the Path B "geometric, not Gevrey-1"
verdict on the kinematic piece.
-/
theorem kinDispSeq_stage3_closure :
    kinDispRatio 0 = 1 ∧
    kinDispRatio 1 = -1 / 8 ∧
    IsGeometric kinDispSeq 1 (1 / 4) ∧
    (∀ k : ℕ, |borelTransform kinDispSeq k| ≤ 1 * (1 / 4) ^ k / k.factorial) :=
  ⟨kinDispRatio_zero, kinDispRatio_one, kinDispSeq_isGeometric,
   kinDispSeq_borelTransform_bounded⟩

end SKEFTHawking.Resurgence
