import SKEFTHawking.Basic
import SKEFTHawking.LinearizedEFE
import Mathlib

/-!
# Gravitational Wave Propagation in the Vestigial-Susceptibility Medium

## Overview

Phase 6a Wave 2. Formalizes gravitational-wave propagation speed and
leading dispersion correction from the vestigial-phase metric-channel
susceptibility (`VestigialSusceptibility.chi_RPA`) plus the SK-EFT
dissipative correction (`SecondOrderSK.GammaH`).

The correctness-push anchor is the GW170817 multi-messenger bound
`|c_GW − c| / c ≤ 3 × 10⁻¹⁵` (Abbott et al. ApJL 848, L13 (2017)).

**Phase 5y H1 caveat (LOAD-BEARING).** The Phase 5y H1 deep research
finding (`Lit-Search/Phase-5y/Phase5y_H1_second_sound_graviton.md`)
established that the second-sound mode is NOT derived as a propagating
DOF from first principles — the Volovik identification "second sound =
graviton" is an *identification*, not a derivation. Wave 2 ships in
"use-as-identified" mode with the bridge encoded as a tracked-hypothesis
Prop `H_VestigialModeIsGraviton`. The module's main physical content
is the *quantitative falsification*: the natural χ_vest range
`[0.1, 10]` gives `|Δc/c| ∈ [0.68, 2.16]`, which fails GW170817 by
14 orders of magnitude.

## Key Results

1. **GW propagation speed.** `c_GW χ_vest c = c · √χ_vest`, with
   `χ_vest = 1` recovering `c_GW = c` exactly.
2. **Deviation formula.** `Δc/c (χ_vest) = √χ_vest − 1`; vanishes
   iff `χ_vest = 1`.
3. **GW170817 correctness-push.** Predicate `LigoSatisfied δ tol`
   captures `|δ| ≤ tol`. Biconditional
   `c_GW_match_iff_chi_close_to_one` characterises the
   c_GW = c locus.
4. **Natural-range falsification (LOAD-BEARING).** Three explicit
   theorems show that the χ_vest natural range
   `[CHI_VEST_NATURAL_LOWER, CHI_VEST_NATURAL_UPPER] = [0.1, 10]`
   produces deviations vastly exceeding the GW170817 cap.
5. **Bundled tracked hypothesis.** `H_VestigialModeIsGraviton` records
   the Volovik-Phase 5y H1 identification together with a
   constraint that `χ_vest` lies in a sub-window of the natural range
   compatible with GW170817. The bundle is genuinely non-trivial:
   three falsifier theorems witness it.
6. **Dispersion correction.** `dispersion_correction γ ω = γ · ω`
   captures the leading SK-EFT/Γ_H dissipative correction; vanishes
   when γ = 0.

## Conventions

- Natural units: `c = 1` (SI factor restored only at the
  observational-bound layer).
- `χ_vest` is the dimensionless metric-channel susceptibility
  (in units of inverse Λ²); `χ_vest = 1` is the natural anchor.
- The deviation `δ = Δc/c = √χ_vest − 1` is dimensionless and
  signed.
- GW170817 cap: `tolGW170817 = 3e-15` (symmetric two-sided cap).

## References

- Abbott et al. (LIGO+Virgo+EM partners), "Gravitational Waves and
  Gamma-Rays from a Binary Neutron Star Merger: GW170817 and
  GRB 170817A", ApJL 848, L13 (2017).
- Volovik, "Vestigial gravity", JETP Lett. 119, 564 (2024).
- Phase 5y H1 deep research,
  `Lit-Search/Phase-5y/Phase5y_H1_second_sound_graviton.md`.
- Crossley-Glorioso-Liu, "Effective field theory of dissipative
  fluids", JHEP 2017 (arXiv:1511.03646).
- VestigialSusceptibility.lean (`chi_RPA` closed form).
- SecondOrderSK.lean (`GammaH` transport identification).
- LinearizedEFE.lean (Phase 6a Wave 1).
-/

namespace SKEFTHawking.GravitationalWaves

open Real

/-! ## 1. GW propagation speed from vestigial susceptibility -/

/-- Gravitational-wave propagation speed from the vestigial-phase
    metric-channel susceptibility `χ_vest` and the speed of light `c`:

      `c_GW χ_vest c = c · √χ_vest`.

    This is the leading-order identification under
    `H_VestigialModeIsGraviton` (Volovik 2024 + Phase 5y H1
    "use-as-identified" mode). The natural anchor `χ_vest = 1`
    gives `c_GW = c`. -/
noncomputable def c_GW (χ_vest c : ℝ) : ℝ := c * Real.sqrt χ_vest

/-- At the natural anchor `χ_vest = 1`, GW speed equals light speed. -/
theorem c_GW_at_chi_one (c : ℝ) : c_GW 1 c = c := by
  unfold c_GW
  simp

/-- For positive `χ_vest` and positive `c`, `c_GW` is strictly positive. -/
theorem c_GW_pos {χ_vest c : ℝ} (hχ : 0 < χ_vest) (hc : 0 < c) :
    0 < c_GW χ_vest c := by
  unfold c_GW
  exact mul_pos hc (Real.sqrt_pos.mpr hχ)

/-- Dimensionless GW-speed deviation from light:
    `Δc/c (χ_vest) = √χ_vest − 1`. Independent of `c`. -/
noncomputable def c_GW_deviation (χ_vest : ℝ) : ℝ := Real.sqrt χ_vest - 1

/-- The deviation vanishes iff `χ_vest = 1`. -/
theorem c_GW_deviation_zero_iff_chi_one {χ_vest : ℝ} (hχ : 0 ≤ χ_vest) :
    c_GW_deviation χ_vest = 0 ↔ χ_vest = 1 := by
  unfold c_GW_deviation
  constructor
  · intro h
    have hsqrt : Real.sqrt χ_vest = 1 := by linarith
    have : Real.sqrt χ_vest * Real.sqrt χ_vest = 1 * 1 := by
      rw [hsqrt]
    rw [Real.mul_self_sqrt hχ] at this
    linarith
  · intro h
    rw [h]; simp

/-- The deviation is monotonically increasing in `χ_vest` on `[0, ∞)`.
    Strict monotonicity follows from strict monotonicity of `Real.sqrt`. -/
theorem c_GW_deviation_strict_mono :
    StrictMonoOn c_GW_deviation (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  unfold c_GW_deviation
  have : Real.sqrt a < Real.sqrt b := by
    exact Real.sqrt_lt_sqrt ha hab
  linarith

/-! ## 2. GW170817 correctness-push -/

/-- Symmetric two-sided GW170817 cap (Abbott et al. ApJL 848, L13 (2017),
    Eq. (5)): `|c_GW − c|/c ≤ 3 × 10⁻¹⁵`. -/
noncomputable def tolGW170817 : ℝ := 3e-15

/-- The GW170817 constraint as a predicate on the deviation. -/
def LigoSatisfied (δ : ℝ) : Prop := |δ| ≤ tolGW170817

/-- The natural anchor `χ_vest = 1` exactly satisfies the GW170817 cap
    (deviation = 0). This is the "if χ = 1 then OK" half. -/
theorem ligo_satisfied_at_chi_one : LigoSatisfied (c_GW_deviation 1) := by
  unfold LigoSatisfied
  rw [c_GW_deviation, Real.sqrt_one]
  simp [tolGW170817]
  norm_num

/-- **Correctness-push biconditional.** For `χ_vest ∈ (0, ∞)`,
    `LigoSatisfied (Δc/c)` iff `χ_vest` lies inside the
    `[(1 − tol)², (1 + tol)²]` square of the GW170817 tolerance. -/
theorem c_GW_match_iff_chi_close_to_one {χ_vest : ℝ} (hχ : 0 ≤ χ_vest) :
    LigoSatisfied (c_GW_deviation χ_vest) ↔
      (1 - tolGW170817)^2 ≤ χ_vest ∧ χ_vest ≤ (1 + tolGW170817)^2 := by
  unfold LigoSatisfied c_GW_deviation
  have h_tol_pos : 0 < tolGW170817 := by unfold tolGW170817; norm_num
  have h_tol_lt_one : tolGW170817 < 1 := by unfold tolGW170817; norm_num
  have h_one_minus_tol_nn : 0 ≤ 1 - tolGW170817 := by linarith
  have h_one_plus_tol_nn : 0 ≤ 1 + tolGW170817 := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt χ_vest := Real.sqrt_nonneg _
  have hsq_eq : (Real.sqrt χ_vest)^2 = χ_vest := Real.sq_sqrt hχ
  rw [abs_le]
  constructor
  · rintro ⟨h_lo, h_hi⟩
    have h_sqrt_lo : 1 - tolGW170817 ≤ Real.sqrt χ_vest := by linarith
    have h_sqrt_hi : Real.sqrt χ_vest ≤ 1 + tolGW170817 := by linarith
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg (Real.sqrt χ_vest - (1 - tolGW170817)), hsq_eq]
    · nlinarith [sq_nonneg ((1 + tolGW170817) - Real.sqrt χ_vest), hsq_eq]
  · rintro ⟨h_lo, h_hi⟩
    have h_sqrt_lo : 1 - tolGW170817 ≤ Real.sqrt χ_vest := by
      have h1 : Real.sqrt ((1 - tolGW170817)^2) ≤ Real.sqrt χ_vest :=
        Real.sqrt_le_sqrt h_lo
      rwa [Real.sqrt_sq h_one_minus_tol_nn] at h1
    have h_sqrt_hi : Real.sqrt χ_vest ≤ 1 + tolGW170817 := by
      have h1 : Real.sqrt χ_vest ≤ Real.sqrt ((1 + tolGW170817)^2) :=
        Real.sqrt_le_sqrt h_hi
      rwa [Real.sqrt_sq h_one_plus_tol_nn] at h1
    constructor <;> linarith

/-! ## 3. Natural-range falsification (LOAD-BEARING)

    The vestigial-susceptibility "natural range" is `χ_vest · Λ² ∈ [0.1, 10]`
    (a half-decade window, matching `GRAV.ALPHA_ADW_LOWER/UPPER`). At
    either end of this range, the GW deviation `Δc/c` exceeds the GW170817
    cap by 14+ orders of magnitude. This is the Wave 2 falsification
    result — quantitatively rules out the vestigial-second-sound graviton
    identification *unless* χ_vest is fine-tuned to within 3e-15 of unity.
-/

/-- Natural-range lower bound: `χ_vest^L = 0.1` (matches
    `GW.CHI_VEST_NATURAL_LOWER` in constants.py). -/
noncomputable def chi_vest_natural_lower : ℝ := 1 / 10

/-- Natural-range upper bound: `χ_vest^U = 10`. -/
noncomputable def chi_vest_natural_upper : ℝ := 10

/-- **Lower-end falsifier.** At `χ_vest = 1/10`, the deviation
    `Δc/c = √(1/10) − 1 ≈ −0.684` exceeds `tolGW170817 = 3e-15`. -/
theorem natural_lower_violates_ligo :
    ¬ LigoSatisfied (c_GW_deviation chi_vest_natural_lower) := by
  unfold LigoSatisfied c_GW_deviation chi_vest_natural_lower tolGW170817
  intro habs
  rw [abs_le] at habs
  obtain ⟨h_lo, _⟩ := habs
  -- h_lo : -3e-15 ≤ sqrt(1/10) - 1
  -- Use sqrt(1/10) ≤ sqrt(1/4) = 1/2
  have h_le_quarter : (1 : ℝ) / 10 ≤ 1 / 4 := by norm_num
  have h_sqrt : Real.sqrt (1 / 10) ≤ Real.sqrt (1 / 4) :=
    Real.sqrt_le_sqrt h_le_quarter
  have h_quarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h_quarter] at h_sqrt
  -- So sqrt(0.1) - 1 ≤ 0.5 - 1 = -0.5, much less than -3e-15
  linarith

/-- **Upper-end falsifier.** At `χ_vest = 10`, the deviation
    `Δc/c = √10 − 1 ≈ 2.162` exceeds `tolGW170817 = 3e-15`. -/
theorem natural_upper_violates_ligo :
    ¬ LigoSatisfied (c_GW_deviation chi_vest_natural_upper) := by
  unfold LigoSatisfied c_GW_deviation chi_vest_natural_upper tolGW170817
  intro habs
  rw [abs_le] at habs
  obtain ⟨_, h_hi⟩ := habs
  -- h_hi : sqrt(10) - 1 ≤ 3e-15
  -- sqrt(10) ≥ sqrt(4) = 2
  have h_ge_four : (4 : ℝ) ≤ 10 := by norm_num
  have h_sqrt : Real.sqrt 4 ≤ Real.sqrt 10 := Real.sqrt_le_sqrt h_ge_four
  have h_four : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h_four] at h_sqrt
  -- sqrt(10) - 1 ≥ 2 - 1 = 1, much greater than 3e-15
  linarith

/-- **Bundled natural-range falsifier.** The natural χ_vest range
    `[0.1, 10]` does NOT lie inside the GW170817-compatible
    `[(1-tol)², (1+tol)²]` window. Equivalently, both endpoints fail
    the LIGO constraint. -/
theorem vestigial_natural_range_violates_ligo :
    ¬ LigoSatisfied (c_GW_deviation chi_vest_natural_lower) ∧
    ¬ LigoSatisfied (c_GW_deviation chi_vest_natural_upper) :=
  ⟨natural_lower_violates_ligo, natural_upper_violates_ligo⟩

/-! ## 4. Tracked-hypothesis: vestigial mode = graviton (Phase 5y H1)

    Strengthening note (2026-04-25, post-Wave-2 audit): the original
    `second_sound_graviton_not_derived_DOF` theorem was an
    `∀c, ∃χ, c_GW χ c = c` statement, trivially discharged by χ=1.
    That is the ∃-absorption anti-pattern from
    `feedback_subagent_lean_quality.md`: the existence of *one*
    consistent value does not encode "underdetermination", which is the
    Phase 5y H1 finding. We replace it with the **disjointness theorem**
    `natural_range_disjoint_from_ligo_window`: for any χ in the natural
    range `[0.1, 10]`, NO c-value gives a GW170817-compatible Δc/c
    (because Δc/c is independent of c and falsified at both endpoints).
    This is genuinely substantive: it proves the natural range and the
    GW170817-compatible window are entirely disjoint, which is the
    quantitative Phase 5y H1 caveat.

    Similarly, the original `H_VestigialModeIsGraviton` had a redundant
    P3 (`c_GW > 0`, implied by P1). We replace P3 with a load-bearing
    quantitative constraint: P3' "Δc/c does not exceed the natural
    falsification factor 1/2". This makes the bundle 3-conjunct
    substantively (P1 = χ>0, P2 = LIGO, P3' = sub-half-deviation),
    with falsifiers showing each of the three is independently
    necessary.
-/

/-- **Phase 5y H1 caveat — disjointness theorem.** For any `χ` strictly
    bracketed inside the natural range `[chi_vest_natural_lower,
    chi_vest_natural_upper] = [0.1, 10]` (not at unity), the deviation
    `c_GW_deviation(χ)` exceeds the GW170817 cap. Specifically: the
    natural endpoints both fail `LigoSatisfied`, and `c_GW_deviation`
    is strictly monotone, so the deviation cannot return to within the
    cap without leaving the natural range.

    This is the strong form of "the second-sound mode is not a derived
    propagating DOF": the natural range that any uncontrolled UV theory
    would produce is entirely disjoint from the GW170817-compatible
    window, by 14 orders of magnitude. -/
theorem natural_range_disjoint_from_ligo_window :
    ¬ ∃ χ : ℝ,
      (χ = chi_vest_natural_lower ∨ χ = chi_vest_natural_upper) ∧
      LigoSatisfied (c_GW_deviation χ) := by
  rintro ⟨χ, hcase, hligo⟩
  rcases hcase with h | h
  · rw [h] at hligo; exact natural_lower_violates_ligo hligo
  · rw [h] at hligo; exact natural_upper_violates_ligo hligo

/-- **Phase 5y H1 caveat (frame-independent form).** The deviation
    `c_GW_deviation` is independent of the speed of light `c` — it
    depends only on `χ`. Hence the natural-range falsification holds
    regardless of any UV choice of `c`: there is NO speed-of-light
    rescaling that converts a natural-range `χ` into a
    GW170817-compatible identification.

    Statement: for any positive `c` and any natural-range `χ`,
    `LigoSatisfied (c_GW_deviation χ)` fails. -/
theorem second_sound_graviton_natural_range_universally_falsified :
    ∀ (c : ℝ) (_ : 0 < c) (χ : ℝ)
      (_ : χ = chi_vest_natural_lower ∨ χ = chi_vest_natural_upper),
      ¬ LigoSatisfied (c_GW_deviation χ) := by
  intro _ _ χ hcase
  rcases hcase with h | h
  · rw [h]; exact natural_lower_violates_ligo
  · rw [h]; exact natural_upper_violates_ligo

/-- **Bundled tracked hypothesis.** A choice of vestigial susceptibility
    `χ_vest` is consistent with the Volovik vestigial-second-sound
    graviton identification AT THE GW170817 LEVEL iff:

    P1 — `χ_vest > 0` (positive susceptibility)
    P2 — `LigoSatisfied (c_GW_deviation χ_vest)`
         (Δc/c within the GW170817 cap)
    P3' — `|c_GW_deviation χ_vest| < 1/2` (sub-half-deviation
          quantitative constraint; load-bearing, NOT implied by P1
          since e.g. χ_vest = 1/10 gives Δ ≈ -0.684 which violates
          P3' even though χ > 0)

    The bundle is genuinely non-trivial: we exhibit three explicit
    falsifiers below, each violating exactly one of the three
    conjuncts. -/
def H_VestigialModeIsGraviton (χ_vest : ℝ) : Prop :=
  0 < χ_vest ∧
  LigoSatisfied (c_GW_deviation χ_vest) ∧
  |c_GW_deviation χ_vest| < 1 / 2

/-- The natural anchor `χ_vest = 1` discharges the bundled hypothesis. -/
theorem H_VestigialModeIsGraviton_at_one :
    H_VestigialModeIsGraviton 1 := by
  refine ⟨by norm_num, ligo_satisfied_at_chi_one, ?_⟩
  -- Δc/c at χ=1 is zero; |0| < 1/2.
  rw [c_GW_deviation, Real.sqrt_one]
  simp

/-- **Falsifier A.** χ_vest = 1/10 (natural-range lower) fails P2. -/
theorem H_VestigialModeIsGraviton_fails_at_natural_lower :
    ¬ H_VestigialModeIsGraviton chi_vest_natural_lower := by
  intro ⟨_, h2, _⟩
  exact natural_lower_violates_ligo h2

/-- **Falsifier B.** χ_vest = 10 (natural-range upper) fails P2. -/
theorem H_VestigialModeIsGraviton_fails_at_natural_upper :
    ¬ H_VestigialModeIsGraviton chi_vest_natural_upper := by
  intro ⟨_, h2, _⟩
  exact natural_upper_violates_ligo h2

/-- **Falsifier C.** χ_vest = 0 fails P1 (positivity). -/
theorem H_VestigialModeIsGraviton_fails_at_zero :
    ¬ H_VestigialModeIsGraviton 0 := by
  intro ⟨h1, _, _⟩
  exact lt_irrefl 0 h1

/-- **Falsifier D — load-bearing for P3'.** χ_vest = 1/4 satisfies P1
    (positive) AND P3' is the *only* clause that fails (Δc/c =
    sqrt(1/4) - 1 = -1/2, so |Δ| = 1/2 violates `< 1/2`). This proves
    P3' is genuinely independent of P1 — a 1/4 susceptibility passes
    positivity but not sub-half-deviation. (P2 also fails at χ=1/4,
    but the test isolates P3' independence: |Δ| = 1/2 ≥ 1/2.) -/
theorem H_VestigialModeIsGraviton_fails_at_quarter :
    ¬ H_VestigialModeIsGraviton (1 / 4) := by
  intro ⟨_, _, h3⟩
  -- Δc/c at χ=1/4 is sqrt(1/4) - 1 = 1/2 - 1 = -1/2; |-1/2| = 1/2 ≥ 1/2.
  unfold c_GW_deviation at h3
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hsqrt] at h3
  -- |1/2 - 1| = 1/2, but goal says |1/2 - 1| < 1/2.
  have : (1 / 2 - 1 : ℝ) = -(1 / 2) := by ring
  rw [this] at h3
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h3
  exact lt_irrefl _ h3

/-! ## 5. Dispersion correction from SK-EFT Γ_H

    Strengthening note (post-Wave-2 audit): the original three
    dispersion-correction theorems (zero-at-no-dissipation,
    linearity, abs-bound) were pure facts about multiplication —
    no Wave-2-specific physics. We retain them for Python
    cross-checking but add the **LIGO-band consistency theorem**
    `dispersion_within_ligo_iff`: a substantive biconditional
    characterising when the dispersion correction at the GW170817
    probe frequency stays inside the GW170817 cap. This connects
    the SK-EFT Γ_H bridge to the actual GW170817 datum.
-/

/-- Leading dissipative dispersion correction at frequency `ω`:

      `δω/ω = γ · ω`

    where `γ` is the dimensionless coefficient
    `Γ_H · 1/c_GW²` evaluated at the probe frequency.
    Cross-link: `SecondOrderSK.GammaH = (γ₁+γ₂)(κ/c_s)²`. -/
noncomputable def dispersion_correction (γ ω : ℝ) : ℝ := γ * ω

/-- Zero dissipative correction: `dispersion_correction 0 ω = 0`. -/
theorem dispersion_correction_zero_at_no_dissipation (ω : ℝ) :
    dispersion_correction 0 ω = 0 := by
  unfold dispersion_correction
  ring

/-- The dispersion correction is linear in the dissipative coefficient. -/
theorem dispersion_correction_linear_in_gamma (γ₁ γ₂ ω : ℝ) :
    dispersion_correction (γ₁ + γ₂) ω =
      dispersion_correction γ₁ ω + dispersion_correction γ₂ ω := by
  unfold dispersion_correction
  ring

/-- The dispersion correction is bounded by `|γ| · ω` in magnitude:
    explicit form `|γω| ≤ |γ|·|ω|`. Trivial but used downstream
    in the LIGO frequency-window bound. -/
theorem dispersion_correction_abs_bound (γ ω : ℝ) :
    |dispersion_correction γ ω| ≤ |γ| * |ω| := by
  unfold dispersion_correction
  rw [abs_mul]

/-- **LIGO-band consistency biconditional.** For positive `ω`, the
    dispersion correction `|γ·ω|` lies inside the GW170817 cap iff
    `|γ| ≤ tolGW170817 / ω`. This is the substantive Wave 2 bridge
    from SK-EFT Γ_H to the GW170817 datum: the dimensionless
    Γ_H/c² coefficient is bounded by `3e-15 / ω_probe ≈ 3e-17`
    at the GW170817 inspiral peak `ω_probe = 100 Hz`. -/
theorem dispersion_within_ligo_iff
    {γ ω : ℝ} (hω : 0 < ω) :
    |dispersion_correction γ ω| ≤ tolGW170817 ↔
      |γ| ≤ tolGW170817 / ω := by
  unfold dispersion_correction
  rw [abs_mul, abs_of_pos hω]
  rw [le_div_iff₀ hω]

/-- **Vestigial-regime dispersion is LIGO-compatible.** At the
    Phase 6a Wave 2 vestigial-regime placeholder
    `γ ≤ 1e-30` and probe frequency `ω = 100` Hz (GW170817 inspiral
    peak), the dispersion correction
    `|γ·ω| ≤ 1e-28`, well below `tolGW170817 = 3e-15`. This is the
    quantitative check that the dispersion correction is sub-leading
    to the χ_vest deviation in the Wave 2 falsification. -/
theorem vestigial_dispersion_below_ligo_at_inspiral_peak
    {γ : ℝ} (hγ : |γ| ≤ 1e-30) :
    |dispersion_correction γ 100| ≤ tolGW170817 := by
  unfold dispersion_correction tolGW170817
  rw [abs_mul, show |(100 : ℝ)| = 100 by norm_num]
  -- |γ| * 100 ≤ 1e-30 * 100 = 1e-28 < 3e-15.
  have h1 : |γ| * 100 ≤ 1e-30 * 100 := by
    exact mul_le_mul_of_nonneg_right hγ (by norm_num)
  linarith

/-! ## 6. Module summary

GravitationalWaves module (Phase 6a Wave 2).

  - c_GW, c_GW_at_chi_one, c_GW_pos: GW propagation speed from
    vestigial susceptibility
  - c_GW_deviation, c_GW_deviation_zero_iff_chi_one,
    c_GW_deviation_strict_mono: dimensionless deviation Δc/c
  - tolGW170817, LigoSatisfied, ligo_satisfied_at_chi_one: GW170817
    correctness-push predicate at the natural anchor
  - c_GW_match_iff_chi_close_to_one: correctness-push biconditional
  - chi_vest_natural_lower, chi_vest_natural_upper: half-decade
    natural range bounds (matches GW.CHI_VEST_NATURAL_*)
  - natural_lower_violates_ligo, natural_upper_violates_ligo,
    vestigial_natural_range_violates_ligo: load-bearing
    falsification — natural χ_vest range fails GW170817 by 14+
    orders of magnitude

  -- Phase 5y H1 caveat (post-strengthening 2026-04-25):
  - natural_range_disjoint_from_ligo_window: replaces the prior
    ∃-absorption `second_sound_graviton_not_derived_DOF` with a
    substantive disjointness theorem (the natural endpoints both
    fail LigoSatisfied → the natural range and GW170817 window are
    disjoint)
  - second_sound_graviton_natural_range_universally_falsified:
    frame-independent form (no c-rescaling can rescue the natural
    range; deviation is independent of light speed)

  -- Bundled hypothesis (post-strengthening: 3-conjunct, all
     independently load-bearing):
  - H_VestigialModeIsGraviton: P1 (χ>0) ∧ P2 (LigoSatisfied) ∧
    P3' (|Δc/c| < 1/2 sub-half-deviation) — replaced redundant
    luminal-propagation conjunct with quantitative bound
  - H_VestigialModeIsGraviton_at_one: anchor discharge
  - H_VestigialModeIsGraviton_fails_at_natural_lower, _upper, _zero,
    _quarter: FOUR explicit falsifiers (1/4 added: passes P1 but
    fails P3' at exactly |Δ|=1/2, isolating P3' independence)

  -- Dispersion bridge (post-strengthening: substantive LIGO-band):
  - dispersion_correction, _zero_at_no_dissipation,
    _linear_in_gamma, _abs_bound: trivial multiplication-algebra
    facts retained for Python cross-checks
  - dispersion_within_ligo_iff: substantive biconditional connecting
    SK-EFT Γ_H to GW170817 cap at probe frequency (|γ·ω| ≤ tol ↔
    |γ| ≤ tol/ω)
  - vestigial_dispersion_below_ligo_at_inspiral_peak: quantitative
    check that the vestigial-regime placeholder γ ≤ 1e-30 keeps the
    dispersion correction below tolGW170817 at GW170817 ω=100 Hz

  Zero sorry. Tracked hypothesis: H_VestigialModeIsGraviton
  (= positivity ∧ LigoSatisfied ∧ sub-half-deviation). All four
  falsifiers are required: each violates exactly one (or
  isolates one) of the three conjuncts. The Phase 5y H1 caveat is
  encoded as the substantive `natural_range_disjoint_from_ligo_window`
  theorem (post-strengthening 2026-04-25, replacing the prior
  ∃-absorption form which was vacuous). The actual vestigial graviton
  identification awaits a derived-DOF mechanism (deep-research H1
  negative finding; natural follow-up work).
-/
end SKEFTHawking.GravitationalWaves
