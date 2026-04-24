import SKEFTHawking.VestigialMapping
import SKEFTHawking.DESIComparison

/-!
# Vestigial-Gravity Effective Fluid Equation of State (H4 Closed Form)

Formalizes the H4 §4–§8 closed-form derivation of the vestigial-gravity
effective fluid EOS `(w_vest, c_s², ζ_vest)`, produced by systematic
analogy to the Fernandes-Fu charge-4e superconductor framework
(Wave 4, `CondensedMatterAnalog.lean` + `VestigialMapping.lean`).

## The H4 closed-form derivation

Using the compact notation `τ = H / (π · T_{c,vest}) = T_dS / T_{c,vest}`
and the vestigial saddle-point free energy (H4 EQ.112)
```
f_vest(τ) = −f₀ · (1 − τ²)²,    f₀ = π N_* T_{c,vest}² / (4 K(κ_*))
```
standard thermodynamic derivatives give (H4 EQ.113-EQ.120):

**Energy density** (EQ.115):
```
ρ_vest(τ) = f₀ · (1 − τ²)(5τ² − 1)
```

**Pressure** (EQ.116):
```
p_vest(τ) = f₀ · (1 − τ²)²
```

**Equation of state** (EQ.117):
```
w_vest(τ) = p_vest / ρ_vest = (1 − τ²) / (5τ² − 1)
```

**Sound speed squared** (EQ.120):
```
c_{s,vest}²(τ) = −(1 − τ²) / (3 − 5τ²)
```

## Verdict summary (H4 §8)

The derivation produces novel physics content — but the resulting EOS
**quantitatively fails DESI DR2** on three independent counts:

1. **Wrong phantom sign.** On the natural branch `τ² < 1/5`, `w_vest < −1`
   (phantom today), opposite to the DESI preference `w₀ > −1` with past
   phantom. No `τ₀ ∈ (0, 1)` yields `w₀ = −0.73`.

2. **Gradient instability.** `c_{s,vest}²(τ) = −(1 − τ²)/(3 − 5τ²)` is
   strictly **negative** at small `τ`: `c_s²(0) = −1/3 < 0`. Vestigial
   perturbations grow exponentially `δχ ∼ e^{|c_s|k η}`, producing
   catastrophic clustering incompatible with `f σ₈ ≈ 0.45` at `z ∼ 0.5`.

3. **Fine-tuning under Λ₀-augmentation.** Adding a bare cosmological
   constant `Λ₀` can reach DESI only at `Λ₀/f₀ ∼ O(1)`, which via EQ.111
   requires `T_{c,vest} ∼ meV` — a `10⁻⁶²` to `10⁻¹²¹` fine-tuning of
   `T_{c,vest}/Λ_UV`, the same Round-4a obstruction transmuted.

**Verdict: NO-GO for DESI; PARTIAL for the framework.** This wave
formalizes all three obstructions as Lean theorems.

## Structural free parameters (GAP-1, GAP-2)

Per the roadmap, two parameters are encoded as free parameters (not axioms):
- `GAP-1`: relaxation rate `Γ_χ` (entropy-production coefficient)
- `GAP-2`: anisotropy coefficient `K(κ_*)`

These reflect genuine physical uncertainty; the closed-form results here
are independent of their values (they enter only through `f₀` and
`T_{c,vest}`).

## References

- H4 closed-form derivation — `Lit-Search/Phase-5y/Phase 5y Hypothesis 4 — Effective Fluid EOS for Volovik-Style Vestigial Gravity.md`
- Volovik, *Vestigial gravity*, JETP Lett. 119, 330 (2024); arXiv:2312.09435
- Fernandes, Fu, PRL 127, 047001 (2021); arXiv:2101.07943
-/

namespace SKEFTHawking.VestigialEOS

open SKEFTHawking.DESIComparison

/-!
## Vestigial thermodynamic parameters

The closed-form derivation depends on two strictly-positive scales:
`f₀` (free-energy normalization, H4 EQ.111) and `T_{c,vest}` (vestigial
onset temperature, H4 EQ.108). The dimensionless ratio
`τ = H/(π T_{c,vest})` is the single evolution variable.
-/

/-- Vestigial-gravity thermodynamic parameters. `T_c` is the vestigial
    onset temperature; `f_0` is the GL free-energy amplitude. Both
    strictly positive. -/
structure VestigialParams where
  /-- GL free-energy amplitude `f_0 = π N_* T_{c,vest}² / (4 K(κ_*))` (H4 EQ.111). -/
  f_0 : ℝ
  /-- Vestigial onset temperature (H4 EQ.108). -/
  T_c : ℝ
  f_0_pos : 0 < f_0
  T_c_pos : 0 < T_c

/-!
## Saddle-point condensate (EQ.109)

`χ₀²(τ) = χ_∞²·(1 − τ²)` with boundary conditions:
- `χ₀²(τ → 0) = χ_∞²` (flat-space GR recovered)
- `χ₀²(τ → 1⁻) = 0` (vestigial melting)
-/

/-- Saddle-point condensate squared `χ₀²(τ) = χ_∞²·(1−τ²)` (H4 EQ.109),
    in units where `χ_∞² = 1` so the value is pure `(1−τ²)`. -/
noncomputable def chi0Sq (τ : ℝ) : ℝ := 1 - τ^2

/-- **VE1 — Saddle-point at zero temperature: `χ₀²(0) = 1`.**

    Boundary condition: in the deep vestigial limit `T_dS → 0`, the
    condensate reaches its asymptotic value `χ_∞² = 1`. -/
theorem chi0Sq_at_zero : chi0Sq 0 = 1 := by
  unfold chi0Sq; ring

/-- **VE2 — Vestigial melting: `χ₀²(τ = 1) = 0`.**

    At the critical `τ = 1` (equivalently `T_dS = T_{c,vest}`), the
    condensate vanishes — geometry melts. -/
theorem chi0Sq_at_melting : chi0Sq 1 = 0 := by
  unfold chi0Sq; ring

/-!
## Free energy (EQ.111)
-/

/-- Vestigial GL free-energy density `f_vest(τ) = −f_0·(1−τ²)²` (H4 EQ.111). -/
noncomputable def f_vest (V : VestigialParams) (τ : ℝ) : ℝ :=
  -V.f_0 * (1 - τ^2)^2

/-- **VE3 — Free energy at zero temperature: `f_vest(0) = −f_0`.**

    Flat-space GR recovered value; the saddle-point free energy reaches
    its minimum. -/
theorem f_vest_at_zero (V : VestigialParams) : f_vest V 0 = -V.f_0 := by
  unfold f_vest; ring

/-- **VE4 — Free energy at melting: `f_vest(τ = 1) = 0`.**

    At the vestigial transition, the GL free energy vanishes (condensate
    gone). -/
theorem f_vest_at_melting (V : VestigialParams) : f_vest V 1 = 0 := by
  unfold f_vest; ring

/-!
## Energy density (EQ.115)
-/

/-- Vestigial energy density `ρ_vest(τ) = f_0·(1−τ²)(5τ²−1)` (H4 EQ.115). -/
noncomputable def rho_vest (V : VestigialParams) (τ : ℝ) : ℝ :=
  V.f_0 * (1 - τ^2) * (5 * τ^2 - 1)

/-- **VE5 — Energy density at zero: `ρ_vest(0) = −f_0`.**

    In the deep vestigial limit, the energy density equals `−f_0`
    (cosmological-constant sign). -/
theorem rho_vest_at_zero (V : VestigialParams) : rho_vest V 0 = -V.f_0 := by
  unfold rho_vest; ring

/-- **VE6 — Energy density vanishes at `τ² = 1/5`.**

    Direct calculation: `(1 − 1/5)(5·1/5 − 1) = (4/5)·0 = 0`. This is
    the pole of `w_vest(τ)` — the EFT breaks down in a narrow window. -/
theorem rho_vest_zero_at_fifth (V : VestigialParams) :
    rho_vest V (Real.sqrt (1/5)) = 0 := by
  unfold rho_vest
  have h : (Real.sqrt (1/5))^2 = 1/5 := by
    rw [Real.sq_sqrt]; norm_num
  rw [h]; ring

/-!
## Pressure (EQ.116)
-/

/-- Vestigial pressure `p_vest(τ) = f_0·(1−τ²)²` (H4 EQ.116). -/
noncomputable def p_vest (V : VestigialParams) (τ : ℝ) : ℝ :=
  V.f_0 * (1 - τ^2)^2

/-- **VE7 — Pressure-free-energy relation: `p_vest = −f_vest`.**

    Direct from the thermodynamic identity `p = −f`. -/
theorem p_vest_eq_neg_f_vest (V : VestigialParams) (τ : ℝ) :
    p_vest V τ = -(f_vest V τ) := by
  unfold p_vest f_vest; ring

/-- **VE8 — Pressure at zero: `p_vest(0) = f_0`.**

    Deep-vestigial pressure equals `+f_0` (positive). -/
theorem p_vest_at_zero (V : VestigialParams) : p_vest V 0 = V.f_0 := by
  unfold p_vest; ring

/-!
## Equation of state (EQ.117) — central result

`w_vest(τ) = (1 − τ²)/(5τ² − 1)` (H4 EQ.117 boxed).

Three key limits:
- `τ → 0`: `w_vest → −1` (cosmological-constant limit)
- `τ² = 1/5`: pole (`ρ_vest = 0`; EFT breaks down)
- `τ = 1`: `w_vest → 0` (dust-like near melting)
-/

/-- Vestigial equation-of-state parameter `w_vest(τ) = (1−τ²)/(5τ²−1)`
    (H4 EQ.117). -/
noncomputable def w_vest (τ : ℝ) : ℝ := (1 - τ^2) / (5 * τ^2 - 1)

/-- **VE9 — Deep vestigial limit: `w_vest(0) = −1`.**

    At `τ → 0` (`H ≪ π T_{c,vest}`), the vestigial EOS reduces to a
    cosmological constant — **the `w = −1` limit is recovered** at small
    `τ`. This is consistent with the Wave 1 Gibbs-Duhem obstruction only
    in the sense that far from melting, vestigial gravity looks ΛCDM-like. -/
theorem w_vest_at_zero : w_vest 0 = -1 := by
  unfold w_vest; norm_num

/-- **VE10 — Dust-like limit: `w_vest(1) = 0`.**

    At the vestigial melting `τ = 1`, the EOS is dust-like — consistent
    with the phase transition having "melted" the condensate. -/
theorem w_vest_at_melting : w_vest 1 = 0 := by
  unfold w_vest; norm_num

/-!
## Sound speed (EQ.120) — gradient-instability theorem

`c_{s,vest}²(τ) = −(1 − τ²)/(3 − 5τ²)` (H4 EQ.120 boxed).

**Fatal feature**: `c_s²(0) = −1/3 < 0`. Vestigial perturbations have
**imaginary sound speed** at late times, producing exponential gradient
instability `δχ ∼ e^{|c_s|kη}` — catastrophic clustering.
-/

/-- Vestigial sound speed squared `c_{s,vest}²(τ) = −(1−τ²)/(3−5τ²)`
    (H4 EQ.120). -/
noncomputable def cs_sq_vest (τ : ℝ) : ℝ := -(1 - τ^2) / (3 - 5 * τ^2)

/-- **VE11 — `c_{s,vest}²(0) = −1/3`: gradient instability at late times.**

    The central **NO-GO** feature of the natural vestigial branch: at the
    deep vestigial limit (which is the DESI-relevant regime `τ ≪ 1`),
    the sound speed squared is **negative**, hence imaginary sound speed,
    hence exponential gradient instability. -/
theorem cs_sq_vest_at_zero : cs_sq_vest 0 = -1/3 := by
  unfold cs_sq_vest; norm_num

/-- **VE12 — Gradient instability: `c_{s,vest}²(0) < 0`.**

    Explicit statement of the instability. This is the second
    H4-identified DESI obstruction (after the phantom-sign mismatch). -/
theorem cs_sq_vest_negative_at_zero : cs_sq_vest 0 < 0 := by
  rw [cs_sq_vest_at_zero]; norm_num

/-!
## CPL parameters at generic τ₀ (EQ.129)
-/

/-- CPL `w₀` at vestigial `τ₀` (H4 EQ.129, first component):
    `w₀(τ₀) = (1 − τ₀²) / (5τ₀² − 1)` (same as `w_vest(τ₀)`). -/
noncomputable def cpl_w0 (τ_0 : ℝ) : ℝ := w_vest τ_0

/-- CPL `w_a` at vestigial `τ₀` (H4 EQ.129, second component, with
    `Ω_m = 0.32` inserted):
    `w_a(τ₀) = −12 · Ω_m · τ₀² / (5τ₀² − 1)²`. -/
noncomputable def cpl_wa (τ_0 Ω_m : ℝ) : ℝ :=
  -12 * Ω_m * τ_0^2 / (5 * τ_0^2 - 1)^2

/-- **VE13 — CPL `w₀` matches `w_vest`.** -/
theorem cpl_w0_eq_w_vest (τ_0 : ℝ) : cpl_w0 τ_0 = w_vest τ_0 := rfl

/-!
## DESI-incompatibility theorem (H4 §7)

The central quantitative result: there is no `τ₀ ∈ (0, 1)` that produces
`w₀ = −0.73`. On `(0, 1/√5)` the EOS is phantom (`w < −1`); on
`(1/√5, 1)` it is positive (dust-like). DESI prefers `w₀ ≈ −0.73`,
which is **not reachable**.
-/

/-- **VE14 — Phantom today on natural branch.**

    For `τ² ∈ (0, 1/5)`, the vestigial EOS has `w_vest(τ) < −1`
    (phantom-today). This is the WRONG sign for DESI (which has
    `w₀ > −1` today). -/
theorem w_vest_phantom_on_natural_branch (τ : ℝ)
    (hτ_pos : 0 < τ^2) (hτ_small : τ^2 < 1/5) :
    w_vest τ < -1 := by
  unfold w_vest
  -- 5τ² - 1 < 0, so dividing flips the inequality
  have h_denom_neg : 5 * τ^2 - 1 < 0 := by linarith
  have h_numer_pos : 0 < 1 - τ^2 := by
    have : τ^2 < 1 := by linarith
    linarith
  -- Need: (1 - τ²) / (5τ² - 1) < -1
  rw [div_lt_iff_of_neg h_denom_neg]
  -- Goal: -1 * (5τ² - 1) < 1 - τ²
  linarith

/-- **VE15 — Positive branch: `w_vest(τ) > 0` for `τ² ∈ (1/5, 1)`.**

    Dust-like EOS on the opposite side of the pole — also ruled out by
    DESI (which wants `w₀ < 0`). -/
theorem w_vest_positive_on_right_branch (τ : ℝ)
    (hτ_large : 1/5 < τ^2) (hτ_less_one : τ^2 < 1) :
    0 < w_vest τ := by
  unfold w_vest
  have h_denom_pos : 0 < 5 * τ^2 - 1 := by linarith
  have h_numer_pos : 0 < 1 - τ^2 := by linarith
  exact div_pos h_numer_pos h_denom_pos

/-- **VE16 — DESI incompatibility (main structural statement).**

    The DESI-preferred `w₀ = −0.73` is NOT in the range of `w_vest`
    restricted to the phantom-today branch `τ² ∈ (0, 1/5)`. On this
    branch the EOS is strictly `< −1`, missing DESI's `−0.73 > −1`. -/
theorem desi_incompatible_on_natural_branch (τ : ℝ)
    (hτ_pos : 0 < τ^2) (hτ_small : τ^2 < 1/5) :
    w_vest τ ≠ -0.73 := by
  have h1 : w_vest τ < -1 := w_vest_phantom_on_natural_branch τ hτ_pos hτ_small
  intro heq
  rw [heq] at h1
  norm_num at h1

/-!
## Wrong-sign crossing theorem
-/

/-- **VE17 — Vestigial is NOT in the DESI region (for any `τ` on the
    natural branch).**

    For a candidate `(w₀, w_a)` derived from vestigial `τ₀²` in the
    phantom-today branch, the `w₀` component fails the DESI 1σ lower
    bound `w₀_min = −0.8`. -/
theorem vestigial_not_in_desi_region (τ_0 Ω_m : ℝ)
    (hτ_pos : 0 < τ_0^2) (hτ_small : τ_0^2 < 1/5) :
    ¬ InDESIRegion { w0 := cpl_w0 τ_0, wa := cpl_wa τ_0 Ω_m } desiDR2_1sigma := by
  intro h
  unfold InDESIRegion desiDR2_1sigma at h
  have := h.1  -- w0_min ≤ w0
  have h_phantom : w_vest τ_0 < -1 :=
    w_vest_phantom_on_natural_branch τ_0 hτ_pos hτ_small
  unfold cpl_w0 at this
  linarith

/-!
## Λ₀-augmentation fine-tuning (H4 EQ.133)
-/

/-- Λ₀-augmentation fine-tuning coefficient: the ratio
    `T_{c,vest} / Λ_UV` at which DESI-scale `τ₀ ∼ 0.5` is achievable.
    Per H4 EQ.154: `log₁₀(Λ_UV/T_{c,vest}) ∈ [62, 121]`. -/
noncomputable def fineTuningLog10 (V : VestigialParams) (Λ_UV : ℝ) : ℝ :=
  Real.log (Λ_UV / V.T_c) / Real.log 10

/-- **VE18a — Fine-tuning bound (H4 EQ.154).**

    If the UV cutoff to vestigial-critical-temperature ratio
    `Λ_UV / T_c ≥ 10^k` for some `k ≥ 0`, then the fine-tuning log
    is at least `k`. In particular, for `k = 62` (the H4 §7 lower
    bound for DESI-reachability via `Λ₀`-augmentation) the tuning
    cost is at least `10⁻⁶²`; at `k = 121` it matches the
    cosmological-constant problem. -/
theorem fine_tuning_log_lower_bound (V : VestigialParams) (Λ_UV : ℝ) (k : ℝ)
    (hΛ : 0 < Λ_UV) (h_ratio : Real.exp (k * Real.log 10) ≤ Λ_UV / V.T_c) :
    k ≤ fineTuningLog10 V Λ_UV := by
  unfold fineTuningLog10
  have hT : 0 < V.T_c := V.T_c_pos
  have h_ratio_pos : 0 < Λ_UV / V.T_c := div_pos hΛ hT
  have h_log10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)
  -- From `exp(k·log 10) ≤ Λ_UV/T_c` take logs both sides.
  have h_log_ineq : k * Real.log 10 ≤ Real.log (Λ_UV / V.T_c) := by
    have h_exp_pos : 0 < Real.exp (k * Real.log 10) := Real.exp_pos _
    calc k * Real.log 10
        = Real.log (Real.exp (k * Real.log 10)) := by
          rw [Real.log_exp]
      _ ≤ Real.log (Λ_UV / V.T_c) := Real.log_le_log h_exp_pos h_ratio
  -- Divide both sides by `log 10 > 0`.
  have := div_le_div_of_nonneg_right h_log_ineq (le_of_lt h_log10_pos)
  rwa [mul_div_assoc, div_self (ne_of_gt h_log10_pos), mul_one] at this

/-!
## Sound-speed-pole diagnostics
-/

/-- **VE18 — Sound speed pole at `τ² = 3/5`.**

    The vestigial sound speed diverges (GL expansion breaks down) at
    `τ² = 3/5`. Beyond this point the effective-fluid description fails. -/
theorem cs_sq_vest_denom_zero_at_three_fifths :
    3 - 5 * ((Real.sqrt (3/5))^2) = 0 := by
  have h : (Real.sqrt (3/5))^2 = 3/5 := by
    rw [Real.sq_sqrt]; norm_num
  rw [h]; ring

/-!
## Main NO-GO theorem
-/

/-- **VE19 — `ρ + p` at the deep vestigial limit.**

    At `τ = 0`: `ρ_vest(0) + p_vest(0) = −f_0 + f_0 = 0`.
    This reproduces the `w = −1` Lorentz-invariance lock of Wave 1 at the
    ΛCDM endpoint. -/
theorem rho_plus_p_zero_at_deep_vestigial (V : VestigialParams) :
    rho_vest V 0 + p_vest V 0 = 0 := by
  rw [rho_vest_at_zero, p_vest_at_zero]; ring

/-- **VE20 — H4 NO-GO bundled theorem.**

    For the vestigial-gravity closed-form EOS on the natural branch
    (`τ² ∈ (0, 1/5)`), the following three obstructions hold jointly:
    1. `w_vest(τ) < −1` (phantom-today, opposite of DESI's `w₀ > −1`)
    2. `c_{s,vest}²(0) < 0` (gradient instability at late times)
    3. The CPL candidate is not in the DESI 1σ region

    This is the Phase 5y H4 verdict, formally stated. -/
theorem h4_no_go_main (τ_0 Ω_m : ℝ)
    (hτ_pos : 0 < τ_0^2) (hτ_small : τ_0^2 < 1/5) :
    w_vest τ_0 < -1 ∧
    cs_sq_vest 0 < 0 ∧
    ¬ InDESIRegion { w0 := cpl_w0 τ_0, wa := cpl_wa τ_0 Ω_m } desiDR2_1sigma := by
  refine ⟨?_, ?_, ?_⟩
  · exact w_vest_phantom_on_natural_branch τ_0 hτ_pos hτ_small
  · exact cs_sq_vest_negative_at_zero
  · exact vestigial_not_in_desi_region τ_0 Ω_m hτ_pos hτ_small

end SKEFTHawking.VestigialEOS
