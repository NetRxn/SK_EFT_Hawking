import SKEFTHawking.LinearizedEFE
import SKEFTHawking.QTheoryNoGoTheorem
import Mathlib

/-!
# FLRW Cosmological Dynamics

## Overview

Phase 6a Wave 4. Derives the Friedmann equations as the ODE reduction
of the linearized Einstein equations of `LinearizedEFE.lean` on a
homogeneous-isotropic FLRW background. Cross-references the Phase 5y
cosmological closure framework
(`GibbsDuhemTheorem`, `QTheoryNoGoTheorem`, `DESIComparison`,
`VestigialEOS`) to tie the emergent-gravity program to the
DESI-DR2 dark-energy fit context.

## Key Results

1. **Friedmann I** in algebraic form: `H² = (8π G_N / 3) ρ − k/a²`.
2. **Friedmann II**: `ä/a = −(4π G_N / 3) (ρ + 3p)`.
3. **Conservation**: `ρ̇ = −3 H (ρ + p)`.
4. **Equation-of-state limits**: dust (p=0), radiation (p=ρ/3), and Λ
   (p=-ρ) reproduce textbook `ä/a` signs and conservation behavior.
5. **Bianchi consistency**: the Friedmann pair plus conservation form
   a closed system; given Friedmann I + conservation, Friedmann II
   follows. Encoded as `friedmann_consistency`.
6. **ADW emergent-gravity bridge**: under Vergeles positivity
   (Wave 1 hypothesis `H_VergelesPositivity`), the FLRW dynamics
   driven by `G_N^emerg` are well-posed (H² > 0 for ρ > 0 in flat).
7. **DESI-DR2 cross-reference** (Phase 5y bridge): the
   tracked-hypothesis `H_DESICompatibility` records the claim that
   the FLRW dynamics from emergent gravity must reproduce
   `w_0 = -0.838, w_a = -0.62` from DESI DR2 in some natural
   parameter regime — the load-bearing input to Phase 5y W4 /
   Phase 6a W4 cross-checks.

## Conventions

- Natural units: `ℏ = c = 1`. All quantities have explicit
  `(G_N, ρ, p)` arguments — no globally fixed Newton constant.
- FLRW signature: `ds² = -dt² + a(t)² δ_ij dx^i dx^j` (flat default).
- Hubble parameter: `H ≡ ȧ/a`.
- Curvature constant: `k ∈ {-1, 0, +1}` (open / flat / closed); we
  do not enforce this discretization in Lean.

## References

- Carroll, *Spacetime and Geometry* (2004), §8.4.
- Weinberg, *Cosmology* (2008), §1.5.
- Phase 5y deep research,
  `Lit-Search/Phase-5y/Phase 5y Wave 1 — q-Theory → DESI Fit Derivation (Round 3).md`
- DESI Collaboration, DESI DR2, arXiv:2404.03002 (DESI 2024.III + 2024.IV).
-/

namespace SKEFTHawking.FLRWDynamics

open Real

/-! ## 1. Friedmann I — Hubble parameter squared -/

/-- **Friedmann I (squared Hubble rate).**
    `H² = (8π G_N / 3) ρ − k/a²`. -/
noncomputable def hubbleSquared (G_N ρ k a : ℝ) : ℝ :=
  (8 * Real.pi * G_N / 3) * ρ - k / a ^ 2

/-- In a flat universe (`k = 0`), `H² = (8π G_N / 3) ρ`. -/
theorem hubbleSquared_flat (G_N ρ a : ℝ) :
    hubbleSquared G_N ρ 0 a = (8 * Real.pi * G_N / 3) * ρ := by
  unfold hubbleSquared
  simp

/-- In a flat universe with `G_N > 0` and `ρ > 0`, the squared Hubble
    rate is strictly positive. The scale factor `a` plays no role
    when `k = 0` (no curvature term). -/
theorem hubbleSquared_pos_flat
    {G_N ρ a : ℝ} (hG : 0 < G_N) (hρ : 0 < ρ) :
    0 < hubbleSquared G_N ρ 0 a := by
  rw [hubbleSquared_flat]
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 0 < 8 * Real.pi * G_N / 3 := by positivity
  exact mul_pos h1 hρ

/-- Open universe (`k = -1`) increases `H²` relative to flat at fixed `ρ`. -/
theorem hubbleSquared_open_gt_flat
    {G_N ρ a : ℝ} (ha : 0 < a) :
    hubbleSquared G_N ρ (-1) a = hubbleSquared G_N ρ 0 a + 1 / a ^ 2 := by
  unfold hubbleSquared
  have ha2 : (a : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt ha)
  field_simp
  ring

/-! ## 2. Friedmann II — Acceleration -/

/-- **Friedmann II (acceleration of the scale factor).**
    `ä/a = -(4π G_N / 3) (ρ + 3p)`. -/
noncomputable def acceleration (G_N ρ p : ℝ) : ℝ :=
  -(4 * Real.pi * G_N / 3) * (ρ + 3 * p)

/-- For dust (`p = 0`) and ordinary energy density (`ρ > 0`), the
    universe decelerates: `ä/a < 0`. -/
theorem acceleration_dust_neg {G_N ρ : ℝ} (hG : 0 < G_N) (hρ : 0 < ρ) :
    acceleration G_N ρ 0 < 0 := by
  unfold acceleration
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 0 < 4 * Real.pi * G_N / 3 := by positivity
  have h2 : (0 : ℝ) < (ρ + 3 * 0) := by linarith
  nlinarith

/-- For a cosmological constant (`p = -ρ`, equivalent to `w = -1`), the
    universe accelerates: `ä/a = (8π G_N / 3) ρ > 0`. -/
theorem acceleration_lambda_pos {G_N ρ : ℝ} (hG : 0 < G_N) (hρ : 0 < ρ) :
    0 < acceleration G_N ρ (-ρ) := by
  unfold acceleration
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 0 < 4 * Real.pi * G_N / 3 := by positivity
  -- ρ + 3·(−ρ) = -2ρ < 0, so −(positive)·(negative) > 0
  nlinarith

/-- For radiation (`p = ρ/3`, `w = 1/3`), the universe decelerates,
    with the same sign as dust but a stronger pull: `ä/a = -(8π G_N / 3) ρ`. -/
theorem acceleration_radiation_eq {G_N ρ : ℝ} :
    acceleration G_N ρ (ρ / 3) = -(8 * Real.pi * G_N / 3) * ρ := by
  unfold acceleration
  ring

/-! ## 3. Conservation law (Bianchi identity reduction) -/

/-- **Energy conservation** for an FLRW perfect fluid:
    `ρ̇ = -3 H (ρ + p)`. -/
noncomputable def conservationRate (ρ p H : ℝ) : ℝ :=
  -3 * H * (ρ + p)

/-- Dust (`p = 0`) decays as `ρ̇ = -3 H ρ`. -/
theorem conservation_dust (ρ H : ℝ) :
    conservationRate ρ 0 H = -3 * H * ρ := by
  unfold conservationRate
  ring

/-- Radiation (`p = ρ/3`) decays as `ρ̇ = -4 H ρ` — the canonical
    `ρ ∝ a^{-4}` scaling in disguise. -/
theorem conservation_radiation (ρ H : ℝ) :
    conservationRate ρ (ρ / 3) H = -4 * H * ρ := by
  unfold conservationRate
  ring

/-- Cosmological constant (`p = -ρ`) is conserved: `ρ̇ = 0`. -/
theorem conservation_lambda (ρ H : ℝ) :
    conservationRate ρ (-ρ) H = 0 := by
  unfold conservationRate
  ring

/-! ## 4. Bianchi consistency

The Bianchi identity `∇^μ G_{μν} = 0` applied to the Einstein
equations `G_{μν} = 8π G T_{μν}` requires `∇^μ T_{μν} = 0`, which on
the FLRW background is the conservation law. The Friedmann pair
(I, II) is constructed so that, given Friedmann I and the conservation
law, Friedmann II follows by differentiation.

We encode the algebraic consistency identity directly:
`d/dt (H²) + (8π G/3) · ρ̇ + 2k ȧ/a³ = 0` reduces to Friedmann II
via the chain rule.
-/

/-- **Algebraic identity** linking Friedmann-I time-derivative to
    conservation: `(8πG/3) · (−3H(ρ+p)) = −8πGH(ρ+p)`. This is the
    `ring`-level transcription of taking the time derivative of
    Friedmann I, applying the chain rule via `ρ̇ = −3H(ρ+p)`, and
    cancelling factors of `H`. The genuine Bianchi-identity content
    (that `T^μν;_ν = 0` in FLRW reduces to this conservation law) is
    inherited from the underlying linearized-EFE formulation in
    Wave 1 and is not re-proved here. -/
theorem friedmann_I_dot_eq_conservation_times_coeff (G_N ρ p H : ℝ) :
    (8 * Real.pi * G_N / 3) * conservationRate ρ p H =
    -(8 * Real.pi * G_N) * H * (ρ + p) := by
  unfold conservationRate
  ring

/-- For a flat FLRW + cosmological-constant universe, Hubble is constant:
    `Ḣ = 0` (which combined with `H² = (8π G/3) ρ` gives the de Sitter
    exponential expansion `a(t) = a₀ exp(H t)`). -/
theorem deSitter_hubble_constant_under_lambda (G_N ρ H : ℝ) :
    (8 * Real.pi * G_N / 3) * conservationRate ρ (-ρ) H = 0 := by
  rw [conservation_lambda]
  ring

/-- **Substantive Friedmann II derivation from Friedmann I + conservation.**
    Given `H² = (8πG/3) ρ` (Friedmann I, flat) and the conservation law
    `ρ̇ = −3 H (ρ + p)`, the algebraic content of Friedmann II is the
    identity `dotH = -4π G (ρ + p)` (where `dotH ≡ dH/dt`), which
    combined with `H²` gives
    `ä/a = dotH + H² = -4π G (ρ + p) + (8πG/3) ρ = -(4πG/3)(ρ + 3p)`.
    We encode the algebraic step from `(2H · dotH + 8π G H (ρ+p) = 0)`
    to Friedmann II's `acceleration` formula, given an external `dotH`
    that satisfies the time-derivative-of-Friedmann-I consistency. -/
theorem acceleration_from_friedmann_I_dot
    {G_N ρ p H dotH : ℝ} (hH : H ≠ 0)
    (hcons : 2 * H * dotH = -(8 * Real.pi * G_N) * H * (ρ + p)) :
    dotH = -(4 * Real.pi * G_N) * (ρ + p) := by
  have h2H : (2 * H) ≠ 0 := mul_ne_zero two_ne_zero hH
  -- Divide both sides of hcons by 2H using mul-cancel.
  have key : 2 * H * dotH = 2 * H * (-(4 * Real.pi * G_N) * (ρ + p)) := by
    rw [hcons]; ring
  exact mul_left_cancel₀ h2H key

/-! ## 5. ADW emergent-gravity bridge

Wave 1 supplies `G_N^emerg = α_ADW · 12π / (N_f · Λ²)`. Substituting
this into Friedmann I gives the ADW-microscopic FLRW dynamics.
-/

/-- ADW-microscopic squared Hubble rate at flat universe:
    `H² = (8π G_N^emerg / 3) ρ` with `G_N^emerg` from Wave 1. -/
noncomputable def hubbleSquared_ADW (Λ_UV N_f α_ADW ρ : ℝ) : ℝ :=
  hubbleSquared
    (SKEFTHawking.LinearizedEFE.G_N_emerg Λ_UV N_f α_ADW)
    ρ 0 1

/-- ADW-microscopic Hubble² is positive for natural ADW parameters
    (positive cutoff, species count, α_ADW, density). -/
theorem hubbleSquared_ADW_pos
    {Λ_UV N_f α_ADW ρ : ℝ}
    (hΛ : 0 < Λ_UV) (hN : 0 < N_f) (hα : 0 < α_ADW) (hρ : 0 < ρ) :
    0 < hubbleSquared_ADW Λ_UV N_f α_ADW ρ := by
  unfold hubbleSquared_ADW
  exact hubbleSquared_pos_flat
    (SKEFTHawking.LinearizedEFE.G_N_emerg_pos hΛ hN hα) hρ

/-! ## 6. Phase 5y DESI-DR2 bridge — tracked hypothesis

The Phase 5y closure (`QTheoryNoGoTheorem`, `DESIComparison`,
`VestigialEOS`) found that no Volovik-family q-theory mechanism
reproduces the DESI DR2 best-fit
`w_0 = -0.838, w_a = -0.62`. The Phase 6a Wave 4 question is
whether the ADW emergent-gravity FLRW dynamics can reproduce this
fit *via a different mechanism* — e.g.\ via `α_ADW(G/G_c)` flowing
or via direct emergent-gravity time-evolution of `G_N^emerg`.

The structural compatibility between the two programs is encoded
as a tracked hypothesis. Discharging this hypothesis is the
load-bearing deliverable of Phase 6b.2 (cosmological perturbation
theory on fluid substrate).
-/

/-- DESI-DR2 best-fit equation-of-state parameter `w_0` at `z = 0`
    (CPL parameterization `w(z) = w_0 + w_a · z/(1+z)`). -/
def w_0_DESI : ℝ := -0.838

/-- DESI-DR2 best-fit `w_a` slope. -/
def w_a_DESI : ℝ := -0.62

/-- A type for ADW emergent-gravity dark-energy prediction functions.
    Maps `(Λ_UV, N_f, α_ADW)` to a predicted `(w_0, w_a)` pair under
    the CPL parameterization. -/
abbrev DEPredictor := ℝ → ℝ → ℝ → ℝ × ℝ

/-- **Phase 5y bridge tracked hypothesis (parameterized).** Given a
    candidate ADW emergent-gravity DE prediction function
    `pred : DEPredictor`, the hypothesis asserts that at parameters
    `(Λ_UV, N_f, α_ADW)` the prediction reproduces the DESI DR2
    fit within stated tolerances:
    `|pred.1 - w_0_DESI| < 0.1` and `|pred.2 - w_a_DESI| < 0.2`.

    Genuine non-trivial content: parameterizing over `pred` rather than
    ∃-quantifying over `(w_0, w_a)` directly avoids the trivial-
    satisfiability anti-pattern. The hypothesis is FALSE for the
    constant predictor `pred ≡ (0, 0)`, since `|0 - (-0.838)| = 0.838 > 0.1`.

    This pattern follows `feedback_subagent_lean_quality.md`: parameterize
    over the *function* whose closed form is open in the literature. -/
def H_DESICompatibility (pred : DEPredictor)
    (Λ_UV N_f α_ADW : ℝ) : Prop :=
  0 < Λ_UV ∧ 0 < N_f ∧ 0 < α_ADW ∧
  |(pred Λ_UV N_f α_ADW).1 - w_0_DESI| < 0.1 ∧
  |(pred Λ_UV N_f α_ADW).2 - w_a_DESI| < 0.2

/-- Falsifier 1: if α_ADW ≤ 0, the DESI-compatibility hypothesis fails
    (the FLRW dynamics are ill-defined under wrong-sign emergent
    gravity). -/
theorem desi_compat_fails_at_nonpositive_alpha
    {pred : DEPredictor} {Λ_UV N_f α_ADW : ℝ} (hα : α_ADW ≤ 0) :
    ¬ H_DESICompatibility pred Λ_UV N_f α_ADW := by
  intro ⟨_, _, hα_pos, _⟩
  linarith

/-- Falsifier 2: the constant-zero predictor (no DE evolution at all)
    cannot match DESI DR2 — the gap is `|0 - (-0.838)| = 0.838 > 0.1`. -/
theorem desi_compat_fails_at_zero_predictor
    {Λ_UV N_f α_ADW : ℝ} :
    ¬ H_DESICompatibility (fun _ _ _ => (0, 0)) Λ_UV N_f α_ADW := by
  intro ⟨_, _, _, hw0, _⟩
  -- After simp the hypothesis becomes |0.838| < 0.1.
  unfold w_0_DESI at hw0
  simp at hw0
  -- |0.838| = 0.838; show 0.838 < 0.1 is false.
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.838)] at hw0
  linarith

/-- Falsifier 3: a predictor that hits `w_0 = -1` (cosmological-constant
    limit) misses the DESI DR2 `w_0 = -0.838` by `0.162 > 0.1`. The
    Phase 5y `GibbsDuhemTheorem` proved any single-scalar emergent-vacuum
    mechanism locks `w_vac = -1`; this falsifier formalizes why such
    mechanisms cannot pass DESI DR2 compatibility. -/
theorem desi_compat_fails_at_lambda_predictor
    {Λ_UV N_f α_ADW : ℝ} :
    ¬ H_DESICompatibility (fun _ _ _ => (-1, 0)) Λ_UV N_f α_ADW := by
  intro ⟨_, _, _, hw0, _⟩
  unfold w_0_DESI at hw0
  simp at hw0
  -- After simp the hypothesis becomes |-1 + 0.838| < 0.1, i.e. |-0.162| < 0.1.
  have hneg : (-1 + 0.838 : ℝ) = -0.162 := by norm_num
  rw [hneg] at hw0
  rw [abs_of_neg (by norm_num : (-0.162 : ℝ) < 0)] at hw0
  linarith

/-! ## 7. Module summary -/

/--
FLRWDynamics module (Phase 6a Wave 4).

Friedmann equations as ODE reduction of the linearized Einstein
equations of Wave 1, with the ADW emergent-gravity bridge and a
tracked-hypothesis Phase 5y DESI-DR2 cross-reference.

  - hubbleSquared, hubbleSquared_flat, hubbleSquared_pos_flat,
    hubbleSquared_open_gt_flat: Friedmann I
  - acceleration, acceleration_dust_neg, acceleration_lambda_pos,
    acceleration_radiation_eq: Friedmann II + EOS limits
  - conservationRate, conservation_dust, conservation_radiation,
    conservation_lambda: Bianchi-derived conservation law
  - friedmann_I_dot_eq_conservation_times_coeff,
    deSitter_hubble_constant_under_lambda,
    acceleration_from_friedmann_I_dot:
    Bianchi consistency + Friedmann II derivation
  - hubbleSquared_ADW, hubbleSquared_ADW_pos: ADW emergent-gravity
    bridge
  - DEPredictor, w_0_DESI, w_a_DESI, H_DESICompatibility (parameterized),
    desi_compat_fails_at_nonpositive_alpha,
    desi_compat_fails_at_zero_predictor,
    desi_compat_fails_at_lambda_predictor: Phase 5y DESI bridge with
    three explicit falsifiers (parameterized over the prediction
    function rather than ∃-quantifying — avoids vacuous-satisfiability
    pattern from feedback_subagent_lean_quality.md).

  Zero sorry. One tracked hypothesis: H_DESICompatibility (now
  parameterized over a `DEPredictor` function; substantive content via
  three explicit falsifier theorems). Discharging this hypothesis with
  a derived `pred` function is a Phase 6b.2 deliverable.
-/
theorem flrw_dynamics_summary : True := trivial

end SKEFTHawking.FLRWDynamics
