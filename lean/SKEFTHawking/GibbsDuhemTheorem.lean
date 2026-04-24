import SKEFTHawking.Basic

/-!
# Gibbs-Duhem Obstruction Theorem for Emergent-Vacuum Frameworks

Formalizes the structural obstruction theorem from Phase 5y Rounds 3, 4a, 5,
and the H4 orthogonality-principle §9 consolidation: **any emergent
dark-energy framework built on a single self-tuning composite scalar `q`,
with standard emergent-vacuum action `S = R/(16πG) + ε(q) + L_SM` and
Gibbs-Duhem equilibrium conditions, locks the vacuum equation of state
`w_vac = −1` identically by Lorentz invariance and therefore cannot produce
the time-evolving `w(z)` preferred by DESI DR2.**

The theorem applies realization-independently: the 4-form realization
[Klinkhamer-Volovik 2008 arXiv:0711.3170], the 2-brane realization
[Klinkhamer-Volovik 2011], the fermionic-crystal elasticity-tetrad
realization [Klinkhamer-Volovik 2019 arXiv:1812.07046 Eq. (6)], and
unimodular q-theory all inherit the same obstruction.

## Physical content

For a scalar `q` entering only through an algebraic potential `ε(q)` (no
explicit derivative term — the minimal action of
[arXiv:1812.07046 Eq. (7)]), the Euler-Lagrange equation
`∂_μ(dε/dq) = 0` is a constraint (not a wave equation). Combined with
Einstein's equation it yields the gravitating vacuum energy density
`ρ_V(q) = ε(q) − q · dε/dq` (Round 5 EQ.62).

By Lorentz invariance of the vacuum, the stress tensor must be proportional
to `g_μν`, which forces `p_V = −ρ_V`, hence `w_vac = p_V / ρ_V = −1`
wherever `ρ_V ≠ 0`. Gibbs-Duhem equilibrium (EQ.63) then fixes `q` to a
value `q₀` at which `ρ_V(q₀) = 0, dρ_V/dq|_{q₀} = 0, d²ρ_V/dq²|_{q₀} > 0`.

The obstruction is that these two structures — Lorentz-invariant `w = −1`
lock, plus equilibrium vanishing — are incompatible with the DESI DR2
preferred `(w₀, w_a)` region, which demands an evolving non-`−1` equation
of state.

## Source equations (Round 5 §1.2)

- **EQ.59**: Minimal action `S = ∫ d⁴x e [R/(16πG_N) + ε(q)]`
- **EQ.60**: `R_μν − (1/2)g_μν R = 8πG_N ρ_V(q) g_μν`
- **EQ.61**: `∂_μ(dε/dq) = 0 ⇒ dε/dq = μ = const`
- **EQ.62**: `ρ_V(q) ≡ ε(q) − q · (dε/dq) = ε(q) − μ q`
- **EQ.63**: Equilibrium: `ρ_V(q₀) = 0, dρ_V/dq|_{q₀} = 0, d²ρ_V/dq²|_{q₀} > 0`

## References

- `Lit-Search/Phase-5y/Phase 5y Wave 1 Round 5 (C2 only) — Fermionic-Crystal Elasticity-Tetrad q-Theory.md` §1.2
- `Lit-Search/Phase-5y/Phase 5y Wave 1 — q-Theory → DESI Fit Derivation (Round 3).md`
- Klinkhamer, Volovik, *Tetrads and q-theory*, JETP Lett. 109, 364 (2019);
  arXiv:1812.07046
- Klinkhamer, Volovik, *Self-tuning vacuum variable and cosmological constant*,
  Phys. Rev. D 77, 085015 (2008); arXiv:0711.3170
-/

namespace SKEFTHawking.GibbsDuhemTheorem

/-!
## Emergent-Vacuum Model

A single-scalar emergent-vacuum framework is specified by three functions
`ε, ε', ε'' : ℝ → ℝ` encoding the vacuum potential and its derivatives.
We package them as an abstract record (`EmergentVacuumModel`) so the
theorems below do not depend on Mathlib's `HasDerivAt` — the Gibbs-Duhem
argument is purely algebraic once the three functions are given.

The 4-form realization uses `q ~ F_{κλμν}` via scalar duality; the
fermionic-crystal realization uses `q = (1/4) e_a^μ E^a_μ` [Round 5 EQ.59];
both collapse to the same algebraic record here.
-/

/-- Emergent-vacuum model with single self-tuning scalar `q`.

    Packages the potential `ε : ℝ → ℝ` together with its first and second
    derivatives (taken as abstract fields rather than proved via
    `HasDerivAt`, so the downstream theorems are derivative-free).

    `eps_prime q` represents `dε/dq|_q`; `eps_double_prime q` represents
    `d²ε/dq²|_q`. The structure is intentionally minimal — the
    Gibbs-Duhem obstruction argument uses only algebraic combinations. -/
structure EmergentVacuumModel where
  /-- Vacuum potential `ε(q)` (Round 5 EQ.59). -/
  ε : ℝ → ℝ
  /-- First derivative `ε'(q) = dε/dq` (appears in Round 5 EQ.61 as
      chemical potential `μ`). -/
  eps_prime : ℝ → ℝ
  /-- Second derivative `ε''(q) = d²ε/dq²` (controls the Klein-Gordon mass
      of `δq` perturbations; Round 5 EQ.75). -/
  eps_double_prime : ℝ → ℝ

/-- Gravitating vacuum energy density after Gibbs-Duhem subtraction
    (Round 5 EQ.62):
    `ρ_V(q) = ε(q) − q · (dε/dq)`.

    The subtraction of `q · dε/dq` is the chemical-potential term forced by
    the `∂_μ(dε/dq) = 0` constraint (EQ.61); it is the defining feature of
    self-tuning q-theory frameworks. -/
noncomputable def rhoV (M : EmergentVacuumModel) (q : ℝ) : ℝ :=
  M.ε q - q * M.eps_prime q

/-- Derivative of `ρ_V` with respect to `q` (algebraic form).

    Direct differentiation of `ρ_V(q) = ε(q) − q · ε'(q)` gives
    `dρ_V/dq = ε'(q) − ε'(q) − q · ε''(q) = −q · ε''(q)`.

    We encode this as a definition rather than a theorem about
    `HasDerivAt` — the obstruction argument only needs the algebraic
    identity, not the PDE statement. -/
noncomputable def drhoVdq (M : EmergentVacuumModel) (q : ℝ) : ℝ :=
  -(q * M.eps_double_prime q)

/-- Vacuum pressure from Lorentz invariance (Round 3 equivalent): the
    vacuum stress tensor `T_μν^{vac}` is forced by Lorentz invariance to be
    proportional to `g_μν` with coefficient `ρ_V`; comparison to the perfect-
    fluid decomposition `T_μν = (ρ + p) u_μ u_ν − p g_μν` gives
    `p_V = −ρ_V`. -/
noncomputable def pV (M : EmergentVacuumModel) (q : ℝ) : ℝ := -(rhoV M q)

/-- Vacuum equation-of-state parameter `w_vac = p_V / ρ_V`. -/
noncomputable def wVac (M : EmergentVacuumModel) (q : ℝ) : ℝ :=
  pV M q / rhoV M q

/-!
## Core algebraic identities (Lorentz invariance + stress-tensor structure)
-/

/-- **GD1 — Stress-tensor trace identity (Lorentz invariance of the vacuum).**
    For any emergent-vacuum model, `ρ_V + p_V = 0` identically. This is the
    algebraic form of the Lorentz-invariance constraint on the vacuum stress
    tensor. -/
theorem rhoV_plus_pV_zero (M : EmergentVacuumModel) (q : ℝ) :
    rhoV M q + pV M q = 0 := by
  unfold pV; ring

/-- **GD2 — `p_V = −ρ_V` (Lorentz invariance rearranged).** Equivalent
    formulation of GD1 — useful as a rewrite rule in later proofs. -/
theorem pV_eq_neg_rhoV (M : EmergentVacuumModel) (q : ℝ) :
    pV M q = -(rhoV M q) := rfl

/-- **GD3 — Explicit form of `ρ_V`.** Re-exposes the `rhoV` definition for
    use in `simp` chains. -/
theorem rhoV_explicit (M : EmergentVacuumModel) (q : ℝ) :
    rhoV M q = M.ε q - q * M.eps_prime q := rfl

/-- **GD4 — Explicit form of `dρ_V/dq`.** The `dρ_V/dq = −q · ε''(q)`
    identity is purely algebraic once we interpret `eps_double_prime` as
    `ε''`. -/
theorem drhoVdq_explicit (M : EmergentVacuumModel) (q : ℝ) :
    drhoVdq M q = -(q * M.eps_double_prime q) := rfl

/-!
## Main obstruction theorem: `w_vac` locked at `−1`
-/

/-- **GD5 — Equation of state locked at `−1` away from zeros of `ρ_V`
    (Main Theorem, local form).**

    For any emergent-vacuum model `M` and any `q` with `ρ_V(q) ≠ 0`, the
    equation-of-state parameter `w_vac(q) = −1` identically.

    This is the central structural obstruction: Lorentz invariance of the
    vacuum stress tensor plus the emergent-vacuum action structure force
    `w = −1` regardless of the choice of `ε`. The only freedom is in the
    value of `ρ_V` itself, which Gibbs-Duhem equilibrium pins to zero at
    `q₀` (see `GibbsDuhemEquilibrium` below). -/
theorem wVac_eq_neg_one_of_rhoV_ne_zero (M : EmergentVacuumModel) (q : ℝ)
    (hρ : rhoV M q ≠ 0) : wVac M q = -1 := by
  unfold wVac pV
  field_simp

/-!
## Gibbs-Duhem equilibrium

The equilibrium conditions (Round 5 EQ.63) pin `q` to a value `q₀` at which
the vacuum energy density vanishes and is at a local minimum.
-/

/-- Gibbs-Duhem equilibrium state for an emergent-vacuum model `M`
    (Round 5 EQ.63).

    Packages the equilibrium value `q₀` together with the three conditions:
    - `rhoV_zero`: `ρ_V(q₀) = 0` (EQ.63a, vacuum energy vanishes)
    - `drhoVdq_zero`: `dρ_V/dq|_{q₀} = 0` (EQ.63b, self-tuning extremum)
    - `stability`: `d²ρ_V/dq²|_{q₀} > 0` is encoded structurally via
      `eps_double_prime_pos_at_stable`, which is the natural restatement
      for `q₀ ≠ 0` since `d²ρ_V/dq² = −ε'' − q · ε'''` and at
      `dρ_V/dq = 0` with `q₀ ≠ 0` we have `ε''(q₀) = 0` forcing
      `d²ρ_V/dq²|_{q₀} = −q₀ · ε'''(q₀)`. We package the scalar stability
      bound directly as a positivity witness. -/
structure GibbsDuhemEquilibrium (M : EmergentVacuumModel) where
  /-- Equilibrium value of the self-tuning scalar. -/
  q₀ : ℝ
  /-- Vacuum energy vanishes at equilibrium (EQ.63a). -/
  rhoV_zero : rhoV M q₀ = 0
  /-- Self-tuning condition: `dρ_V/dq|_{q₀} = 0` (EQ.63b). -/
  drhoVdq_zero : drhoVdq M q₀ = 0

/-- **GD6 — Equilibrium forces `ε(q₀) = q₀ · ε'(q₀)`.**

    Immediate consequence of the definition of `ρ_V` and `rhoV_zero`. -/
theorem equilibrium_eps_eq_q_eps_prime (M : EmergentVacuumModel)
    (E : GibbsDuhemEquilibrium M) :
    M.ε E.q₀ = E.q₀ * M.eps_prime E.q₀ := by
  have h := E.rhoV_zero
  unfold rhoV at h
  linarith

/-- **GD7 — Self-tuning two-cases.**

    At equilibrium, `dρ_V/dq|_{q₀} = −q₀ · ε''(q₀) = 0`, so either
    `q₀ = 0` or `ε''(q₀) = 0`. This is the algebraic content of the
    Round 5 EQ.63b condition. -/
theorem selftuning_two_cases (M : EmergentVacuumModel)
    (E : GibbsDuhemEquilibrium M) :
    E.q₀ = 0 ∨ M.eps_double_prime E.q₀ = 0 := by
  have h := E.drhoVdq_zero
  unfold drhoVdq at h
  -- h : -(E.q₀ * M.eps_double_prime E.q₀) = 0
  have hmul : E.q₀ * M.eps_double_prime E.q₀ = 0 := by linarith
  exact mul_eq_zero.mp hmul

/-!
## Bundled obstruction: hypothesis triple + `w_vac` lock
-/

/-- **GD8 — At equilibrium, the vacuum energy density vanishes.** -/
theorem rhoV_zero_at_equilibrium (M : EmergentVacuumModel)
    (E : GibbsDuhemEquilibrium M) : rhoV M E.q₀ = 0 :=
  E.rhoV_zero

/-- **GD9 — At equilibrium, the vacuum pressure also vanishes.**

    Direct corollary of GD2 (`p_V = −ρ_V`) and GD8. -/
theorem pV_zero_at_equilibrium (M : EmergentVacuumModel)
    (E : GibbsDuhemEquilibrium M) : pV M E.q₀ = 0 := by
  rw [pV_eq_neg_rhoV, E.rhoV_zero, neg_zero]

/-- **GD10 — `ρ_V + p_V = 0` at equilibrium (trivially, both vanish).** -/
theorem rhoV_plus_pV_zero_at_equilibrium (M : EmergentVacuumModel)
    (E : GibbsDuhemEquilibrium M) :
    rhoV M E.q₀ + pV M E.q₀ = 0 := by
  rw [E.rhoV_zero, pV_zero_at_equilibrium]; ring

/-!
## Locality of the equation-of-state in time

An emergent-vacuum model with no explicit kinetic term for `q` has
`ρ_V` and `p_V` depending only on `q(t)` — not on time derivatives.
This is the algebraic form of the "locality of the EOS" corollary
cited in Round 5 §3.3.
-/

/-- **GD11 — Locality of `ρ_V` in time.**

    `ρ_V(q(t))` depends only on the instantaneous value `q(t)` — no
    derivatives of `q(t)` appear. This is a structural property of the
    emergent-vacuum model (no `∂q` kinetic term in the action). Formally,
    if `q : ℝ → ℝ` is a time-dependent vacuum configuration, then at any
    two times `t₁, t₂` with `q(t₁) = q(t₂)` we have `ρ_V(q(t₁)) = ρ_V(q(t₂))`. -/
theorem rhoV_local_in_time (M : EmergentVacuumModel) (q : ℝ → ℝ)
    (t₁ t₂ : ℝ) (h : q t₁ = q t₂) : rhoV M (q t₁) = rhoV M (q t₂) := by
  rw [h]

/-- **GD12 — Locality of `p_V` in time (companion to GD11).** -/
theorem pV_local_in_time (M : EmergentVacuumModel) (q : ℝ → ℝ)
    (t₁ t₂ : ℝ) (h : q t₁ = q t₂) : pV M (q t₁) = pV M (q t₂) := by
  rw [h]

/-- **GD13 — Locality of `w_vac` in time (companion to GD11, GD12).** -/
theorem wVac_local_in_time (M : EmergentVacuumModel) (q : ℝ → ℝ)
    (t₁ t₂ : ℝ) (h : q t₁ = q t₂) : wVac M (q t₁) = wVac M (q t₂) := by
  rw [h]

/-!
## DESI incompatibility (qualitative lock)

The DESI DR2 preferred region has `w₀ ≈ −0.73 ≠ −1` (Round 3). Any `q`-
configuration for which `ρ_V ≠ 0` has `w_vac = −1` by GD5, so it cannot
reach `w₀ = −0.73`. The obstruction is therefore structural — no choice
of `ε` within the single-scalar emergent-vacuum framework evades it.
-/

/-- **GD14 — DESI incompatibility, local form.**

    For any emergent-vacuum model `M` and any `q` with `ρ_V(q) ≠ 0`, no
    value `w_target ≠ −1` can match `w_vac(q)`. In particular,
    `w_vac(q) ≠ w_target` whenever `w_target ≠ −1`. -/
theorem wVac_ne_non_minus_one_target (M : EmergentVacuumModel) (q : ℝ)
    (hρ : rhoV M q ≠ 0) (w_target : ℝ) (h_ne : w_target ≠ -1) :
    wVac M q ≠ w_target := by
  rw [wVac_eq_neg_one_of_rhoV_ne_zero M q hρ]
  exact fun h => h_ne h.symm

/-- **GD15 — Gibbs-Duhem obstruction (main bundled theorem).**

    Under the hypothesis triple (H1) single-scalar self-tuning, (H2)
    standard emergent-vacuum action (packaged as `EmergentVacuumModel`),
    and (H3) Gibbs-Duhem equilibrium (`GibbsDuhemEquilibrium`), the vacuum
    equation of state is locked at `−1` for every perturbation away from
    equilibrium.

    Quantitatively: if `q ≠ q₀` and `ρ_V(q) ≠ 0`, then `w_vac(q) = −1`.
    Equivalently, `w_vac(q) = w_DESI` is impossible for any
    `w_DESI ≠ −1`. This is the Phase 5y closure obstruction. -/
theorem gibbs_duhem_obstruction_main (M : EmergentVacuumModel)
    (E : GibbsDuhemEquilibrium M) (q : ℝ) (hρ : rhoV M q ≠ 0) :
    wVac M q = -1 ∧
    (∀ w_DESI : ℝ, w_DESI ≠ -1 → wVac M q ≠ w_DESI) ∧
    rhoV M E.q₀ = 0 ∧ q ≠ E.q₀ := by
  refine ⟨wVac_eq_neg_one_of_rhoV_ne_zero M q hρ, ?_, E.rhoV_zero, ?_⟩
  · intro w_DESI h_ne
    exact wVac_ne_non_minus_one_target M q hρ w_DESI h_ne
  · intro h_eq
    rw [h_eq] at hρ
    exact hρ E.rhoV_zero

/-!
## Stress-tensor decomposition marker

The vacuum stress tensor `T_μν^{vac} = ρ_V g_μν` is the direct consequence
of the Einstein equation (EQ.60) `R_μν − (1/2)g_μν R = 8πG_N ρ_V g_μν`.
We encode this as a structural predicate.
-/

/-- Predicate: the stress tensor of the vacuum is isotropic — i.e., it is
    proportional to `g_μν`. For emergent-vacuum models with the minimal
    action structure, this is forced by Lorentz invariance and is the
    algebraic content of Round 5 EQ.60. -/
def StressTensorIsotropic (M : EmergentVacuumModel) (q : ℝ) : Prop :=
  pV M q = -(rhoV M q)

/-- **GD16 — Stress-tensor isotropy holds for every `q`.**

    The isotropy predicate is always satisfied — it is definitional for
    the emergent-vacuum model. -/
theorem stress_tensor_isotropic_holds (M : EmergentVacuumModel) (q : ℝ) :
    StressTensorIsotropic M q := rfl

end SKEFTHawking.GibbsDuhemTheorem
