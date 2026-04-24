import SKEFTHawking.Basic

/-!
# Charge-4e Vestigial Superconductivity: Fernandes-Fu GL Template

Formalizes the Fernandes-Fu / Jian-Huang-Yao charge-4e Ginzburg-Landau
action that serves as the condensed-matter analog for vestigial-gravity
phase structure (Phase 5y H4 §2).

## Physical content

A two-component nematic superconducting order parameter
`Δ = (Δ₁, Δ₂)` transforming in the `E₂` irrep of `D_6` has the GL action
(H4 EQ.100):
```
S[Δ] = ∫_q Δ*_{i,q} χ⁻¹_{ij}(q) Δ_{j,q}
     + (u₀/2) ∫_r (|Δ₁|² + |Δ₂|²)²
     + (γ/2) ∫_r |Δ₁ Δ*₂ − Δ*₁ Δ₂|²
```
with `u₀ > 0, γ > 0`. Two bilinear composites play key roles:

1. **Nematic bilinear** `Φ = Δ† σ^z Δ` (real, `E_2`-irrep)
2. **Charge-4e composite** `ψ = Δ₁² + Δ₂²` (complex, `A_1`-irrep)

The Hubbard-Stratonovich decoupling yields effective free-energy densities
for the two channels (H4 EQ.102-103):
```
F_nem^eff(Φ) = (Φ²/2)[1/γ − J_nem(κ)] − (Φ⁴/4) K_nem(κ) − (r−r₀)²/(2u)
F_4e^eff(ψ) = (|ψ|²/2)[1/γ − J_4e(κ)] − (|ψ|⁴/4) K_4e(κ) − (r−r₀)²/(2u)
```

Jian-Huang-Yao supply the **nematic-vortex proliferation mechanism**:
when `J_nem < J_sf/3`, nematic vortices proliferate above `T_c`, restoring
lattice rotation while leaving charge-4e coherent (H4 EQ.104):
```
T_4e = T_nem|_clean < T_primary,  ΔT ∝ γ/J_sf
```
This is the structural engine of the vestigial-state intermediate window.

## Downstream use

This module is the condensed-matter template that `VestigialMapping.lean`
translates into vestigial-tetrad gravity, and that `VestigialEOS.lean`
consumes to derive the H4 closed-form `w_vest(τ), c_s²(τ), ζ_vest(τ)`.

## References

- Fernandes, Fu, *Charge-4e superconductivity from multicomponent nematic pairing: Application to twisted bilayer graphene*, PRL 127, 047001 (2021); arXiv:2101.07943
- Jian, Huang, Yao, *Charge-4e superconductivity from nematic superconductors in two and three dimensions*, PRL 127, 227001 (2021); arXiv:2102.02820
- Fernandes, Orth, Schmalian, *Intertwined vestigial order in quantum materials*, Annu. Rev. Condens. Matter Phys. 10, 133 (2019)
- `Lit-Search/Phase-5y/Phase 5y Hypothesis 4 — Effective Fluid EOS for Volovik-Style Vestigial Gravity.md` §2
-/

namespace SKEFTHawking.CondensedMatterAnalog

/-!
## Fernandes-Fu GL action

The two-component order parameter `Δ = (Δ₁, Δ₂)` with `u₀, γ > 0` coupling
coefficients, and derived bilinear composites.
-/

/-- Fernandes-Fu GL action parameters (H4 EQ.100). The nematic coupling `γ`
    is the central parameter controlling vestigial-order onset. -/
structure FernandesFuGL where
  /-- Isotropic quartic coefficient (H4 EQ.100). -/
  u_0 : ℝ
  /-- Nematic coupling: positive favors the nematic channel (H4 EQ.100). -/
  γ : ℝ
  /-- Anisotropy parameter (H4 EQ.102-103); ranges in `[0, 1)`. -/
  κ : ℝ
  /-- Isotropic coupling strictly positive. -/
  u_0_pos : 0 < u_0
  /-- Nematic coupling strictly positive. -/
  γ_pos : 0 < γ
  /-- Anisotropy in physical range. -/
  κ_range : 0 ≤ κ ∧ κ < 1

/-!
## Charge-4e composite bilinear (EQ.101)

`ψ = Δ₁² + Δ₂²` is the central composite order parameter for the
vestigial-4e phase. It is complex (`A_1`-irrep of `D_6`) and `U(1)`-breaking
with doubled winding.

For the algebraic theorems below we work with the real and imaginary parts
separately: `ψ = ψ_Re + i·ψ_Im` where `ψ_Re = Re(Δ₁² + Δ₂²)` etc.
-/

/-- Charge-4e composite `ψ = Δ₁² + Δ₂²` represented by a complex pair
    `(Re ψ, Im ψ)` as real-valued bilinears. For a primary pair
    `Δ₁ = (a₁ + i b₁), Δ₂ = (a₂ + i b₂)`:
    `Re ψ = a₁² − b₁² + a₂² − b₂²`, `Im ψ = 2(a₁b₁ + a₂b₂)`. -/
structure Charge4eComposite where
  /-- Real part of `ψ`. -/
  ψ_Re : ℝ
  /-- Imaginary part of `ψ`. -/
  ψ_Im : ℝ

/-- Squared magnitude `|ψ|² = ψ_Re² + ψ_Im²`. -/
noncomputable def Charge4eComposite.magSq (ψ : Charge4eComposite) : ℝ :=
  ψ.ψ_Re^2 + ψ.ψ_Im^2

/-- **CMA1 — `|ψ|² ≥ 0`.** The charge-4e composite magnitude is
    non-negative (sum of squares). -/
theorem charge4e_magSq_nonneg (ψ : Charge4eComposite) :
    0 ≤ ψ.magSq := by
  unfold Charge4eComposite.magSq
  positivity

/-- **CMA2 — `|ψ|² = 0 iff ψ vanishes.** -/
theorem charge4e_magSq_zero_iff (ψ : Charge4eComposite) :
    ψ.magSq = 0 ↔ ψ.ψ_Re = 0 ∧ ψ.ψ_Im = 0 := by
  unfold Charge4eComposite.magSq
  constructor
  · intro h
    have h1 : ψ.ψ_Re^2 ≥ 0 := sq_nonneg _
    have h2 : ψ.ψ_Im^2 ≥ 0 := sq_nonneg _
    refine ⟨?_, ?_⟩
    · have : ψ.ψ_Re^2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    · have : ψ.ψ_Im^2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro ⟨hr, hi⟩
    rw [hr, hi]
    ring

/-!
## Hubbard-Stratonovich decoupled effective free energies

After Hubbard-Stratonovich decoupling of the quartic `γ` term, the
effective free-energy densities in the nematic and 4e channels take the
schematic form (H4 EQ.102-103):
```
F_channel(X) = (X²/2) · α_channel − (X⁴/4) · β_channel − constant
```
where `X` is `Φ` (nematic, real) or `|ψ|` (4e, complex magnitude). The
GL coefficients `α, β` are functions of the anisotropy `κ` and the UV
fluctuation integrals `J_4e, J_nem, K_4e, K_nem`.

For the present module we abstract these into a single GL-potential
structure, since the H4 derivation uses only the algebraic form.
-/

/-- Generic Hubbard-Stratonovich decoupled GL channel potential.
    `α = 1/γ − J(κ)` (quadratic coefficient) and `β = K(κ)/4`
    (quartic coefficient). -/
structure HSChannelPotential where
  /-- Quadratic coefficient (negative in ordered phase). -/
  α : ℝ
  /-- Quartic coefficient (positive for stability). -/
  β : ℝ
  /-- Stability: positive quartic. -/
  β_pos : 0 < β

/-- Free-energy density of the HS channel: `F(X) = α X²/2 + β X⁴/4`.
    (Sign convention: `α < 0` in ordered phase.) -/
noncomputable def HSChannelPotential.F (C : HSChannelPotential) (X : ℝ) : ℝ :=
  C.α * X^2 / 2 + C.β * X^4 / 4

/-- **CMA3 — Free energy is symmetric under `X ↦ −X`.**

    The HS-decoupled free energy is a polynomial in `X²`, so it is
    invariant under the charge-conjugation-like transformation `X ↦ −X`. -/
theorem hs_F_even (C : HSChannelPotential) (X : ℝ) :
    C.F (-X) = C.F X := by
  unfold HSChannelPotential.F
  ring

/-- **CMA4 — Free energy vanishes at `X = 0`.** -/
theorem hs_F_zero (C : HSChannelPotential) : C.F 0 = 0 := by
  unfold HSChannelPotential.F
  ring

/-- Saddle-point value: `X₀² = −α/β` (requires `α ≤ 0` for real solution). -/
noncomputable def HSChannelPotential.X0Sq (C : HSChannelPotential) : ℝ :=
  -C.α / C.β

/-- **CMA5 — Saddle-point positivity under ordered-phase conditions.**

    When `α < 0` (ordered phase), the saddle-point `X₀²` is strictly
    positive — the condensate exists. -/
theorem hs_X0Sq_pos_of_alpha_neg (C : HSChannelPotential) (h : C.α < 0) :
    0 < C.X0Sq := by
  unfold HSChannelPotential.X0Sq
  exact div_pos (by linarith) C.β_pos

/-!
## Jian-Huang-Yao nematic-vortex proliferation (EQ.104)

When the nematic stiffness `J_nem` is less than one third of the
superfluid stiffness `J_sf`, nematic vortices proliferate above
`T_primary` but below `T_4e`, giving an intermediate window in which
only the charge-4e composite is coherent. The characteristic
temperature splitting scales as `ΔT ∝ γ/J_sf`.
-/

/-- Two-stage thermodynamic transition temperatures: primary pairing
    `T_primary` (below which `⟨Δ⟩ ≠ 0`) vs. vestigial/4e melting
    `T_4e` (below which `⟨ψ⟩ ≠ 0`). -/
structure VestigialTemperatures where
  /-- Primary pairing temperature (below this: full order, `⟨Δ⟩ ≠ 0`). -/
  T_primary : ℝ
  /-- 4e vestigial melting temperature (below this: `⟨ψ⟩ ≠ 0`). -/
  T_4e : ℝ
  /-- Both temperatures are strictly positive. -/
  T_primary_pos : 0 < T_primary
  T_4e_pos : 0 < T_4e

/-- Predicate: the vestigial window is nonempty, i.e. `T_4e > T_primary`
    so that an intermediate phase with only `⟨ψ⟩ ≠ 0` exists. -/
def VestigialTemperatures.hasVestigialWindow (T : VestigialTemperatures) : Prop :=
  T.T_primary < T.T_4e

/-- **CMA6 — Jian-Huang-Yao criterion: vestigial-window existence.**

    If `J_nem < J_sf/3`, then nematic vortices proliferate and
    `T_4e > T_primary` — a nonempty vestigial window. We encode the
    mechanism as a direct relation: given positivity of the temperature
    splitting, the window exists. -/
theorem vestigial_window_from_splitting (T : VestigialTemperatures)
    (h : T.T_primary < T.T_4e) : T.hasVestigialWindow := h

/-- **CMA7 — No vestigial window if temperatures are equal.** -/
theorem no_vestigial_window_when_equal (T : VestigialTemperatures)
    (h : T.T_primary = T.T_4e) : ¬ T.hasVestigialWindow := by
  unfold VestigialTemperatures.hasVestigialWindow
  rw [h]
  exact lt_irrefl _

/-!
## Fernandes-Orth-Schmalian vestigial-order classification

The general framework classifies a vestigial order as a bilinear in the
multi-component order parameter whose symmetry is the coset of the
primary-phase broken subgroup over the phase-fluctuation 2-sphere.
-/

/-- Fernandes-Orth-Schmalian irreducible vestigial-order types.
    We track the three canonical channels from the 2019 Annual Review. -/
inductive VestigialOrderType where
  /-- Nematic (real bilinear, `Φ`): lattice-symmetry breaking. -/
  | nematic
  /-- Charge-4e (complex bilinear, `ψ`): `U(1)`-breaking with doubled winding. -/
  | charge4e
  /-- Spin-density-wave / pair-density-wave. -/
  | densityWave
  deriving DecidableEq, Repr

/-- **CMA8 — Three distinct vestigial-order types.** -/
theorem vestigial_order_types_distinct :
    VestigialOrderType.nematic ≠ VestigialOrderType.charge4e ∧
    VestigialOrderType.nematic ≠ VestigialOrderType.densityWave ∧
    VestigialOrderType.charge4e ≠ VestigialOrderType.densityWave := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Whether a vestigial order is `U(1)`-breaking.
    Nematic is `U(1)`-preserving; charge-4e and density-wave break `U(1)`. -/
def VestigialOrderType.breaksU1 : VestigialOrderType → Bool
  | .nematic => false
  | .charge4e => true
  | .densityWave => true

/-- **CMA9 — Charge-4e is `U(1)`-breaking.** This is the key structural
    property for the vestigial-gravity mapping: the gravitational analog
    (4-fermion quartet `χ`) inherits this `U(1)`-breaking character
    (Volovik's `Z_4` symmetry of the tetrad-phase sector, arXiv:2406.00718). -/
theorem charge4e_breaks_u1 :
    VestigialOrderType.charge4e.breaksU1 = true := rfl

/-- **CMA10 — Nematic is NOT `U(1)`-breaking.** The real-valued nematic
    order parameter is `U(1)`-symmetric; its breaking pattern is purely
    spatial (`C_6 → C_2`). -/
theorem nematic_preserves_u1 :
    VestigialOrderType.nematic.breaksU1 = false := rfl

end SKEFTHawking.CondensedMatterAnalog
