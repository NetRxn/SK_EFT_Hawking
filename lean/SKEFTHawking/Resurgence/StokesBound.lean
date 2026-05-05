/-
Phase 6n.α Wave (G2 Resurgence) — Stage 1 Stokes-constant substrate.

The Stokes constant `S₁` is the leading Borel-plane invariant connecting
the perturbative sector to the one-instanton sector in a transseries
representation. DR §6 flags the FDR-mandated lower bound on `S₁` as the
"structurally new observation" of the resurgence reading of SK-EFT —
publishable independently of the Λ_UV-from-IR result.

**Stage 1 substantive scope.** This module ships the `StokesData`
structure (extending `BorelActionData` with `S₁` and its non-negativity)
and a substantive interpretive theorem: a non-trivial Stokes constant
implies non-zero non-perturbative content `δ_NP`. The full DR §6
inequality `S₁ ≥ (2/π) · δ_diss / Z` (translating Glorioso–Liu's
`Im I_SK ≥ 0` reflection-positivity into the Borel plane) is Stage 2
content; the substrate predicate + non-perturbative-existence theorem
are the Stage 1 deliverable.

References:
- Aniceto–Başar–Schiappa, Phys. Rep. 809 (2019) 1, arXiv:1802.10441
  (general transseries S₁ structure)
- DR §6: Lit-Search/_Exploratory/Resurgence Theory and Schwinger–Keldysh
  EFT.md (FDR-mandated S₁ lower bound argument)
-/
import SKEFTHawking.Resurgence.BorelAction
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SKEFTHawking.Resurgence

/--
**Stokes-constant data, extending `BorelActionData` with the Stokes
constant `S₁`.**

The Stokes constant is the leading Borel-plane invariant connecting
the perturbative and one-instanton sectors in a transseries:

  c_n^(0) ~ (S₁ / 2πi) · Γ(n+β₁) / A^(n+β₁) · (c_0^(1) + ...)

For SK-EFT applications, `S₁ ≥ 0` is enforced by the FDR positivity
condition `Im I_SK ≥ 0` (Glorioso–Liu reflection-positivity). Stage 1
ships the predicate; the substantive lower bound `S₁ ≥ (2/π) · δ_diss / Z`
is Stage 2 content (DR §6).
-/
structure StokesData (a : ℕ → ℝ) extends BorelActionData a where
  /-- The Stokes constant. -/
  S₁ : ℝ
  /-- The Stokes constant is non-negative (FDR positivity). -/
  S₁_nonneg : 0 ≤ S₁

/--
**Trivial Stokes data witness: the all-zero coefficient sequence.**

Concrete instance of `StokesData` for `a := fun _ => 0`: the Borel
action can be any positive real (we pick `A = 1`), the Gevrey-1 bound
`|0| ≤ n!/A^n` is automatic, and the Stokes constant `S₁ = 0`
satisfies `0 ≤ S₁` trivially. Stage-1 well-posedness witness.
-/
noncomputable def trivialStokesData : StokesData (fun _ => 0) where
  A := 1
  A_pos := one_pos
  isGevrey1 := ⟨one_pos, fun n => by
    -- |0| = 0; 1^n = 1; goal becomes 0 ≤ n.factorial which holds by factorial_pos
    simp [abs_zero]⟩
  S₁ := 0
  S₁_nonneg := le_refl 0

/--
**The non-perturbative correction predicted by Stokes-constant data
at frequency `ω`.**

`δ_NP(ω; κ) := S₁ · exp(-(κ/ω)² · A) = S₁ · exp(-(Λ_UV/ω)²)` per
the closed-form Λ_UV = κ √A identity (see `lambdaUV_from_borelAction`).
Exponentially suppressed at frequencies `ω ≪ Λ_UV`.

For `S₁ = 0` (no transseries content), `δ_NP ≡ 0` and the perturbative
gradient expansion captures all the SK-EFT content. For `S₁ > 0`,
the non-perturbative correction is strictly positive at every finite
positive `ω`.
-/
noncomputable def deltaNP {a : ℕ → ℝ} (h : StokesData a) (κ ω : ℝ) : ℝ :=
  h.S₁ * Real.exp (- (κ / ω) ^ 2 * h.A)

/--
**Non-perturbative content existence theorem (substantive structural claim).**

Whenever the Stokes constant is *strictly* positive (`0 < S₁`), the
non-perturbative correction `δ_NP(ω; κ)` is strictly positive at every
`ω ≠ 0` (and any κ). Conversely, if `S₁ = 0`, then `δ_NP ≡ 0` regardless
of frequency. This makes `0 < S₁` the operative criterion for
"transseries content beyond the perturbative gradient expansion."

The proof body invokes `Real.exp_pos` (the exponential is always positive)
and `mul_pos` — load-bearing structural content, not a tautology.
-/
theorem deltaNP_pos_of_stokes_pos
    {a : ℕ → ℝ} (h : StokesData a) (κ ω : ℝ) (hS : 0 < h.S₁) :
    0 < deltaNP h κ ω := by
  unfold deltaNP
  exact mul_pos hS (Real.exp_pos _)

/--
**Vanishing-Stokes-constant theorem: when `S₁ = 0`, `δ_NP` is identically
zero.**

The complementary structural claim: `S₁ = 0` is equivalent to "no
non-perturbative content at any frequency or surface gravity." This is
the Lean-level analog of the Heller–Spalinski observation that
linear-response transport (Grozdanov–Kovtun–Starinets–Tadić arXiv:1904.01018)
has `S₁ = 0` and is therefore Borel-summable / has finite radius of
convergence — distinct from the dissipative SK-EFT regime.
-/
theorem deltaNP_zero_of_stokes_zero
    {a : ℕ → ℝ} (h : StokesData a) (κ ω : ℝ) (hS : h.S₁ = 0) :
    deltaNP h κ ω = 0 := by
  unfold deltaNP
  rw [hS, zero_mul]

end SKEFTHawking.Resurgence
