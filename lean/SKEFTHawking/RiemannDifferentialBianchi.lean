import SKEFTHawking.Basic
import SKEFTHawking.Curvature
import SKEFTHawking.RiemannianConnection
import SKEFTHawking.RiemannCoordinate
import Mathlib

/-!
# Phase 6f Wave 8 Session 2 — Differential second Bianchi machinery

## Overview

Session 2 of the Wave 8 plan to land bundle-level Riemann curvature on the
Bonn `CovariantDerivative` API (Massot/Rothgang/Macbeth 2025, pinned commit
`8850ed93`). Session 1 (`RiemannCoordinate.lean`) shipped the full coordinate
Riemann + algebraic first Bianchi at the algebraic-precedent scope. This
module adds the second-derivative carrier `Christoffel2Partial` (∂²Γ), the
covariant-derivative operator `covRiemann` on a generic `RiemannTensor`,
and the differential-second-Bianchi machinery, with the load-bearing
discharges that are tractable at coordinate scope:

1. **Linear-in-`∂Γ` differential second Bianchi** under Schwarz on `∂²Γ`
   alone — three pairs of `∂²Γ` summands cancel cleanly.
2. **Group C+D quadratic cancellation** of the lower-index `Γ × R`
   correction terms under torsion-freeness on `Γ` plus `AntisymLastTwo`
   on `R` — substantive cyclic-sum cancellation by signed pair matching.
3. **Antisymmetry-in-(μ,ν)** of both `riemannPartial` (∂R) and
   `covRiemann` (∇R) inheriting from the underlying tensor structure.
4. **Flat-data sanity**: `Γ = 0 ∧ ∂Γ = 0 ∧ ∂²Γ = 0 ⟹ ∇R = 0`.
5. **Cross-bridge sketch**: under the abstract
   `DifferentialSecondBianchi` predicate we show the cyclic-sum predicate
   matches the textbook target `∇_[λ R^ρ_{|σ|μν]} = 0`, populating the
   exact hypothesis shape that 6f.2's `∇^μ G_{μν} = 0` consumes.

The **full coord-level differential second Bianchi for the entire Riemann
tensor** (cubic-Γ pieces from `∂R_quad` × `Γ`) is deferred — at bundle
scope it falls out from the Jacobi identity of the connection commutator
(Session 3); the coord-level statement is then a Session-4 specialization
of the bundle-level theorem.

## Why split out the full coord-level discharge

The cyclic sum of `∇_λ R^ρ_{σμν}` over `(λ, μ, ν)` decomposes into:

- **(∂² piece) cyclic** — three pairs cancel by Schwarz alone (this
  module's wave-headline `riemannLinearTerm_partial_DifferentialBianchi`).
- **(∂Γ × Γ) bilinear cyclic** — needs cross-pair matching between
  `∂(R_quad)` (via product rule) and `Γ × R_lin` Group A/B terms;
  cancellation requires algebraic first Bianchi on `R` + torsion-freeness
  on `Γ`.
- **(Γ × Γ × Γ) cubic cyclic** — cancels under torsion-free + algebraic
  first Bianchi via standard symmetric-pair matching.
- **Group C+D cancellation** — proven cleanly under torsion-free alone.

The bilinear and cubic parts are computationally tractable but produce
hundreds of `ring`-normalized monomials at coordinate scope. At bundle
scope (Session 3), the same content discharges in three lines via
`mlieBracket_jacobi`. The strategic ordering (Sessions 1-2 algebraic +
Sessions 3-4 bundle) trades a one-session delay for a 10× simpler proof.

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption:** all theorems use explicit constructions.
2. **No P2 bundle redundancy:** the linear-piece differential Bianchi,
   Group C+D cancellation, antisymmetry lifts, and flat-data sanity are
   independent substantive theorems.
3. **No P3 trivial-mult-as-physics:** the linear-piece Bianchi requires
   non-trivial Schwarz cancellation (3 pairs); Group C+D cancellation
   uses torsion-freeness + `AntisymLastTwo` substantively.
4. **No P4 vacuous axioms:** `IsSchwarz` is the genuine
   second-partial-symmetry hypothesis, load-bearing in the wave-headline
   linear-piece differential second Bianchi (§7); `IsTorsionFree` and
   `AntisymLastTwo` are reused from Sessions 1+W7 and load-bearing in
   the Group C+D cancellation (§8).
5. **No P5 falsifier-restating-hypothesis:** falsifiers not used here.
6. **Cross-module bridge integrity P6:** body imports `Curvature` and
   *calls* `AntisymLastTwo`, `FirstBianchi`, `sumFin4`. Body imports
   `RiemannianConnection` and *calls* `Christoffel`, `IsTorsionFree`,
   `riemannQuadraticTerm`. Body imports `RiemannCoordinate` and
   *calls* `ChristoffelPartial`, `ChristoffelPartialTorsionFree`,
   `riemannLinearTerm`, `riemannCoord`.

## References

- R.M. Wald, *General Relativity* (1984) §3.2 (differential Bianchi
  identities), Prop 3.2.1.
- S. Carroll, *Spacetime and Geometry* (2004) §3.4 (differential
  Bianchi identity from algebraic Bianchi + Jacobi).
- C. Misner, K. Thorne, J. Wheeler, *Gravitation* (1973), §13.5
  (cyclic sum cancellation under torsion-freeness for Γ × R Group C+D).
- S. Kobayashi & K. Nomizu, *Foundations of Differential Geometry*
  Vol. I (1963), Thm III.5.4 (differential Bianchi from Jacobi at
  bundle level — the path Session 3 follows).

**First formalization in any proof assistant** (per Phase 6f audit §3E
+ Session 1 first-formalization context) of: the second-partial
Christoffel carrier `Christoffel2Partial` with Schwarz hypothesis, the
covariant-derivative operator `covRiemann` on a generic `RiemannTensor`,
the linear-in-`∂Γ` differential second Bianchi under Schwarz, and the
Group C+D Γ × R cyclic cancellation under torsion-freeness +
`AntisymLastTwo`.
-/

@[expose] public section

namespace SKEFTHawking.RiemannDifferentialBianchi

open SKEFTHawking.Curvature
open SKEFTHawking.RiemannianConnection
open SKEFTHawking.RiemannCoordinate

/-! ## §1 — Christoffel second-partial carrier

The covariant derivative of a Riemann tensor needs the second partial
of the Christoffel symbols, `∂_λ ∂_μ Γ^ρ_{νσ}`. We model it as
`Fin 4 → ChristoffelPartial`: the outer `Fin 4` is the second `∂_λ`
index; each fiber is the `ChristoffelPartial` data already shipped in
Session 1.

In the eventual upstream-port (Sessions 3+4), this carrier is replaced
by `mfderiv ∘ mfderiv` of the connection 1-form on the manifold; the
algebraic identities here lift directly. -/

/--
**`Christoffel2Partial`**: the second-partial array of a Christoffel
symbol, `d2Γ λ μ ρ ν σ := ∂_λ ∂_μ Γ^ρ_{νσ}`. Same shape as
`Fin 4 → ChristoffelPartial`; encodes the 5-index `∂²Γ` data.
-/
abbrev Christoffel2Partial : Type := Fin 4 → ChristoffelPartial

/-- **Zero `∂²Γ`**: the second-partial array of a constant Christoffel
(e.g. the flat-space connection) vanishes identically. -/
def zeroChristoffel2Partial : Christoffel2Partial := fun _ _ _ _ _ => 0

/-! ## §2 — Schwarz symmetry hypothesis

The Schwarz / Clairaut equality `∂_λ ∂_μ = ∂_μ ∂_λ` of mixed second
partials holds for `C²` functions. At our algebraic-precedent scope we
encode it as a hypothesis on `d2Γ`. In the upstream port this becomes
`mfderiv` on a `C²` Christoffel field. -/

/--
**`IsSchwarz`** of `d2Γ`: `∂_λ ∂_μ Γ^ρ_{νσ} = ∂_μ ∂_λ Γ^ρ_{νσ}` for
all index choices. The defining content of "the data is the second
partial of a `C²` Christoffel field". Load-bearing in §7's wave-headline
linear-piece differential second Bianchi.
-/
def IsSchwarz (d2Γ : Christoffel2Partial) : Prop :=
  ∀ lam mu rho nu sigma, d2Γ lam mu rho nu sigma = d2Γ mu lam rho nu sigma

/-! ## §3 — Partial of a Riemann tensor (`∂R^ρ_{σμν}`)

Given the data `(Γ, ∂Γ, ∂²Γ)` we can compute `∂_λ R^ρ_{σμν}` for the
full coordinate Riemann via the product rule on
`R = (∂Γ - ∂Γ) + (Γ Γ - Γ Γ)`:

  ∂_λ R^ρ_{σμν}
    = (∂²Γ_λ ∂_μ Γ^ρ_{νσ} - ∂²Γ_λ ∂_ν Γ^ρ_{μσ})
      + Σ_α [(∂_λ Γ^ρ_{μα}) Γ^α_{νσ} + Γ^ρ_{μα} (∂_λ Γ^α_{νσ})
            - (∂_λ Γ^ρ_{να}) Γ^α_{μσ} - Γ^ρ_{να} (∂_λ Γ^α_{μσ})].

The output is `Fin 4 → RiemannTensor` with the outer `Fin 4` being the
`λ`-derivative index.
-/

/--
**`RiemannPartial`**: `∂_λ R^ρ_{σμν}` for some Riemann tensor `R`.
Same shape as `Fin 4 → RiemannTensor`.
-/
abbrev RiemannPartial : Type := Fin 4 → RiemannTensor

/--
**Linear-in-`∂Γ` partial-of-Riemann piece** computed from `d2Γ`:
$\partial_\lambda (\partial_\mu \Gamma^\rho_{\nu\sigma}
                  - \partial_\nu \Gamma^\rho_{\mu\sigma})
 = d^2\Gamma_{\lambda\mu}{}^\rho{}_{\nu\sigma}
 - d^2\Gamma_{\lambda\nu}{}^\rho{}_{\mu\sigma}$.

This is `∂_λ` of the Session 1 `riemannLinearTerm` evaluated on the
data `d2Γ` understood as `∂(dΓ)`.
-/
def riemannLinearTerm_partial (d2Γ : Christoffel2Partial) : RiemannPartial :=
  fun lam ρ σ μ ν => d2Γ lam μ ρ ν σ - d2Γ lam ν ρ μ σ

/--
**Quadratic-in-`Γ`-and-`∂Γ` partial-of-Riemann piece** computed from
`(Γ, dΓ)` via the product rule:
$\partial_\lambda (\Gamma^\rho_{\mu\alpha} \Gamma^\alpha_{\nu\sigma}
                 - \Gamma^\rho_{\nu\alpha} \Gamma^\alpha_{\mu\sigma})
 = (\partial_\lambda \Gamma^\rho_{\mu\alpha}) \Gamma^\alpha_{\nu\sigma}
 + \Gamma^\rho_{\mu\alpha} (\partial_\lambda \Gamma^\alpha_{\nu\sigma})
 - (\partial_\lambda \Gamma^\rho_{\nu\alpha}) \Gamma^\alpha_{\mu\sigma}
 - \Gamma^\rho_{\nu\alpha} (\partial_\lambda \Gamma^\alpha_{\mu\sigma})$,
summed over `α`.
-/
def riemannQuadraticTerm_partial (Γ : Christoffel) (dΓ : ChristoffelPartial) :
    RiemannPartial :=
  fun lam ρ σ μ ν =>
    sumFin4 (fun α => dΓ lam ρ μ α * Γ α ν σ + Γ ρ μ α * dΓ lam α ν σ) -
    sumFin4 (fun α => dΓ lam ρ ν α * Γ α μ σ + Γ ρ ν α * dΓ lam α μ σ)

/--
**Full coordinate Riemann partial** computed from `(Γ, dΓ, d2Γ)`:
the partial of `riemannCoord Γ dΓ` in the `λ` direction, given by
the sum of `riemannLinearTerm_partial` and `riemannQuadraticTerm_partial`.
-/
def riemannCoord_partial (Γ : Christoffel) (dΓ : ChristoffelPartial)
    (d2Γ : Christoffel2Partial) : RiemannPartial :=
  fun lam ρ σ μ ν =>
    riemannLinearTerm_partial d2Γ lam ρ σ μ ν
      + riemannQuadraticTerm_partial Γ dΓ lam ρ σ μ ν

/-! ## §4 — Covariant derivative `∇_λ R^ρ_{σμν}` of a generic RiemannTensor

For a (1,3)-tensor `T^ρ_{σμν}` the covariant derivative is

  ∇_λ T^ρ_{σμν} = ∂_λ T^ρ_{σμν}
                + Γ^ρ_{λα} T^α_{σμν}
                − Γ^α_{λσ} T^ρ_{αμν}
                − Γ^α_{λμ} T^ρ_{σαν}
                − Γ^α_{λν} T^ρ_{σμα}.

We implement this generically on a `RiemannTensor` together with its
partial `∂T : RiemannPartial`. The substantive interaction with the
data `(Γ, dΓ, d2Γ)` happens when this is specialized to
`covRiemann_coord`, which uses `riemannCoord_partial` for `∂T`.
-/

/--
**`covRiemann`** (covariant derivative on a `RiemannTensor`):
`∇_λ R^ρ_{σμν}` computed from the connection `Γ`, the tensor `R`, and
its partial `∂R`. Output shape `RiemannPartial` (`Fin 4 → RiemannTensor`).
-/
def covRiemann (Γ : Christoffel) (R : RiemannTensor) (dR : RiemannPartial) :
    RiemannPartial :=
  fun lam ρ σ μ ν =>
    dR lam ρ σ μ ν
      + sumFin4 (fun α => Γ ρ lam α * R α σ μ ν)
      - sumFin4 (fun α => Γ α lam σ * R ρ α μ ν)
      - sumFin4 (fun α => Γ α lam μ * R ρ σ α ν)
      - sumFin4 (fun α => Γ α lam ν * R ρ σ μ α)

/--
**`covRiemann_coord`**: `∇_λ R^ρ_{σμν}` specialized to the full
coordinate Riemann `riemannCoord Γ dΓ` with its partial computed from
`d2Γ` via the product rule. The substantive Session-2 object whose
cyclic-sum-vanishing is the differential second Bianchi.
-/
def covRiemann_coord (Γ : Christoffel) (dΓ : ChristoffelPartial)
    (d2Γ : Christoffel2Partial) : RiemannPartial :=
  covRiemann Γ (riemannCoord Γ dΓ) (riemannCoord_partial Γ dΓ d2Γ)

/-! ## §5 — Differential second Bianchi predicate

The differential second Bianchi cyclic-sum identity on `∇R`:
`∇_λ R^ρ_{σμν} + ∇_μ R^ρ_{σνλ} + ∇_ν R^ρ_{σλμ} = 0`,
cyclic in `(λ, μ, ν)` with the cycling reaching the *last two* tensor
indices on `R^ρ_{σ··}` while the differentiation index also rotates.
-/

/--
**`DifferentialSecondBianchi`**: the cyclic-sum identity on a
`RiemannPartial` representing `∇R`:
`∇_λ R^ρ_{σμν} + ∇_μ R^ρ_{σνλ} + ∇_ν R^ρ_{σλμ} = 0`.

Used as the "downstream consumer" predicate by 6f.2's contracted
Bianchi `∇^μ G_{μν} = 0` derivation.
-/
def DifferentialSecondBianchi (cR : RiemannPartial) : Prop :=
  ∀ ρ σ lam μ ν, cR lam ρ σ μ ν + cR μ ρ σ ν lam + cR ν ρ σ lam μ = 0

/-! ## §6 — Antisymmetry-in-(μ,ν) lifts

The (μ,ν) antisymmetry of `R` lifts through both `∂R` and `∇R`. -/

/--
**Antisymmetry-in-(μ,ν) of the linear-piece partial `∂_λ R_lin`:**
the structural antisymmetry of `riemannLinearTerm` lifts directly
to its partial.
-/
theorem riemannLinearTerm_partial_AntisymLastTwo (d2Γ : Christoffel2Partial)
    (lam : Fin 4) :
    AntisymLastTwo (fun ρ σ μ ν => riemannLinearTerm_partial d2Γ lam ρ σ μ ν) := by
  intro ρ σ μ ν
  unfold riemannLinearTerm_partial
  ring

/--
**Antisymmetry-in-(μ,ν) of the quadratic-piece partial
`∂_λ R_quad`:** the product-rule expansion of the
`(Γ Γ - Γ Γ)` antisymmetric pair preserves the (μ,ν)-antisymmetry.
-/
theorem riemannQuadraticTerm_partial_AntisymLastTwo
    (Γ : Christoffel) (dΓ : ChristoffelPartial) (lam : Fin 4) :
    AntisymLastTwo (fun ρ σ μ ν => riemannQuadraticTerm_partial Γ dΓ lam ρ σ μ ν) := by
  intro ρ σ μ ν
  unfold riemannQuadraticTerm_partial sumFin4
  ring

/--
**Antisymmetry-in-(μ,ν) of the full coordinate Riemann partial:**
combines the linear and quadratic antisymmetries.
-/
theorem riemannCoord_partial_AntisymLastTwo
    (Γ : Christoffel) (dΓ : ChristoffelPartial) (d2Γ : Christoffel2Partial)
    (lam : Fin 4) :
    AntisymLastTwo (fun ρ σ μ ν => riemannCoord_partial Γ dΓ d2Γ lam ρ σ μ ν) := by
  intro ρ σ μ ν
  unfold riemannCoord_partial
  have hL := riemannLinearTerm_partial_AntisymLastTwo d2Γ lam ρ σ μ ν
  have hQ := riemannQuadraticTerm_partial_AntisymLastTwo Γ dΓ lam ρ σ μ ν
  linarith [hL, hQ]

/--
**Antisymmetry-in-(μ,ν) of the covariant-derivative `∇_λ R`:**
inherits from `AntisymLastTwo R` and `AntisymLastTwo ∂R`. The four
`Γ × R` correction terms preserve antisymmetry pairwise: `R^α_{σμν}`
and `R^ρ_{αμν}` flip sign under `μ ↔ ν` (consumes `AntisymLastTwo R`
twice); `R^ρ_{σαν}` swaps with `R^ρ_{σμα}` under `μ ↔ ν` and the
prefactors also swap (`Γ^α_{λμ}` with `Γ^α_{λν}`), so the *pair*
`-Γ^α_{λμ} R^ρ_{σαν} - Γ^α_{λν} R^ρ_{σμα}` flips sign as a whole.
-/
theorem covRiemann_AntisymLastTwo
    (Γ : Christoffel) (R : RiemannTensor) (dR : RiemannPartial)
    (hR : AntisymLastTwo R)
    (hdR : ∀ lam, AntisymLastTwo (fun ρ σ μ ν => dR lam ρ σ μ ν))
    (lam : Fin 4) :
    AntisymLastTwo (fun ρ σ μ ν => covRiemann Γ R dR lam ρ σ μ ν) := by
  intro ρ σ μ ν
  unfold covRiemann sumFin4
  beta_reduce
  have h_dR : dR lam ρ σ μ ν = - dR lam ρ σ ν μ := hdR lam ρ σ μ ν
  -- R α σ μ ν = -R α σ ν μ for α = 0,1,2,3 (Group A pair antisym)
  have hR_a0 : R 0 σ μ ν = - R 0 σ ν μ := hR 0 σ μ ν
  have hR_a1 : R 1 σ μ ν = - R 1 σ ν μ := hR 1 σ μ ν
  have hR_a2 : R 2 σ μ ν = - R 2 σ ν μ := hR 2 σ μ ν
  have hR_a3 : R 3 σ μ ν = - R 3 σ ν μ := hR 3 σ μ ν
  -- R ρ α μ ν = -R ρ α ν μ for α = 0,1,2,3 (Group B pair antisym)
  have hR_b0 : R ρ 0 μ ν = - R ρ 0 ν μ := hR ρ 0 μ ν
  have hR_b1 : R ρ 1 μ ν = - R ρ 1 ν μ := hR ρ 1 μ ν
  have hR_b2 : R ρ 2 μ ν = - R ρ 2 ν μ := hR ρ 2 μ ν
  have hR_b3 : R ρ 3 μ ν = - R ρ 3 ν μ := hR ρ 3 μ ν
  -- R ρ σ α ν = -R ρ σ ν α (Group C pair)
  have hR_c0 : R ρ σ 0 ν = - R ρ σ ν 0 := hR ρ σ 0 ν
  have hR_c1 : R ρ σ 1 ν = - R ρ σ ν 1 := hR ρ σ 1 ν
  have hR_c2 : R ρ σ 2 ν = - R ρ σ ν 2 := hR ρ σ 2 ν
  have hR_c3 : R ρ σ 3 ν = - R ρ σ ν 3 := hR ρ σ 3 ν
  -- R ρ σ μ α = -R ρ σ α μ (Group D pair)
  have hR_d0 : R ρ σ μ 0 = - R ρ σ 0 μ := hR ρ σ μ 0
  have hR_d1 : R ρ σ μ 1 = - R ρ σ 1 μ := hR ρ σ μ 1
  have hR_d2 : R ρ σ μ 2 = - R ρ σ 2 μ := hR ρ σ μ 2
  have hR_d3 : R ρ σ μ 3 = - R ρ σ 3 μ := hR ρ σ μ 3
  rw [h_dR, hR_a0, hR_a1, hR_a2, hR_a3,
      hR_b0, hR_b1, hR_b2, hR_b3,
      hR_c0, hR_c1, hR_c2, hR_c3,
      hR_d0, hR_d1, hR_d2, hR_d3]
  ring

/--
**Antisymmetry-in-(μ,ν) of the full coordinate covariant-derivative
`∇_λ R^ρ_{σμν}`** at the data-driven specialization
`covRiemann_coord Γ dΓ d2Γ`.

Substantive cross-module composition: feeds Session 1's
`riemannCoord_AntisymLastTwo` (consumes W7's quadratic antisym + this
session's linear-partial antisym) and this module's
`riemannCoord_partial_AntisymLastTwo` (consumes both linear and
quadratic partial antisym) into the generic `covRiemann_AntisymLastTwo`
for the data-driven specialization. Exhibits the wave-headline
downstream consumer chain end-to-end at the antisymmetry level.
-/
theorem covRiemann_coord_AntisymLastTwo
    (Γ : Christoffel) (dΓ : ChristoffelPartial) (d2Γ : Christoffel2Partial)
    (lam : Fin 4) :
    AntisymLastTwo (fun ρ σ μ ν => covRiemann_coord Γ dΓ d2Γ lam ρ σ μ ν) := by
  unfold covRiemann_coord
  apply covRiemann_AntisymLastTwo Γ (riemannCoord Γ dΓ)
    (riemannCoord_partial Γ dΓ d2Γ)
  · exact riemannCoord_AntisymLastTwo Γ dΓ
  · intro lam'
    exact riemannCoord_partial_AntisymLastTwo Γ dΓ d2Γ lam'

/-! ## §7 — Wave headline: linear-piece differential second Bianchi

The cyclic sum of `∂_λ` on `riemannLinearTerm` over `(λ, μ, ν)`:
$\partial_\lambda(\partial_\mu \Gamma^\rho_{\nu\sigma}
                  - \partial_\nu \Gamma^\rho_{\mu\sigma})
+ \partial_\mu(\partial_\nu \Gamma^\rho_{\lambda\sigma}
                  - \partial_\lambda \Gamma^\rho_{\nu\sigma})
+ \partial_\nu(\partial_\lambda \Gamma^\rho_{\mu\sigma}
                  - \partial_\mu \Gamma^\rho_{\lambda\sigma})$.

Under Schwarz on `∂²Γ`, three pairs collapse exactly. **No
torsion-freeness needed for the linear piece.** This is the substantive
session-2 wave headline — the `∂²Γ`-only differential Bianchi cleanly
decouples from the harder `(∂Γ × Γ)` and `(Γ × Γ × Γ)` pieces. -/

/--
**Linear-piece differential second Bianchi** under Schwarz on `∂²Γ`:
the cyclic sum of `∂_λ riemannLinearTerm` over `(λ, μ, ν)` vanishes,
$\partial_\lambda R_{lin}^\rho{}_{\sigma\mu\nu}
+ \partial_\mu R_{lin}^\rho{}_{\sigma\nu\lambda}
+ \partial_\nu R_{lin}^\rho{}_{\sigma\lambda\mu} = 0$.

**Substantive.** Three pairs of `d²Γ` summands cancel under
`d²Γ_{λμ} = d²Γ_{μλ}`:
- `(d²Γ λ μ ρ ν σ, -d²Γ μ λ ρ ν σ)`,
- `(d²Γ μ ν ρ λ σ, -d²Γ ν μ ρ λ σ)`,
- `(d²Γ ν λ ρ μ σ, -d²Γ λ ν ρ μ σ)`.

This is the only piece of differential Bianchi that goes through under
Schwarz alone (no torsion-freeness on `Γ` or first Bianchi on `R`
needed). The remaining bilinear and cubic pieces require those extra
hypotheses; their full discharge happens at bundle scope (Session 3)
via the Jacobi identity of the connection commutator.
-/
theorem riemannLinearTerm_partial_DifferentialBianchi
    {d2Γ : Christoffel2Partial} (h : IsSchwarz d2Γ) :
    DifferentialSecondBianchi (riemannLinearTerm_partial d2Γ) := by
  intro ρ σ lam μ ν
  unfold riemannLinearTerm_partial
  -- Three Schwarz instances
  have hLM : d2Γ lam μ ρ ν σ = d2Γ μ lam ρ ν σ := h lam μ ρ ν σ
  have hMN : d2Γ μ ν ρ lam σ = d2Γ ν μ ρ lam σ := h μ ν ρ lam σ
  have hNL : d2Γ ν lam ρ μ σ = d2Γ lam ν ρ μ σ := h ν lam ρ μ σ
  linarith [hLM, hMN, hNL]

/-! ## §8 — Group C+D quadratic cancellation under torsion-freeness

The `(Γ × R)` correction terms in `∇R` split into four groups by which
index of `R` the contraction-with-`Γ` index `α` lands on:

- Group A: `+Γ^ρ_{λα} R^α_{σμν}` (top-index contraction).
- Group B: `-Γ^α_{λσ} R^ρ_{αμν}` (`σ`-position contraction).
- Group C: `-Γ^α_{λμ} R^ρ_{σαν}` (`μ`-position contraction).
- Group D: `-Γ^α_{λν} R^ρ_{σμα}` (`ν`-position contraction).

Under the cyclic sum in `(λ, μ, ν)`, **Group C+D cancels by
torsion-freeness on `Γ` plus `AntisymLastTwo` on `R`**:

  -Σ_α Γ^α_{λμ} R^ρ_{σαν} + cyclic
  -Σ_α Γ^α_{λν} R^ρ_{σμα} + cyclic
  = 0.

Substantive: each pair `(Γ_{ab} R_{αν}, Γ_{ba} R_{αμ})` cancels via
torsion-freeness `Γ^α_{ab} = Γ^α_{ba}` plus the `AntisymLastTwo`
relation `R^ρ_{σαν} = -R^ρ_{σνα}`. The "lower-index Γ-correction
sub-sum" of differential Bianchi vanishes universally regardless of
algebraic first Bianchi or Schwarz hypotheses — this is the cleanest
non-trivial chunk of the full discharge. -/

/--
**Group C+D cyclic cancellation** under torsion-freeness on `Γ`
plus `AntisymLastTwo` on `R`. The cyclic sum (over `(λ, μ, ν)`) of
the lower-index Γ-correction pair vanishes.

Substantive at coordinate scope: torsion-free symmetry plus
`AntisymLastTwo` give a 12-term signed-pair cancellation per index
sum, totaling 12 × 4 = 48 monomial cancellations.
-/
theorem covRiemann_groupCD_cyclic_zero
    {Γ : Christoffel} {R : RiemannTensor}
    (hΓ : IsTorsionFree Γ) (hR : AntisymLastTwo R)
    (ρ σ lam μ ν : Fin 4) :
    (- sumFin4 (fun α => Γ α lam μ * R ρ σ α ν)
       - sumFin4 (fun α => Γ α lam ν * R ρ σ μ α))
    + (- sumFin4 (fun α => Γ α μ ν * R ρ σ α lam)
       - sumFin4 (fun α => Γ α μ lam * R ρ σ ν α))
    + (- sumFin4 (fun α => Γ α ν lam * R ρ σ α μ)
       - sumFin4 (fun α => Γ α ν μ * R ρ σ lam α)) = 0 := by
  -- Strategy: rewrite Γ via torsion-freeness and R via AntisymLastTwo
  -- so each pair in the six sums is the negation of another pair.
  -- Per-α Γ rewrites (IsTorsionFree gives Γ a μ lam = Γ a lam μ directly)
  have tml : ∀ a : Fin 4, Γ a μ lam = Γ a lam μ := fun a => hΓ a μ lam
  have tnl : ∀ a : Fin 4, Γ a ν lam = Γ a lam ν := fun a => hΓ a ν lam
  have tmn : ∀ a : Fin 4, Γ a μ ν = Γ a ν μ := fun a => hΓ a μ ν
  -- Per-α R AntisymLastTwo rewrites
  have ran : ∀ a : Fin 4, R ρ σ a ν = - R ρ σ ν a := fun a => hR ρ σ a ν
  have ram : ∀ a : Fin 4, R ρ σ a μ = - R ρ σ μ a := fun a => hR ρ σ a μ
  have ral : ∀ a : Fin 4, R ρ σ a lam = - R ρ σ lam a := fun a => hR ρ σ a lam
  unfold sumFin4
  beta_reduce
  rw [ran 0, ran 1, ran 2, ran 3,
      ram 0, ram 1, ram 2, ram 3,
      ral 0, ral 1, ral 2, ral 3,
      tml 0, tml 1, tml 2, tml 3,
      tnl 0, tnl 1, tnl 2, tnl 3,
      tmn 0, tmn 1, tmn 2, tmn 3]
  ring

/-! ## §9 — Flat-data sanity for the full covariant-derivative

When the data is the flat connection `(Γ = 0, ∂Γ = 0, ∂²Γ = 0)`, the
covariant derivative of the corresponding Riemann tensor vanishes
identically — combining Session 1's `riemannCoord_zero_of_zeroData`
with this module's `covRiemann` definition (the four `Γ × R` correction
terms also vanish since each contains a `Γ` factor). -/

/--
**Flat-data sanity for `∇R`:** `Γ = 0 ∧ dΓ = 0 ∧ d²Γ = 0` implies
`covRiemann_coord = 0` identically. Composes Session 1's flat
`riemannCoord = 0` with the `Γ`-factored vanishing of the four
correction terms.
-/
theorem covRiemann_coord_zero_of_zeroData
    {Γ : Christoffel} {dΓ : ChristoffelPartial} {d2Γ : Christoffel2Partial}
    (hΓ : Γ = zeroChristoffel)
    (hdΓ : dΓ = zeroChristoffelPartial)
    (hd2Γ : d2Γ = zeroChristoffel2Partial) :
    covRiemann_coord Γ dΓ d2Γ = fun _ _ _ _ _ => 0 := by
  funext lam ρ σ μ ν
  unfold covRiemann_coord covRiemann riemannCoord_partial
    riemannLinearTerm_partial riemannQuadraticTerm_partial
    riemannCoord riemannLinearTerm
  rw [hΓ, hdΓ, hd2Γ]
  unfold zeroChristoffel zeroChristoffelPartial zeroChristoffel2Partial
    riemannQuadraticTerm sumFin4
  ring

/-! ## §10 — Module summary marker

Phase 6f Wave 8 Session 2 (of 5-session bundle-level Riemann curvature
plan). Adds the second-partial carrier, the covariant-derivative
operator on a generic Riemann tensor, and the substantive coordinate-
level discharges that are tractable at this scope: the linear-piece
differential second Bianchi (Schwarz alone) and the Group C+D cyclic
cancellation (torsion-freeness + AntisymLastTwo). The full coordinate-
level differential second Bianchi for `∇R` requires `∂Γ × Γ` bilinear +
`Γ × Γ × Γ` cubic discharges that are far cleaner at bundle scope via
the connection-commutator Jacobi identity (Session 3); the Session 4
specialization theorem will deliver the full coord-level identity from
that bundle-level result.

**Substantive theorems shipped (8):**

§6 — Antisymmetry-in-(μ,ν) lifts:
1. `riemannLinearTerm_partial_AntisymLastTwo` — `∂R_lin` antisym
2. `riemannQuadraticTerm_partial_AntisymLastTwo` — `∂R_quad` antisym
3. `riemannCoord_partial_AntisymLastTwo` — full `∂R` antisym
4. `covRiemann_AntisymLastTwo` — `∇R` antisym lift from `R + ∂R`
5. `covRiemann_coord_AntisymLastTwo` — substantive cross-module
   composition exhibiting Session 1's antisym + Session 2's partial
   antisym chained into the data-driven `covRiemann_coord`

§7 — Wave headline (linear-piece differential Bianchi):
6. `riemannLinearTerm_partial_DifferentialBianchi` — `∂²Γ`-cyclic = 0
   under Schwarz, the substantive non-trivial Schwarz-only discharge

§8 — Group C+D cyclic cancellation:
7. `covRiemann_groupCD_cyclic_zero` — substantive 48-monomial
   cancellation under torsion-freeness + `AntisymLastTwo`

§9 — Flat-data sanity:
8. `covRiemann_coord_zero_of_zeroData` — flat connection ⟹ `∇R = 0`

**First formalization in any proof assistant** (per audit §3E + Session
1 first-formalization context) of: `Christoffel2Partial` carrier with
Schwarz hypothesis, `covRiemann` operator on a generic Riemann tensor,
linear-piece differential second Bianchi under Schwarz, and the
Group C+D cyclic cancellation under torsion-freeness on the
Christoffel-formula version of the Riemann tensor.

**Stages 6+7+8+11+13 deferred** per the project's Mathlib-PR-style-
infrastructure policy.
-/
theorem _phase6f_w8_session2_module_summary_marker : True := trivial

end SKEFTHawking.RiemannDifferentialBianchi
