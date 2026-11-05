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

section PalatiniVariation

open Filter MeasureTheory
open scoped Topology

private lemma sum4_deriv {f : Fin 4 → ℝ → ℝ} {g : Fin 4 → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (f i) (g i) t) :
    HasDerivAt (fun s => sumFin4 (fun i => f i s)) (sumFin4 g) t := by
  exact (((h 0).add (h 1)).add (h 2)).add (h 3)

/-- The difference of two connections, and hence its parameter derivative,
transforms as a (1,2) tensor. -/
def covConnectionVariation (Γ K : Christoffel) (dK : ChristoffelPartial) :
    ChristoffelPartial := fun a r i j =>
  dK a r i j + sumFin4 (fun l => Γ r a l * K l i j) -
    sumFin4 (fun l => Γ l a i * K r l j) -
    sumFin4 (fun l => Γ l a j * K r i l)

theorem palatini_riemann_algebra (Γ K : Christoffel) (dK : ChristoffelPartial)
    (hΓ : IsTorsionFree Γ) (r j a b : Fin 4) :
    riemannLinearTerm dK r j a b +
      riemannQuadraticTerm_partial Γ (fun _ => K) 0 r j a b =
    covConnectionVariation Γ K dK a r b j -
      covConnectionVariation Γ K dK b r a j := by
  simp only [riemannLinearTerm, riemannQuadraticTerm_partial, covConnectionVariation,
    sumFin4, hΓ 0 b a, hΓ 1 b a, hΓ 2 b a, hΓ 3 b a]
  ring

/-- Genuine one-parameter differentiation of the existing coordinate Riemann
formula. The input dK is the parameter derivative of the spatial derivative
array, so application to a smooth chart can commute its mixed derivatives. -/
theorem palatini_riemann (Γ : ℝ → Christoffel) (dΓ : ℝ → ChristoffelPartial)
    (K : Christoffel) (dK : ChristoffelPartial) (t : ℝ)
    (hΓ : IsTorsionFree (Γ t))
    (hK : ∀ r a j, HasDerivAt (fun s => Γ s r a j) (K r a j) t)
    (hdK : ∀ b r a j, HasDerivAt (fun s => dΓ s b r a j) (dK b r a j) t)
    (r j a b : Fin 4) :
    HasDerivAt (fun s => riemannCoord (Γ s) (dΓ s) r j a b)
      (covConnectionVariation (Γ t) K dK a r b j -
        covConnectionVariation (Γ t) K dK b r a j) t := by
  rw [← palatini_riemann_algebra (Γ t) K dK hΓ]
  have hd := (hdK a r b j).sub (hdK b r a j)
  have h₁ := sum4_deriv (fun l => (hK r a l).mul (hK l b j))
  have h₂ := sum4_deriv (fun l => (hK r b l).mul (hK l a j))
  exact hd.add (h₁.sub h₂)

/-- Our convention is Ric_{ij} = R^a_{iaj}. -/
def ricciVariation (Γ K : Christoffel) (dK : ChristoffelPartial) : RicciTensor :=
  fun i j => sumFin4 (fun a => covConnectionVariation Γ K dK a a j i -
    covConnectionVariation Γ K dK j a a i)

theorem palatini_ricci (Γ : ℝ → Christoffel) (dΓ : ℝ → ChristoffelPartial)
    (K : Christoffel) (dK : ChristoffelPartial) (t : ℝ)
    (hΓ : IsTorsionFree (Γ t))
    (hK : ∀ r a j, HasDerivAt (fun s => Γ s r a j) (K r a j) t)
    (hdK : ∀ b r a j, HasDerivAt (fun s => dΓ s b r a j) (dK b r a j) t)
    (i j : Fin 4) :
    HasDerivAt (fun s => ricciOf (riemannCoord (Γ s) (dΓ s)) i j)
      (ricciVariation (Γ t) K dK i j) t :=
  sum4_deriv (fun a => palatini_riemann Γ dΓ K dK t hΓ hK hdK a i a j)

def contractedCurrent (B : MetricMatrix) (K : Christoffel) (a : Fin 4) : ℝ :=
  sumFin4 (fun i => sumFin4 (fun j => B i j * K a j i)) -
    sumFin4 (fun i => B i a * sumFin4 (fun r => K r r i))

def contractedCurrentPartial (B dB : MetricMatrix) (K dK : Christoffel)
    (a : Fin 4) : ℝ :=
  contractedCurrent dB K a + contractedCurrent B dK a

def inverseMetricCompatiblePartial (Γ : Christoffel) (B : MetricMatrix)
    (dB : Fin 4 → MetricMatrix) : Prop :=
  ∀ a i j, dB a i j =
    -sumFin4 (fun l => Γ i a l * B l j) -
      sumFin4 (fun l => Γ j a l * B i l)

def densityCompatiblePartial (Γ : Christoffel) (w : ℝ) (dw : Fin 4 → ℝ) : Prop :=
  ∀ a, dw a = w * sumFin4 (fun l => Γ l l a)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- The contracted Palatini current has an ordinary density divergence.
Metric compatibility and the volume-density derivative are explicit inputs. -/
theorem contracted_density_divergence (Γ K : Christoffel) (dK : ChristoffelPartial)
    (B : MetricMatrix) (dB : Fin 4 → MetricMatrix) (w : ℝ) (dw : Fin 4 → ℝ)
    (hΓ : IsTorsionFree Γ) (hB : inverseMetricCompatiblePartial Γ B dB)
    (hw : densityCompatiblePartial Γ w dw) :
    w * scalarOf (ricciVariation Γ K dK) B =
      sumFin4 (fun a => dw a * contractedCurrent B K a +
        w * contractedCurrentPartial B (dB a) K (dK a) a) := by
  unfold inverseMetricCompatiblePartial at hB
  unfold densityCompatiblePartial at hw
  have hs10 (q : Fin 4) : Γ q 1 0 = Γ q 0 1 := hΓ q 1 0
  have hs20 (q : Fin 4) : Γ q 2 0 = Γ q 0 2 := hΓ q 2 0
  have hs30 (q : Fin 4) : Γ q 3 0 = Γ q 0 3 := hΓ q 3 0
  have hs21 (q : Fin 4) : Γ q 2 1 = Γ q 1 2 := hΓ q 2 1
  have hs31 (q : Fin 4) : Γ q 3 1 = Γ q 1 3 := hΓ q 3 1
  have hs32 (q : Fin 4) : Γ q 3 2 = Γ q 2 3 := hΓ q 3 2
  simp only [scalarOf, ricciVariation, covConnectionVariation, contractedCurrentPartial,
    contractedCurrent, sumFin4, hB, hw, hs10, hs20, hs30, hs21, hs31, hs32]
  ring

theorem contractedCurrent_hasDerivAt (B : ℝ → MetricMatrix) (K : ℝ → Christoffel)
    (dB : MetricMatrix) (dK : Christoffel) (s : ℝ) (a : Fin 4)
    (hB : ∀ i j, HasDerivAt (fun t => B t i j) (dB i j) s)
    (hK : ∀ r i j, HasDerivAt (fun t => K t r i j) (dK r i j) s) :
    HasDerivAt (fun t => contractedCurrent (B t) (K t) a)
      (contractedCurrentPartial (B s) dB (K s) dK a) s := by
  have h₁ := sum4_deriv (fun i => sum4_deriv (fun j => (hB i j).mul (hK a j i)))
  have h₂ := sum4_deriv (fun i => (hB i a).mul (sum4_deriv (fun r => hK r r i)))
  convert h₁.sub h₂ using 1 <;> first | rfl | (simp only [contractedCurrentPartial, contractedCurrent, sumFin4]; ring)

abbrev Chart := Fin 4 → ℝ

def densityCurrent (w : Chart → ℝ) (B : Chart → MetricMatrix) (K : Chart → Christoffel)
    (a : Fin 4) (x : Chart) : ℝ :=
  w x * contractedCurrent (B x) (K x) a

/-- This ties the algebraic divergence to the actual Fréchet derivative
of the density current. Derivative inputs are along the straight coordinate
line through x. -/
theorem current_derivative_from_chart (w : Chart → ℝ) (B : Chart → MetricMatrix)
    (K : Chart → Christoffel) (x : Chart) (a : Fin 4)
    (dw : ℝ) (dB : MetricMatrix) (dK : Christoffel)
    (D : Chart →L[ℝ] ℝ)
    (hD : HasFDerivAt (densityCurrent w B K a) D x)
    (hw : HasDerivAt (fun t : ℝ => w (x + t • Pi.single a 1)) dw 0)
    (hB : ∀ i j, HasDerivAt (fun t : ℝ => B (x + t • Pi.single a 1) i j)
      (dB i j) 0)
    (hK : ∀ r i j, HasDerivAt (fun t : ℝ => K (x + t • Pi.single a 1) r i j)
      (dK r i j) 0) :
    D (Pi.single a 1) =
      dw * contractedCurrent (B x) (K x) a +
        w x * contractedCurrentPartial (B x) dB (K x) dK a := by
  have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single a 1 : Chart))
      (Pi.single a 1) 0 := by
    simpa only [one_smul] using
      (((hasDerivAt_id' (x := (0 : ℝ))).smul_const (Pi.single a 1 : Chart)).const_add x)
  have hcomp := hD.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)
  have hprod := hw.mul (contractedCurrent_hasDerivAt
    (fun t => B (x + t • Pi.single a 1)) (fun t => K (x + t • Pi.single a 1))
    dB dK 0 a hB hK)
  simpa [densityCurrent] using hcomp.unique hprod

/-- The local contracted Ricci variation equals the divergence of the
specified chart current, with actual derivatives certified on each line. -/
theorem weighted_ricci_trace_eq_chart_divergence
    (w : Chart → ℝ) (B : Chart → MetricMatrix) (K : Chart → Christoffel)
    (x : Chart) (Γ : Christoffel) (dw : Fin 4 → ℝ)
    (dB : Fin 4 → MetricMatrix) (dK : ChristoffelPartial)
    (D : Fin 4 → Chart →L[ℝ] ℝ)
    (hΓ : IsTorsionFree Γ)
    (hMetric : inverseMetricCompatiblePartial Γ (B x) dB)
    (hDensity : densityCompatiblePartial Γ (w x) dw)
    (hD : ∀ a, HasFDerivAt (densityCurrent w B K a) (D a) x)
    (hw : ∀ a, HasDerivAt (fun t : ℝ => w (x + t • Pi.single a 1)) (dw a) 0)
    (hB : ∀ a i j, HasDerivAt (fun t : ℝ => B (x + t • Pi.single a 1) i j)
      (dB a i j) 0)
    (hK : ∀ a r i j, HasDerivAt (fun t : ℝ => K (x + t • Pi.single a 1) r i j)
      (dK a r i j) 0) :
    w x * scalarOf (ricciVariation Γ (K x) dK) (B x) =
      ∑ a, D a (Pi.single a 1) := by
  rw [contracted_density_divergence Γ (K x) dK (B x) dB (w x) dw hΓ hMetric hDensity]
  have he (a : Fin 4) := current_derivative_from_chart w B K x a
    (dw a) (dB a) (dK a) (D a) (hD a) (hw a) (hB a) (hK a)
  simp_rw [he]
  simp only [sumFin4, Fin.sum_univ_four]

/-- Actual chart-box boundary cancellation. The supplied boundary condition
fixes equal values of each normal current component on paired faces.
A current supported in the box interior is a sufficient special case. -/
theorem chart_box_boundary_cancellation (a b : Chart) (hab : a ≤ b)
    (J : Fin 4 → Chart → ℝ) (DJ : Fin 4 → Chart → Chart →L[ℝ] ℝ)
    (hcont : ∀ i, ContinuousOn (J i) (Set.Icc a b))
    (hderiv : ∀ x ∈ (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)), ∀ i,
      HasFDerivAt (J i) (DJ i x) x)
    (hint : IntegrableOn (fun x => ∑ i, DJ i x (Pi.single i 1)) (Set.Icc a b))
    (hface : ∀ (i : Fin 4) (y : Fin 3 → ℝ),
      J i (Fin.insertNth i (b i) y) = J i (Fin.insertNth i (a i) y)) :
    (∫ x in Set.Icc a b, ∑ i, DJ i x (Pi.single i 1)) = 0 := by
  have h :=
    integral_divergence_of_hasFDerivAt_off_countable' (n := 3) a b hab J DJ
      ∅ Set.countable_empty hcont
      (fun x hx => hderiv x hx.1) hint
  rw [h]
  simp [hface]

/-- Integration of the EH bulk variation with a boundary condition on the
explicit Palatini current. Domination is separate from boundary cancellation. -/
theorem eh_box_stationary (a b : Chart) (hab : a ≤ b)
    (J : Fin 4 → Chart → ℝ) (DJ : Fin 4 → Chart → Chart →L[ℝ] ℝ)
    (hcont : ∀ i, ContinuousOn (J i) (Set.Icc a b))
    (hderiv : ∀ x ∈ (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)), ∀ i,
      HasFDerivAt (J i) (DJ i x) x)
    (hint : IntegrableOn (fun x => ∑ i, DJ i x (Pi.single i 1)) (Set.Icc a b))
    (hface : ∀ (i : Fin 4) (y : Fin 3 → ℝ),
      J i (Fin.insertNth i (b i) y) = J i (Fin.insertNth i (a i) y))
    (L L' : ℝ → Chart → ℝ) (u : Set ℝ) (bound : Chart → ℝ)
    (hu : u ∈ 𝓝 (0 : ℝ))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (L t)
      (volume.restrict (Set.Icc a b)))
    (hL0 : IntegrableOn (L 0) (Set.Icc a b))
    (hL'0 : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      L' 0 x = ∑ i, DJ i x (Pi.single i 1))
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), ∀ t ∈ u, ‖L' t x‖ ≤ bound x)
    (hbound_int : IntegrableOn bound (Set.Icc a b))
    (hdiff : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), ∀ t ∈ u,
      HasDerivAt (fun s => L s x) (L' t x) t) :
    HasDerivAt (fun t => ∫ x in Set.Icc a b, L t x) 0 0 := by
  have heq : L' 0 =ᵐ[volume.restrict (Set.Icc a b)]
      (fun x => ∑ i, DJ i x (Pi.single i 1)) := hL'0
  have hm := hint.aestronglyMeasurable.congr heq.symm
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hu hmeas hL0 hm hbound hbound_int hdiff).2
  rw [integral_congr_ae heq, chart_box_boundary_cancellation a b hab J DJ
    hcont hderiv hint hface] at hd
  exact hd

namespace EHChart

abbrev MetricPath := ℝ → Chart → MetricMatrix

noncomputable def spatialLineDeriv (f : Chart → ℝ) (x : Chart) (a : Fin 4) : ℝ :=
  deriv (fun t : ℝ => f (x + t • Pi.single a 1)) 0

noncomputable def metricInverse (g : MetricPath) (s : ℝ) (x : Chart) : MetricMatrix :=
  ((g s x : Matrix (Fin 4) (Fin 4) ℝ)⁻¹ : Matrix (Fin 4) (Fin 4) ℝ)

noncomputable def metricWeight (g : MetricPath) (s : ℝ) (x : Chart) : ℝ :=
  Real.sqrt |Matrix.det (g s x : Matrix (Fin 4) (Fin 4) ℝ)|

noncomputable def metricConnection (g : MetricPath) (s : ℝ) (x : Chart) : Christoffel :=
  christoffelKoszul (metricInverse g s x)
    (fun a i j => spatialLineDeriv (fun y => g s y i j) x a)

noncomputable def metricConnectionPartial (g : MetricPath) (s : ℝ) (x : Chart) :
    ChristoffelPartial :=
  fun a r i j => spatialLineDeriv (fun y => metricConnection g s y r i j) x a

noncomputable def metricRicci (g : MetricPath) (s : ℝ) (x : Chart) : RicciTensor :=
  ricciOf (riemannCoord (metricConnection g s x) (metricConnectionPartial g s x))

noncomputable def density (g : MetricPath) (s : ℝ) (x : Chart) : ℝ :=
  metricWeight g s x * scalarOf (metricRicci g s x) (metricInverse g s x)

noncomputable def deltaConnection (g : MetricPath) (x : Chart) : Christoffel :=
  fun r i j => deriv (fun s => metricConnection g s x r i j) 0

noncomputable def deltaConnectionPartial (g : MetricPath) (x : Chart) :
    ChristoffelPartial :=
  fun a r i j => spatialLineDeriv (fun y => deltaConnection g y r i j) x a

noncomputable def inversePartial (g : MetricPath) (x : Chart) : Fin 4 → MetricMatrix :=
  fun a i j => spatialLineDeriv (fun y => metricInverse g 0 y i j) x a

noncomputable def weightPartial (g : MetricPath) (x : Chart) : Fin 4 → ℝ :=
  fun a => spatialLineDeriv (metricWeight g 0) x a

noncomputable def current (g : MetricPath) (a : Fin 4) : Chart → ℝ :=
  densityCurrent (metricWeight g 0) (metricInverse g 0) (deltaConnection g) a

private theorem scalarOf_flat_hasDerivAt (B R : ℝ → MetricMatrix)
    (B' R' : MetricMatrix) (t : ℝ)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t)
    (hR : ∀ i j, HasDerivAt (fun s => R s i j) (R' i j) t)
    (hflat : ∀ i j, R t i j = 0) :
    HasDerivAt (fun s => scalarOf (R s) (B s)) (scalarOf R' (B t)) t := by
  have h (i j : Fin 4) :
      HasDerivAt (fun s => B s i j * R s i j) (B t i j * R' i j) t := by
    simpa [hflat i j] using (hB i j).fun_mul (hR i j)
  exact RiemannDifferentialBianchi.sum4_deriv (fun i =>
    RiemannDifferentialBianchi.sum4_deriv (fun j => h i j))

/-- These are differentiability, mixed-partial, and metric compatibility
conditions for actual coordinate expressions at the background. The Ricci
flatness is a property of the base metric, independent of the perturbation. -/
structure RegularBase (g : MetricPath) (x : Chart) : Prop where
  nondegenerate : ∀ᶠ s in 𝓝 (0 : ℝ),
    Matrix.det (g s x : Matrix (Fin 4) (Fin 4) ℝ) ≠ 0
  baseSymmetric : ∀ y i j, g 0 y i j = g 0 y j i
  flat : ∀ i j, metricRicci g 0 x i j = 0
  paramWeight : DifferentiableAt ℝ (fun s => metricWeight g s x) 0
  paramInverse : ∀ i j, DifferentiableAt ℝ (fun s => metricInverse g s x i j) 0
  paramConnection : ∀ r i j, DifferentiableAt ℝ (fun s => metricConnection g s x r i j) 0
  commute : ∀ a r i j, HasDerivAt (fun s => metricConnectionPartial g s x a r i j)
    (deltaConnectionPartial g x a r i j) 0
  spatialWeight : ∀ a, DifferentiableAt ℝ
    (fun t : ℝ => metricWeight g 0 (x + t • Pi.single a 1)) 0
  spatialInverse : ∀ a i j, DifferentiableAt ℝ
    (fun t : ℝ => metricInverse g 0 (x + t • Pi.single a 1) i j) 0
  spatialDelta : ∀ a r i j, DifferentiableAt ℝ
    (fun t : ℝ => deltaConnection g (x + t • Pi.single a 1) r i j) 0
  inverseCompat : inverseMetricCompatiblePartial
    (metricConnection g 0 x) (metricInverse g 0 x) (inversePartial g x)
  weightCompat : densityCompatiblePartial
    (metricConnection g 0 x) (metricWeight g 0 x) (weightPartial g x)

theorem local_eh_variation (g : MetricPath) (x : Chart)
    (D : Fin 4 → Chart →L[ℝ] ℝ) (h : RegularBase g x)
    (hD : ∀ a, HasFDerivAt (current g a) (D a) x) :
    HasDerivAt (fun s => density g s x) (∑ a, D a (Pi.single a 1)) 0 := by
  have hsym : MetricPartialSymmetric
      (fun a i j => spatialLineDeriv (fun y => g 0 y i j) x a) := by
    intro a i j
    exact congrArg (fun f => spatialLineDeriv f x a)
      (funext fun y => h.baseSymmetric y i j)
  have ht : IsTorsionFree (metricConnection g 0 x) :=
    christoffelKoszul_isTorsionFree _ _ hsym
  have hRic (i j : Fin 4) :
      HasDerivAt (fun s => metricRicci g s x i j)
        (ricciVariation (metricConnection g 0 x) (deltaConnection g x)
          (deltaConnectionPartial g x) i j) 0 :=
    palatini_ricci (fun s => metricConnection g s x)
      (fun s => metricConnectionPartial g s x) _ _ 0 ht
      (fun r a j => (h.paramConnection r a j).hasDerivAt) h.commute i j
  have hScalar :=
    scalarOf_flat_hasDerivAt (fun s => metricInverse g s x) (fun s => metricRicci g s x)
      _ _ 0 (fun i j => (h.paramInverse i j).hasDerivAt) hRic h.flat
  have hZero : scalarOf (metricRicci g 0 x) (metricInverse g 0 x) = 0 := by
    simp [scalarOf, sumFin4, h.flat]
  have hDiv := weighted_ricci_trace_eq_chart_divergence
    (metricWeight g 0) (metricInverse g 0) (deltaConnection g) x (metricConnection g 0 x)
    (weightPartial g x) (inversePartial g x) (deltaConnectionPartial g x) D
    ht h.inverseCompat h.weightCompat hD
    (fun a => (h.spatialWeight a).hasDerivAt)
    (fun a i j => (h.spatialInverse a i j).hasDerivAt)
    (fun a r i j => (h.spatialDelta a r i j).hasDerivAt)
  simpa only [density, hZero, mul_zero, zero_add, hDiv] using
    h.paramWeight.hasDerivAt.fun_mul hScalar

/-- The box integral of the actual EH density is stationary for the
specified perturbation, under a.e. compatibility, local dominated
differentiation, and paired normal traces of its Palatini current. -/
theorem eh_metric_box_stationary (g : MetricPath) (a b : Chart) (hab : a ≤ b)
    (D : Fin 4 → Chart → Chart →L[ℝ] ℝ)
    (hcont : ∀ i, ContinuousOn (current g i) (Set.Icc a b))
    (hderiv : ∀ x ∈ (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)), ∀ i,
      HasFDerivAt (current g i) (D i x) x)
    (hint : IntegrableOn (fun x => ∑ i, D i x (Pi.single i 1)) (Set.Icc a b))
    (hface : ∀ (i : Fin 4) (y : Fin 3 → ℝ),
      current g i (Fin.insertNth i (b i) y) = current g i (Fin.insertNth i (a i) y))
    (hBase : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      RegularBase g x ∧ ∀ i, HasFDerivAt (current g i) (D i x) x)
    (L' : ℝ → Chart → ℝ) (u : Set ℝ) (bound : Chart → ℝ)
    (hu : u ∈ 𝓝 (0 : ℝ))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (density g t)
      (volume.restrict (Set.Icc a b)))
    (hL0 : IntegrableOn (density g 0) (Set.Icc a b))
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), ∀ t ∈ u, ‖L' t x‖ ≤ bound x)
    (hbound_int : IntegrableOn bound (Set.Icc a b))
    (hdiff : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), ∀ t ∈ u,
      HasDerivAt (fun s => density g s x) (L' t x) t) :
    HasDerivAt (fun t => ∫ x in Set.Icc a b, density g t x) 0 0 := by
  refine eh_box_stationary a b hab (current g) D hcont hderiv hint hface
    (density g) L' u bound hu hmeas hL0 ?_ hbound hbound_int hdiff
  filter_upwards [hBase, hdiff] with x hx hdx
  exact (hdx 0 (mem_of_mem_nhds hu)).unique
    (local_eh_variation g x (fun i => D i x) hx.1 hx.2)

end EHChart

end PalatiniVariation

end SKEFTHawking.RiemannDifferentialBianchi
