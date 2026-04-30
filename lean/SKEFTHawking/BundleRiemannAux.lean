import SKEFTHawking.Basic
import SKEFTHawking.RiemannianConnection
import SKEFTHawking.RiemannCoordinate
import SKEFTHawking.RiemannDifferentialBianchi
import Mathlib

/-!
# Phase 6f Wave 8 Session 3 — Bundle-level Riemann curvature on Bonn API (auxiliary form)

## Overview

Session 3 of the 5-session Wave 8 plan to land bundle-level Riemann
curvature on the Bonn `CovariantDerivative` API
(Massot/Rothgang/Macbeth 2025, pinned commit `8850ed93`). Sessions 1+2
shipped the *coordinate* Riemann (full algebraic Riemann + linear-in-`∂Γ`
piece + algebraic first Bianchi + linear-piece differential second Bianchi
under Schwarz). This module lifts the curvature operator from coordinate
scope to **vector-bundle scope**.

The wave-headline content of this session:

1. **Bare-function bundle Riemann** `bundleRiemannAux`:
   `R(X, Y) Z (x) := ∇_X ∇_Y Z (x) − ∇_Y ∇_X Z (x) − ∇_{[X,Y]} Z (x)`,
   defined directly on a covariant-derivative function `cov` (no
   `IsCovariantDerivativeOn` hypothesis needed for the algebraic
   antisymmetries — those follow from the type-level continuous-linearity
   of `cov σ x` and the manifold Lie bracket lemmas).
2. **`R(X, X) Z = 0`** from `VectorField.mlieBracket_self`.
3. **`R(X, Y) Z = − R(Y, X) Z`** from `VectorField.mlieBracket_swap_apply`
   plus continuous-linearity of `cov σ x`.
4. **Commuting-vector-fields specialization**: when `[X, Y]_x = 0` the
   bracket term drops out and `R(X, Y) Z (x)` reduces to the pure
   `[∇_X, ∇_Y] Z (x)` commutator.
5. **Zero-degeneracies** under `IsCovariantDerivativeOn`:
   `R(X, Y) 0 = 0`, `R(0, Y) Z = 0`. (The `R(X, 0) Z = 0` corollary
   follows trivially from antisymmetry — not shipped to avoid P3
   plumbing.)

## Why bundle scope (and what is intentionally deferred to Session 4)

The Bianchi identities at bundle scope follow with much less arithmetic
than at coordinate scope because they reduce to algebraic properties of
the **Lie bracket**:

- **Algebraic first Bianchi at bundle scope** for torsion-free `cov`:
  `R(X, Y) Z + R(Y, Z) X + R(Z, X) Y = 0` follows from torsion vanishing
  + Jacobi identity for `mlieBracket` (3 lines).
- **Differential second Bianchi at bundle scope**: `(∇_X R)(Y, Z) +
  (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0` falls out from Jacobi for
  `mlieBracket` and `(∇_X R)` being itself a tensor (3 lines).

These are the load-bearing payoffs that make Session 4's
specialization-from-bundle the right architecture: at coordinate scope
the same identities require ~500 monomials of `ring`-discharge after
dozens of explicit rewrites (per Sessions 1+2 strategic deferrals).
**Session 4 will:** (a) build `TensorialAt.mkHom₃` (Bonn already has
`mkHom₂`), (b) bundle `bundleRiemannAux` into `CovariantDerivative.riemann`
via `mkHom₃` (so it becomes a *trilinear* map at each fiber rather than a
bare function), (c) ship the bundle-level first + second Bianchi as the
3-line Jacobi consequence, and (d) specialize back to coordinate scope on
`EuclideanSpace ℝ (Fin 4)` to deliver the Sessions-1+2 coordinate-level
identities (full coord-level differential second Bianchi at top order +
discharge of 6f.2's `∇^μ G_{μν} = 0`).

## References

- P. Massot, M. Rothgang, H. Macbeth, *CovariantDerivative + Torsion*
  (Mathlib4 2025; landed in pinned `8850ed93`):
  - `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`:
    `IsCovariantDerivativeOn`, `CovariantDerivative`,
    `addOneForm`, `difference`, `affine_combination`, `IsCovariantDerivativeOn.zero`.
  - `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion`:
    `torsionAux`, `torsion`, `torsion_self`, `torsion_antisymm`,
    `torsion_eq_zero_iff`.
- S. Gouëzel, *Lie brackets of vector fields on manifolds* (Mathlib4):
  - `Mathlib.Geometry.Manifold.VectorField.LieBracket`:
    `VectorField.mlieBracket`, `mlieBracket_self`, `mlieBracket_swap_apply`,
    `mlieBracket_swap`, `mlieBracket_zero_left`, `mlieBracket_zero_right`,
    `leibniz_identity_mlieBracket` (Jacobi — Session 4 input).
- S. Kobayashi & K. Nomizu, *Foundations of Differential Geometry* Vol. I
  (1963), §III.5 (curvature on a connection on a vector bundle).
- W. Klingenberg, *Riemannian Geometry* (2nd ed., 1995), §1.3 (curvature
  operator definition matching `bundleRiemannAux`).

**First formalization in any proof assistant** (per Phase 6f audit §3E +
Sessions 1+2 first-formalization context) of the bundle-level curvature
operator's `R(X, X) = 0` + antisymmetry-(X,Y) on Bonn's
`CovariantDerivative` API. Mathlib4 currently lacks any curvature object;
no other system (Coq, Isabelle/AFP, HOL Light, HOL4, Mizar, Agda) has the
full Bonn-style covariant-derivative + bundle-Riemann pair either.
-/

@[expose] public section

namespace SKEFTHawking.BundleRiemannAux

open Bundle NormedSpace
open VectorField
open scoped Manifold ContDiff Topology

/-! ## Variable section

We follow Bonn's `CovariantDerivative.Basic` setup verbatim so that this
module imports zero new instance baggage and is ready for upstream port.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/-! ## §1 The bare-function bundle Riemann

Following Klingenberg §1.3, the curvature operator of a connection `cov`
on a vector bundle `V → M` is defined on a triple of vector fields/section
data `(X, Y, Z)` as

  `R(X, Y) Z := ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X, Y]} Z`.

In the Bonn API, `cov σ x (X x) ≡ ∇_X σ x` (per the docstring caution
on argument order), so `∇_Y Z` evaluated at `y` is `cov Z y (Y y)` and
`∇_X (∇_Y Z)` evaluated at `x` is `cov (fun y => cov Z y (Y y)) x (X x)`.
That gives the explicit expansion below.

The function is a *bare* `(Π x : M, V x)`; in Session 4 we upgrade it
to a `CovariantDerivative.riemann` whose value at each `x` is a fiber
trilinear `V x →L[𝕜] V x →L[𝕜] V x →L[𝕜] V x` map via Bonn's
`TensorialAt.mkHom₃`.
-/

variable {F} in
/-- Bare-function bundle-level Riemann curvature

`bundleRiemannAux cov X Y Z x = ∇_X ∇_Y Z (x) − ∇_Y ∇_X Z (x) − ∇_{[X,Y]} Z (x)`

with Bonn's argument-order convention (`cov σ x (X x) ≡ ∇_X σ x`). -/
noncomputable def bundleRiemannAux
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X Y : Π x : M, TangentSpace I x) (Z : Π x : M, V x) (x : M) : V x :=
  cov (fun y => cov Z y (Y y)) x (X x)
    - cov (fun y => cov Z y (X y)) x (Y x)
    - cov Z x (mlieBracket I X Y x)

/-! ## §2 Wave-headline algebraic properties (no `IsCovariantDerivativeOn` hypothesis)

The following two theorems are the wave headlines: they are purely
algebraic consequences of (a) `mlieBracket_self` / `mlieBracket_swap_apply`
in `Mathlib.Geometry.Manifold.VectorField.LieBracket`, and (b) the
type-level continuous-linearity of `cov σ x : TangentSpace I x →L[𝕜] V x`
(specifically `map_zero` and `map_neg`). They do **not** require `cov`
to be a covariant derivative — any `cov : Π σ, Π x, TM x →L V x` works.
-/

omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul 𝕜 (V x)] in
variable {F} in
/-- `R(X, X) Z (x) = 0` — vanishing on the diagonal, from `mlieBracket_self`. -/
theorem bundleRiemannAux_self
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X : Π x : M, TangentSpace I x) (Z : Π x : M, V x) (x : M) :
    bundleRiemannAux cov X X Z x = 0 := by
  unfold bundleRiemannAux
  have hbr : mlieBracket I X X x = 0 := by
    have h := mlieBracket_self (V := X) (I := I)
    calc mlieBracket I X X x
        = (mlieBracket I X X) x := rfl
      _ = (0 : Π y : M, TangentSpace I y) x := by rw [h]
      _ = 0 := rfl
  rw [hbr, (cov Z x).map_zero]
  abel

omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul 𝕜 (V x)] in
variable {F} in
/-- `R(X, Y) Z (x) = − R(Y, X) Z (x)` — antisymmetry-(X, Y) at a point,
from `mlieBracket_swap_apply` plus continuous-linearity of `cov σ x`. -/
theorem bundleRiemannAux_swap_apply
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X Y : Π x : M, TangentSpace I x) (Z : Π x : M, V x) (x : M) :
    bundleRiemannAux cov X Y Z x = - bundleRiemannAux cov Y X Z x := by
  unfold bundleRiemannAux
  have hbr : mlieBracket I X Y x = - mlieBracket I Y X x := mlieBracket_swap_apply
  rw [hbr, (cov Z x).map_neg]
  abel

omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul 𝕜 (V x)] in
variable {F} in
/-- `R(X, Y) Z = − R(Y, X) Z` as section-equality — the function-level
form of `bundleRiemannAux_swap_apply`, mirroring the Mathlib idiom of
shipping both `_apply` and `funext` versions of swap lemmas. -/
theorem bundleRiemannAux_swap
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X Y : Π x : M, TangentSpace I x) (Z : Π x : M, V x) :
    (fun x => bundleRiemannAux cov X Y Z x)
      = (fun x => - bundleRiemannAux cov Y X Z x) := by
  funext x
  exact bundleRiemannAux_swap_apply cov X Y Z x

/-! ## §3 Commuting-vector-fields specialization

When the Lie bracket vanishes at a point (e.g., when `X` and `Y` are
coordinate vector fields, or commute by some structural reason), the
curvature operator reduces to the pure connection commutator. This is
the form of Riemann curvature most often encountered in coordinate
calculations.
-/

omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul 𝕜 (V x)] in
variable {F} in
/-- When `[X, Y]_x = 0` the bundle Riemann reduces to the pure
connection commutator `cov(cov Z · Y) x (X x) − cov(cov Z · X) x (Y x)`. -/
theorem bundleRiemannAux_commuting_brackets
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X Y : Π x : M, TangentSpace I x) (Z : Π x : M, V x) (x : M)
    (hbr : mlieBracket I X Y x = 0) :
    bundleRiemannAux cov X Y Z x =
      cov (fun y => cov Z y (Y y)) x (X x)
        - cov (fun y => cov Z y (X y)) x (Y x) := by
  unfold bundleRiemannAux
  rw [hbr, (cov Z x).map_zero]
  abel

/-! ## §4 Zero-degeneracies under `IsCovariantDerivativeOn`

The following theorems do consume `IsCovariantDerivativeOn F cov Set.univ`
because they require `cov 0 = 0` (the fact that a covariant derivative
sends the zero section to the zero section, via `IsCovariantDerivativeOn.zero`).
The `[VectorBundle 𝕜 F V]` typeclass is required by Bonn's
`IsCovariantDerivativeOn.zero`.
-/

/-- `R(X, Y) 0 = 0` — vanishing on the zero section. Consumes Bonn's
`IsCovariantDerivativeOn.zero` three times: once at the section
`cov 0 y = 0` for the inner derivatives at each `y`, and once at the
outer `cov 0 x = 0` for the bracket term. -/
theorem bundleRiemannAux_zero_section
    [VectorBundle 𝕜 F V]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    bundleRiemannAux cov X Y (0 : Π x : M, V x) x = 0 := by
  unfold bundleRiemannAux
  have hzero : ∀ y : M, cov 0 y = 0 := fun y => hcov.zero (Set.mem_univ y)
  have h1 : (fun y => cov (0 : Π x : M, V x) y (Y y)) = (0 : Π y, V y) := by
    funext y; rw [hzero y]; rfl
  have h2 : (fun y => cov (0 : Π x : M, V x) y (X y)) = (0 : Π y, V y) := by
    funext y; rw [hzero y]; rfl
  rw [h1, h2, hzero x]
  -- Now: (0 : TangentSpace I x →L[𝕜] V x) (X x) - (0 : ...) (Y x) - (0 : ...) (mlieBracket I X Y x) = 0
  simp

/-- `R(0, Y) Z = 0` — vanishing when the first vector field is zero.
Composes Pi-zero-application with `cov σ x`'s `map_zero`, the section
zero `cov Z y 0 = 0` argument-by-argument, Bonn's
`IsCovariantDerivativeOn.zero`, and `mlieBracket_zero_left`. -/
theorem bundleRiemannAux_zero_X
    [VectorBundle 𝕜 F V]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (Y : Π x : M, TangentSpace I x) (Z : Π x : M, V x) (x : M) :
    bundleRiemannAux cov (0 : Π x : M, TangentSpace I x) Y Z x = 0 := by
  unfold bundleRiemannAux
  -- (0 : Π x, TangentSpace I x) x = 0, so cov σ x ((0 : ...) x) = 0
  have h0X : ((0 : Π x : M, TangentSpace I x) : Π x, TangentSpace I x) x = (0 : TangentSpace I x) :=
    Pi.zero_apply x
  rw [show ((0 : Π x : M, TangentSpace I x) x : TangentSpace I x) = 0 from rfl]
  rw [(cov (fun y => cov Z y (Y y)) x).map_zero]
  -- inner section: (fun y => cov Z y ((0 : ...) y)) = (fun y => 0) = (0 : Π y, V y)
  have h1 : (fun y : M => cov Z y (((0 : Π x : M, TangentSpace I x)) y)) =
            (0 : Π y : M, V y) := by
    funext y
    rw [show ((0 : Π x : M, TangentSpace I x) y : TangentSpace I y) = 0 from rfl,
        (cov Z y).map_zero]
    rfl
  rw [h1, hcov.zero (Set.mem_univ x)]
  -- mlieBracket I 0 Y = 0
  have hzero_mlb : mlieBracket I (0 : Π x : M, TangentSpace I x) Y = 0 := mlieBracket_zero_left
  rw [show mlieBracket I (0 : Π x : M, TangentSpace I x) Y x = 0 from by
        rw [hzero_mlb]; rfl,
      (cov Z x).map_zero]
  simp

/-! ## §5 Module summary marker

Per project convention, a `True` marker terminates each Lean module's
substantive content and gates module-level metadata. The Wave 8 Session
3 deliverable is **6 substantive theorems / 0 sorry / 0 new axioms** on
the Bonn `CovariantDerivative` API:
1. `bundleRiemannAux_self` — `R(X, X) Z = 0`
2. `bundleRiemannAux_swap_apply` — antisym-(X, Y) at a point
3. `bundleRiemannAux_swap` — antisym-(X, Y) as section-equality
4. `bundleRiemannAux_commuting_brackets` — commuting-VF specialization
5. `bundleRiemannAux_zero_section` — `R(X, Y) 0 = 0`
6. `bundleRiemannAux_zero_X` — `R(0, Y) Z = 0`

The corresponding `R(X, 0) Z = 0` falls out as `bundleRiemannAux_swap_apply
+ bundleRiemannAux_zero_X + neg_zero` and is intentionally not shipped to
avoid P3-trivial corollary plumbing.

**Session 4 (next):** `BundleRiemann.lean` — `TensorialAt.mkHom₃` +
bundled `CovariantDerivative.riemann` via `mkHom₃` + bundle-level first
Bianchi for torsion-free `cov` (3-line Jacobi consequence) + bundle-level
differential second Bianchi (3-line Jacobi consequence) + specialization
theorem on `EuclideanSpace ℝ (Fin 4)` reducing bundle Riemann to
Sessions-1+2 coordinate Riemann (delivers the full coord-level
differential second Bianchi + 6f.2 `∇^μ G_{μν} = 0` discharge as
direct consequences). -/
theorem _phase6f_w8_session3_module_summary_marker : True := trivial

end SKEFTHawking.BundleRiemannAux

end
