/-
# Phase 5q.H close-out — HOMOLOGY FINITE-DIMENSIONALITY TRANSFER (homotopy/homeo invariance bricks)

The capstone cohomology MV datum (`PinPlusTraceCapstoneCohomologyMV.lean`) bottoms out in the
all-degree homology finiteness of the two MV pieces `A ≃ M` (cyl side) and `B ≃ D⁵` (handle side) and
their overlap. This module banks the GENERAL, carrier-agnostic bricks that transfer homology
finite-dimensionality along a homotopy equivalence / homeomorphism, so those per-piece finiteness facts
reduce to the standard homotopy-type inputs (`H_*(M) < ∞` for a closed manifold, `H_*(D⁵) < ∞` for the
contractible handle) rather than being carried opaquely.

## The bricks (all kernel-pure, general in `X, Y : TopCat`)

* **`finiteDimensional_homology_of_homotopyEquiv`** — `Hₙ₊₁(X) < ∞` ⟸ `Hₙ₊₁(Y) < ∞`, given a homotopy
  equivalence `X ≃ Y` (witnessed by `g ∘ f ≃ id`, `f ∘ g ≃ id`), via
  `Homology.map_bijective_of_homotopyEquiv` packaged as a `LinearEquiv`. Degree `≥ 1`
  (homotopy invariance).
* **`finiteDimensional_homology_of_homeo_all`** — `Hₙ(X) < ∞` ⟸ `Hₙ(Y) < ∞` in EVERY degree, given
  maps `f`/`g` with identity composites (the two halves of a homeomorphism), via
  `Homology.map_bijective_of_comp_id_all` (functoriality only, so degree `0` too).
* **`finiteDimensional_homology_of_homeomorph`** — the `Homeomorph`-packaged form: `Hₙ(X) < ∞` ⟸
  `Hₙ(Y) < ∞` for `e : X ≃ₜ Y`, every degree — the shape the constructed pieces `sub A ≃ₜ M`,
  `sub B ≃ₜ D⁵` supply.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularHomotopyInvariance

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.SingularHomologyFiniteTransfer

noncomputable section

/-- **Homology finite-dimensionality transfers along a homotopy equivalence** (degree `≥ 1`): given
`f : X → Y`, `g : Y → X` with `g ∘ f ≃ id_X` and `f ∘ g ≃ id_Y`, `Hₙ₊₁(X)` is finite-dimensional as
soon as `Hₙ₊₁(Y)` is (`Homology.map f` is a `LinearEquiv` by `map_bijective_of_homotopyEquiv`). -/
theorem finiteDimensional_homology_of_homotopyEquiv {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : slice Hgf 0 = g.comp f)
    (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X) (Hfg : C(↑Y × unitInterval, ↑Y))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Homology Y (n + 1))) :
    FiniteDimensional (ZMod 2) (Homology X (n + 1)) := by
  haveI := h
  exact (LinearEquiv.ofBijective (Homology.map f (n + 1))
    (Homology.map_bijective_of_homotopyEquiv f g Hgf hgf0 hgf1 Hfg hfg0 hfg1 n)).symm.finiteDimensional

/-- **Homology finite-dimensionality transfers along an identity-composite pair** (every degree,
functoriality only): maps `f`/`g` with `g ∘ f = id_X`, `f ∘ g = id_Y` give `Hₙ(X) < ∞ ⟸ Hₙ(Y) < ∞`. -/
theorem finiteDimensional_homology_of_homeo_all {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Homology Y n)) :
    FiniteDimensional (ZMod 2) (Homology X n) := by
  haveI := h
  exact (LinearEquiv.ofBijective (Homology.map f n)
    (Homology.map_bijective_of_comp_id_all f g hgf hfg n)).symm.finiteDimensional

/-- **Homology finite-dimensionality transfers along a homeomorphism** (every degree): for `e : X ≃ₜ Y`,
`Hₙ(X) < ∞ ⟸ Hₙ(Y) < ∞`. The `Homeomorph`-packaged form of `finiteDimensional_homology_of_homeo_all`
— the shape the constructed MV pieces (`sub A ≃ₜ M`, `sub B ≃ₜ D⁵`) supply. -/
theorem finiteDimensional_homology_of_homeomorph {X Y : TopCat} (e : ↑X ≃ₜ ↑Y) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Homology Y n)) :
    FiniteDimensional (ZMod 2) (Homology X n) :=
  finiteDimensional_homology_of_homeo_all (⟨e, e.continuous⟩ : C(↑X, ↑Y))
    (⟨e.symm, e.symm.continuous⟩ : C(↑Y, ↑X))
    (ContinuousMap.ext fun x => e.symm_apply_apply x)
    (ContinuousMap.ext fun y => e.apply_symm_apply y) n h

end

end SKEFTHawking.SingularHomologyFiniteTransfer
