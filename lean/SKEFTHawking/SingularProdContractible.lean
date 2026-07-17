/-
# Phase 5q.H close-out — the mod-2 mirror of the contractible-factor collapse
# `Hₙ₊₁(Y × C; ℤ/2) ≅ Hₙ₊₁(Y; ℤ/2)`

The mod-2 twin of `SingularProdContractibleInt` (whose own docstring flags this exact mirror as the
intended future work: "Every continuous-map-level construction … is coefficient-agnostic — the
future mod-2 mirror of this module only re-instantiates the homology layer"). For ANY space `Y` and
a factor `C` carrying a contraction (`H(·,0) = id`, `H(·,1) = const c₀`), the first-factor projection
induces an isomorphism on mod-2 homology in every positive degree: a product with a contractible
factor collapses onto the other factor. No Künneth machinery is needed — the projection/section pair
is a homotopy equivalence, and the in-tree mod-2 homotopy invariance
(`SingularHomotopyInvariance.Homology.map_bijective_of_homotopyEquiv`) does the rest.

Only §1 (the product data) and §2 (the collapse) are ported here — the exact slice this project's
`SphereDisk = S²×D³` needs (§0's homeomorphism-transport and §3's subtype-seam sections of the
integral original are NOT needed for this brick and are left for a future full mirror, should a
mod-2 computation of `S²×S²` itself ever be undertaken).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularHomotopyInvariance

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularFunctoriality (Homology.map)
open SKEFTHawking.SingularHomotopyInvariance (slice Homology.map_bijective_of_homotopyEquiv)

namespace SKEFTHawking.SingularProdContractible

/-! ## §1. The product data: projection, section, and the interpolating homotopies -/

/-- `Y × C` as a topological space object (the product topology). -/
abbrev ProdSp (Y C : TopCat) : TopCat := TopCat.of (↑Y × ↑C)

/-- The first-factor projection `Y × C → Y`. -/
def prodFst (Y C : TopCat) : C(↑(ProdSp Y C), ↑Y) := ⟨Prod.fst, continuous_fst⟩

/-- The section `y ↦ (y, c₀)` of the projection at a chosen basepoint of the factor. -/
def prodSect (Y C : TopCat) (c₀ : ↑C) : C(↑Y, ↑(ProdSp Y C)) :=
  ⟨fun y => (y, c₀), (continuous_id.prodMk continuous_const)⟩

/-- The section is a strict right inverse of the projection: `prodFst ∘ prodSect = id`. -/
theorem prodFst_comp_prodSect (Y C : TopCat) (c₀ : ↑C) :
    (prodFst Y C).comp (prodSect Y C c₀) = ContinuousMap.id ↑Y :=
  ContinuousMap.ext fun _ => rfl

/-- The constant (stationary) homotopy on `Y`: every slice is the identity. Witnesses the strict
half `prodFst ∘ prodSect = id` in the homotopy-equivalence binder shape. -/
def constHomotopy (Y : TopCat) : C(↑Y × unitInterval, ↑Y) := ⟨Prod.fst, continuous_fst⟩

theorem slice_constHomotopy (Y : TopCat) (r : unitInterval) :
    slice (constHomotopy Y) r = ContinuousMap.id ↑Y :=
  ContinuousMap.ext fun _ => rfl

/-- **The product homotopy** `((y, c), t) ↦ (y, H(c, 1 − t))` interpolating `prodSect ∘ prodFst ≃
id` from a contraction `H` of the factor — time-REVERSED (`1 − t` via `unitInterval.symm`) so that
`slice 0 = prodSect ∘ prodFst` and `slice 1 = id`, the exact binder shape
`Homology.map_bijective_of_homotopyEquiv` consumes. -/
noncomputable def prodHomotopy (Y C : TopCat) (H : C(↑C × unitInterval, ↑C)) :
    C(↑(ProdSp Y C) × unitInterval, ↑(ProdSp Y C)) :=
  ⟨fun p => (p.1.1, H (p.1.2, unitInterval.symm p.2)),
    ((continuous_fst.comp continuous_fst).prodMk (H.continuous.comp
      ((continuous_snd.comp continuous_fst).prodMk
        (unitInterval.continuous_symm.comp continuous_snd))))⟩

/-- The product homotopy's `t = 0` slice is `prodSect ∘ prodFst` (the factor sits at the
contraction's endpoint `H(·, 1) = c₀`). -/
theorem slice_prodHomotopy_zero (Y C : TopCat) (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C))
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) :
    slice (prodHomotopy Y C H) 0 = (prodSect Y C c₀).comp (prodFst Y C) := by
  refine ContinuousMap.ext fun p => ?_
  show (p.1, H (p.2, unitInterval.symm 0)) = (p.1, c₀)
  rw [unitInterval.symm_zero]
  exact congrArg (Prod.mk p.1) (ContinuousMap.congr_fun h1 p.2)

/-- The product homotopy's `t = 1` slice is the identity (the factor sits at the contraction's
start `H(·, 0) = id`). -/
theorem slice_prodHomotopy_one (Y C : TopCat) (H : C(↑C × unitInterval, ↑C))
    (h0 : slice H 0 = ContinuousMap.id ↑C) :
    slice (prodHomotopy Y C H) 1 = ContinuousMap.id ↑(ProdSp Y C) := by
  refine ContinuousMap.ext fun p => ?_
  show (p.1, H (p.2, unitInterval.symm 1)) = p
  rw [unitInterval.symm_one]
  exact (congrArg (Prod.mk p.1) (ContinuousMap.congr_fun h0 p.2)).trans rfl

/-! ## §2. The collapse: `Hₙ₊₁(Y × C; ℤ/2) ≅ Hₙ₊₁(Y; ℤ/2)` for a contractible factor -/

/-- **The projection is a homology isomorphism (bijective) in every positive degree** when the
factor carries a contraction: `prodFst`/`prodSect` are homotopy inverse (`prodHomotopy` one way,
strictly the other), so mod-2 homotopy invariance applies. -/
theorem prodFst_bijective (Y C : TopCat) (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C))
    (h0 : slice H 0 = ContinuousMap.id ↑C) (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Function.Bijective (Homology.map (prodFst Y C) (n + 1)) :=
  Homology.map_bijective_of_homotopyEquiv (prodFst Y C) (prodSect Y C c₀)
    (prodHomotopy Y C H) (slice_prodHomotopy_zero Y C c₀ H h1) (slice_prodHomotopy_one Y C H h0)
    (constHomotopy Y) ((slice_constHomotopy Y 0).trans (prodFst_comp_prodSect Y C c₀).symm)
    (slice_constHomotopy Y 1) n

/-- **The contractible-factor collapse** `Hₙ₊₁(Y × C; ℤ/2) ≃ₗ[ZMod 2] Hₙ₊₁(Y; ℤ/2)`, induced by the
first-factor projection. The product-homology arc's first reusable primitive, mod-2. -/
noncomputable def prodContractibleEquiv (Y C : TopCat) (c₀ : ↑C)
    (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Homology (ProdSp Y C) (n + 1) ≃ₗ[ZMod 2] Homology Y (n + 1) :=
  LinearEquiv.ofBijective (Homology.map (prodFst Y C) (n + 1))
    (prodFst_bijective Y C c₀ H h0 h1 n)

end SKEFTHawking.SingularProdContractible
