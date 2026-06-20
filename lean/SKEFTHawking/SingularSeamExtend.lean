import Mathlib
import SKEFTHawking.SingularCapChainIncl
import SKEFTHawking.SingularExcision

/-!
# Phase 5q.F (w₂-foundation) — the seam extend-by-zero cochain

Foundational infrastructure for the Poincaré-duality **connecting-square** match: given a nested pair
of subspaces `T : Set ↑(sub S)` (so `T` is a subspace of the subspace `sub S ⊆ X`), the restriction
of cochains along the seam inclusion `sub T ↪ sub S` is `pullbackCochain T k` (precomposition with
`simplexIncl`). We construct its **section** — the *extend-by-zero* cochain `seamExtend a` of a cochain
`a : SingularCochain (sub T) k`, which is `a` on simplices that factor through `T` and `0` off `T`:

  `pullbackCochain T k (seamExtend a) = a`.

The crux is the **simplex corestriction** `seamCorestrict`: a `sub S`-simplex `σ` whose realization
lands in `T` is the inclusion `simplexIncl T k σ'` of a unique `sub T`-simplex `σ'`. We adapt the
construction inside `single_mem_subspaceChains_of_subordinate` (`SingularExcision.lean`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}` only).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularExcision

namespace SKEFTHawking.SingularSeamExtend

variable {X : TopCat} {S : Set X} (T : Set ↥(sub S)) (k : ℕ)

/-- The "factors through `T`" predicate on a `sub S`-simplex: its realization range lands in `T`. -/
def FactorsThrough (σ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))) : Prop :=
  Set.range ((sub S).toSSetObjEquiv (op (SimplexCategory.mk k)) σ) ⊆ T

/-- **The simplex corestriction**: a `sub S`-simplex `σ` whose realization lands in `T`, corestricted
to a `sub T`-simplex. Adapts `single_mem_subspaceChains_of_subordinate`. -/
noncomputable def seamCorestrict
    (σ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k)))
    (hσ : FactorsThrough T k σ) :
    (TopCat.toSSet.obj (sub T)).obj (op (SimplexCategory.mk k)) :=
  letI g := (sub S).toSSetObjEquiv (op (SimplexCategory.mk k)) σ
  ((sub T).toSSetObjEquiv (op (SimplexCategory.mk k))).symm
    (⟨fun t => ⟨g t, hσ ⟨t, rfl⟩⟩, g.continuous.subtype_mk fun t => hσ ⟨t, rfl⟩⟩ :
      C(stdSimplex ℝ (Fin (k + 1)), sub T))

/-- `seamCorestrict` is a section of `simplexIncl`: including the corestricted simplex back recovers
`σ`. -/
theorem simplexIncl_seamCorestrict
    (σ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k)))
    (hσ : FactorsThrough T k σ) :
    simplexIncl T k (seamCorestrict T k σ hσ) = σ := by
  apply ((sub S).toSSetObjEquiv (op (SimplexCategory.mk k))).injective
  rw [toSSetObjEquiv_simplexIncl, seamCorestrict, Equiv.apply_symm_apply]
  rfl

/-- **The seam extend-by-zero cochain**: extend a `sub T`-cochain `a` to a `sub S`-cochain that is `a`
on simplices that factor through `T` (corestricted via `seamCorestrict`) and `0` off `T`. -/
noncomputable def seamExtend (a : SingularCochain (sub T) k) : SingularCochain (sub S) k :=
  fun σ =>
    haveI : Decidable (FactorsThrough T k σ) := Classical.dec _
    if h : FactorsThrough T k σ then a (seamCorestrict T k σ h) else 0

/-- **The pullback inverts the extension**: restricting `seamExtend a` along the seam inclusion
`sub T ↪ sub S` recovers `a`. On a `sub T`-simplex `τ`, `simplexIncl T k τ` factors through `T` (its
range is in `T` by `range_simplexIncl_subset`), so the `dite`-true branch fires; the corestriction of
the inclusion is `τ` (`seamCorestrict ∘ simplexIncl = id`, from `simplexIncl` being a mono section). -/
theorem pullbackCochain_seamExtend (a : SingularCochain (sub T) k) :
    pullbackCochain T k (seamExtend T k a) = a := by
  funext τ
  have hfac : FactorsThrough T k (simplexIncl T k τ) := range_simplexIncl_subset T τ
  have hcore : seamCorestrict T k (simplexIncl T k τ) hfac = τ :=
    simplexIncl_injective T k (simplexIncl_seamCorestrict T k _ hfac)
  rw [pullbackCochain_apply, seamExtend, dif_pos hfac, hcore]

end SKEFTHawking.SingularSeamExtend
