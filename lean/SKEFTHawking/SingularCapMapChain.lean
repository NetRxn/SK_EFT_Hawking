import Mathlib
import SKEFTHawking.SingularHomologyMod2
import SKEFTHawking.SingularCohomologyMod2
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularRelativeCap
import SKEFTHawking.SingularKroneckerFunctoriality

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — cap–pushforward naturality (cap-seam-transport)

`cap_mapChain` is the naturality of the cap product under a continuous pushforward `φ_# = mapChain φ`:

    a ⌢ (φ_# z) = φ_# ((pullbackCochainMap φ a) ⌢ z).

The cap-side analogue of `cap_chainIncl` (which is the `simplexIncl` special case). The proof is the same
`Finsupp.induction` + `frontFace`/`backFace` commute with the simplex pushforward `mapSimplex φ`
(`frontFace_mapSimplex` / `backFace_mapSimplex`, the pushforward analogues of `frontFace_simplexIncl`).

The connecting-square `hLHS` needs exactly this: the LHS V-part `boundaryExtract (cap g̃|_V w)` is
seam-transported (`mapChain` of the identity-on-X seam homeos) into `sub (U∩V)`, and `cap_mapChain` moves
the cap through the transport so it lands as `cap (g↾) c` (the form `cross_realization_match.hLHS` wants).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularFunctoriality
  SKEFTHawking.SingularKroneckerFunctoriality

namespace SKEFTHawking.SingularCapMapChain

open CategoryTheory Opposite

/-- **`frontFace` commutes with the simplex pushforward** (naturality of `mapSimplex φ` against the
front-face inclusion `frontIncl`, the pushforward analogue of `frontFace_simplexIncl`). -/
theorem frontFace_mapSimplex {X Y : TopCat} (φ : C(↑X, ↑Y)) {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    frontFace (mapSimplex φ σ) = mapSimplex φ (frontFace σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk p))).injective
  simp only [mapSimplex, frontFace, Equiv.apply_symm_apply]
  rfl

/-- **`backFace` commutes with the simplex pushforward** (the back-face analogue of
`frontFace_mapSimplex`). -/
theorem backFace_mapSimplex {X Y : TopCat} (φ : C(↑X, ↑Y)) {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    backFace (mapSimplex φ σ) = mapSimplex φ (backFace σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk q))).injective
  simp only [mapSimplex, backFace, Equiv.apply_symm_apply]
  rfl

/-- **Cap–pushforward naturality**: `a ⌢ (φ_# z) = φ_# ((pullbackCochainMap φ a) ⌢ z)`. -/
theorem cap_mapChain {X Y : TopCat} (φ : C(↑X, ↑Y)) {k m : ℕ} (a : SingularCochain Y k)
    (z : SingularChain X (k + m)) :
    cap a (mapChain φ (k + m) z) = mapChain φ m (cap (pullbackCochainMap φ k a) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single σ s =>
      rw [mapChain_single, cap_single_smul, cap_single_smul, capBasis, capBasis,
        pullbackCochainMap_apply, frontFace_mapSimplex, backFace_mapSimplex, map_smul, map_smul,
        mapChain_single]

end SKEFTHawking.SingularCapMapChain
