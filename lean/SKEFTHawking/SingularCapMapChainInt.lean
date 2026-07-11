import Mathlib
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularFunctorialityInt

/-!
# Phase 5q.H (E1 integral naturality) — cap–pushforward naturality, ℤ side (hcore brick 6e-b)

`capInt_mapChain` is the integral mirror of the mod-2 `SingularCapMapChain.cap_mapChain`: the
naturality of the integral cap product under a continuous pushforward `φ_# = mapChainInt φ`,

    a ⌢ (φ_# z) = φ_# ((pullbackCochainMapInt φ a) ⌢ z).

`pullbackCochainMapInt` (the integral cochain precomposition `(φ^* f) σ = f (mapSimplex φ σ)`) is
NEW — the ℤ mirror of `SingularKroneckerFunctoriality.pullbackCochainMap` did not previously exist,
since no ℤ-side Kronecker/cochain-functoriality module has been built yet. Likewise
`frontFace_mapSimplexInt` / `backFace_mapSimplexInt` (naturality of the Alexander–Whitney front/back
split against `mapSimplex φ`, for the ℤ-model `frontFace`/`backFace` from `SingularCupInt`) are new.
Both are proved by the identical argument to their mod-2 counterparts (`frontFace`/`backFace` are
coefficient-free simplicial-set operations; `IntersectionFormEvenInt.frontFace_eq` / `backFace_eq`
record that the ℤ- and ℤ/2-model `frontFace`/`backFace` agree by `rfl`).

The `capInt_mapChain` proof is the verbatim integral transliteration of `cap_mapChain`'s
`Finsupp.induction_linear` + `capBasisInt` unfolding, swapping in the ℤ-linear
`capInt`/`capInt_single_smul`/`capBasisInt` (`IntCapProductInt`) and
`mapChainInt`/`mapChainInt_single` (`SingularFunctorialityInt`) for their mod-2 counterparts.
Used by the seam-match `hmatch` to transport the `B`-part cap through the seam homeomorphism.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctoriality (mapSimplex)
open SKEFTHawking.SingularFunctorialityInt

namespace SKEFTHawking.SingularCapMapChainInt

/-- **`frontFace` commutes with the simplex pushforward**, ℤ side (integral mirror of
`SingularCohomologyFunctoriality.frontFace_mapSimplex`, over the ℤ-model `frontFace` from
`SingularCupInt`). -/
theorem frontFace_mapSimplexInt {X Y : TopCat} (φ : C(↑X, ↑Y)) {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    frontFace (mapSimplex φ σ) = mapSimplex φ (frontFace (p := p) (q := q) σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk p))).injective
  simp only [mapSimplex, frontFace, Equiv.apply_symm_apply]
  rfl

/-- **`backFace` commutes with the simplex pushforward**, ℤ side (the back-face analogue of
`frontFace_mapSimplexInt`). -/
theorem backFace_mapSimplexInt {X Y : TopCat} (φ : C(↑X, ↑Y)) {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    backFace (mapSimplex φ σ) = mapSimplex φ (backFace (p := p) (q := q) σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk q))).injective
  simp only [mapSimplex, backFace, Equiv.apply_symm_apply]
  rfl

/-- **ℤ cochain pullback** `φ^* : Cⁿ(Y;ℤ) → Cⁿ(X;ℤ)`, `(φ^* f) σ = f (mapSimplex φ σ)` — the
integral mirror of `SingularKroneckerFunctoriality.pullbackCochainMap`. -/
noncomputable def pullbackCochainMapInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (f : SingularCochainInt Y n) : SingularCochainInt X n :=
  fun σ => f (mapSimplex φ σ)

@[simp] theorem pullbackCochainMapInt_apply {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (f : SingularCochainInt Y n) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    pullbackCochainMapInt φ n f σ = f (mapSimplex φ σ) := rfl

/-- **Cap–pushforward naturality**, ℤ side: `a ⌢ (φ_# z) = φ_# ((pullbackCochainMapInt φ a) ⌢ z)`.
The integral mirror of `SingularCapMapChain.cap_mapChain`. -/
theorem capInt_mapChain {X Y : TopCat} (φ : C(↑X, ↑Y)) {k m : ℕ} (a : SingularCochainInt Y k)
    (z : SingularChainInt X (k + m)) :
    capInt (m := m) a (mapChainInt φ (k + m) z)
      = mapChainInt φ m (capInt (m := m) (pullbackCochainMapInt φ k a) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single σ s =>
      rw [mapChainInt_single, capInt_single_smul, capInt_single_smul, capBasisInt, capBasisInt,
        pullbackCochainMapInt_apply, frontFace_mapSimplexInt, backFace_mapSimplexInt, map_smul,
        map_smul, mapChainInt_single]

end SKEFTHawking.SingularCapMapChainInt
