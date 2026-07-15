/-
# Phase 5q.H (W-A addClosure, layer 2) — naturality of the relative Wu operations across a pair map

The relative cup products `relCupH14`, `relCupH23` and the relative Steenrod square `relSq2` commute
with the relative cohomology pullback `relCohomPullback` along a map of pairs `φ : (X, SX) → (Y, SY)`.
This is the block-diagonality engine of the disjoint-union Wu assembly (`addClosure`): applied to the
two inclusions `inl`, `inr` it says the union's Wu operations restrict to the summands' Wu operations,
so the union Lefschetz pairing is block-diagonal and the union Wu class is the pair of the summands'.

The cup engine is `SingularCohomologyFunctoriality.cochainPullback_cup` (Alexander–Whitney naturality);
the `relSq2` engine is the general simplicial-operator naturality `map_op_mapSimplex` (the arbitrary-`g`
version of `face_mapSimplex`), giving `cochainPullback φ (cupOne33 x y) = cupOne33 (φ*x) (φ*y)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyDisjointSum
import SKEFTHawking.SingularRelativeCup
import SKEFTHawking.SingularRelativeSteenrodSq2

namespace SKEFTHawking.SingularRelativeCupSqNaturality

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularBockstein SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeCohomologyDisjointSum

/-! ## §1. The relative cup naturality -/

variable {X Y : TopCat} (φ : C(↑X, ↑Y)) {SX : Set ↑X} {SY : Set ↑Y} (hφ : Set.MapsTo φ SX SY)

/-- **`relCupH14` naturality**: `φ*(v ⌣ y) = φ*v ⌣ φ*y` across a pair map — absolute pullback on the
left `H¹` factor, relative pullback on the right `H⁴` factor and the `H⁵` result. -/
theorem relCohomPullback_relCupH14 (v : Cohomology Y 1) (y : RelativeCohomology SY 4) :
    relCohomPullback φ hφ 5 (relCupH14 v y)
      = relCupH14 (cohomologyPullback φ 1 v) (relCohomPullback φ hφ 4 y) := by
  obtain ⟨fc, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  apply congrArg (RelativeCohomology.mk SX 5)
  apply Subtype.ext
  apply Subtype.ext
  exact cochainPullback_cup φ fc.1 (gc.1 : SingularCochain Y 4)

/-- **`relCupH23` naturality**: `φ*(v ⌣ y) = φ*v ⌣ φ*y` on the `H² × H³(X,S) → H⁵(X,S)` cup. -/
theorem relCohomPullback_relCupH23 (v : Cohomology Y 2) (y : RelativeCohomology SY 3) :
    relCohomPullback φ hφ 5 (relCupH23 v y)
      = relCupH23 (cohomologyPullback φ 2 v) (relCohomPullback φ hφ 3 y) := by
  obtain ⟨fc, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  apply congrArg (RelativeCohomology.mk SX 5)
  apply Subtype.ext
  apply Subtype.ext
  exact cochainPullback_cup φ fc.1 (gc.1 : SingularCochain Y 3)

/-! ## §2. General simplicial-operator naturality and `relSq2` naturality -/

/-- **General simplicial-operator naturality of the simplex pushforward**: for any morphism
`g : [m] ⟶ [n]`, restricting `mapSimplex φ σ` along `g` is `mapSimplex φ` of the restriction of `σ`.
The arbitrary-`g` version of `face_mapSimplex` (`g = δ i`); `mapSimplex φ` realizes to `φ ∘ σ̃`, and
`g` acts by precomposition on the realization. -/
theorem map_op_mapSimplex {X Y : TopCat} (ψ : C(↑X, ↑Y)) {m n : ℕ}
    (g : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj Y).map g.op (mapSimplex ψ σ)
      = mapSimplex ψ ((TopCat.toSSet.obj X).map g.op σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk m))).injective
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rfl

/-- **Cup-`1` pullback naturality** (cochain level): `φ*(x ⌣₁ y) = φ*x ⌣₁ φ*y`. Each `cupOne33`
term is a product of two `g`-face restrictions, and `map_op_mapSimplex` moves `mapSimplex φ` through
each. -/
theorem cochainPullback_cupOne33 {X Y : TopCat} (ψ : C(↑X, ↑Y)) (a b : SingularCochain Y 3) :
    cochainPullback ψ 5 (cupOne33 a b)
      = cupOne33 (cochainPullback ψ 3 a) (cochainPullback ψ 3 b) := by
  funext σ
  show cupOne33 a b (mapSimplex ψ σ)
    = cupOne33 (cochainPullback ψ 3 a) (cochainPullback ψ 3 b) σ
  simp only [cupOne33, cochainPullback_apply, map_op_mapSimplex]

/-- **`relSq2` naturality**: `φ*(Sq² y) = Sq²(φ* y)` across a pair map — the substrate relative
Steenrod square commutes with the relative pullback. -/
theorem relCohomPullback_relSq2 (y : RelativeCohomology SY 3) :
    relCohomPullback φ hφ 5 (relSq2 y) = relSq2 (relCohomPullback φ hφ 3 y) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  apply congrArg (RelativeCohomology.mk SX 5)
  apply Subtype.ext
  apply Subtype.ext
  show cochainPullback φ 5 (cupOne33 a.1.1 a.1.1)
    = cupOne33 (cochainPullback φ 3 a.1.1) (cochainPullback φ 3 a.1.1)
  exact cochainPullback_cupOne33 φ a.1.1 a.1.1

/-! ## §3. The Bockstein `relSq1` naturality -/

/-- **Bockstein cochain pullback naturality** (cochain level): `φ*(Sq¹_cochain a) = Sq¹_cochain(φ*a)`.
The `ℤ/4` lift is a pointwise value operation and the `ℤ/4` coboundary is an alternating face sum, both
of which commute with the pullback (`face_mapSimplex`); `half` is pointwise. -/
theorem cochainPullback_Sq1cochain {X Y : TopCat} (ψ : C(↑X, ↑Y)) {n : ℕ} (a : SingularCochain Y n) :
    cochainPullback ψ (n + 1) (Sq1cochain a) = Sq1cochain (cochainPullback ψ n a) := by
  funext σ
  show Sq1cochain a (mapSimplex ψ σ) = Sq1cochain (cochainPullback ψ n a) σ
  unfold Sq1cochain
  congr 1

/-- **`relSq1` naturality**: `φ*(Sq¹ y) = Sq¹(φ* y)` across a pair map (the `(1,4)` leg's substrate
Bockstein commutes with the relative pullback). -/
theorem relCohomPullback_relSq1 (y : RelativeCohomology SY 4) :
    relCohomPullback φ hφ 5 (relSq1 (n := 3) y) = relSq1 (n := 3) (relCohomPullback φ hφ 4 y) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  apply congrArg (RelativeCohomology.mk SX 5)
  apply Subtype.ext
  apply Subtype.ext
  show cochainPullback φ 5 (Sq1cochain a.1.1) = Sq1cochain (cochainPullback φ 4 a.1.1)
  exact cochainPullback_Sq1cochain φ a.1.1

end SKEFTHawking.SingularRelativeCupSqNaturality
