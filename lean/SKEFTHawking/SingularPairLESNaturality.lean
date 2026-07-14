/-
# Phase 5q.H (W-A collar) — naturality of the pair LES under subspace enlargement + the mono four-lemma

Banks the reusable algebra that discharges the cylinder's collar-injectivity residual
`Injective (relIncl (∂W ⊆ Kᶜ))` (the `hinj` hypothesis of
`PoincareLefschetzRelFundClassCylinder.cylinder_determinedByInteriorPoints`):

* the three naturality squares of the `SingularPairLES` long exact sequence under a subspace
  enlargement `S' ⊆ S` — the vertical maps being the subspace-inclusion homology map `subMap`
  (`Homology.map` of `sub S' ↪ sub S`), the identity on `Hₙ(X)`, and `relIncl`;
* `relIncl_injective_of_subMap` — the **mono four-lemma**
  (`LinearMap.injective_of_surjective_of_injective_of_injective`) applied to the two pairs' LES's:
  `relIncl (S' ⊆ S) (n+1)` is injective once `subMap` is surjective in degree `n+1` and injective in
  degree `n`. This reduces the collar residual to the subspace inclusion being a homology iso in the
  two relevant degrees — supplied for the explicit cylinder collar by the clamp deformation retraction
  (companion module).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularRelativeFunctoriality
import SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularPairLESNaturality

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality

variable {X : TopCat} {S' S : Set ↑X}

/-! ## §1. The left vertical map: the subspace-inclusion homology map -/

/-- The subtype inclusion `sub S' → sub S` for `S' ⊆ S`, as a `TopCat` morphism (`Set.inclusion`). -/
def subInclMap (h : S' ⊆ S) : C(↑(sub S'), ↑(sub S)) :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- The subspace-inclusion homology map `Hₙ(sub S') → Hₙ(sub S)` for `S' ⊆ S` (`Homology.map` of the
subtype inclusion). The left vertical maps of the pair-LES naturality ladder. -/
noncomputable def subMap (h : S' ⊆ S) (n : ℕ) :
    Homology (sub S') n →ₗ[ZMod 2] Homology (sub S) n :=
  Homology.map (subInclMap h) n

/-- `subMap` on a homology class `[z]` pushes the cycle forward along the subtype inclusion. -/
theorem subMap_mk (h : S' ⊆ S) (n : ℕ) (z : cycles (sub S') n) :
    subMap h n (Homology.mk (sub S') n z) = Homology.mk (sub S) n (cyclesMap (subInclMap h) n z) :=
  Homology.map_mk (subInclMap h) n z

/-- The subtype inclusion `sub S' → sub S` composed with the ambient inclusion `sub S ↪ X` is the
ambient inclusion `sub S' ↪ X` (both are `Subtype.val`). -/
theorem ambIncl_comp_subInclMap (h : S' ⊆ S) :
    (ambIncl S).comp (subInclMap h) = ambIncl S' := rfl

/-- The chain inclusion `sub S ↪ X` absorbs the subtype-inclusion pushforward `sub S' → sub S`:
`chainIncl S ∘ mapChain (subInclMap) = chainIncl S'` (both include a `sub S'`-chain into `X`). -/
theorem chainIncl_mapChain_subInclMap (h : S' ⊆ S) (n : ℕ) (w : SingularChain (sub S') n) :
    chainIncl S n (mapChain (subInclMap h) n w) = chainIncl S' n w := by
  rw [← mapChain_ambIncl, ← mapChain_comp, ambIncl_comp_subInclMap, mapChain_ambIncl]

/-- Subspace chains are monotone in the subspace: `C_n(S') ⊆ C_n(S)` for `S' ⊆ S`. -/
theorem subspaceChains_mono (h : S' ⊆ S) (n : ℕ) :
    subspaceChains S' n ≤ subspaceChains S n := by
  rintro _ ⟨w, rfl⟩
  exact ⟨mapChain (subInclMap h) n w, chainIncl_mapChain_subInclMap h n w⟩

/-! ## §2. The three naturality squares -/

/-- **Square 1 (`homIncl`)**: `homIncl S ∘ subMap = homIncl S'` — the subspace-inclusion map commutes
with the LES inclusion `i_*` (both are `Homology.map` of `Subtype.val`, functorially). -/
theorem homIncl_subMap (h : S' ⊆ S) (n : ℕ) (x : Homology (sub S') n) :
    homIncl S n (subMap h n x) = homIncl S' n x := by
  rw [subMap, ← Homology.map_ambIncl, ← Homology.map_ambIncl, ← LinearMap.comp_apply,
    ← Homology.map_comp, ambIncl_comp_subInclMap]

/-- **Square 2 (`homProj`)**: `relIncl ∘ homProj S' = homProj S` — the relative projection `j_*` is
natural under subspace enlargement (top vertical map is the identity on `Hₙ(X)`). -/
theorem relIncl_homProj (h : S' ⊆ S) (n : ℕ) (x : Homology X n) :
    relIncl h n (homProj S' n x) = homProj S n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relIncl h n (homProj S' n (Homology.mk X n z)) = homProj S n (Homology.mk X n z)
  rw [homProj_mk, homProj_mk, relIncl_mk]
  refine congrArg (RelativeHomology.mk S n) (Subtype.ext ?_)
  simp only [relCyclesMap_coe, relMapChain_mk, mapChain_id]

/-- **Square 3 (`connecting`)**: `connecting S ∘ relIncl = subMap ∘ connecting S'` — the snake
connecting map `δ` is natural under subspace enlargement. -/
theorem connecting_subMap (h : S' ⊆ S) (n : ℕ) (y : RelativeHomology S' (n + 1)) :
    connecting S n (relIncl h (n + 1) y) = subMap h n (connecting S' n y) := by
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective S' n y
  have hcS : (c : SingularChain X (n + 1)) ∈ relCycleLift S n :=
    Submodule.mem_comap.mpr (subspaceChains_mono h n (Submodule.mem_comap.mp c.2))
  have hrel : relIncl h (n + 1) (relCycleToHom S' n c)
      = relCycleToHom S n ⟨(c : SingularChain X (n + 1)), hcS⟩ := by
    rw [relCycleToHom_apply, relCycleToHom_apply, relIncl_mk]
    refine congrArg (RelativeHomology.mk S (n + 1)) (Subtype.ext ?_)
    simp only [relCyclesMap_coe, relMapChain_mk, mapChain_id]
  rw [hrel, connecting_relCycleToHom, connecting_relCycleToHom, connectingLift_apply,
    connectingLift_apply, subMap_mk]
  refine congrArg (Homology.mk (sub S) n) (Subtype.ext ?_)
  rw [cyclesMap_coe]
  apply chainIncl_injective S n
  rw [chainIncl_boundaryExtract, chainIncl_mapChain_subInclMap, chainIncl_boundaryExtract]

/-! ## §3. The mono four-lemma reduction -/

/-- **Collar-injectivity reduction (mono four-lemma).** `relIncl (S' ⊆ S) (n+1)` is injective once the
subspace-inclusion homology map is surjective in degree `n+1` and injective in degree `n`. Applies the
module-level mono four-lemma (`LinearMap.injective_of_surjective_of_injective_of_injective`) to the map
of pair-LES's `(X, S') → (X, S)`, with the three naturality squares above and the exactness of both
LES's. This is exactly the reduction of the collar residual `Injective (relIncl (∂W ⊆ Kᶜ))` to the
subspace inclusion being a homology iso in the two relevant degrees. -/
theorem relIncl_injective_of_subMap (h : S' ⊆ S) (n : ℕ)
    (hsurj : Function.Surjective (subMap h (n + 1)))
    (hinj : Function.Injective (subMap h n)) :
    Function.Injective (relIncl h (n + 1)) :=
  LinearMap.injective_of_surjective_of_injective_of_injective
    (f₁ := homIncl S' (n + 1)) (f₂ := homProj S' (n + 1)) (f₃ := connecting S' n)
    (g₁ := homIncl S (n + 1)) (g₂ := homProj S (n + 1)) (g₃ := connecting S n)
    (i₁ := subMap h (n + 1)) (i₂ := LinearMap.id) (i₃ := relIncl h (n + 1)) (i₄ := subMap h n)
    (hc₁ := by ext x; simpa using homIncl_subMap h (n + 1) x)
    (hc₂ := by ext x; simpa using (relIncl_homProj h (n + 1) x).symm)
    (hc₃ := by ext y; simpa using connecting_subMap h n y)
    (hf₁ := exact_homIncl_homProj S' (n + 1))
    (hf₂ := exact_homProj_connecting S' n)
    (hg₁ := exact_homIncl_homProj S (n + 1))
    hsurj (fun _ _ hab => hab) hinj

end SKEFTHawking.SingularPairLESNaturality
