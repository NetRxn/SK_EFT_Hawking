/-
# Phase 5q.F — functoriality of singular ℤ/2 cohomology (toward the ξ_Pin⁺ `TangentialData` instance)

The faithful Pin⁺ `TangentialData` instance carries `Mfd s = H¹(s.M; ℤ/2)`-torsor of Pin⁺ structures, and
its closure operations (disjoint union, cylinder, boundary restriction along a bordism) are the maps on
`H¹` induced by the corresponding continuous maps. This module builds that **functoriality**: a continuous
map `f : Y ⟶ X` of spaces induces `f* : Cochain X n → Cochain Y n` (precomposition with the simplicial
map `toSSet.map f`), a cochain-complex map (commutes with `δ` by naturality of `toSSet.map f`), hence a
map `Cohomology X n → Cohomology Y n`.
-/
import SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularCohomologyMod2

open CategoryTheory Opposite

variable {X Y Z : TopCat}

/-- The **induced map on singular `n`-cochains** of a continuous map `f : Y ⟶ X`: precompose a cochain on
`X` with the simplicial map `toSSet.map f` (a `ZMod 2`-linear map `Cochain X n → Cochain Y n`). -/
noncomputable def inducedCochainₗ (f : Y ⟶ X) (n : ℕ) :
    SingularCochain X n →ₗ[ZMod 2] SingularCochain Y n where
  toFun g := fun σ => g ((TopCat.toSSet.map f).app (op (SimplexCategory.mk n)) σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inducedCochainₗ_apply (f : Y ⟶ X) (n : ℕ) (g : SingularCochain X n)
    (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk n))) :
    inducedCochainₗ f n g σ = g ((TopCat.toSSet.map f).app (op (SimplexCategory.mk n)) σ) := rfl

/-- **`f*` commutes with `δ`** (the induced map is a cochain-complex map). The naturality of the
simplicial map `toSSet.map f` with respect to the cofaces `δ i` gives `f*(∂ᵢσ) = ∂ᵢ(f*σ)`, so the
alternating (mod 2: plain) sums agree. -/
theorem coboundary_inducedCochain (f : Y ⟶ X) (n : ℕ) (g : SingularCochain X n) :
    coboundary Y n (inducedCochainₗ f n g) = inducedCochainₗ f (n + 1) (coboundary X n g) := by
  funext σ
  simp only [coboundary_apply, inducedCochainₗ_apply, face]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact congrArg g (congrFun ((TopCat.toSSet.map f).naturality (SimplexCategory.δ i).op) σ).symm

/-- The induced map sends cocycles to cocycles. -/
theorem inducedCochainₗ_mem_ker (f : Y ⟶ X) (n : ℕ) (g : SingularCochain X n)
    (hg : coboundaryₗ X n g = 0) : coboundaryₗ Y n (inducedCochainₗ f n g) = 0 := by
  show coboundary Y n (inducedCochainₗ f n g) = 0
  rw [coboundary_inducedCochain]
  show inducedCochainₗ f (n + 1) (coboundary X n g) = 0
  rw [show coboundary X n g = coboundaryₗ X n g from rfl, hg, map_zero]

/-- **The induced map on singular `ℤ/2` cohomology** `f* : Hⁿ(X;ℤ/2) → Hⁿ(Y;ℤ/2)` of a continuous map
`f : Y ⟶ X`. Well-defined: `f*` preserves cocycles (`inducedCochainₗ_mem_ker`) and coboundaries (from
`coboundary_inducedCochain`), so it descends to the quotient. -/
noncomputable def inducedCohomology (f : Y ⟶ X) (n : ℕ) :
    Cohomology X n →ₗ[ZMod 2] Cohomology Y n :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((inducedCochainₗ f n).domRestrict (LinearMap.ker (coboundaryₗ X n))).codRestrict
        (LinearMap.ker (coboundaryₗ Y n)) fun gc => by
          rw [LinearMap.mem_ker]
          exact inducedCochainₗ_mem_ker f n gc.1 (LinearMap.mem_ker.mp gc.2)))
    (by
      intro gc hgc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hgc
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      cases n with
      | zero =>
        rw [show coboundaryRange X 0 = ⊥ from rfl, Submodule.mem_bot] at hgc
        rw [show coboundaryRange Y 0 = ⊥ from rfl, Submodule.mem_bot, hgc, map_zero]
      | succ m =>
        obtain ⟨h, hh⟩ := hgc
        exact ⟨inducedCochainₗ f m h, by rw [← hh]; exact (coboundary_inducedCochain f m h).symm⟩)

@[simp] theorem inducedCohomology_mk (f : Y ⟶ X) (n : ℕ)
    (gc : LinearMap.ker (coboundaryₗ X n)) :
    inducedCohomology f n (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨inducedCochainₗ f n gc.1,
          inducedCochainₗ_mem_ker f n gc.1 (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ Y n)) := rfl

/-! ### Functor laws (`id* = id`, `(g ≫ f)* = f* ∘ g*`) — the operative content of the ξ_Pin⁺ ops -/

/-- `(𝟙 X)* = id` on cochains. -/
theorem inducedCochainₗ_id (n : ℕ) : inducedCochainₗ (𝟙 X) n = LinearMap.id := by
  ext g σ
  simp only [inducedCochainₗ_apply, CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app,
    CategoryTheory.types_id_apply, LinearMap.id_coe, id_eq]

/-- `(g ≫ f)* = f* ∘ g*` on cochains (contravariant functoriality). -/
theorem inducedCochainₗ_comp {Z : TopCat} (g : Z ⟶ Y) (f : Y ⟶ X) (n : ℕ) :
    inducedCochainₗ (g ≫ f) n = (inducedCochainₗ g n).comp (inducedCochainₗ f n) := by
  ext h σ
  simp only [inducedCochainₗ_apply, CategoryTheory.Functor.map_comp, CategoryTheory.NatTrans.comp_app,
    CategoryTheory.types_comp_apply, LinearMap.coe_comp, Function.comp_apply]

/-- `(𝟙 X)* = id` on cohomology. -/
@[simp] theorem inducedCohomology_id (n : ℕ) : inducedCohomology (𝟙 X) n = LinearMap.id := by
  ext x
  obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [inducedCohomology_mk, LinearMap.id_apply]
  congr 1

/-- `(g ≫ f)* = f* ∘ g*` on cohomology (contravariant functoriality). -/
theorem inducedCohomology_comp {Z : TopCat} (g : Z ⟶ Y) (f : Y ⟶ X) (n : ℕ) :
    inducedCohomology (g ≫ f) n = (inducedCohomology g n).comp (inducedCohomology f n) := by
  ext x
  obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [inducedCohomology_mk, LinearMap.comp_apply, inducedCohomology_mk, inducedCohomology_mk]
  congr 1

end SKEFTHawking.SingularCohomologyMod2
