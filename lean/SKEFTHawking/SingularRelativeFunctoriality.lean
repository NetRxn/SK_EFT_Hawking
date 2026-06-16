import Mathlib
import SKEFTHawking.SingularExcision
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularDisjointUnion

/-!
# Functoriality of relative homology

A **map of pairs** `φ : (X, A) → (Y, B)` (a continuous `φ : X → Y` with `φ(A) ⊆ B`) induces
`Hₙ(X, A) → Hₙ(Y, B)`: the pushforward `φ_#` sends `A`-chains to `B`-chains (an `A`-valued simplex
post-composed with `φ` is `B`-valued), so it descends to relative chains and then to relative
homology. A homeomorphism of pairs induces an isomorphism. This is the engine of the chart↔excision
bridge `Hₙ(M, M∖x) ≅ Hₙ(ℝⁿ, ℝⁿ∖0)` for the fundamental class.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularExcision
open SKEFTHawking.SingularDisjointUnion

namespace SKEFTHawking.SingularRelativeFunctoriality

/-- The realization of a pushforward simplex is `φ` post-composed with the realization. -/
theorem range_realize_mapSimplex {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    Set.range (Y.toSSetObjEquiv (op (SimplexCategory.mk n)) (mapSimplex φ σ))
      = φ '' Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) := by
  rw [mapSimplex, Equiv.apply_symm_apply, ← Set.range_comp]
  rfl

/-- **`φ_#` sends `A`-chains to `B`-chains** when `φ` maps `A` into `B`: an `A`-valued simplex
post-composed with `φ` is `B`-valued (`single_mem_subspaceChains_of_subordinate`). -/
theorem mapChain_mem_subspaceChains {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y}
    (hAB : Set.MapsTo φ A B) (n : ℕ) (c : SingularChain X n)
    (hc : c ∈ subspaceChains (S := A) n) :
    mapChain φ n c ∈ subspaceChains (S := B) n := by
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  | single σ' a =>
      rw [chainIncl_single, mapChain_single,
        show Finsupp.single (mapSimplex φ (simplexIncl A n σ')) a
          = a • Finsupp.single (mapSimplex φ (simplexIncl A n σ')) (1 : ZMod 2) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      refine (subspaceChains (S := B) n).smul_mem a ?_
      apply single_mem_subspaceChains_of_subordinate (A := B)
      rw [range_realize_mapSimplex]
      exact (Set.image_mono (range_realize_simplexIncl A σ')).trans hAB.image_subset

variable {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo φ A B)

/-- **The induced map on relative chains** `C(X, A) → C(Y, B)` (the pushforward `φ_#` descended). -/
noncomputable def relMapChain (n : ℕ) : RelativeChain A n →ₗ[ZMod 2] RelativeChain B n :=
  Submodule.mapQ _ _ (mapChain φ n) (fun c hc => mapChain_mem_subspaceChains φ hAB n c hc)

@[simp] theorem relMapChain_mk (n : ℕ) (c : SingularChain X n) :
    relMapChain φ hAB n (RelativeChain.mk A n c) = RelativeChain.mk B n (mapChain φ n c) :=
  Submodule.mapQ_apply _ _ _ _

/-- **`φ_#` is a relative chain map**: it commutes with the relative boundary. -/
theorem relMapChain_relBoundary (n : ℕ) (x : RelativeChain A (n + 1)) :
    relBoundary B n (relMapChain φ hAB (n + 1) x) = relMapChain φ hAB n (relBoundary A n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relBoundary B n (relMapChain φ hAB (n + 1) (RelativeChain.mk A (n + 1) c))
      = relMapChain φ hAB n (relBoundary A n (RelativeChain.mk A (n + 1) c))
  rw [relMapChain_mk, relBoundary_mk, relBoundary_mk, relMapChain_mk]
  exact congrArg (RelativeChain.mk B n) (chainBoundary_mapChain φ c)

/-- `φ_#` preserves relative cycles. -/
theorem relMapChain_mem_relCycles (n : ℕ) (z : RelativeChain A n) (hz : z ∈ relCycles A n) :
    relMapChain φ hAB n z ∈ relCycles B n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
      show relMapChain φ hAB (m + 1) z ∈ LinearMap.ker (relBoundary B m)
      rw [LinearMap.mem_ker, relMapChain_relBoundary]
      rw [show relBoundary A m z = 0 from hz, map_zero]

/-- `φ_#` preserves relative boundaries. -/
theorem relMapChain_mem_relBoundaries (n : ℕ) (z : RelativeChain A n) (hz : z ∈ relBoundaries A n) :
    relMapChain φ hAB n z ∈ relBoundaries B n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨relMapChain φ hAB (n + 1) w, relMapChain_relBoundary φ hAB n w⟩

/-- `φ_#` restricted to relative cycles. -/
noncomputable def relCyclesMap (n : ℕ) : relCycles A n →ₗ[ZMod 2] relCycles B n :=
  (relMapChain φ hAB n).restrict (fun z hz => relMapChain_mem_relCycles φ hAB n z hz)

@[simp] theorem relCyclesMap_coe (n : ℕ) (z : relCycles A n) :
    (relCyclesMap φ hAB n z : RelativeChain B n) = relMapChain φ hAB n (z : RelativeChain A n) := rfl

/-- **The induced map on relative homology** `Hₙ(X, A) → Hₙ(Y, B)`. -/
noncomputable def RelativeHomology.map (n : ℕ) :
    RelativeHomology A n →ₗ[ZMod 2] RelativeHomology B n :=
  Submodule.mapQ _ _ (relCyclesMap φ hAB n) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    exact relMapChain_mem_relBoundaries φ hAB n _ hzb)

@[simp] theorem RelativeHomology.map_mk (n : ℕ) (z : relCycles A n) :
    RelativeHomology.map φ hAB n (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk (relCyclesMap φ hAB n z) :=
  Submodule.mapQ_apply _ _ _ _

/-- `φ_#` on relative chains is functorial. -/
theorem relMapChain_comp {Z : TopCat} (ψ : C(↑Y, ↑Z)) {C : Set ↑Z} (hBC : Set.MapsTo ψ B C)
    (n : ℕ) (x : RelativeChain A n) :
    relMapChain (ψ.comp φ) (hBC.comp hAB) n x
      = relMapChain ψ hBC n (relMapChain φ hAB n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relMapChain (ψ.comp φ) (hBC.comp hAB) n (RelativeChain.mk A n c)
      = relMapChain ψ hBC n (relMapChain φ hAB n (RelativeChain.mk A n c))
  rw [relMapChain_mk (ψ.comp φ) (hBC.comp hAB), relMapChain_mk φ hAB, relMapChain_mk ψ hBC]
  exact congrArg (RelativeChain.mk C n) (mapChain_comp ψ φ n c)

theorem relMapChain_id {X : TopCat} {A : Set ↑X} (n : ℕ) (x : RelativeChain A n) :
    relMapChain (ContinuousMap.id ↑X) (Set.mapsTo_id A) n x = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relMapChain (ContinuousMap.id ↑X) (Set.mapsTo_id A) n (RelativeChain.mk A n c)
      = RelativeChain.mk A n c
  rw [relMapChain_mk (ContinuousMap.id ↑X) (Set.mapsTo_id A), mapChain_id]

/-- **Relative-homology functoriality** `Hₙ(ψ ∘ φ) = Hₙ(ψ) ∘ Hₙ(φ)`. -/
theorem RelativeHomology.map_comp {Z : TopCat} (ψ : C(↑Y, ↑Z)) {C : Set ↑Z}
    (hBC : Set.MapsTo ψ B C) (n : ℕ) :
    RelativeHomology.map (ψ.comp φ) (hBC.comp hAB) n
      = (RelativeHomology.map ψ hBC n).comp (RelativeHomology.map φ hAB n) := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelativeHomology.map_mk (ψ.comp φ) (hBC.comp hAB), LinearMap.comp_apply,
    RelativeHomology.map_mk φ hAB, RelativeHomology.map_mk ψ hBC]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (relMapChain_comp φ hAB ψ hBC n z))

/-- **Relative-homology functoriality** `Hₙ(id) = id`. -/
theorem RelativeHomology.map_id {X : TopCat} {A : Set ↑X} (n : ℕ) :
    RelativeHomology.map (ContinuousMap.id ↑X) (Set.mapsTo_id A) n = LinearMap.id := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelativeHomology.map_mk (ContinuousMap.id ↑X) (Set.mapsTo_id A), LinearMap.id_apply]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  rw [relCyclesMap_coe (ContinuousMap.id ↑X) (Set.mapsTo_id A)]
  exact relMapChain_id n (z : RelativeChain A n)

/-- Chain-level: if `q ∘ p = id`, the relative pushforward of `q` undoes that of `p`. -/
theorem relMapChain_eq_id_of_comp_id {P Q : TopCat} (p : C(↑P, ↑Q)) (q : C(↑Q, ↑P))
    {S : Set ↑P} {T : Set ↑Q} (hST : Set.MapsTo p S T) (hTS : Set.MapsTo q T S)
    (hqp : q.comp p = ContinuousMap.id ↑P) (m : ℕ) (x : RelativeChain S m) :
    relMapChain q hTS m (relMapChain p hST m x) = x := by
  refine (relMapChain_comp (φ := p) (hAB := hST) (ψ := q) (hBC := hTS) (n := m) x).symm.trans ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relMapChain (q.comp p) (hTS.comp hST) m (RelativeChain.mk S m c) = RelativeChain.mk S m c
  rw [relMapChain_mk (q.comp p) (hTS.comp hST), hqp, mapChain_id]

/-- Homology-level: if `g ∘ f = id`, then `Hₙ(g) ∘ Hₙ(f) = id`. -/
theorem relHomology_map_map_eq_id {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo f A B) (hBA : Set.MapsTo g B A)
    (hgf : g.comp f = ContinuousMap.id ↑X) (n : ℕ) (x : RelativeHomology A n) :
    RelativeHomology.map g hBA n (RelativeHomology.map f hAB n x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelativeHomology.map_mk, RelativeHomology.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [relCyclesMap_coe]
  exact relMapChain_eq_id_of_comp_id f g hAB hBA hgf n (z : RelativeChain A n)

/-- **A homeomorphism of pairs induces an isomorphism on relative homology** in EVERY degree —
the engine of the chart↔excision bridge `Hₙ(M, M∖x) ≅ Hₙ(ℝⁿ, ℝⁿ∖0)`. -/
theorem RelativeHomology.map_bijective_of_comp_id {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo f A B) (hBA : Set.MapsTo g B A)
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (RelativeHomology.map f hAB n) :=
  ⟨fun a b hab => by
      have := congrArg (RelativeHomology.map g hBA n) hab
      rwa [relHomology_map_map_eq_id f g hAB hBA hgf n a,
        relHomology_map_map_eq_id f g hAB hBA hgf n b] at this,
    fun y => ⟨RelativeHomology.map g hBA n y, relHomology_map_map_eq_id g f hBA hAB hfg n y⟩⟩

end SKEFTHawking.SingularRelativeFunctoriality
