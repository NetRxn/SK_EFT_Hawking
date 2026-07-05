import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularFunctorialityInt
import SKEFTHawking.SingularDisjointUnion

/-!
# Functoriality of integral relative homology (brick 14f, part A)

Signed mirror of `SingularRelativeFunctoriality` over ℤ. A **map of pairs** `φ : (X, A) → (Y, B)`
(continuous `φ : X → Y` with `φ(A) ⊆ B`) induces `Hₙ(X, A; ℤ) → Hₙ(Y, B; ℤ)`; a homeomorphism of
pairs induces an iso in every degree. The engine of the integral chart↔excision bridge
`H₄(M, M∖x; ℤ) ≅ H₄(ℝ⁴, ℝ⁴∖0; ℤ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularFunctoriality (mapSimplex)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularExcisionIsoInt (single_mem_subspaceChainsInt_of_subordinate)
open SKEFTHawking.SingularDisjointUnion (range_realize_simplexIncl)

namespace SKEFTHawking.SingularRelativeFunctorialityInt

/-- The realization of a pushforward simplex is `φ` post-composed with the realization. -/
theorem range_realize_mapSimplex {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    Set.range (Y.toSSetObjEquiv (op (SimplexCategory.mk n)) (mapSimplex φ σ))
      = φ '' Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) := by
  rw [mapSimplex, Equiv.apply_symm_apply, ← Set.range_comp]
  rfl

/-- **`φ_#` sends `A`-chains to `B`-chains** (integral) when `φ` maps `A` into `B`. -/
theorem mapChainInt_mem_subspaceChainsInt {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y}
    (hAB : Set.MapsTo φ A B) (n : ℕ) (c : SingularChainInt X n)
    (hc : c ∈ subspaceChainsInt A n) :
    mapChainInt φ n c ∈ subspaceChainsInt B n := by
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  | single σ' a =>
      rw [chainIncl_single, mapChainInt_single,
        show Finsupp.single (mapSimplex φ (simplexIncl A n σ')) a
          = a • Finsupp.single (mapSimplex φ (simplexIncl A n σ')) (1 : ℤ) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      refine (subspaceChainsInt B n).smul_mem a ?_
      apply single_mem_subspaceChainsInt_of_subordinate (A := B)
      rw [range_realize_mapSimplex]
      exact (Set.image_mono (range_realize_simplexIncl A σ')).trans hAB.image_subset

variable {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo φ A B)

/-- **The induced map on relative chains** `C(X, A;ℤ) → C(Y, B;ℤ)`. -/
noncomputable def relMapChainInt (n : ℕ) : RelativeChainInt A n →ₗ[ℤ] RelativeChainInt B n :=
  Submodule.mapQ _ _ (mapChainInt φ n) (fun c hc => mapChainInt_mem_subspaceChainsInt φ hAB n c hc)

@[simp] theorem relMapChainInt_mk (n : ℕ) (c : SingularChainInt X n) :
    relMapChainInt φ hAB n (RelativeChainInt.mk A n c) = RelativeChainInt.mk B n (mapChainInt φ n c) :=
  Submodule.mapQ_apply _ _ _ _

/-- **`φ_#` is a relative chain map** (integral). -/
theorem relMapChainInt_relBoundaryInt (n : ℕ) (x : RelativeChainInt A (n + 1)) :
    relBoundaryInt B n (relMapChainInt φ hAB (n + 1) x) = relMapChainInt φ hAB n (relBoundaryInt A n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relBoundaryInt B n (relMapChainInt φ hAB (n + 1) (RelativeChainInt.mk A (n + 1) c))
      = relMapChainInt φ hAB n (relBoundaryInt A n (RelativeChainInt.mk A (n + 1) c))
  rw [relMapChainInt_mk, relBoundaryInt_mk, relBoundaryInt_mk, relMapChainInt_mk]
  exact congrArg (RelativeChainInt.mk B n) (chainBoundary_mapChainInt φ c)

/-- `φ_#` preserves relative cycles. -/
theorem relMapChainInt_mem_relCyclesInt (n : ℕ) (z : RelativeChainInt A n) (hz : z ∈ relCyclesInt A n) :
    relMapChainInt φ hAB n z ∈ relCyclesInt B n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
      show relMapChainInt φ hAB (m + 1) z ∈ LinearMap.ker (relBoundaryInt B m)
      rw [LinearMap.mem_ker, relMapChainInt_relBoundaryInt]
      rw [show relBoundaryInt A m z = 0 from hz, map_zero]

/-- `φ_#` preserves relative boundaries. -/
theorem relMapChainInt_mem_relBoundariesInt (n : ℕ) (z : RelativeChainInt A n)
    (hz : z ∈ relBoundariesInt A n) : relMapChainInt φ hAB n z ∈ relBoundariesInt B n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨relMapChainInt φ hAB (n + 1) w, relMapChainInt_relBoundaryInt φ hAB n w⟩

/-- `φ_#` restricted to relative cycles. -/
noncomputable def relCyclesMapInt (n : ℕ) : relCyclesInt A n →ₗ[ℤ] relCyclesInt B n :=
  (relMapChainInt φ hAB n).restrict (fun z hz => relMapChainInt_mem_relCyclesInt φ hAB n z hz)

@[simp] theorem relCyclesMapInt_coe (n : ℕ) (z : relCyclesInt A n) :
    (relCyclesMapInt φ hAB n z : RelativeChainInt B n) = relMapChainInt φ hAB n (z : RelativeChainInt A n) := rfl

/-- **The induced map on relative homology** `Hₙ(X, A;ℤ) → Hₙ(Y, B;ℤ)`. -/
noncomputable def RelHomologyInt.map (n : ℕ) :
    RelHomologyInt A n →ₗ[ℤ] RelHomologyInt B n :=
  Submodule.mapQ _ _ (relCyclesMapInt φ hAB n) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    exact relMapChainInt_mem_relBoundariesInt φ hAB n _ hzb)

@[simp] theorem RelHomologyInt.map_mk (n : ℕ) (z : relCyclesInt A n) :
    RelHomologyInt.map φ hAB n (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk (relCyclesMapInt φ hAB n z) :=
  Submodule.mapQ_apply _ _ _ _

/-- `φ_#` on relative chains is functorial. -/
theorem relMapChainInt_comp {Z : TopCat} (ψ : C(↑Y, ↑Z)) {C : Set ↑Z} (hBC : Set.MapsTo ψ B C)
    (n : ℕ) (x : RelativeChainInt A n) :
    relMapChainInt (ψ.comp φ) (hBC.comp hAB) n x
      = relMapChainInt ψ hBC n (relMapChainInt φ hAB n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relMapChainInt (ψ.comp φ) (hBC.comp hAB) n (RelativeChainInt.mk A n c)
      = relMapChainInt ψ hBC n (relMapChainInt φ hAB n (RelativeChainInt.mk A n c))
  rw [relMapChainInt_mk (ψ.comp φ) (hBC.comp hAB), relMapChainInt_mk φ hAB, relMapChainInt_mk ψ hBC]
  exact congrArg (RelativeChainInt.mk C n) (mapChainInt_comp ψ φ n c)

theorem relMapChainInt_id {X : TopCat} {A : Set ↑X} (n : ℕ) (x : RelativeChainInt A n) :
    relMapChainInt (ContinuousMap.id ↑X) (Set.mapsTo_id A) n x = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relMapChainInt (ContinuousMap.id ↑X) (Set.mapsTo_id A) n (RelativeChainInt.mk A n c)
      = RelativeChainInt.mk A n c
  rw [relMapChainInt_mk (ContinuousMap.id ↑X) (Set.mapsTo_id A), mapChainInt_id]

/-- Chain-level: if `q ∘ p = id`, the relative pushforward of `q` undoes that of `p`. -/
theorem relMapChainInt_eq_id_of_comp_id {P Q : TopCat} (p : C(↑P, ↑Q)) (q : C(↑Q, ↑P))
    {S : Set ↑P} {T : Set ↑Q} (hST : Set.MapsTo p S T) (hTS : Set.MapsTo q T S)
    (hqp : q.comp p = ContinuousMap.id ↑P) (m : ℕ) (x : RelativeChainInt S m) :
    relMapChainInt q hTS m (relMapChainInt p hST m x) = x := by
  refine (relMapChainInt_comp (φ := p) (hAB := hST) (ψ := q) (hBC := hTS) (n := m) x).symm.trans ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relMapChainInt (q.comp p) (hTS.comp hST) m (RelativeChainInt.mk S m c) = RelativeChainInt.mk S m c
  rw [relMapChainInt_mk (q.comp p) (hTS.comp hST), hqp, mapChainInt_id]

/-- Homology-level: if `g ∘ f = id`, then `Hₙ(g) ∘ Hₙ(f) = id`. -/
theorem relHomologyInt_map_map_eq_id {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo f A B) (hBA : Set.MapsTo g B A)
    (hgf : g.comp f = ContinuousMap.id ↑X) (n : ℕ) (x : RelHomologyInt A n) :
    RelHomologyInt.map g hBA n (RelHomologyInt.map f hAB n x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelHomologyInt.map_mk, RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [relCyclesMapInt_coe]
  exact relMapChainInt_eq_id_of_comp_id f g hAB hBA hgf n (z : RelativeChainInt A n)

/-- **A homeomorphism of pairs induces an iso on integral relative homology in every degree.** -/
theorem RelHomologyInt.map_bijective_of_comp_id {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo f A B) (hBA : Set.MapsTo g B A)
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (RelHomologyInt.map f hAB n) :=
  ⟨fun a b hab => by
      have := congrArg (RelHomologyInt.map g hBA n) hab
      rwa [relHomologyInt_map_map_eq_id f g hAB hBA hgf n a,
        relHomologyInt_map_map_eq_id f g hAB hBA hgf n b] at this,
    fun y => ⟨RelHomologyInt.map g hBA n y, relHomologyInt_map_map_eq_id g f hBA hAB hfg n y⟩⟩

end SKEFTHawking.SingularRelativeFunctorialityInt
