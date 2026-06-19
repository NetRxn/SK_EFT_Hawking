import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.SingularRelativeEmpty

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-empty) — relative cohomology rel the empty subspace

`RelativeCohomology (∅ : Set X) n ≅ Cohomology X n`: relative singular ℤ/2 cohomology rel the EMPTY
subspace equals absolute cohomology. The cohomology dual of `SingularRelativeEmpty.relHomologyEmptyEquiv`,
and the bridge `Hⁱ(M | M) = RelativeCohomology (Mᶜ = ∅) i ≅ Hⁱ(M)` — at `K = univ` the relative
Poincaré-duality map `D_K` over `M∖K = ∅` becomes the absolute `capH · [M]`.

The mechanism dual to the homology case: `subspaceChains ∅ n = ⊥` (`SingularRelativeEmpty`), so a cochain
vanishing on `subspaceChains ∅ n` vanishes on `⊥` — i.e. **every** cochain is a relative `∅`-cochain,
`relCochains ∅ n = ⊤`. Then `relCochains ∅ n ≃ SingularCochain X n`, under which `relCoboundaryₗ ↔
coboundaryₗ` (`relCoboundaryₗ_coe`), so the cocycles/coboundaries correspond and the cohomology
subquotients are linearly equivalent.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeEmpty

namespace SKEFTHawking.SingularRelativeCohomologyEmpty

variable {X : TopCat}

/-! ## §1. Every cochain is a relative `∅`-cochain: `relCochains ∅ n = ⊤` -/

/-- **Key fact**: `relCochains (∅ : Set X) n = ⊤` — every cochain vanishes on `subspaceChains ∅ n = ⊥`. -/
theorem relCochains_empty_eq_top (n : ℕ) : relCochains (∅ : Set X) n = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f c hc
  rw [subspaceChains_empty_eq_bot, Submodule.mem_bot] at hc
  subst hc
  exact map_zero (kroneckerₗ n f)

/-- The relative cochains rel the empty subspace are the absolute cochains: `Cⁿ(X, ∅) ≃ Cⁿ(X)`. -/
noncomputable def cochainEmptyEquiv (n : ℕ) :
    relCochains (∅ : Set X) n ≃ₗ[ZMod 2] SingularCochain X n :=
  (LinearEquiv.ofEq _ _ (relCochains_empty_eq_top n)).trans Submodule.topEquiv

@[simp] theorem cochainEmptyEquiv_apply (n : ℕ) (f : relCochains (∅ : Set X) n) :
    cochainEmptyEquiv n f = (f : SingularCochain X n) :=
  rfl

/-- The coboundary intertwiner: `cochainEmptyEquiv` carries the relative coboundary to the absolute
coboundary, `e ∘ δ_rel = δ ∘ e` (both restrict the absolute `coboundaryₗ`, `relCoboundaryₗ_coe`). -/
theorem cochainEmptyEquiv_relCoboundary (n : ℕ) (f : relCochains (∅ : Set X) n) :
    cochainEmptyEquiv (n + 1) (relCoboundaryₗ (∅ : Set X) n f)
      = coboundaryₗ X n (cochainEmptyEquiv n f) := by
  rw [cochainEmptyEquiv_apply, cochainEmptyEquiv_apply, relCoboundaryₗ_coe]
  rfl

/-! ## §2. Cocycles and coboundaries correspond; the cohomology equivalence -/

/-- `cochainEmptyEquiv` carries the relative cocycles onto the absolute cocycles. -/
theorem map_cochainEmptyEquiv_ker (n : ℕ) :
    Submodule.map (cochainEmptyEquiv (X := X) n).toLinearMap (LinearMap.ker (relCoboundaryₗ (∅ : Set X) n))
      = LinearMap.ker (coboundaryₗ X n) := by
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← cochainEmptyEquiv_relCoboundary, hg, map_zero]
  · intro hf
    refine ⟨(cochainEmptyEquiv n).symm f, ?_, by simp⟩
    apply (cochainEmptyEquiv (n + 1)).injective
    rw [cochainEmptyEquiv_relCoboundary, map_zero, LinearEquiv.apply_symm_apply, hf]

/-- `cochainEmptyEquiv` carries the relative coboundary range onto the absolute coboundary range. -/
theorem map_cochainEmptyEquiv_coboundaryRange (n : ℕ) :
    Submodule.map (cochainEmptyEquiv (X := X) n).toLinearMap (relCoboundaryRange (∅ : Set X) n)
      = coboundaryRange X n := by
  cases n with
  | zero =>
    rw [show relCoboundaryRange (∅ : Set X) 0 = (⊥ : Submodule (ZMod 2) (relCochains (∅ : Set X) 0)) from rfl,
      show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) (SingularCochain X 0)) from rfl,
      Submodule.map_bot]
  | succ m =>
    ext f
    simp only [show relCoboundaryRange (∅ : Set X) (m + 1) = LinearMap.range (relCoboundaryₗ (∅ : Set X) m)
        from rfl,
      show coboundaryRange X (m + 1) = LinearMap.range (coboundaryₗ X m) from rfl,
      Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨cochainEmptyEquiv m g, (cochainEmptyEquiv_relCoboundary m g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨relCoboundaryₗ (∅ : Set X) m ((cochainEmptyEquiv m).symm g),
        ⟨(cochainEmptyEquiv m).symm g, rfl⟩,
        by rw [cochainEmptyEquiv_relCoboundary, LinearEquiv.apply_symm_apply]⟩

/-- The restriction of `cochainEmptyEquiv` to the cocycles: `ker (relCoboundaryₗ ∅ n) ≃ₗ ker (coboundaryₗ X n)`. -/
noncomputable def cocyclesEmptyEquiv (n : ℕ) :
    LinearMap.ker (relCoboundaryₗ (∅ : Set X) n) ≃ₗ[ZMod 2] LinearMap.ker (coboundaryₗ X n) :=
  ((cochainEmptyEquiv (X := X) n).submoduleMap (LinearMap.ker (relCoboundaryₗ (∅ : Set X) n))).trans
    (LinearEquiv.ofEq _ _ (map_cochainEmptyEquiv_ker n))

theorem cocyclesEmptyEquiv_coe (n : ℕ) (z : LinearMap.ker (relCoboundaryₗ (∅ : Set X) n)) :
    (cocyclesEmptyEquiv n z : SingularCochain X n)
      = cochainEmptyEquiv n (z : relCochains (∅ : Set X) n) :=
  rfl

/-- **`RelativeCohomology (∅ : Set X) n ≃ₗ Cohomology X n`** — relative singular ℤ/2 cohomology rel the
empty subspace equals absolute cohomology. The cohomology dual of `relHomologyEmptyEquiv`; the bridge
`Hⁱ(M | M) ≅ Hⁱ(M)` under which `D_univ` becomes `capH · [M]`. -/
noncomputable def relCohomologyEmptyEquiv (n : ℕ) :
    RelativeCohomology (∅ : Set X) n ≃ₗ[ZMod 2] Cohomology X n :=
  Submodule.Quotient.equiv
    ((relCoboundaryRange (∅ : Set X) n).submoduleOf (LinearMap.ker (relCoboundaryₗ (∅ : Set X) n)))
    ((coboundaryRange X n).submoduleOf (LinearMap.ker (coboundaryₗ X n)))
    (cocyclesEmptyEquiv n)
    (by
      ext z
      simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.coe_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩
        show cochainEmptyEquiv n (w : relCochains (∅ : Set X) n) ∈ coboundaryRange X n
        have hmap : cochainEmptyEquiv n (w : relCochains (∅ : Set X) n)
            ∈ Submodule.map (cochainEmptyEquiv (X := X) n).toLinearMap (relCoboundaryRange (∅ : Set X) n) :=
          ⟨_, hw, rfl⟩
        rwa [map_cochainEmptyEquiv_coboundaryRange] at hmap
      · intro hz
        refine ⟨(cocyclesEmptyEquiv n).symm z, ?_, by simp⟩
        show ((cocyclesEmptyEquiv n).symm z : relCochains (∅ : Set X) n) ∈ relCoboundaryRange (∅ : Set X) n
        have hzc : (z : SingularCochain X n) ∈ coboundaryRange X n := hz
        rw [← map_cochainEmptyEquiv_coboundaryRange] at hzc
        obtain ⟨w, hw, hwz⟩ := hzc
        have heq : ((cocyclesEmptyEquiv n).symm z : relCochains (∅ : Set X) n) = w := by
          apply (cochainEmptyEquiv n).injective
          show cochainEmptyEquiv n ((cocyclesEmptyEquiv n).symm z : relCochains (∅ : Set X) n)
            = cochainEmptyEquiv n w
          have h1 : (cochainEmptyEquiv n) w = (z : SingularCochain X n) := hwz
          rw [h1]
          exact congrArg Subtype.val (LinearEquiv.apply_symm_apply (cocyclesEmptyEquiv n) z)
        rw [heq]; exact hw)

/-- The computation rule: `relCohomologyEmptyEquiv` sends the relative class of a relative cocycle `z`
to the absolute class of the corresponding absolute cocycle `cocyclesEmptyEquiv n z`. -/
theorem relCohomologyEmptyEquiv_mk (n : ℕ) (z : LinearMap.ker (relCoboundaryₗ (∅ : Set X) n)) :
    relCohomologyEmptyEquiv n (RelativeCohomology.mk (∅ : Set X) n z)
      = Cohomology.mk X n (cocyclesEmptyEquiv n z) :=
  rfl

end SKEFTHawking.SingularRelativeCohomologyEmpty
