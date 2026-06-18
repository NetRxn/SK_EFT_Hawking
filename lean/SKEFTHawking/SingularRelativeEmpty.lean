/-
# Phase 5q.F (w₂-foundation, brick 72c-3w) — relative homology rel the empty subspace

`RelativeHomology (∅ : Set X) n ≅ Homology X n`: relative singular ℤ/2 homology of `X` relative to
the EMPTY subspace equals absolute homology. This is the bridge `Hᵢ(M | M) = RelativeHomology (Mᶜ = ∅) i
≅ Hᵢ(M)` from the relative `Hₙ(M|·)` framework to absolute `Hₙ(M)` (needed for the fundamental class).

The mechanism: `sub ∅ = ↥(∅ : Set X)` is an empty topological space, so it has no singular `n`-simplices,
so `SingularChain (sub ∅) n` is the zero module, so `subspaceChains ∅ n = range (chainIncl ∅ n) = ⊥`.
Then `RelativeChain ∅ n = SingularChain X n ⧸ ⊥ ≃ SingularChain X n` (`Submodule.quotEquivOfEqBot`), and
under this equivalence `relBoundary ↔ chainBoundary`, `relCycles ↔ cycles`, `relBoundaries ↔ boundaries`,
so the subquotients `RelativeHomology ∅ n` and `Homology X n` are linearly equivalent.

Kernel-pure (`{propext, Classical.choice, Quot.sound}` only).
-/
import Mathlib
import SKEFTHawking.SingularHomologyMod2
import SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularRelativeEmpty

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2

variable {X : TopCat}

/-! ## §1. The empty subspace has no chains: `subspaceChains ∅ n = ⊥` -/

/-- The codomain `sub (∅ : Set X)` is an empty space. -/
instance isEmpty_subEmpty : IsEmpty ↥(sub (∅ : Set X)) :=
  Set.isEmpty_coe_sort.mpr rfl

/-- The standard `n`-simplex maps into `sub (∅ : Set X)` — but there are none: `sub ∅` is empty. -/
instance isEmpty_emptySimplex (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (sub (∅ : Set X))).obj (op (SimplexCategory.mk n))) := by
  constructor
  rintro ⟨f⟩
  obtain ⟨x⟩ : Nonempty ↑(SimplexCategory.toTop.obj (SimplexCategory.mk n)) := inferInstance
  exact (isEmpty_subEmpty (X := X)).false (f.hom x)

/-- The singular chains of the empty subspace are the zero module. -/
theorem singularChain_empty_subsingleton (n : ℕ) :
    Subsingleton (SingularChain (sub (∅ : Set X)) n) :=
  inferInstance

/-- **Key fact**: `subspaceChains (∅ : Set X) n = ⊥`. -/
theorem subspaceChains_empty_eq_bot (n : ℕ) :
    subspaceChains (∅ : Set X) n = ⊥ := by
  haveI := singularChain_empty_subsingleton (X := X) n
  rw [subspaceChains, Submodule.eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y 0, map_zero]

/-! ## §2. `RelativeChain ∅ n ≃ₗ SingularChain X n` and the boundary intertwiner -/

/-- The relative chains rel the empty subspace are the absolute chains: `C_n(X, ∅) ≃ C_n(X)`, the
quotient by the zero submodule. -/
noncomputable def chainEmptyEquiv (n : ℕ) :
    RelativeChain (∅ : Set X) n ≃ₗ[ZMod 2] SingularChain X n :=
  Submodule.quotEquivOfEqBot (subspaceChains (∅ : Set X) n) (subspaceChains_empty_eq_bot n)

@[simp] theorem chainEmptyEquiv_mk (n : ℕ) (c : SingularChain X n) :
    chainEmptyEquiv n (RelativeChain.mk (∅ : Set X) n c) = c :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ c

/-- The boundary intertwiner: `chainEmptyEquiv` carries the relative boundary to the absolute
boundary, `e ∘ ∂_rel = ∂ ∘ e`. -/
theorem chainEmptyEquiv_relBoundary (n : ℕ) (c : RelativeChain (∅ : Set X) (n + 1)) :
    chainEmptyEquiv n (relBoundary (∅ : Set X) n c)
      = chainBoundary X n (chainEmptyEquiv (n + 1) c) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [show Submodule.Quotient.mk c = RelativeChain.mk (∅ : Set X) (n + 1) c from rfl,
    relBoundary_mk, chainEmptyEquiv_mk, chainEmptyEquiv_mk]

/-! ## §3. Cycles and boundaries correspond; the homology equivalence -/

/-- `chainEmptyEquiv` carries the relative cycles onto the absolute cycles. -/
theorem map_chainEmptyEquiv_relCycles (n : ℕ) :
    Submodule.map (chainEmptyEquiv (X := X) n).toLinearMap (relCycles (∅ : Set X) n) = cycles X n := by
  cases n with
  | zero =>
    rw [relCycles, cycles, Submodule.map_top,
      LinearMap.range_eq_top.mpr (chainEmptyEquiv 0).surjective]
  | succ m =>
    show Submodule.map (chainEmptyEquiv (X := X) (m + 1)).toLinearMap
        (LinearMap.ker (relBoundary (∅ : Set X) m))
      = LinearMap.ker (chainBoundary X m)
    ext c
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← chainEmptyEquiv_relBoundary, hz, map_zero]
    · intro hc
      refine ⟨(chainEmptyEquiv (m + 1)).symm c, ?_, by simp⟩
      apply (chainEmptyEquiv m).injective
      rw [chainEmptyEquiv_relBoundary, map_zero, LinearEquiv.apply_symm_apply, hc]

/-- `chainEmptyEquiv` carries the relative boundaries onto the absolute boundaries. -/
theorem map_chainEmptyEquiv_relBoundaries (n : ℕ) :
    Submodule.map (chainEmptyEquiv (X := X) n).toLinearMap (relBoundaries (∅ : Set X) n)
      = boundaries X n := by
  ext c
  simp only [relBoundaries, boundaries, Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨chainEmptyEquiv (n + 1) d, (chainEmptyEquiv_relBoundary n d).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨relBoundary (∅ : Set X) n ((chainEmptyEquiv (n + 1)).symm d),
      ⟨(chainEmptyEquiv (n + 1)).symm d, rfl⟩,
      by rw [chainEmptyEquiv_relBoundary, LinearEquiv.apply_symm_apply]⟩

/-- The restriction of `chainEmptyEquiv` to the cycles: `relCycles ∅ n ≃ₗ cycles X n`. -/
noncomputable def cyclesEmptyEquiv (n : ℕ) :
    relCycles (∅ : Set X) n ≃ₗ[ZMod 2] cycles X n :=
  ((chainEmptyEquiv (X := X) n).submoduleMap (relCycles (∅ : Set X) n)).trans
    (LinearEquiv.ofEq _ _ (map_chainEmptyEquiv_relCycles n))

theorem cyclesEmptyEquiv_coe (n : ℕ) (z : relCycles (∅ : Set X) n) :
    (cyclesEmptyEquiv n z : SingularChain X n)
      = chainEmptyEquiv n (z : RelativeChain (∅ : Set X) n) :=
  rfl

/-- **`RelativeHomology (∅ : Set X) n ≃ₗ Homology X n`** — relative singular ℤ/2 homology rel the
empty subspace equals absolute homology. The bridge `Hᵢ(M | M) = RelativeHomology (Mᶜ = ∅) i ≅ Hᵢ(M)`,
from the relative `Hₙ(M|·)` framework to absolute `Hₙ(M)` for the fundamental class. -/
noncomputable def relHomologyEmptyEquiv (n : ℕ) :
    RelativeHomology (∅ : Set X) n ≃ₗ[ZMod 2] Homology X n :=
  Submodule.Quotient.equiv
    ((relBoundaries (∅ : Set X) n).submoduleOf (relCycles (∅ : Set X) n))
    ((boundaries X n).submoduleOf (cycles X n))
    (cyclesEmptyEquiv n)
    (by
      ext z
      simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.coe_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩
        show chainEmptyEquiv n (w : RelativeChain (∅ : Set X) n) ∈ boundaries X n
        have hmap : chainEmptyEquiv n (w : RelativeChain (∅ : Set X) n)
            ∈ Submodule.map (chainEmptyEquiv (X := X) n).toLinearMap (relBoundaries (∅ : Set X) n) :=
          ⟨_, hw, rfl⟩
        rwa [map_chainEmptyEquiv_relBoundaries] at hmap
      · intro hz
        refine ⟨(cyclesEmptyEquiv n).symm z, ?_, by simp⟩
        show ((cyclesEmptyEquiv n).symm z : RelativeChain (∅ : Set X) n) ∈ relBoundaries (∅ : Set X) n
        have hzc : (z : SingularChain X n) ∈ boundaries X n := hz
        rw [← map_chainEmptyEquiv_relBoundaries] at hzc
        obtain ⟨w, hw, hwz⟩ := hzc
        have heq : ((cyclesEmptyEquiv n).symm z : RelativeChain (∅ : Set X) n) = w := by
          apply (chainEmptyEquiv n).injective
          show chainEmptyEquiv n ((cyclesEmptyEquiv n).symm z : RelativeChain (∅ : Set X) n)
            = chainEmptyEquiv n w
          have h1 : (chainEmptyEquiv n) w = (z : SingularChain X n) := hwz
          rw [h1]
          exact congrArg Subtype.val (LinearEquiv.apply_symm_apply (cyclesEmptyEquiv n) z)
        rw [heq]; exact hw)

/-- The computation rule: `relHomologyEmptyEquiv` sends the relative class of a relative cycle `z` to
the absolute class of the corresponding absolute cycle `cyclesEmptyEquiv n z`. -/
theorem relHomologyEmptyEquiv_mk (n : ℕ) (z : relCycles (∅ : Set X) n) :
    relHomologyEmptyEquiv n (RelativeHomology.mk (∅ : Set X) n z)
      = Homology.mk X n (cyclesEmptyEquiv n z) :=
  rfl

end SKEFTHawking.SingularRelativeEmpty
