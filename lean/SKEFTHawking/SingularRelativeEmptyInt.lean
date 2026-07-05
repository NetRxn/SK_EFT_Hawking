import Mathlib
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularRelativeEmpty

/-!
# Integral relative homology rel the empty subspace (brick 18d)

`RelHomologyInt (∅ : Set X) n ≃ₗ[ℤ] Homology X n`: integral relative singular homology of `X` relative
to the EMPTY subspace equals absolute homology. The bridge `Hᵢ(M | M) = RelHomologyInt (Mᶜ = ∅) i ≅
Hᵢ(M;ℤ)` from the relative `Hₙ(M|·;ℤ)` framework to absolute `Hₙ(M;ℤ)` — the transport that carries the
oriented fundamental class produced by the univ chart-cover induction (`hasOrientedFundClassInt univ`,
whose witness lives in `Hₙ(M | univ) = Hₙ(M, ∅)`) into `Homology M`, i.e. the `[M]` field of
`IntOrientationData`. The ℤ mirror of `SingularRelativeEmpty.relHomologyEmptyEquiv`.

Mechanism (identical to mod-2, over ℤ): `sub ∅` is empty ⟹ no integral chains ⟹
`subspaceChainsInt ∅ n = ⊥` ⟹ `RelativeChainInt ∅ n = SingularChainInt X n ⧸ ⊥ ≃ SingularChainInt X n`
(`Submodule.quotEquivOfEqBot`); under this the relative boundary/cycles/boundaries match the absolute
ones, so the subquotients are ℤ-linearly equivalent. The empty-subspace facts (`isEmpty_subEmpty`,
`isEmpty_emptySimplex`) are coefficient-free and reused from the mod-2 development.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularRelativeEmptyInt

variable {X : TopCat}

/-! ## §1. The empty subspace has no integral chains: `subspaceChainsInt ∅ n = ⊥` -/

/-- The integral singular chains of the empty subspace are the zero module (the free ℤ-module on the
empty simplex type — `SingularRelativeEmpty.isEmpty_emptySimplex`). -/
theorem singularChainInt_empty_subsingleton (n : ℕ) :
    Subsingleton (SingularChainInt (sub (∅ : Set X)) n) := by
  haveI := SKEFTHawking.SingularRelativeEmpty.isEmpty_emptySimplex (X := X) n
  infer_instance

/-- **Key fact**: `subspaceChainsInt (∅ : Set X) n = ⊥`. -/
theorem subspaceChainsInt_empty_eq_bot (n : ℕ) :
    subspaceChainsInt (∅ : Set X) n = ⊥ := by
  haveI := singularChainInt_empty_subsingleton (X := X) n
  rw [subspaceChainsInt, Submodule.eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y 0, map_zero]

/-! ## §2. `RelativeChainInt ∅ n ≃ₗ SingularChainInt X n` and the boundary intertwiner -/

/-- The integral relative chains rel the empty subspace are the absolute chains: `C_n(X, ∅; ℤ) ≃
C_n(X; ℤ)`, the quotient by the zero submodule. -/
noncomputable def chainEmptyEquivInt (n : ℕ) :
    RelativeChainInt (∅ : Set X) n ≃ₗ[ℤ] SingularChainInt X n :=
  Submodule.quotEquivOfEqBot (subspaceChainsInt (∅ : Set X) n) (subspaceChainsInt_empty_eq_bot n)

@[simp] theorem chainEmptyEquivInt_mk (n : ℕ) (c : SingularChainInt X n) :
    chainEmptyEquivInt n (RelativeChainInt.mk (∅ : Set X) n c) = c :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ c

/-- The boundary intertwiner: `chainEmptyEquivInt` carries the relative boundary to the absolute
boundary, `e ∘ ∂_rel = ∂ ∘ e`. -/
theorem chainEmptyEquivInt_relBoundaryInt (n : ℕ) (c : RelativeChainInt (∅ : Set X) (n + 1)) :
    chainEmptyEquivInt n (relBoundaryInt (∅ : Set X) n c)
      = chainBoundary X n (chainEmptyEquivInt (n + 1) c) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [show Submodule.Quotient.mk c = RelativeChainInt.mk (∅ : Set X) (n + 1) c from rfl,
    relBoundaryInt_mk, chainEmptyEquivInt_mk, chainEmptyEquivInt_mk]

/-! ## §3. Cycles and boundaries correspond; the homology equivalence -/

/-- `chainEmptyEquivInt` carries the relative cycles onto the absolute cycles. -/
theorem map_chainEmptyEquivInt_relCyclesInt (n : ℕ) :
    Submodule.map (chainEmptyEquivInt (X := X) n).toLinearMap (relCyclesInt (∅ : Set X) n)
      = cycles X n := by
  cases n with
  | zero =>
    rw [relCyclesInt, cycles, Submodule.map_top,
      LinearMap.range_eq_top.mpr (chainEmptyEquivInt 0).surjective]
  | succ m =>
    show Submodule.map (chainEmptyEquivInt (X := X) (m + 1)).toLinearMap
        (LinearMap.ker (relBoundaryInt (∅ : Set X) m))
      = LinearMap.ker (chainBoundary X m)
    ext c
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← chainEmptyEquivInt_relBoundaryInt, hz, map_zero]
    · intro hc
      refine ⟨(chainEmptyEquivInt (m + 1)).symm c, ?_, by simp⟩
      apply (chainEmptyEquivInt m).injective
      rw [chainEmptyEquivInt_relBoundaryInt, map_zero, LinearEquiv.apply_symm_apply, hc]

/-- `chainEmptyEquivInt` carries the relative boundaries onto the absolute boundaries. -/
theorem map_chainEmptyEquivInt_relBoundariesInt (n : ℕ) :
    Submodule.map (chainEmptyEquivInt (X := X) n).toLinearMap (relBoundariesInt (∅ : Set X) n)
      = boundaries X n := by
  ext c
  simp only [relBoundariesInt, boundaries, Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨chainEmptyEquivInt (n + 1) d, (chainEmptyEquivInt_relBoundaryInt n d).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨relBoundaryInt (∅ : Set X) n ((chainEmptyEquivInt (n + 1)).symm d),
      ⟨(chainEmptyEquivInt (n + 1)).symm d, rfl⟩,
      by rw [chainEmptyEquivInt_relBoundaryInt, LinearEquiv.apply_symm_apply]⟩

/-- The restriction of `chainEmptyEquivInt` to the cycles: `relCyclesInt ∅ n ≃ₗ cycles X n`. -/
noncomputable def cyclesEmptyEquivInt (n : ℕ) :
    relCyclesInt (∅ : Set X) n ≃ₗ[ℤ] cycles X n :=
  ((chainEmptyEquivInt (X := X) n).submoduleMap (relCyclesInt (∅ : Set X) n)).trans
    (LinearEquiv.ofEq _ _ (map_chainEmptyEquivInt_relCyclesInt n))

theorem cyclesEmptyEquivInt_coe (n : ℕ) (z : relCyclesInt (∅ : Set X) n) :
    (cyclesEmptyEquivInt n z : SingularChainInt X n)
      = chainEmptyEquivInt n (z : RelativeChainInt (∅ : Set X) n) :=
  rfl

/-- **`RelHomologyInt (∅ : Set X) n ≃ₗ[ℤ] Homology X n`** — integral relative homology rel the empty
subspace equals absolute homology. The bridge `Hᵢ(M | M) ≅ Hᵢ(M;ℤ)` carrying the univ fundamental-class
witness into `Homology M`. The ℤ mirror of `SingularRelativeEmpty.relHomologyEmptyEquiv`. -/
noncomputable def relHomologyEmptyEquivInt (n : ℕ) :
    RelHomologyInt (∅ : Set X) n ≃ₗ[ℤ] Homology X n :=
  Submodule.Quotient.equiv
    ((relBoundariesInt (∅ : Set X) n).submoduleOf (relCyclesInt (∅ : Set X) n))
    ((boundaries X n).submoduleOf (cycles X n))
    (cyclesEmptyEquivInt n)
    (by
      ext z
      simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.coe_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩
        show chainEmptyEquivInt n (w : RelativeChainInt (∅ : Set X) n) ∈ boundaries X n
        have hmap : chainEmptyEquivInt n (w : RelativeChainInt (∅ : Set X) n)
            ∈ Submodule.map (chainEmptyEquivInt (X := X) n).toLinearMap
                (relBoundariesInt (∅ : Set X) n) :=
          ⟨_, hw, rfl⟩
        rwa [map_chainEmptyEquivInt_relBoundariesInt] at hmap
      · intro hz
        refine ⟨(cyclesEmptyEquivInt n).symm z, ?_, by simp⟩
        show ((cyclesEmptyEquivInt n).symm z : RelativeChainInt (∅ : Set X) n)
          ∈ relBoundariesInt (∅ : Set X) n
        have hzc : (z : SingularChainInt X n) ∈ boundaries X n := hz
        rw [← map_chainEmptyEquivInt_relBoundariesInt] at hzc
        obtain ⟨w, hw, hwz⟩ := hzc
        have heq : ((cyclesEmptyEquivInt n).symm z : RelativeChainInt (∅ : Set X) n) = w := by
          apply (chainEmptyEquivInt n).injective
          show chainEmptyEquivInt n ((cyclesEmptyEquivInt n).symm z : RelativeChainInt (∅ : Set X) n)
            = chainEmptyEquivInt n w
          have h1 : (chainEmptyEquivInt n) w = (z : SingularChainInt X n) := hwz
          rw [h1]
          exact congrArg Subtype.val (LinearEquiv.apply_symm_apply (cyclesEmptyEquivInt n) z)
        rw [heq]; exact hw)

/-- The computation rule: `relHomologyEmptyEquivInt` sends the relative class of a relative cycle `z`
to the absolute class of the corresponding absolute cycle `cyclesEmptyEquivInt n z`. -/
theorem relHomologyEmptyEquivInt_mk (n : ℕ) (z : relCyclesInt (∅ : Set X) n) :
    relHomologyEmptyEquivInt n (RelHomologyInt.mk (∅ : Set X) n z)
      = Homology.mk X n (cyclesEmptyEquivInt n z) :=
  rfl

end SKEFTHawking.SingularRelativeEmptyInt
