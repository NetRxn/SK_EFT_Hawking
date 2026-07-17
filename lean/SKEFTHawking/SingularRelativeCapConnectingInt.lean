import Mathlib
import SKEFTHawking.SingularRelativeCapHomologyInt
import SKEFTHawking.SingularPullbackDualityCapSubInt

/-!
# Phase 5q.H close-out — the **cap–boundary naturality** `∂(a ⌢ [W,∂W]) = (-1)ᵏ · (ι*a ⌢ [∂W])`

The geometric crux mediating the substrate's PD-intertwining `hadj`: the **naturality of the connecting
homomorphism `∂ : Hₙ(X,S;ℤ) → Hₙ₋₁(S;ℤ)` along the cap product**. For an absolute cocycle `a` and a
relative fundamental class `[W,∂W] ∈ H_{k+d+2}(X,S;ℤ)`,

  `∂ (a ⌢ [W,∂W]) = (-1)ᵏ · ((ι*a) ⌢ ∂[W,∂W])`   in  `H_{d+1}(∂W;ℤ)`,

where `ι*a = pullbackCochainInt a` is the restriction of `a` to `∂W = sub S`, `⌢` on the left is the
integral relative cap `SingularRelativeCapHomologyInt.capRelHInt`, and on the right the absolute cap
`SingularCohomologyInt.capHInt` on `sub S`. This is the boundary-of-a-cap formula, chain-level:
`boundaryExtract (a ⌢ Z) = (-1)ᵏ · ((ι*a) ⌢ boundaryExtract Z)` (`boundaryExtract_capInt`), pushed through
`connectingInt`.

Combined with the banked closed-boundary cup-cap (`kroneckerHInt_cupH24`) on the LHS and the banked
`δ ⊣ ∂` adjunction (`SingularRelativeCohomDeltaInt.relKroneckerHInt_deltaRelHInt`) on the RHS, this is the
final geometric gap of the σ+hcob unlock: the identity
`⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` that couples the boundary intersection form to the pair connecting map.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeCapHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularCapChainInclInt (pullbackCochainInt capInt_chainIncl)

namespace SKEFTHawking.SingularRelativeCapConnectingInt

variable {X : TopCat} {S : Set X} {k d : ℕ}

/-! ## §1. The restriction of an absolute cocycle to the subspace `∂W = sub S` -/

/-- **The restriction `ι* : Hᵏ(X;ℤ) → Hᵏ(∂W;ℤ)` on a cocycle representative.** `pullbackCochainInt a` is
a cocycle on `sub S` when `a` is a cocycle on `X` (`coboundary_pullbackCochainInt` + linearity of the
pullback). The cochain-level ingredient of `ι*`. -/
noncomputable def restrictCocycleInt (a : LinearMap.ker (coboundaryₗ X k)) :
    LinearMap.ker (coboundaryₗ (sub S) k) :=
  ⟨pullbackCochainInt S k a.1, by
    rw [LinearMap.mem_ker]
    show coboundary (sub S) k (pullbackCochainInt S k a.1) = 0
    rw [SKEFTHawking.SingularPullbackDualityCapSubInt.coboundary_pullbackCochainInt,
      show coboundary X k a.1 = coboundaryₗ X k a.1 from rfl, LinearMap.mem_ker.mp a.2]
    rfl⟩

@[simp] theorem restrictCocycleInt_coe (a : LinearMap.ker (coboundaryₗ X k)) :
    (restrictCocycleInt (S := S) a : SingularCochainInt (sub S) k) = pullbackCochainInt S k a.1 :=
  rfl

/-! ## §2. The cap of a relative fundamental cycle is again a lift-cycle -/

/-- **The cap `a ⌢ Z` of a relative-cycle lift `Z` is again a lift-cycle.** `∂(a ⌢ Z) = (-1)ᵏ·(a ⌢ ∂Z)`
(`capInt_cocycle_chainMap`), and `∂Z ∈ C(S)` (`Z ∈ relCycleLift`), so `a ⌢ ∂Z ∈ C(S)`
(`cap_mem_subspaceChainsInt`) — closed under the unit `(-1)ᵏ`. -/
theorem capInt_mem_relCycleLift (a : LinearMap.ker (coboundaryₗ X k))
    (Z : relCycleLift S (k + d + 1)) :
    capInt (m := d + 2) a.1 (Z : SingularChainInt X (k + d + 1 + 1)) ∈ relCycleLift S (d + 1) := by
  show chainBoundary X (d + 1) (capInt (m := d + 2) a.1 (Z : SingularChainInt X (k + d + 1 + 1)))
      ∈ subspaceChainsInt S (d + 1)
  rw [capInt_cocycle_chainMap a.1 (LinearMap.mem_ker.mp a.2)]
  exact Submodule.smul_mem _ _ (cap_mem_subspaceChainsInt a.1 (Submodule.mem_comap.mp Z.2))

/-! ## §3. The cap–boundary identity at the chain level -/

/-- **The cap–boundary formula, chain level.** `boundaryExtract (a ⌢ Z) = (-1)ᵏ · ((ι*a) ⌢ boundaryExtract Z)`
— the boundary of the capped relative cycle is the restriction `ι*a` capped against the boundary cycle
`∂Z = [∂W]`. Proof by `chainIncl`-injectivity: both include to `(-1)ᵏ·(a ⌢ ∂Z)`, via `capInt_cocycle_chainMap`,
`SingularCapChainInclInt.capInt_chainIncl`, and `chainIncl_boundaryExtract`. This is the geometric heart of
the substrate's `hadj`. -/
theorem boundaryExtract_capInt (a : LinearMap.ker (coboundaryₗ X k))
    (Z : relCycleLift S (k + d + 1)) :
    boundaryExtract S (d + 1) ⟨capInt (m := d + 2) a.1 Z, capInt_mem_relCycleLift a Z⟩
      = (-1 : ℤ) ^ k • capInt (m := d + 1) (pullbackCochainInt S k a.1)
          (boundaryExtract S (k + d + 1) Z) := by
  apply chainIncl_injective S (d + 1)
  rw [chainIncl_boundaryExtract, capInt_cocycle_chainMap a.1 (LinearMap.mem_ker.mp a.2), map_smul,
    ← capInt_chainIncl (S := S) (m := d + 1)]
  exact congrArg (fun t => (-1 : ℤ) ^ k • capInt (m := d + 1) a.1 t)
    (chainIncl_boundaryExtract S (k + d + 1) Z).symm

/-! ## §4. The cap–boundary naturality on (co)homology classes — the mediation crux -/

/-- **Cap–boundary naturality of the connecting map** `∂ (a ⌢ [W,∂W]) = (-1)ᵏ · ((ι*a) ⌢ ∂[W,∂W])`.
The relative cap `capRelHInt a` intertwines the pair connecting map `connectingInt` with the absolute cap
`capHInt` on `∂W = sub S` (against the restriction `ι*a`), up to the graded unit `(-1)ᵏ`. Descends
`boundaryExtract_capInt` through `connectingInt_relCycleToHom` / `connectingLift`. The integral core of the
substrate's PD-intertwining `hadj` for `[W,∂W]`-carrying witnesses. -/
theorem connectingInt_capRelHInt (a : LinearMap.ker (coboundaryₗ X k))
    (Z : relCycleLift S (k + d + 1)) :
    connectingInt S (d + 1)
        (capRelHInt (S := S) k (d + 1) (Cohomology.mk X k a) (relCycleToHom S (k + d + 1) Z))
      = (-1 : ℤ) ^ k • capHInt (X := sub S) k d (Cohomology.mk (sub S) k (restrictCocycleInt a))
          (connectingInt S (k + d + 1) (relCycleToHom S (k + d + 1) Z)) := by
  have hcap : capRelHInt (S := S) k (d + 1) (Cohomology.mk X k a) (relCycleToHom S (k + d + 1) Z)
      = relCycleToHom S (d + 1) ⟨capInt (m := d + 2) a.1 Z, capInt_mem_relCycleLift a Z⟩ :=
    rfl
  rw [hcap, connectingInt_relCycleToHom, connectingLift_apply, connectingInt_relCycleToHom,
    connectingLift_apply, capHInt_mk_mk, ← Homology.mk_smul]
  refine congrArg (Homology.mk (sub S) (d + 1)) (Subtype.ext ?_)
  rw [SetLike.val_smul, capCyclesIntₗ_coe, restrictCocycleInt_coe]
  exact boundaryExtract_capInt a Z

end SKEFTHawking.SingularRelativeCapConnectingInt
